import VersoBlog


namespace Berso

open Verso.Genre.Blog

open Verso Verso.Doc Verso.Output Verso.Output.Html Verso.Doc.Html Verso.Doc.Html.HtmlT Verso.FS
open Verso.Code.Hover renaming State → State
open Verso.Code renaming LinkTargets → LinkTargets
open Verso.Genre.Blog.Generate
open Verso.Genre.Blog.Template.Params renaming forPart → forPart


def writePage (theme : Theme) (params : Template.Params) (template : Template := theme.pageTemplate) : GenerateM Unit := do
  ensureDir <| (← currentDir)
  let ⟨baseTemplate, modParams⟩ := theme.adHocTemplates (Array.mk (← currentPath)) |>.getD ⟨template, id⟩
  let output ← rewriteOutput <| ← Template.renderMany [baseTemplate, theme.primaryTemplate] <| modParams <| params
  let header := (← read).header
  IO.FS.withFile ((← currentDir).join "index.html") .write fun h => do
    h.putStrLn header
    h.putStrLn output.asString
  let headerOutput ← rewriteOutput <| ← Template.render Template.builtinHeader <| modParams <| params
  IO.FS.withFile ((← currentDir).join "index-head.html") .write fun h => do
    h.putStrLn headerOutput.asString

def writeBlog (theme : Theme) (id : Lean.Name) (txt : Part Page) (posts : Array BlogPost) : GenerateM Unit := do
  for post in posts do
    if post.contents.metadata.map (·.draft) == some true && !(← showDrafts) then continue

    inPost post do
      IO.println s!"Generating post {← currentDir}"
      let postParams : Template.Params ← match post.contents.metadata with
        | none => forPart post.contents
        | some md => (·.insert "metadata" ⟨.mk md, #[]⟩) <$> forPart post.contents
      writePage theme postParams (template := theme.postTemplate)

  let «meta» ←
    match (← read).xref.blogs.find? id with
    | none => logError s!"Blog {id} not found in traverse pass!"; pure {}
    | some «meta» => pure «meta»

  for (cat, contents) in meta.categories.toArray.qsort (·.1.name < ·.1.name) do
    withReader (fun c => {c with ctxt.path := c.ctxt.path ++ [cat.slug]}) <| do
      IO.println s!"Generating category page {← currentDir}"
      let catPosts ← contents.toList.filterMapM (m := GenerateM) fun postId => do
        let some addr := (← read).xref.pageIds.find? postId
          | pure none
        let some post := posts.find? (·.id == postId)
          | pure none
        pure <| some (addr, post)
      let postList := {{
        <ul class="post-list">
          {{← catPosts.mapM fun (_addr, p) => do
            theme.archiveEntryTemplate.render (.ofList [("path", ⟨.mk "..", #[]⟩), ("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
        </ul>
      }}
      let catParams := Template.Params.ofList [("title", cat.name), ("category", ⟨.mk cat, #[]⟩), ("posts", ⟨.mk postList, #[]⟩)]
      writePage theme catParams (template := theme.categoryTemplate)

  let postList := {{
    <ul class="post-list">
      {{← posts.mapM fun p => do
        theme.archiveEntryTemplate.render (.ofList [("post", ⟨.mk p, #[]⟩), ("summary", ⟨.mk (← summarize p), #[]⟩)])}}
    </ul>
  }}
  let allCats : Post.Categories := .mk <| meta.categories.toArray.map fun (c, _) =>
    (c.slug, c)
  let pageParams : Template.Params := (← forPart txt).insert "posts" ⟨.mk postList, #[]⟩ |>.insert "categories" ⟨.mk allCats, #[]⟩
  writePage theme pageParams
where
  summarize (p : BlogPost) : GenerateM Html := do
    Html.seq <$> p.summary.mapM (GenerateM.toHtml Post)


partial def Dir.generate (theme : Theme) (dir : Dir) : GenerateM Unit :=
  inDir dir <|
  match dir with
  | .page _ _ txt subPages => do
    IO.println s!"Generating page '{← currentDir}'"
    -- TODO more configurable template context
    writePage theme (← forPart txt)
    for p in subPages do
      Berso.Dir.generate theme p
  | .blog _ id txt posts => do
    IO.println s!"Generating blog section '{← currentDir}'"
    writeBlog theme id txt posts
  | .static _ file => do
    IO.println s!"Copying from static '{file}' to '{(← currentDir)}'"
    let dest ← currentDir
    if ← dest.pathExists then
      if ← dest.isDir then
        IO.FS.removeDirAll dest
      else
        IO.FS.removeFile dest
    copyRecursively (← currentConfig).logError file dest

def Site.generate (theme : Theme) (site : Site) : GenerateM Unit := do
  match site with
  | .page _ txt subPages =>
    writePage theme (← forPart txt)
    for p in subPages do
      Berso.Dir.generate theme p
  | .blog id txt posts =>
    writeBlog theme id txt posts

open Template in
def blogMain (theme : Theme) (site : Site) (relativizeUrls := true) (linkTargets : Code.LinkTargets TraverseContext := {})
    (options : List String) (components : Components := by exact %registered_components)
    (header : String := Html.doctype) :
    IO UInt32 := do
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg ← opts {logError := logError} options
  let (site, xref) ← site.traverse cfg components
  let rw := if relativizeUrls then
      some <| relativize
    else none
  let initGenCtx : Generate.Context := {
    site := site,
    ctxt := { path := [], config := cfg, components },
    xref := xref,
    dir := cfg.destination,
    config := cfg,
    header := header,
    rewriteHtml := rw,
    linkTargets := linkTargets,
    components := components
  }
  let (((), st), _) ← Berso.Site.generate theme site initGenCtx .empty {}
  IO.FS.writeFile (cfg.destination.join "-verso-docs.json") (toString st.dedup.docJson)
  for (name, content, sourceMap?) in xref.jsFiles do
    FS.ensureDir (cfg.destination.join "-verso-js")
    IO.FS.writeFile (cfg.destination.join "-verso-js" |>.join name) content
    if let some (name, content) := sourceMap? then
      IO.FS.writeFile (cfg.destination.join "-verso-js" |>.join name) content
  for (name, content) in xref.cssFiles do
    FS.ensureDir (cfg.destination.join "-verso-css")
    IO.FS.writeFile (cfg.destination.join "-verso-css" |>.join name) content
  if (← hasError.get) then
    IO.eprintln "Errors were encountered!"
    return 1
  else
    return 0
where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--drafts"::more) => opts {cfg with showDrafts := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg
  urlAttr (name : String) : Bool := name ∈ ["href", "src", "data", "poster"]
  rwAttr (attr : String × String) : ReaderT TraverseContext Id (String × String) := do
    if urlAttr attr.fst && "/".isPrefixOf attr.snd then
      let path := (← read).path
      pure { attr with
        snd := String.join (List.replicate path.length "../") ++ attr.snd.drop 1
      }
    else
      pure attr
  rwTag (tag : String) (attrs : Array (String × String)) (content : Html) : ReaderT TraverseContext Id (Option Html) := do
    pure <| some <| .tag tag (← attrs.mapM rwAttr) content
  relativize _err ctxt html :=
    pure <| html.visitM (m := ReaderT TraverseContext Id) (tag := rwTag) |>.run ctxt

end Berso
