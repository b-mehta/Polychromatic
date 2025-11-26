import VersoBlog

open Verso Genre Blog

section

open Verso Doc Output Html Concrete ToHtml Elab Monad Template ArgParse Lean.Quote

inline_component footnote where
  toHtml _ _ goI contents := do
    pure {{<span class="footnote">{{← contents.mapM goI}}</span>}}

@[role_expander footnote]
def footnoteImpl : RoleExpander
  | _, stxs => do pure #[← ``(footnote #[$(← stxs.mapM elabInline),*])]

block_component exercise where
  toHtml _ _ _goI goB contents := do
    pure {{
      <details class="auto-number">
        <summary></summary>
        {{← contents.mapM goB}}
      </details>
    }}

@[directive_expander exercise]
def exerciseImpl : DirectiveExpander
  | _, stxs => do
    let contents ← stxs.mapM elabBlock
    let val ← ``(exercise #[ $contents,* ])
    pure #[val]

block_component aside (title : String) where
  toHtml _ _ _goI goB contents := do
    pure {{
      <details>
        <summary>{{title}}</summary>
        {{← contents.mapM goB}}
      </details>
    }}

@[directive_expander aside]
def asideImpl : DirectiveExpander
  | args, stxs => do
    let title ← ArgParse.run (.positional `asideTitle .string) args
    let contents ← stxs.mapM elabBlock
    let val ← ``(aside $(quote title) #[ $contents,* ])
    pure #[val]

def mermaidJs : String := "mermaid.initialize({
startOnLoad: true,
htmlLabels: true,
});"

block_component graph (data : String) where
  toHtml _ _ _ _ _ := do
    pure {{<pre class="mermaid" markdown="0">{{ Html.text false data }}</pre>}}
  jsFiles := #[("mermaid-init.js", mermaidJs)]

@[code_block graph]
def graphImpl : CodeBlockExpanderOf Unit
  | _, stxs => do
    let val ← ``(graph $(quote stxs.getString) #[])
    pure val

end
