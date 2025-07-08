
window.onload = () => {

    // Don't show hovers inside of closed tactic states
    function blockedByTactic(elem) {
      let parent = elem.parentNode;
      while (parent && "classList" in parent) {
        if (parent.classList.contains("tactic")) {
          const toggle = parent.querySelector("input.tactic-toggle");
          if (toggle) {
            return !toggle.checked;
          }
        }
        parent = parent.parentNode;
      }
      return false;
    }

    function blockedByTippy(elem) {
      // Don't show a new hover until the old ones are all closed.
      // Scoped to the nearest "top-level block" to avoid being O(n) in the size of the document.
      var block = elem;
      const topLevel = new Set(["section", "body", "html", "nav", "header"]);
      while (block.parentNode && !topLevel.has(block.parentNode.nodeName.toLowerCase())) {
        block = block.parentNode;
      }
      for (const child of block.querySelectorAll(".token, .has-info")) {
        if (child._tippy && child._tippy.state.isVisible) { return true };
      }
      return false;
    }

    for (const c of document.querySelectorAll(".hl.lean .token")) {
        if (c.dataset.binding != "") {
            c.addEventListener("mouseover", (event) => {
                if (blockedByTactic(c)) {return;}
                const context = c.closest(".hl.lean").dataset.leanContext;
                for (const example of document.querySelectorAll(".hl.lean")) {
                    if (example.dataset.leanContext == context) {
                        for (const tok of example.querySelectorAll(".token")) {
                            if (c.dataset.binding == tok.dataset.binding) {
                                tok.classList.add("binding-hl");
                            }
                        }
                    }
                }
            });
        }
        c.addEventListener("mouseout", (event) => {
            for (const tok of document.querySelectorAll(".hl.lean .token")) {
                tok.classList.remove("binding-hl");
            }
        });
    }
    /* Render docstrings */
    if ('undefined' !== typeof marked) {
        for (const d of document.querySelectorAll("code.docstring, pre.docstring")) {
            const str = d.innerText;
            const html = marked.parse(str);
            const rendered = document.createElement("div");
            rendered.classList.add("docstring");
            rendered.innerHTML = html;
            d.parentNode.replaceChild(rendered, d);
        }
    }
    // Add hovers
    let siteRoot = typeof __versoSiteRoot !== 'undefined' ? __versoSiteRoot : "/";
    let docsJson = siteRoot + "-verso-docs.json";
    fetch(docsJson).then((resp) => resp.json()).then((versoDocData) => {

      function hideParentTooltips(element) {
        let parent = element.parentElement;
        while (parent) {
          const tippyInstance = parent._tippy;
          if (tippyInstance) {
            tippyInstance.hide();
          }
          parent = parent.parentElement;
        }
      }



      const defaultTippyProps = {
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: "click",
        // */
        /* theme: "lean", */
        maxWidth: "none",
        appendTo: () => document.body,
        interactive: true,
        delay: [100, null],
        /* ignoreAttributes: true, */
        followCursor: 'initial',
        onShow(inst) {
          if (inst.reference.className == 'tactic') {

            const toggle = inst.reference.querySelector("input.tactic-toggle");
            if (toggle && toggle.checked) {
              return false;
            }
            hideParentTooltips(inst.reference);
            //if (blockedByTippy(inst.reference)) { return false; }

          } else if (inst.reference.querySelector(".hover-info") || "versoHover" in inst.reference.dataset) {
            if (blockedByTactic(inst.reference)) { return false };
            if (blockedByTippy(inst.reference)) { return false; }
          } else { // Nothing to show here!
            return false;
          }
        },
        content (tgt) {
          const content = document.createElement("span");
          if (tgt.className == 'tactic') {
            const state = tgt.querySelector(".tactic-state").cloneNode(true);
            state.style.display = "block";
            content.appendChild(state);
            content.style.display = "block";
            content.className = "hl lean popup";
          } else {
            content.className = "hl lean";
            content.style.display = "block";
            content.style.maxHeight = "300px";
            content.style.overflowY = "auto";
            content.style.overflowX = "hidden";
            const hoverId = tgt.dataset.versoHover;
            const hoverInfo = tgt.querySelector(".hover-info");
            if (hoverId) { // Docstrings from the table
              // TODO stop doing an implicit conversion from string to number here
              let data = versoDocData[hoverId];
              if (data) {
                const info = document.createElement("span");
                info.className = "hover-info";
                info.style.display = "block";
                info.innerHTML = data;
                content.appendChild(info);
                /* Render docstrings - TODO server-side */
                if ('undefined' !== typeof marked) {
                    for (const d of content.querySelectorAll("code.docstring, pre.docstring")) {
                        const str = d.innerText;
                        const html = marked.parse(str);
                        const rendered = document.createElement("div");
                        rendered.classList.add("docstring");
                        rendered.innerHTML = html;
                        d.parentNode.replaceChild(rendered, d);
                    }
                }
              } else {
                content.innerHTML = "Failed to load doc ID: " + hoverId;
              }
            } else if (hoverInfo) { // The inline info, still used for compiler messages
              content.appendChild(hoverInfo.cloneNode(true));
            }
            const extraLinks = tgt.parentElement.dataset['versoLinks'];
            if (extraLinks) {
              try {
                const extras = JSON.parse(extraLinks);
                const links = document.createElement('ul');
                links.className = 'extra-doc-links';
                extras.forEach((l) => {
                  const li = document.createElement('li');
                  li.innerHTML = "<a href=\"" + l['href'] + "\" title=\"" + l.long + "\">" + l.short + "</a>";
                  links.appendChild(li);
                });
                content.appendChild(links);
              } catch (error) {
                console.error(error);
              }
            }
          }
          return content;
        }
      };


      document.querySelectorAll('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort').forEach(element => {
        element.setAttribute('data-tippy-theme', 'lean');
      });
      document.querySelectorAll('.hl.lean .has-info.warning').forEach(element => {
        element.setAttribute('data-tippy-theme', 'warning message');
      });
      document.querySelectorAll('.hl.lean .has-info.info').forEach(element => {
        element.setAttribute('data-tippy-theme', 'info message');
      });
      document.querySelectorAll('.hl.lean .has-info.error').forEach(element => {
        element.setAttribute('data-tippy-theme', 'error message');
      });
      document.querySelectorAll('.hl.lean .tactic').forEach(element => {
        element.setAttribute('data-tippy-theme', 'tactic');
      });
      let insts = tippy('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .has-info, .hl.lean .tactic, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort', defaultTippyProps);
  });
}