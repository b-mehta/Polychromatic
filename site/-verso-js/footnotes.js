document.addEventListener('DOMContentLoaded', () => {
  initSmoothScroll();
  initFootnotes();
});

/**
 * Initializes smooth scrolling and highlighting for on-page anchor links.
 */
function initSmoothScroll() {
  document.body.addEventListener('click', (e) => {
    // Find the nearest ancestor link that points to an on-page anchor
    const link = e.target.closest('a[href^="#"]');
    if (!link?.hash || link.hash === '#') return;

    let targetElement;
    try {
      // Use decodeURIComponent to handle special characters in IDs
      targetElement = document.querySelector(decodeURIComponent(link.hash));
    } catch (error) {
      console.warn(`Invalid selector for href: ${link.hash}`, error);
      return;
    }
    if (!targetElement) return;

    e.preventDefault();

    let elementToFocus = targetElement;

    // Special handling for footnote back-links for a better focus experience
    if (link.hasAttribute('data-footnote-backlink')) {
      const parentListItem = link.closest('li[data-footnote-ref]');
      if (parentListItem) {
        // Find the original footnote reference (e.g., [1]) in the main content
        const originalRefLink = targetElement.querySelector(`a[href="#${parentListItem.id}"]`);
        if (originalRefLink) {
          elementToFocus = originalRefLink;
        }
      }
    }

    // Re-trigger CSS animation if element is already highlighted
    if (targetElement.classList.contains('footnote-highlight')) {
      targetElement.classList.remove('footnote-highlight');
      void targetElement.offsetWidth; // Force browser reflow
    }
    targetElement.classList.add('footnote-highlight');

    targetElement.scrollIntoView({ behavior: 'smooth', block: 'start' });

    // Manage focus for accessibility
    elementToFocus.setAttribute('tabindex', -1);
    elementToFocus.focus({ preventScroll: true });

    // Clean up after animation
    targetElement.addEventListener('animationend', () => {
      targetElement.classList.remove('footnote-highlight');
      elementToFocus.removeAttribute('tabindex');
    }, { once: true });
  });
}

/**
 * Finds all footnote spans, converts them to links, and generates a
 * footnote list at the bottom of the page.
 * This version is more robust, accessible, and maintainable.
 */
function initFootnotes() {
  const footnoteSpans = document.querySelectorAll('span.footnote');
  const container = document.getElementById('footnotes-container');

  if (!container || footnoteSpans.length === 0) {
    if (container) container.style.display = 'none';
    return;
  }

  const footnotesList = document.createElement('ol');
  const fragment = document.createDocumentFragment();

  footnoteSpans.forEach((span, index) => {
    const i = index + 1;
    const footnoteId = `footnote-ref-${i}`;

    // 1. Create the superscript reference link (e.g., [1]) in the text
    const refLink = document.createElement('sup');
    refLink.innerHTML = `<a href="#${footnoteId}" aria-describedby="footnotes-label">[${i}]</a>`;

    // 2. Create the footnote list item
    const listItem = document.createElement('li');
    listItem.id = footnoteId;
    listItem.dataset.footnoteRef = ''; // Marker for initSmoothScroll
    listItem.append(...span.childNodes);

    // 3. Create a back-link (↩) if a suitable parent block is found
    const parentBlock = span.closest('p, li, blockquote, div, section, article');
    if (parentBlock) {
      const sourceId = `footnote-source-${i}`;
      if (!parentBlock.id) {
        parentBlock.id = sourceId;
      }

      const backLink = document.createElement('a');
      backLink.href = `#${parentBlock.id}`;
      backLink.textContent = ' ↩';
      backLink.setAttribute('aria-label', 'Back to content');
      backLink.dataset.footnoteBacklink = ''; // Marker for initSmoothScroll
      listItem.appendChild(backLink);
    }

    fragment.appendChild(listItem);
    span.replaceWith(refLink);
  });

  footnotesList.appendChild(fragment);

  // 4. Create the main "Footnotes" heading
  const heading = document.createElement('h2');
  heading.id = 'footnotes-label'; // For the aria-describedby attribute
  heading.textContent = 'Footnotes';

  container.append(heading, footnotesList);
}