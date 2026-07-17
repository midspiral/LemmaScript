import { defineConfig } from "astro/config"
import starlight from "@astrojs/starlight"
import starlightLinksValidator from "starlight-links-validator"
import { visit } from "unist-util-visit"
import { existsSync, statSync } from "node:fs"
import { fileURLToPath } from "node:url"
import { join } from "node:path"

// The synced docs (see scripts/sync-docs.mjs) keep their repo-relative links —
// doc-to-doc links are rewritten to site routes there, but links into the repo
// itself (e.g. examples/, lakefile.lean) survive as relative paths that would 404
// on the site. Rewrite those to absolute GitHub URLs at render time. By the
// time we see an href, routed doc links are already absolute (/spec/), so we
// only touch genuinely repo-relative targets.
const REPO_ROOT = fileURLToPath(new URL("../", import.meta.url))
const GH = "https://github.com/midspiral/LemmaScript"
const BRANCH = "main"

function rehypeRepoLinks() {
  return (tree) => {
    visit(tree, "element", (node) => {
      if (node.tagName !== "a") return
      const href = node.properties?.href
      if (typeof href !== "string" || href === "") return
      if (/^(https?:|mailto:|tel:|#|\/)/.test(href)) return // external / anchor / already-routed

      const [rawPath, anchor] = href.split("#")
      const path = rawPath.replace(/^\.\//, "")
      const abs = join(REPO_ROOT, path)
      if (!existsSync(abs)) {
        // Missing targets are the build-failing concern, but a throw here is
        // useless: it runs inside content rendering, where Starlight's loader
        // catches it per-page, drops the page, and lets the build limp on to a
        // misleading link-validator cascade (e.g. "/spec/ invalid"). The real
        // gate lives in sync-docs.mjs (prebuild), which fails before Astro
        // starts. This is just a backstop warning.
        console.warn(`[rehypeRepoLinks] link target not found in repo: ${href}`)
      }
      const kind = existsSync(abs) && statSync(abs).isDirectory() ? "tree" : "blob"
      node.properties.href = `${GH}/${kind}/${BRANCH}/${path}${anchor ? "#" + anchor : ""}`
    })
  }
}

// Cross-doc links written lazily as `[SPEC.md](SPEC.md)` in the source markdown
// arrive here already routed (sync-docs rewrote the href to /spec/) but still
// showing the bare filename as text. Swap that filename for a human name. We
// only touch links whose visible text IS a bare *.md filename, so intentional
// text like `[SPEC.md §2]` or `[TOOLS.md#narrow-rules]` is left untouched.
const LINK_NAMES = {
  "/case-studies/": "Case studies & examples",
  "/subset/": "Supported TypeScript subset",
  "/getting-started/": "Getting started in an existing codebase",
  "/howto_greenfield/": "Start a new project",
  "/spec/": "Specification",
  "/spec-dafny/": "Dafny backend spec",
  "/spec-lean/": "Lean backend spec",
  "/tools/": "Toolchain architecture",
  "/design/": "Design",
  "/architecture-narrowing/": "Narrowing architecture",
  "/agents/": "Guidance for agents",
}
const BARE_FILENAME = /^[A-Za-z0-9_]+\.md$/

function rehypeLinkNames() {
  return (tree) => {
    visit(tree, "element", (node) => {
      if (node.tagName !== "a") return
      const href = node.properties?.href
      if (typeof href !== "string" || !href.startsWith("/")) return
      const name = LINK_NAMES[href.split("#")[0]]
      if (!name) return
      const kids = node.children
      if (kids.length !== 1 || kids[0].type !== "text" || !BARE_FILENAME.test(kids[0].value)) return
      node.children = [{ type: "text", value: name }]
    })
  }
}

// https://astro.build/config
export default defineConfig({
  site: "https://docs.lemmascript.org",
  markdown: { rehypePlugins: [rehypeRepoLinks, rehypeLinkNames] },
  integrations: [
    starlight({
      customCss: ["./src/styles/custom.css"],
      plugins: [starlightLinksValidator()],
      favicon: "/favicon.svg",
      title: "LemmaScript",
      description: "A verification toolchain for TypeScript — generate Lean 4 or Dafny from annotated code.",
      social: [{ icon: "github", label: "GitHub", href: "https://github.com/midspiral/LemmaScript" }],
      sidebar: [
        {
          label: "Start here",
          items: [
            { label: "What is LemmaScript?", link: "/" },
            { label: "Installation", link: "/installation/" },
            { label: "How the loop works", link: "/how-the-loop-works/" },
            { label: "How to: Brownfield", link: "/getting-started/" },
          ],
        },
        {
          label: "Tutorials",
          items: [
            {
              label: "Quorum (Beginner)",
              items: [
                { label: "Introduction", link: "/tutorials/quorum/00-introduction/" },
                { label: "Step 1: Environment Setup", link: "/tutorials/quorum/01-setup/" },
                { label: "Step 2: The Design Document", link: "/tutorials/quorum/02-design/" },
                { label: "Step 3: Build the Domain Core", link: "/tutorials/quorum/03-domain-core/" },
                { label: "Step 4: Verify the Domain", link: "/tutorials/quorum/04-verify/" },
                { label: "Step 5: Check Your Guarantees", link: "/tutorials/quorum/05-proof-review/" },
                { label: "Step 6: The UI Layer", link: "/tutorials/quorum/06-ui-layer/" },
                { label: "Step 7: Adding a Verified Feature", link: "/tutorials/quorum/07-iteration/" },
              ],
            },
          ],
        },
        {
          label: "Reference",
          items: [
            { label: "CLI (lsc)", link: "/reference/cli/" },
            { label: "Supported TypeScript subset", link: "/subset/" },
            { label: "Specification", link: "/spec/" },
            { label: "Dafny backend", link: "/spec-dafny/" },
            { label: "Lean backend", link: "/spec-lean/" },
          ],
        },
        {
          label: "Under the hood",
          items: [
            { label: "Design rationale", link: "/design/" },
            { label: "Toolchain architecture", link: "/tools/" },
            { label: "Architecture: narrowing", link: "/architecture-narrowing/" },
            { label: "Guidance for agents", link: "/agents/" },
            { label: "Case studies & examples", link: "/case-studies/" },
          ],
        },
      ],
    }),
  ],
})
