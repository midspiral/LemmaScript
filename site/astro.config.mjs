import { defineConfig } from "astro/config"
import starlight from "@astrojs/starlight"
import { visit } from "unist-util-visit"
import { existsSync, statSync } from "node:fs"
import { fileURLToPath } from "node:url"
import { join } from "node:path"

// The synced docs (see scripts/sync-docs.mjs) keep their repo-relative links —
// doc-to-doc links are rewritten to site routes there, but links into the repo
// itself (e.g. examples/, AGENTS.md) survive as relative paths that would 404
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
        console.warn(`[rehypeRepoLinks] link target not found in repo: ${href}`)
      }
      const kind = existsSync(abs) && statSync(abs).isDirectory() ? "tree" : "blob"
      node.properties.href = `${GH}/${kind}/${BRANCH}/${path}${anchor ? "#" + anchor : ""}`
    })
  }
}

// https://astro.build/config
export default defineConfig({
  site: "https://lemmascript.com",
  markdown: { rehypePlugins: [rehypeRepoLinks] },
  integrations: [
    starlight({
      title: "LemmaScript",
      description: "A verification toolchain for TypeScript — generate Lean 4 or Dafny from annotated code.",
      social: [{ icon: "github", label: "GitHub", href: "https://github.com/midspiral/LemmaScript" }],
      sidebar: [
        { label: "Getting started", link: "/getting-started/" },
        {
          label: "Tutorials",
          items: [{ label: "Build a verified app (greenfield)", link: "/tutorials/greenfield/" }],
        },
        {
          label: "Specification",
          items: [
            { label: "Overview", link: "/spec/" },
            { label: "Dafny backend", link: "/spec-dafny/" },
            { label: "Lean backend", link: "/spec-lean/" },
          ],
        },
        { label: "Tools", link: "/tools/" },
        {
          label: "Design",
          items: [
            { label: "Design rationale", link: "/design/" },
            { label: "Architecture: narrowing", link: "/architecture-narrowing/" },
          ],
        },
      ],
    }),
  ],
})
