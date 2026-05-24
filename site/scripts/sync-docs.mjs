// Render the repo's root markdown as the site's docs WITHOUT moving or editing
// the source files. We copy each surfaced doc into Starlight's content dir
// (generated + git-ignored), deriving the page title from its first `# H1` and
// rewriting cross-doc links to site routes. The root .md files stay the single
// source of truth, exactly where they are.

import { readFileSync, writeFileSync, mkdirSync, rmSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const ROOT = join(here, "..", "..") // repo root: site/scripts -> site -> repo
const OUT = join(here, "..", "src", "content", "docs")

// Which root docs become site pages (AGENTS.md is agent-only — excluded).
const DOCS = [
  { src: "README.md", out: "index.md" }, // home / overview
  { src: "GETTING_STARTED.md", out: "getting-started.md" },
  { src: "TUTORIAL_GREENFIELD.md", out: "tutorials/greenfield.md" },
  { src: "SPEC.md", out: "spec.md" },
  { src: "SPEC_DAFNY.md", out: "spec-dafny.md" },
  { src: "SPEC_LEAN.md", out: "spec-lean.md" },
  { src: "TOOLS.md", out: "tools.md" },
  { src: "DESIGN.md", out: "design.md" },
  { src: "ARCHITECTURE_NARROWING.md", out: "architecture-narrowing.md" },
]

// filename -> site route, for rewriting cross-doc links so site nav works.
const ROUTES = {
  "README.md": "/",
  "GETTING_STARTED.md": "/getting-started/",
  "TUTORIAL_GREENFIELD.md": "/tutorials/greenfield/",
  "SPEC.md": "/spec/",
  "SPEC_DAFNY.md": "/spec-dafny/",
  "SPEC_LEAN.md": "/spec-lean/",
  "TOOLS.md": "/tools/",
  "DESIGN.md": "/design/",
  "ARCHITECTURE_NARROWING.md": "/architecture-narrowing/",
}

function titleAndBody(md) {
  const lines = md.split("\n")
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]
    const m = line.match(/^#\s+(.+?)\s*$/)
    if (m) {
      let start = i + 1
      while (start < lines.length && lines[start].trim() === "") start++
      return { title: m[1], body: lines.slice(start).join("\n") }
    }
    if (line.trim() !== "") break // content before any H1 — don't strip anything
  }
  return { title: "LemmaScript", body: md }
}

function rewriteLinks(md) {
  let out = md
  for (const [file, route] of Object.entries(ROUTES)) {
    const esc = file.replace(/\./g, "\\.")
    // ](file) or ](./file), optionally with a #section anchor (preserved)
    const re = new RegExp(`\\]\\((?:\\./)?${esc}(#[^)]*)?\\)`, "g")
    out = out.replace(re, (_m, anchor = "") => `](${route}${anchor})`)
  }
  return out
}

const esc = (s) => s.replace(/"/g, '\\"')

rmSync(OUT, { recursive: true, force: true })
mkdirSync(OUT, { recursive: true })

for (const { src, out } of DOCS) {
  const raw = readFileSync(join(ROOT, src), "utf8")
  const { title, body } = titleAndBody(raw)
  const target = join(OUT, out)
  mkdirSync(dirname(target), { recursive: true })
  writeFileSync(target, `---\ntitle: "${esc(title)}"\n---\n\n${rewriteLinks(body)}`)
}

console.log(`synced ${DOCS.length} docs → site/src/content/docs/`)
