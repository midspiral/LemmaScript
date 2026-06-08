// Render the repo's root markdown as the site's docs WITHOUT moving or editing
// the source files. We copy each surfaced doc into Starlight's content dir
// (generated + git-ignored), deriving the page title from its first `# H1` and
// rewriting cross-doc links to site routes. The root .md files stay the single
// source of truth, exactly where they are.

import { readFileSync, writeFileSync, mkdirSync, rmSync, existsSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const ROOT = join(here, "..", "..") // repo root: site/scripts -> site -> repo
const OUT = join(here, "..", "src", "content", "docs")

// Which root docs become site pages.
const DOCS = [
  { src: "README.md", out: "index.md" }, // home / overview
  { src: "SUBSET.md", out: "subset.md" },
  { src: "GETTING_STARTED.md", out: "getting-started.md" },
  { src: "TUTORIAL_GREENFIELD.md", out: "howto_greenfield.md" },
  { src: "SPEC.md", out: "spec.md" },
  { src: "SPEC_DAFNY.md", out: "spec-dafny.md" },
  { src: "SPEC_LEAN.md", out: "spec-lean.md" },
  { src: "TOOLS.md", out: "tools.md" },
  { src: "DESIGN.md", out: "design.md" },
  { src: "ARCHITECTURE_NARROWING.md", out: "architecture-narrowing.md" },
  { src: "AGENTS.md", out: "agents.md" },
]

// filename -> site route, for rewriting cross-doc links so site nav works.
const ROUTES = {
  "README.md": "/",
  "SUBSET.md": "/subset/",
  "GETTING_STARTED.md": "/getting-started/",
  "TUTORIAL_GREENFIELD.md": "/howto_greenfield/",
  "SPEC.md": "/spec/",
  "SPEC_DAFNY.md": "/spec-dafny/",
  "SPEC_LEAN.md": "/spec-lean/",
  "TOOLS.md": "/tools/",
  "DESIGN.md": "/design/",
  "ARCHITECTURE_NARROWING.md": "/architecture-narrowing/",
  "AGENTS.md": "/agents/",
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

// After cross-doc links are rewritten to /routes/, the only remaining relative
// `](target)` links point into the repo (e.g. examples/foo.ts, lakefile.lean).
// If such a target doesn't exist (e.g. a doc references a file that was never
// committed), the failure otherwise surfaces only as a baffling downstream
// "invalid link" cascade from the link validator: the render-time check in
// astro.config's rehypeRepoLinks throws, but Starlight's content loader catches
// that per-page, drops the page, and lets the build continue — so the page that
// *links to* the dropped page is what gets flagged. We catch it here instead,
// in the prebuild, where a throw aborts cleanly and names the offending doc.
const REPO_LINK = /\]\((?!https?:|mailto:|tel:|#|\/)([^)\s]+)\)/g
function missingRepoLinks(src, md) {
  const missing = []
  for (const [, raw] of md.matchAll(REPO_LINK)) {
    const target = raw.split("#")[0].replace(/^\.\//, "")
    if (target && !existsSync(join(ROOT, target))) missing.push(`${src} → ${target}`)
  }
  return missing
}

// Remove only the generated docs, not the whole dir, so manually-added pages survive.
for (const d of DOCS) rmSync(join(OUT, d.out), { force: true })
mkdirSync(OUT, { recursive: true })

const broken = []
for (const { src, out } of DOCS) {
  const raw = readFileSync(join(ROOT, src), "utf8")
  const { title, body } = titleAndBody(raw)
  const rewritten = rewriteLinks(body)
  broken.push(...missingRepoLinks(src, rewritten))
  const target = join(OUT, out)
  mkdirSync(dirname(target), { recursive: true })
  writeFileSync(target, `---\ntitle: "${esc(title)}"\n---\n\n${rewritten}`)
}

if (broken.length) {
  const msg = `[sync-docs] ${broken.length} broken repo-relative doc link(s) — target file not found:\n  ${broken.join("\n  ")}`
  if (process.env.CI) throw new Error(`${msg}\nCommit the missing file or fix the link.`)
  console.warn(`${msg}\n(warning only; this would fail the build in CI)`)
}

console.log(`synced ${DOCS.length} docs → site/src/content/docs/`)
