# LemmaScript website

The [docs.lemmascript.org](https://docs.lemmascript.org) site — [Astro](https://astro.build) +
[Starlight](https://starlight.astro.build), deployed to GitHub Pages.

## The docs are the repo's root markdown

Edit the canonical docs **at the repo root** (`CASE_STUDIES.md`, `SPEC.md`,
`GETTING_STARTED.md`, `TUTORIAL_GREENFIELD.md`, …). `scripts/sync-docs.mjs` (run automatically
before `dev`/`build`) renders them into Starlight's content dir — deriving each page title
from its first `# H1` unless overridden and rewriting cross-doc links. `CASE_STUDIES.md`
maps to `/case-studies/`; links to `README.md` point to the
[GitHub repo](https://github.com/midspiral/LemmaScript), preserving section anchors.
These generated files in `src/content/docs/` are git-ignored; edit their root sources.
The homepage and tutorials are hand-written in `src/content/docs/`.

### Adding a new root doc

To surface a new `FOO.md` (with route `/foo/`), edit four places:

1. **`scripts/sync-docs.mjs` → `DOCS`** — `{ src: "FOO.md", out: "foo.md" }`, so the doc gets rendered into the content dir.
2. **`scripts/sync-docs.mjs` → `ROUTES`** — `"FOO.md": "/foo/"`, so cross-doc links *to* it are rewritten from the filename to the site route.
3. **`astro.config.mjs` → `sidebar`** — add a `{ label, link: "/foo/" }` entry so it appears in the nav.
4. **`astro.config.mjs` → `LINK_NAMES`** — `"/foo/": "Foo"`, so lazy `[FOO.md](FOO.md)` links render with a human name instead of the bare filename.

## Develop

```sh
npm install
npm run dev        # http://localhost:4321
npm run build      # static site → dist/
```

## Deploy

Pushing to `main` triggers `.github/workflows/site.yml`, which builds and deploys to GitHub
Pages. No manual step.

## Custom domain (docs.lemmascript.org)

`public/CNAME` pins the domain. One-time DNS + repo setup:

- **`docs` `CNAME`** → `midspiral.github.io`
- Repo **Settings → Pages**: set the custom domain to `docs.lemmascript.org` and tick **Enforce HTTPS** (served over HTTPS via the auto-provisioned cert).
