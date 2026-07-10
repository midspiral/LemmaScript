# LemmaScript website

The [docs.lemmascript.org](https://docs.lemmascript.org) site — [Astro](https://astro.build) +
[Starlight](https://starlight.astro.build), deployed to GitHub Pages.

## The docs are the repo's root markdown

Edit the canonical docs **at the repo root** (`README.md`, `SPEC.md`, `GETTING_STARTED.md`,
`TUTORIAL.md`, …). `scripts/sync-docs.mjs` (run automatically before `dev`/`build`) renders
them into Starlight's content dir — deriving each page title from its first `# H1`, mapping
`README.md` to the home, and rewriting cross-doc links. The generated `src/content/docs/` is
git-ignored; never edit it by hand.

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
