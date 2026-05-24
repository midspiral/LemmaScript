# LemmaScript website

The [lemmascript.com](https://lemmascript.com) site — [Astro](https://astro.build) +
[Starlight](https://starlight.astro.build), deployed to GitHub Pages.

## The docs are the repo's root markdown

Edit the canonical docs **at the repo root** (`README.md`, `SPEC.md`, `GETTING_STARTED.md`,
`TUTORIAL.md`, …). `scripts/sync-docs.mjs` (run automatically before `dev`/`build`) renders
them into Starlight's content dir — deriving each page title from its first `# H1`, mapping
`README.md` to the home, and rewriting cross-doc links. The generated `src/content/docs/` is
git-ignored; never edit it by hand.

To surface a new root doc: add it to `DOCS` (and `ROUTES`) in `scripts/sync-docs.mjs` and to
the `sidebar` in `astro.config.mjs`.

## Develop

```sh
npm install
npm run dev        # http://localhost:4321
npm run build      # static site → dist/
```

## Deploy

Pushing to `main` triggers `.github/workflows/site.yml`, which builds and deploys to GitHub
Pages. No manual step.

## Custom domain (lemmascript.com)

`public/CNAME` pins the domain. One-time DNS + repo setup:

- **Apex `A`** → `185.199.108.153`, `185.199.109.153`, `185.199.110.153`, `185.199.111.153`
- **Apex `AAAA`** → `2606:50c0:8000::153`, `2606:50c0:8001::153`, `2606:50c0:8002::153`, `2606:50c0:8003::153`
- **`www` `CNAME`** → `midspiral.github.io`
- Repo **Settings → Pages**: set the custom domain to `lemmascript.com` and tick **Enforce HTTPS** (`.dev`/`.com` both served over HTTPS via the auto-provisioned cert).
- At your registrar, **301-redirect** `lemmascript.dev` and `lemmascript.org` → `lemmascript.com`.
