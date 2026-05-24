import { defineConfig } from "astro/config"
import starlight from "@astrojs/starlight"

// https://astro.build/config
export default defineConfig({
  site: "https://lemmascript.com",
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
