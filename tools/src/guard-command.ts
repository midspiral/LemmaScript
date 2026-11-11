import { execFileSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

/** Forward to the packaged guard CLI, using this compiler for extraction. */
export function runGuard(args: string[]): void {
  if (Number(process.versions.node.split(".")[0]) < 22) {
    console.error("`lsc guard` requires Node.js 22 or newer.");
    process.exit(1);
  }

  let cli: string;
  try {
    cli = createRequire(import.meta.url).resolve("lemmascript-guard/dist/guard.js");
  } catch {
    console.error("`lsc guard` needs lemmascript-guard >= 0.1.0; reinstall lemmascript with optional dependencies enabled (--include=optional).");
    process.exit(1);
  }

  try {
    execFileSync(process.execPath, [cli, ...args], {
      stdio: "inherit",
      env: {
        ...process.env,
        // A checkout can have another lemmascript version installed as a peer.
        // Use this build by default, while retaining the explicit dev override.
        LEMMASCRIPT: process.env.LEMMASCRIPT || fileURLToPath(new URL("../../", import.meta.url)),
      },
    });
  } catch (err) {
    const status = (err as { status?: number | null }).status;
    if (typeof status === "number") process.exit(status);
    console.error(err instanceof Error ? err.message : String(err));
    process.exit(1);
  }
}
