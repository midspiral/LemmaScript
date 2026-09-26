/** F* artifacts and verification for the experimental, self-contained subset. */
import { copyFileSync, existsSync, mkdtempSync, readFileSync, rmSync } from "fs";
import { execFileSync } from "child_process";
import { createHash } from "crypto";
import { tmpdir } from "os";
import path from "path";
import { proofRegen } from "./proof-files.js";
export { proofGen as fstarGen, proofCheckDiff as fstarCheckDiff } from "./proof-files.js";

export function fstarPaths(source: string, root: string) {
  const relative = path.relative(root, source).split(path.sep).join("/");
  const digest = createHash("sha256").update(relative).digest("hex").slice(0, 12);
  const stem = path.basename(source, ".ts").replace(/[^A-Za-z0-9]/g, "_");
  const moduleName = `LS.M${stem}_${digest}`;
  const proof = path.join(path.dirname(source), `${moduleName}.fst`);
  return { moduleName, proof, gen: proof + ".gen", base: proof + ".base" };
}

// Only resource tuning is accepted. In particular, never allow lax checking,
// selective verification, query admission, or flags that only parse/extract.
export function fstarFlags(extraFlags?: string): string[] {
  const tokens = extraFlags?.trim().split(/\s+/).filter(Boolean) ?? [];
  const allowed = new Set(["--fuel", "--ifuel", "--max_fuel", "--max_ifuel", "--z3rlimit", "--z3rlimit_factor", "--z3seed"]);
  const result: string[] = [];
  for (let i = 0; i < tokens.length; i++) {
    const [flag, inline, ...rest] = tokens[i].split("=");
    if (!allowed.has(flag)) throw new Error(`F*: unsupported verifier flag '${flag}'; only fuel and Z3 resource/seed options are accepted`);
    const value = inline ?? tokens[++i];
    if (rest.length || value === undefined || !/^\d+$/.test(value)) throw new Error(`F*: ${flag} expects a non-negative integer`);
    result.push(flag, value);
  }
  return result;
}

/** Remove comments/strings for a conservative policy check, preserving tokens. */
function codeOnly(source: string): string {
  let code = "", i = 0;
  while (i < source.length) {
    if (source.startsWith("//", i)) {
      const end = source.indexOf("\n", i);
      i = end < 0 ? source.length : end;
      code += " ";
    } else if (source.startsWith("(*", i)) {
      let depth = 1;
      i += 2;
      while (i < source.length && depth) {
        if (source.startsWith("(*", i)) { depth++; i += 2; }
        else if (source.startsWith("*)", i)) { depth--; i += 2; }
        else i++;
      }
      if (depth) throw new Error("F*: unterminated proof comment");
      code += " ";
    } else if (source[i] === '"') {
      i++;
      while (i < source.length && source[i] !== '"') i += source[i] === "\\" ? 2 : 1;
      if (i === source.length) throw new Error("F*: unterminated proof string");
      i++; code += " ";
    } else code += source[i++];
  }
  return code;
}

export function checkFstarProof(source: string): void {
  const code = codeOnly(source);
  if (/#\s*(?:[\w-]*options|lang)\b|\b(?:set_options|push_options|pop_options|reset_options)\b/.test(code)) {
    throw new Error("F*: source option directives are not supported; pass approved resource options through --extra-flags");
  }
  if (/\[@|\b(?:assume|admit|admitP|unsafe_coerce)\b/.test(code)) {
    throw new Error("F*: admissions, assumptions, unsafe casts, and declaration attributes are not supported in proof additions");
  }
}

export function fstarVerify(proof: string, timeLimit?: number, extraFlags?: string): boolean {
  let scratch: string | undefined;
  try {
    const flags = fstarFlags(extraFlags);
    checkFstarProof(readFileSync(proof, "utf8"));
    if (existsSync(proof + "i")) throw new Error("F*: .fsti companions are not supported; verification must check the generated implementation");
    // A private working directory prevents a sibling .fsti, .checked file, or
    // unverified project module from replacing the implementation we check.
    // This first backend supports one TS module plus the installed F* library.
    scratch = mkdtempSync(path.join(tmpdir(), "lsc-fstar-"));
    const file = path.basename(proof);
    copyFileSync(proof, path.join(scratch, file));
    console.log(`Running F* verification: ${proof}`);
    const output = execFileSync(process.env.FSTAR_EXE || "fstar.exe", [
      ...flags, "--report_assumes", "error", "--force", file,
    ], {
      cwd: scratch, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"],
      timeout: timeLimit === undefined ? undefined : timeLimit * 1000,
      killSignal: "SIGKILL", maxBuffer: 16 * 1024 * 1024,
    });
    process.stdout.write(output);
    return true;
  } catch (e: any) {
    if (e?.stdout) process.stdout.write(e.stdout);
    if (e?.stderr) process.stderr.write(e.stderr);
    if (e?.code === "ENOENT") console.error("ERROR: fstar.exe not found on PATH — verification never ran. Install F*: https://github.com/FStarLang/FStar/blob/master/INSTALL.md");
    else if (e?.code === "ETIMEDOUT") console.error(`ERROR: F* exceeded the ${timeLimit}s process time limit.`);
    else if (e?.status === undefined) console.error(e instanceof Error ? e.message : String(e));
    return false;
  } finally {
    if (scratch) rmSync(scratch, { recursive: true, force: true });
  }
}

export function fstarRegen(gen: string, proof: string, base: string, text: string, timeLimit?: number, extraFlags?: string, noVerify = false): void {
  proofRegen(gen, proof, base, text, () => fstarVerify(proof, timeLimit, extraFlags), noVerify);
}
