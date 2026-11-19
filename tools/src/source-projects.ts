import { Project, ScriptTarget, type SourceFile } from "ts-morph";
import path from "node:path";
import { findUp } from "./config.js";

/** Full TypeScript projects shared for the duration of one CLI batch. */
export class SourceProjects {
  private readonly projects = new Map<string, { project: Project; sources: Set<SourceFile> }>();

  load(filePath: string): SourceFile {
    const absPath = path.resolve(filePath);
    const tsConfigFilePath = findUp("tsconfig.json", absPath) ?? undefined;
    const cached = tsConfigFilePath ? this.projects.get(tsConfigFilePath) : undefined;
    const existing = cached?.project.getSourceFile(absPath);
    if (existing && cached?.sources.has(existing)) return existing;

    // Keep every configured file and its dependencies: otherwise ambient
    // declarations and module augmentations can silently change the model.
    const project = tsConfigFilePath
      ? new Project({ tsConfigFilePath })
      : new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"] } });
    const included = project.getSourceFile(absPath);
    if (tsConfigFilePath && included) {
      this.projects.set(tsConfigFilePath, { project, sources: new Set(project.getSourceFiles()) });
      return included;
    }

    // An explicitly requested file outside the configured graph may introduce
    // globals or augmentations. Give it a fresh project so it cannot affect
    // later entries. Files without a tsconfig likewise remain independent.
    const sourceFile = project.addSourceFileAtPath(absPath);
    project.resolveSourceFileDependencies();
    return sourceFile;
  }
}
