import type { TestProject } from 'vitest/node';
import { startServer } from '../pocket-ic.js';

declare module 'vitest' {
  export interface ProvidedContext {
    picUrl: string;
  }
}

export default async function setup(project: TestProject) {
  const server = await startServer();
  project.provide('picUrl', server.getUrl());
  return () => server.stop();
}
