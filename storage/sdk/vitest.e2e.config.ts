import { defineConfig } from 'vitest/config';

// PocketIC flows: real vetKD keys, and 20-22 bit proofs of work solved in JS.
export default defineConfig({
  test: {
    include: ['test/e2e/*.test.ts'],
    globalSetup: ['test/e2e/global-setup.ts'],
    testTimeout: 120_000,
    hookTimeout: 120_000,
  },
});
