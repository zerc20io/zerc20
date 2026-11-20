import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: { include: ['test/e2e/*.test.ts'], testTimeout: 1_200_000, hookTimeout: 300_000 },
});
