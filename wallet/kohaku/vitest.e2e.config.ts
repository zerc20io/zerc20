import { defineConfig } from 'vitest/config';
import { kohaku } from './vitest.config.js';

export default defineConfig({
  test: { include: ['test/e2e/*.test.ts'], server: kohaku, testTimeout: 1_200_000, hookTimeout: 300_000 },
});
