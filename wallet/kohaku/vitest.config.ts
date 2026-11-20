import { defineConfig } from 'vitest/config';

// Vite bundles the Kohaku packages rather than leaving them to Node: they import their own files without extensions,
// which only a bundler resolves.
export const kohaku = { deps: { inline: [/@kohaku-eth\//] } };

export default defineConfig({ test: { include: ['test/*.test.ts'], server: kohaku } });
