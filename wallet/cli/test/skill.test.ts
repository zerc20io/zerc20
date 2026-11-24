import { existsSync, mkdirSync, mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { expect, test } from 'vitest';
import { installSkill, skillText } from '../src/skill.js';

test('the skill names every command and option the help does, as an agent learns the program from it', () => {
  const help = /const HELP = `([\s\S]*?)`;/.exec(readFileSync(new URL('../src/main.ts', import.meta.url), 'utf8'))![1];
  const commands = [...help.split('\nThe key')[0].matchAll(/^ {2}([a-z-]+(?: start)?)/gm)].map((m) => m[1]);
  expect(commands).toContain('install-skill');
  for (const command of commands) expect(skillText()).toContain(`zerc20 ${command}`);
  for (const [option] of help.matchAll(/--[a-z-]+/g)) expect(skillText()).toContain(option);
});

test('the skill is installed for the agents a machine has, and for none it has not', () => {
  const home = mkdtempSync(join(tmpdir(), 'zerc20-skill-'));
  expect(() => installSkill(home)).toThrow('no coding agent');
  // Codex reads the directory agents share, which its own tells is wanted
  mkdirSync(join(home, '.codex'));
  const shared = join(home, '.agents/skills/zerc20-cli/SKILL.md');
  expect(installSkill(home)).toEqual([shared]);
  expect(existsSync(join(home, '.claude'))).toBe(false);
  mkdirSync(join(home, '.claude'));
  expect(installSkill(home)).toEqual([join(home, '.claude/skills/zerc20-cli/SKILL.md'), shared]);
  expect(readFileSync(shared, 'utf8')).toBe(skillText());
});
