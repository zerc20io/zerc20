// The skill that teaches a coding agent this program. It ships with the program, so the two are of one release.

import { copyFileSync, existsSync, mkdirSync, readFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Failure } from './errors.js';

const SKILL = fileURLToPath(new URL('../skill/SKILL.md', import.meta.url));

export const skillText = () => readFileSync(SKILL, 'utf8');

/** Where agents read a user's skills, each with the directories that tell an agent reading it is on this machine.
 * Claude Code reads its own; Codex, Cursor, Gemini CLI and opencode all read the shared one. */
const PLACES = [
  { skills: '.claude/skills', agents: ['.claude'] },
  { skills: '.agents/skills', agents: ['.agents', '.codex', '.cursor', '.gemini', '.config/opencode'] },
];

/** Where a copy of the skill goes in each place. */
const copyIn = (home: string, place: (typeof PLACES)[number]) => join(home, place.skills, 'zerc20-cli', 'SKILL.md');

/** The copies of the skill on this machine. */
export const installedSkills = (home = homedir()) => PLACES.map((p) => copyIn(home, p)).filter((f) => existsSync(f));

/** Whether a copy here is another release's: what it tells an agent may not hold of this one. */
export const staleSkill = (home = homedir()) =>
  installedSkills(home).some((f) => readFileSync(f, 'utf8') !== skillText());

/** Copies the skill to where the agents on this machine read theirs, over an older copy, and returns the files it
 * wrote. Nothing is written for an agent that is not here. */
export function installSkill(home = homedir()): string[] {
  const written = PLACES.filter((p) => p.agents.some((a) => existsSync(join(home, a)))).map((p) => {
    const file = copyIn(home, p);
    mkdirSync(dirname(file), { recursive: true });
    copyFileSync(SKILL, file);
    return file;
  });
  if (written.length === 0)
    throw new Failure(
      'no coding agent is on this machine: `zerc20 skill` prints the skill, for where yours reads its own',
    );
  return written;
}
