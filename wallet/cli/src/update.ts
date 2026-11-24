// Whether this release is the newest, asked of npm once a day, and the command that brings the newest. What npm
// answers is only ever shown: nothing a command does or trusts comes from it.

import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Failure } from './errors.js';
import { home } from './files.js';
import { installedSkills, staleSkill } from './skill.js';

const PACKAGE = '@zerc20/cli';
const DAY = 24 * 3600 * 1000;

/** What npm last said of the release `version`: the newest one, and why this one is withdrawn, if it is. */
interface Seen {
  version: string;
  at: number;
  latest: string;
  withdrawn: string | null;
}

/** What a user of `version` is told of `seen`: that their release is withdrawn, before that a newer one is out. */
export function notice(version: string, seen: Pick<Seen, 'latest' | 'withdrawn'>): string | null {
  if (seen.withdrawn !== null)
    return `This release of zerc20 (${version}) is withdrawn: ${seen.withdrawn}\nInstall the newest: zerc20 update`;
  const newer = seen.latest.localeCompare(version, undefined, { numeric: true }) > 0;
  return newer ? `zerc20 ${seen.latest} is out (this is ${version}): zerc20 update` : null;
}

/** What npm's short document of the package says of `version`. Its text reaches a terminal, so only printable
 * characters of it are kept, and a version is one only if it reads as one. */
async function ask(version: string, registry: string, now: number): Promise<Seen> {
  const r = await fetch(`${registry}/${PACKAGE}`, {
    headers: { accept: 'application/vnd.npm.install-v1+json' },
    signal: AbortSignal.timeout(2000),
  });
  const doc = (await r.json()) as {
    'dist-tags': { latest: string };
    versions: Record<string, { deprecated?: string } | undefined>;
  };
  const latest = doc['dist-tags'].latest;
  if (!/^\d+\.\d+\.\d+$/.test(latest)) throw new Error('not a version');
  const withdrawn = doc.versions[version]?.deprecated;
  return {
    version,
    at: now,
    latest,
    withdrawn: withdrawn
      ? String(withdrawn)
          .replace(/[^\x20-\x7e]/g, '')
          .slice(0, 200)
      : null,
  };
}

/** What to say of this release, `version`, after a command: null when it is the newest, when npm was asked within
 * the day and said so, or when the user or a CI run wants nothing asked. A registry out of reach is asked again a
 * day later, not by every command, and never fails the command. */
export async function updateNotice(
  version: string,
  registry = 'https://registry.npmjs.org',
  now = Date.now(),
): Promise<string | null> {
  if (process.env.ZERC20_NO_UPDATE_CHECK || process.env.CI) return null;
  try {
    const file = join(home(), 'update.json');
    let seen: Seen | null = null;
    try {
      const kept = JSON.parse(readFileSync(file, 'utf8')) as Seen;
      // what was said of another release says nothing of this one
      if (kept.version === version) seen = kept;
    } catch {
      // never asked yet
    }
    if (!seen || now - seen.at > DAY) {
      const known = seen ?? { version, latest: version, withdrawn: null };
      seen = await ask(version, registry, now).catch(() => ({ ...known, at: now }));
      mkdirSync(home(), { recursive: true });
      writeFileSync(file, JSON.stringify(seen));
    }
    return notice(version, seen);
  } catch {
    return null;
  }
}

/** The lines a command ends with, on standard error: of a newer release, and of a skill here that is not this
 * release's. */
export async function notices(version: string): Promise<string[]> {
  const lines = [await updateNotice(version)];
  if (staleSkill()) lines.push('The zerc20 skill coding agents read here is of another release: zerc20 install-skill');
  return lines.filter((line) => line !== null);
}

/** Installs the newest release with npm, as this one was, and has it copy its skill over those installed here: this
 * process is still the release before it. */
export function update(): void {
  const run = (command: string, args: string[]) =>
    spawnSync(command, args, { stdio: 'inherit', shell: process.platform === 'win32' && command === 'npm' });
  const npm = run('npm', ['install', '-g', `${PACKAGE}@latest`]);
  if (npm.status !== 0) throw new Failure(`npm did not install it${npm.error ? `: ${npm.error.message}` : ''}`);
  if (installedSkills().length > 0) run(process.execPath, [process.argv[1], 'install-skill']);
}
