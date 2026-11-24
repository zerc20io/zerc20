import { mkdtempSync } from 'node:fs';
import { createServer } from 'node:http';
import type { AddressInfo } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { expect, test, vi } from 'vitest';
import { notice, updateNotice } from '../src/update.js';

test('a newer release is told of, a withdrawn one first, and the newest release of nothing', () => {
  expect(notice('0.9.0', { latest: '0.9.0', withdrawn: null })).toBeNull();
  expect(notice('0.9.0', { latest: '0.10.0', withdrawn: null })).toContain('zerc20 0.10.0 is out (this is 0.9.0)');
  // a release ahead of npm's, as one being built is
  expect(notice('0.10.0', { latest: '0.9.0', withdrawn: null })).toBeNull();
  expect(notice('0.9.0', { latest: '0.9.0', withdrawn: 'it pays twice' })).toContain('withdrawn: it pays twice');
});

test('npm is asked once a day, shown without what a terminal would obey, and a silent one fails no command', async () => {
  vi.stubEnv('CI', '');
  vi.stubEnv('ZERC20_NO_UPDATE_CHECK', '');
  vi.stubEnv('ZERC20_HOME', mkdtempSync(join(tmpdir(), 'zerc20-update-')));
  let asked = 0;
  let answer = JSON.stringify({
    'dist-tags': { latest: '0.2.0' },
    versions: { '0.1.0': { deprecated: 'broken\u001b[2J' }, '0.2.0': {} },
  });
  const server = createServer((_, res) => void (asked++, res.end(answer))).listen(0);
  const registry = `http://127.0.0.1:${(server.address() as AddressInfo).port}`;
  const day = 24 * 3600 * 1000;
  try {
    expect(await updateNotice('0.1.0', registry, 0)).toContain('withdrawn: broken[2J\n');
    expect(await updateNotice('0.1.0', registry, day)).toContain('withdrawn');
    expect(asked).toBe(1);
    // the release just installed is asked about anew
    expect(await updateNotice('0.2.0', registry, day)).toBeNull();
    expect(asked).toBe(2);
    answer = 'not JSON';
    expect(await updateNotice('0.2.0', registry, 2 * day + 1)).toBeNull();
    expect(await updateNotice('0.2.0', registry, 2 * day + 2)).toBeNull();
    expect(asked).toBe(3);
    vi.stubEnv('ZERC20_NO_UPDATE_CHECK', '1');
    expect(await updateNotice('0.1.0', registry, 9 * day)).toBeNull();
    expect(asked).toBe(3);
  } finally {
    server.close();
    vi.unstubAllEnvs();
  }
});
