// How a command ends when it cannot go on: what it prints, and the status it exits with.

/** The command line itself is wrong: exits 2. */
export class Usage extends Error {}

/** The command could not do what was asked: exits 1. */
export class Failure extends Error {}

/** What went wrong, as its errors tell it down their causes. A viem error tells one failure over at each cause, with the
 * request it made and a link to its docs: of those, the failure once, with what the RPC answered and which RPC it was. */
export function told(e: Error): string {
  const lines: string[] = [];
  for (let c: unknown = e; c instanceof Error; c = c.cause) {
    const { shortMessage, details } = c as { shortMessage?: string; details?: string };
    if (shortMessage === undefined) {
      lines.push(c.message);
      continue;
    }
    let url: string | undefined;
    for (let d: unknown = c; d instanceof Error; d = d.cause) url ??= (d as { url?: string }).url;
    const answered = details && !shortMessage.includes(details) ? details : '';
    lines.push([shortMessage, answered, url ? `(${url})` : ''].filter(Boolean).join(' '));
    break;
  }
  return lines.join('\n');
}
