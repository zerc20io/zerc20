// How a command ends when it cannot go on: what it prints, and the status it exits with.

/** The command line itself is wrong: exits 2. */
export class Usage extends Error {}

/** The command could not do what was asked: exits 1. */
export class Failure extends Error {}
