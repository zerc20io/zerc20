// The merge decider keys a prover on this machine loads: those of the setup the chains' merge verifier is generated
// from, which every network shares. Pinned here rather than read beside the download, so that the server they come
// from cannot hand out another key: a proving key made to leak would put the witness in the proof.

export const MERGE_KEYS = {
  setup: '20261021T210800Z-98c5f43',
  pk: {
    file: 'merge_decider_pk.bin',
    bytes: 6_465_237_728,
    sha256: 'e5c2f6ba4fc3fc10a9703fb5316f5b674c855e469310a23997912f5ef18ee037',
  },
  vk: {
    file: 'merge_decider_vk.bin',
    bytes: 50_466,
    sha256: '144087672d80dcb11e0f9075f81d9453304328206c68e31d5b0d7b77474b36df',
  },
} as const;

/** Where a key of the setup is served. */
export const mergeKeyUrl = (file: string) => `https://artifacts.v2.zerc20.io/merge/${MERGE_KEYS.setup}/${file}`;
