declare module 'snarkjs' {
  export interface Groth16Proof {
    pi_a: string[];
    pi_b: string[][];
    pi_c: string[];
  }
  type File = string | { type: 'mem'; data: Uint8Array };
  export const groth16: {
    fullProve(input: object, wasm: File, zkey: File): Promise<{ proof: Groth16Proof; publicSignals: string[] }>;
  };
}
