// The zerc20_storage Candid interface (canister/zerc20_storage.did), by hand: generated bindings
// target the older @dfinity/* packages.

import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';
import type { Principal } from '@icp-sdk/core/principal';

export type KindName = 'Outgoing' | 'Lane';
export type Kind = { [K in KindName]: { [P in K]: null } }[KindName];

export type Action =
  | {
      OpenChannel: {
        inbox: Uint8Array;
        enc_announcement: Uint8Array;
        outgoing_id: Uint8Array;
        enc_outgoing: Uint8Array;
      };
    }
  | { Put: { kind: Kind; id: Uint8Array; data: Uint8Array } };

export interface AuditRequest {
  target: Uint8Array;
  notify_key: Uint8Array;
  transport_public_key: Uint8Array;
}

export interface Registration {
  address: Uint8Array;
  public_key: Uint8Array;
  notify_key: Uint8Array;
  escrow: Uint8Array;
  expiry_ns: bigint;
  signature: Uint8Array;
}

export interface Slot {
  data: Uint8Array;
  at_ns: bigint;
}

export interface AuditRecord {
  auditor: Principal;
  target: Uint8Array;
  notify_key: Uint8Array;
  transport_public_key: Uint8Array;
  at_ns: bigint;
}

export type CanisterError = { Occupied: Uint8Array } | { Rejected: string };
export type Result<T> = { Ok: T } | { Err: CanisterError };

export interface Service {
  escrow_public_key: ActorMethod<[], Result<Uint8Array>>;
  register: ActorMethod<[Registration, bigint], Result<null>>;
  registration: ActorMethod<[Uint8Array, [] | [Uint8Array]], [] | [Registration]>;
  audit_escrow_key: ActorMethod<[AuditRequest], Result<Uint8Array>>;
  validate_audit_escrow_key: ActorMethod<[AuditRequest], { Ok: string } | { Err: string }>;
  get_audits: ActorMethod<[bigint, number], AuditRecord[]>;
  submit: ActorMethod<[Action[], bigint], Result<null>>;
  get_announcements: ActorMethod<[Uint8Array, number, number], Uint8Array[]>;
  get_slots: ActorMethod<[Kind, Uint8Array[]], ([] | [Slot])[]>;
  get_log: ActorMethod<[bigint, number], Uint8Array[]>;
  log_length: ActorMethod<[], bigint>;
}

export const idlFactory: IDL.InterfaceFactory = ({ IDL }) => {
  const Blob = IDL.Vec(IDL.Nat8);
  const Error = IDL.Variant({ Occupied: Blob, Rejected: IDL.Text });
  const BlobResult = IDL.Variant({ Ok: Blob, Err: Error });
  const UnitResult = IDL.Variant({ Ok: IDL.Null, Err: Error });
  const Kind = IDL.Variant({ Outgoing: IDL.Null, Lane: IDL.Null });
  const Action = IDL.Variant({
    OpenChannel: IDL.Record({ inbox: Blob, enc_announcement: Blob, outgoing_id: Blob, enc_outgoing: Blob }),
    Put: IDL.Record({ kind: Kind, id: Blob, data: Blob }),
  });
  const AuditRequest = IDL.Record({ target: Blob, notify_key: Blob, transport_public_key: Blob });
  const Registration = IDL.Record({
    address: Blob,
    public_key: Blob,
    notify_key: Blob,
    escrow: Blob,
    expiry_ns: IDL.Nat64,
    signature: Blob,
  });
  const Slot = IDL.Record({ data: Blob, at_ns: IDL.Nat64 });
  const AuditRecord = IDL.Record({
    auditor: IDL.Principal,
    target: Blob,
    notify_key: Blob,
    transport_public_key: Blob,
    at_ns: IDL.Nat64,
  });
  return IDL.Service({
    escrow_public_key: IDL.Func([], [BlobResult], []),
    register: IDL.Func([Registration, IDL.Nat64], [UnitResult], []),
    registration: IDL.Func([Blob, IDL.Opt(Blob)], [IDL.Opt(Registration)], ['query']),
    audit_escrow_key: IDL.Func([AuditRequest], [BlobResult], []),
    validate_audit_escrow_key: IDL.Func([AuditRequest], [IDL.Variant({ Ok: IDL.Text, Err: IDL.Text })], ['query']),
    get_audits: IDL.Func([IDL.Nat64, IDL.Nat32], [IDL.Vec(AuditRecord)], ['query']),
    submit: IDL.Func([IDL.Vec(Action), IDL.Nat64], [UnitResult], []),
    get_announcements: IDL.Func([Blob, IDL.Nat32, IDL.Nat32], [IDL.Vec(Blob)], ['query']),
    get_slots: IDL.Func([Kind, IDL.Vec(Blob)], [IDL.Vec(IDL.Opt(Slot))], ['query']),
    get_log: IDL.Func([IDL.Nat64, IDL.Nat32], [IDL.Vec(Blob)], ['query']),
    log_length: IDL.Func([], [IDL.Nat64], ['query']),
  });
};
