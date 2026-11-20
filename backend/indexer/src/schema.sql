-- One database per chain. Every event row keeps its block so a reorg rollback is "delete above block N".
CREATE TABLE IF NOT EXISTS commitments (
  idx          bigint PRIMARY KEY,   -- ledger index == tree position
  block_number bigint NOT NULL,
  log_index    bigint NOT NULL,
  block_hash   bytea  NOT NULL,
  tx_hash      bytea  NOT NULL,
  fields       bytea  NOT NULL,      -- 4 x 32-byte big-endian words, as in Committed
  hash_chain   bytea  NOT NULL,      -- ledger hash chain after this commitment
  block_time   bigint NOT NULL       -- its block's time, unix seconds
);
CREATE INDEX IF NOT EXISTS commitments_block ON commitments (block_number, idx);
CREATE TABLE IF NOT EXISTS nullifiers (
  pos          bigint PRIMARY KEY,   -- order of appearance on chain
  nullifier    bytea  NOT NULL,
  block_number bigint NOT NULL,
  log_index    bigint NOT NULL,
  block_hash   bytea  NOT NULL,
  tx_hash      bytea  NOT NULL
);
CREATE INDEX IF NOT EXISTS nullifiers_block ON nullifiers (block_number, pos);
-- RootProved and Recovered, next to the root this indexer computed for the same size. A recovery steps back
-- (new_index <= old_index) and starts a new era, in which an index may be proved again.
CREATE TABLE IF NOT EXISTS roots (
  pos                bigint PRIMARY KEY,   -- order of proof
  new_index          bigint NOT NULL,
  old_index          bigint NOT NULL,
  root               bytea  NOT NULL,
  local_root         bytea  NOT NULL,
  partial_chunk_root bytea,              -- roots of the last, partial chunk and page at new_index; NULL if none
  partial_page_root  bytea,
  block_number       bigint NOT NULL,
  log_index          bigint NOT NULL,
  block_time         bigint                -- its block's time, unix seconds; NULL where unknown
);
CREATE INDEX IF NOT EXISTS roots_block ON roots (block_number);
-- a database that lacks it gains it, NULL on the roots it already holds
ALTER TABLE roots ADD COLUMN IF NOT EXISTS block_time bigint;
-- roots of full chunks (2^12 commitments) and full pages (2^12 chunks)
CREATE TABLE IF NOT EXISTS chunk_roots (
  chunk bigint PRIMARY KEY,
  root  bytea  NOT NULL
);
CREATE TABLE IF NOT EXISTS page_roots (
  page bigint PRIMARY KEY,
  root bytea  NOT NULL
);
-- reorg window only
CREATE TABLE IF NOT EXISTS blocks (
  number      bigint PRIMARY KEY,
  hash        bytea  NOT NULL,
  parent_hash bytea  NOT NULL
);
CREATE TABLE IF NOT EXISTS cursor (
  id           int PRIMARY KEY CHECK (id = 1),
  block_number bigint NOT NULL,
  block_hash   bytea            -- NULL while backfilling outside the reorg window, and after a repair
);
