//! Flushes deposit addresses once funds reach them, paying the gas and taking a flat fee out of each.

pub mod api;
pub mod contracts;
pub mod store;
pub mod watch;

use alloy::primitives::Address;
use alloy::providers::DynProvider;
use parking_lot::Mutex;
use zerc20_common::{Fees, Sender};

/// State shared by the registration API and the watcher.
pub struct App {
    /// Sends with the relayer key, which pays for every flush.
    pub sender: Sender,
    /// `sender`'s, for reads.
    pub provider: DynProvider,
    pub factory: Address,
    /// Where the fees of new registrations go.
    pub fee_recipient: Address,
    /// The fee per token id, in the underlying's base units. Only these tokens are served.
    pub fees: Fees,
    pub store: Mutex<store::Store>,
}
