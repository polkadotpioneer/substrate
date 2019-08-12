// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Test utilities

use super::*;

use std::cell::RefCell;
use srml_support::{impl_outer_origin, parameter_types};
use primitives::{H256, Blake2Hasher};
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
use sr_primitives::{
	Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header,
};
use system::EnsureSignedBy;

impl_outer_origin! {
	pub enum Origin for Test {}
}

// For testing the module, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of modules we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const CandidateDeposit: u64 = 25;
	pub const Period: u64 = 4;

	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: u32 = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();

	pub const ExistentialDeposit: u64 = 0;
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
	pub const TransactionBaseFee: u64 = 0;
	pub const TransactionByteFee: u64 = 0;
}

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = ();
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type WeightMultiplierUpdate = ();
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
}

impl balances::Trait for Test {
	type Balance = u64;
	type OnFreeBalanceZero = ();
	type OnNewAccount = ();
	type Event = ();
	type TransactionPayment = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
	type TransactionBaseFee = TransactionBaseFee;
	type TransactionByteFee = TransactionByteFee;
	type WeightToFee = ();
}

parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
	pub const Three: u64 = 3;
}

thread_local! {
	pub static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
}

pub struct TestChangeMembers;
impl ChangeMembers<u64> for TestChangeMembers {
	fn set_members_sorted(new_members: &[u64], _old_members: &[u64]) {
		MEMBERS.with(|m| *m.borrow_mut() = new_members.to_vec());
	}

	fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
		let mut old_plus_incoming = MEMBERS.with(|m| m.borrow().to_vec());
		old_plus_incoming.extend_from_slice(incoming);
		old_plus_incoming.sort();
		let mut new_plus_outgoing = new.to_vec();
		new_plus_outgoing.extend_from_slice(outgoing);
		new_plus_outgoing.sort();
		assert_eq!(old_plus_incoming, new_plus_outgoing);

		MEMBERS.with(|m| *m.borrow_mut() = new.to_vec());
	}
}

impl Trait for Test {
	type Event = ();
	type AddOrigin = EnsureSignedBy<One, u64>;
	type KickOrigin = EnsureSignedBy<Two, u64>;
	type MembershipInitialized = TestChangeMembers;
	type MembershipChanged = TestChangeMembers;

	type Currency = balances::Module<Self>;
	type CandidateDeposit = CandidateDeposit;
	type Period = Period;
	type Score = u64;
	type ScoreOrigin = EnsureSignedBy<Three, u64>;
}

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
pub fn new_test_ext() -> sr_io::TestExternalities<Blake2Hasher> {
	let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	// We use default for brevity, but you can configure as desired if needed.
	balances::GenesisConfig::<Test> {
		balances: vec![
			(5, 500_000),
			(10, 500_000),
			(15, 500_000),
			(20, 500_000),
			(21, 500_000),
			(30, 500_000),
			(99, 1),
		],
		vesting: vec![],
	}.assimilate_storage(&mut t).unwrap();
	GenesisConfig::<Test>{
		pool: vec![
			(5, None),
			(10, Some(1)),
			(20, Some(2)),
			(21, Some(2)),
			(30, Some(3)),
		],
		member_count: 2,
		.. Default::default()
	}.assimilate_storage(&mut t).unwrap();
	t.into()
}
