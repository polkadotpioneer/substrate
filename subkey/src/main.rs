// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")]
extern crate test;

use std::{str::FromStr, io::{stdin, Read}, convert::TryInto};
use hex_literal::hex;
use clap::load_yaml;
use bip39::{Mnemonic, Language, MnemonicType};
use primitives::{
	ed25519, sr25519, hexdisplay::HexDisplay, Pair, Public, blake2_256,
	crypto::{Ss58Codec, set_default_ss58_version, Ss58AddressFormat}
};
use codec::{Encode, Decode};
use sr_primitives::generic::Era;
use node_primitives::{Balance, Index, Hash};
use node_runtime::{Call, UncheckedExtrinsic, BalancesCall, Runtime};

mod vanity;

trait Crypto {
	type Pair: Pair<Public=Self::Public>;
	type Public: Public + Ss58Codec + AsRef<[u8]> + std::hash::Hash;
	fn pair_from_suri(suri: &str, password: Option<&str>) -> Self::Pair {
		Self::Pair::from_string(suri, password).expect("Invalid phrase")
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String { pair.public().to_ss58check() }
	fn public_from_pair(pair: &Self::Pair) -> Vec<u8> { pair.public().as_ref().to_owned() }
	fn print_from_uri(
		uri: &str,
		password: Option<&str>,
		network_override: Option<Ss58AddressFormat>,
	) where <Self::Pair as Pair>::Public: Sized + Ss58Codec + AsRef<[u8]> {
		if let Ok((pair, seed)) = Self::Pair::from_phrase(uri, password) {
			println!("Secret phrase `{}` is account:\n  Secret seed: 0x{}\n  Public key (hex): 0x{}\n  Address (SS58): {}",
				uri,
				HexDisplay::from(&seed.as_ref()),
				HexDisplay::from(&Self::public_from_pair(&pair)),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok(pair) = Self::Pair::from_string(uri, password) {
			println!("Secret Key URI `{}` is account:\n  Public key (hex): 0x{}\n  Address (SS58): {}",
				uri,
				HexDisplay::from(&Self::public_from_pair(&pair)),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok((public, v)) = <Self::Pair as Pair>::Public::from_string_with_version(uri) {
			let v = network_override.unwrap_or(v);
			println!("Public Key URI `{}` is account:\n  Network ID/version: {}\n  Public key (hex): 0x{}\n  Address (SS58): {}",
				uri,
				String::from(v),
				HexDisplay::from(&public.as_ref()),
				public.to_ss58check_with_version(v)
			);
		} else {
			println!("Invalid phrase/URI given");
		}
	}
}

struct Ed25519;

impl Crypto for Ed25519 {
	type Pair = ed25519::Pair;
	type Public = ed25519::Public;

	fn pair_from_suri(suri: &str, password_override: Option<&str>) -> Self::Pair {
		ed25519::Pair::from_legacy_string(suri, password_override)
	}
}

struct Sr25519;

impl Crypto for Sr25519 {
	type Pair = sr25519::Pair;
	type Public = sr25519::Public;
}

fn execute<C: Crypto>(matches: clap::ArgMatches) where
	<<C as Crypto>::Pair as Pair>::Signature: AsRef<[u8]> + AsMut<[u8]> + Default,
	<<C as Crypto>::Pair as Pair>::Public: Sized + AsRef<[u8]> + Ss58Codec,
{
	let extra = |i: Index, f: Balance| {
		(
			system::CheckGenesis::<Runtime>::new(),
			system::CheckEra::<Runtime>::from(Era::Immortal),
			system::CheckNonce::<Runtime>::from(i),
			system::CheckWeight::<Runtime>::new(),
			balances::TakeFees::<Runtime>::from(f),
		)
	};
	let password = matches.value_of("password");
	let maybe_network: Option<Ss58AddressFormat> = matches.value_of("network")
		.map(|network| network.try_into()
			.expect("Invalid network name: must be polkadot/substrate/kusama")
		);
	if let Some(network) = maybe_network {
		set_default_ss58_version(network);
	}
	match matches.subcommand() {
		("generate", Some(matches)) => {
			// create a new randomly generated mnemonic phrase
			let words = matches.value_of("words")
				.map(|x| usize::from_str(x).expect("Invalid number given for --words"))
				.map(|x| MnemonicType::for_word_count(x)
					.expect("Invalid number of words given for phrase: must be 12/15/18/21/24")
				).unwrap_or(MnemonicType::Words12);
			let mnemonic = Mnemonic::new(words, Language::English);
			C::print_from_uri(mnemonic.phrase(), password, maybe_network);
		}
		("inspect", Some(matches)) => {
			let uri = matches.value_of("uri")
				.expect("URI parameter is required; thus it can't be None; qed");
			C::print_from_uri(uri, password, maybe_network);
		}
		("vanity", Some(matches)) => {
			let desired: String = matches.value_of("pattern").map(str::to_string).unwrap_or_default();
			let result = vanity::generate_key::<C>(&desired).expect("Key generation failed");
			C::print_from_uri(
				&format!("0x{}", HexDisplay::from(&result.seed.as_ref())),
				None,
				maybe_network
			);
		}
		("sign", Some(matches)) => {
			let suri = matches.value_of("suri")
				.expect("secret URI parameter is required; thus it can't be None; qed");
			let pair = C::pair_from_suri(suri, password);
			let mut message = vec![];
			stdin().lock().read_to_end(&mut message).expect("Error reading from stdin");
			if matches.is_present("hex") {
				message = hex::decode(&message).expect("Invalid hex in message");
			}
			let sig = pair.sign(&message);
			println!("{}", hex::encode(&sig));
		}
		("transfer", Some(matches)) => {
			let signer = matches.value_of("from")
				.expect("parameter is required; thus it can't be None; qed");
			let signer = Sr25519::pair_from_suri(signer, password);

			let to = matches.value_of("to")
				.expect("parameter is required; thus it can't be None; qed");
			let to = sr25519::Public::from_string(to).ok().or_else(||
				sr25519::Pair::from_string(to, password).ok().map(|p| p.public())
			).expect("Invalid 'to' URI; expecting either a secret URI or a public URI.");

			let amount = matches.value_of("amount")
				.expect("parameter is required; thus it can't be None; qed");
			let amount = str::parse::<Balance>(amount)
				.expect("Invalid 'amount' parameter; expecting an integer.");

			let index = matches.value_of("index")
				.expect("parameter is required; thus it can't be None; qed");
			let index = str::parse::<Index>(index)
				.expect("Invalid 'amount' parameter; expecting an integer.");

			let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

			let genesis_hash: Hash = match matches.value_of("genesis").unwrap_or("alex") {
				"elm" => hex!["10c08714a10c7da78f40a60f6f732cf0dba97acfb5e2035445b032386157d5c3"].into(),
				"alex" => hex!["dcd1346701ca8396496e52aa2785b1748deb6db09551b72159dcb3e08991025b"].into(),
				h => hex::decode(h).ok().and_then(|x| Decode::decode(&mut &x[..]).ok())
					.expect("Invalid genesis hash or unrecognised chain identifier"),
			};

			println!("Using a genesis hash of {}", HexDisplay::from(&genesis_hash.as_ref()));

			let raw_payload = (
				function,
				extra(index, 0),
				(&genesis_hash, &genesis_hash),
			);
			let signature = raw_payload.using_encoded(|payload| if payload.len() > 256 {
				signer.sign(&blake2_256(payload)[..])
			} else {
				println!("Signing {}", HexDisplay::from(&payload));
				signer.sign(payload)
			});
			let extrinsic = UncheckedExtrinsic::new_signed(
				raw_payload.0,
				signer.public().into(),
				signature.into(),
				extra(index, 0),
			);
			println!("0x{}", hex::encode(&extrinsic.encode()));
		}
		("sign-transaction", Some(matches)) => {
			let s = matches.value_of("suri")
				.expect("secret URI parameter is required; thus it can't be None; qed");
			let signer = Sr25519::pair_from_suri(s, password);

			let index = matches.value_of("nonce")
				.expect("nonce is required; thus it can't be None; qed");
			let index = str::parse::<Index>(index)
				.expect("Invalid 'index' parameter; expecting an integer.");

			let call = matches.value_of("call")
				.expect("call is required; thus it can't be None; qed");
			let function: Call = hex::decode(&call).ok()
				.and_then(|x| Decode::decode(&mut &x[..]).ok()).unwrap();

			let genesis_hash: Hash = match matches.value_of("genesis").unwrap_or("alex") {
				"elm" => hex!["10c08714a10c7da78f40a60f6f732cf0dba97acfb5e2035445b032386157d5c3"].into(),
				"alex" => hex!["dcd1346701ca8396496e52aa2785b1748deb6db09551b72159dcb3e08991025b"].into(),
				h => hex::decode(h).ok().and_then(|x| Decode::decode(&mut &x[..]).ok())
					.expect("Invalid genesis hash or unrecognised chain identifier"),
			};

			println!("Using a genesis hash of {}", HexDisplay::from(&genesis_hash.as_ref()));

			let raw_payload = (
				function,
				extra(index, 0),
				(&genesis_hash, &genesis_hash),
			);
			let signature = raw_payload.using_encoded(|payload|
				if payload.len() > 256 {
					signer.sign(&blake2_256(payload)[..])
				} else {
					signer.sign(payload)
				}
			);

			let extrinsic = UncheckedExtrinsic::new_signed(
				raw_payload.0,
				signer.public().into(),
				signature.into(),
				extra(index, 0),
			);

			println!("0x{}", hex::encode(&extrinsic.encode()));
		}
		("verify", Some(matches)) => {
			let sig_data = matches.value_of("sig")
				.expect("signature parameter is required; thus it can't be None; qed");
			let mut sig = <<C as Crypto>::Pair as Pair>::Signature::default();
			let sig_data = hex::decode(sig_data).expect("signature is invalid hex");
			if sig_data.len() != sig.as_ref().len() {
				panic!("signature is an invalid length. {} bytes is not the expected value of {} bytes", sig_data.len(), sig.as_ref().len());
			}
			sig.as_mut().copy_from_slice(&sig_data);
			let uri = matches.value_of("uri")
				.expect("public uri parameter is required; thus it can't be None; qed");
			let pubkey = <<C as Crypto>::Pair as Pair>::Public::from_string(uri).ok().or_else(||
				<C as Crypto>::Pair::from_string(uri, password).ok().map(|p| p.public())
			).expect("Invalid URI; expecting either a secret URI or a public URI.");
			let mut message = vec![];
			stdin().lock().read_to_end(&mut message).expect("Error reading from stdin");
			if matches.is_present("hex") {
				message = hex::decode(&message).expect("Invalid hex in message");
			}
			if <<C as Crypto>::Pair as Pair>::verify(&sig, &message, &pubkey) {
				println!("Signature verifies correctly.")
			} else {
				println!("Signature invalid.")
			}
		}
		_ => print_usage(&matches),
	}
}

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml)
		.version(env!("CARGO_PKG_VERSION"))
		.get_matches();

	if matches.is_present("ed25519") {
		execute::<Ed25519>(matches)
	} else {
		execute::<Sr25519>(matches)
	}
}

fn print_usage(matches: &clap::ArgMatches) {
	println!("{}", matches.usage());
}

#[cfg(test)]
mod tests {
	use super::{Hash, Decode};
	#[test]
	fn should_work() {
		let s = "0123456789012345678901234567890123456789012345678901234567890123";

		let d1: Hash = hex::decode(s).ok().and_then(|x| Decode::decode(&mut &x[..]).ok()).unwrap();

		let d2: Hash = {
			let mut gh: [u8; 32] = Default::default();
			gh.copy_from_slice(hex::decode(s).unwrap().as_ref());
			Hash::from(gh)
		};

		assert_eq!(d1, d2);
	}
}
