use metashrew_support::index_pointer::KeyValuePointer;
use metashrew_support::compat::to_arraybuffer_layout;
use metashrew_support::block::AuxpowBlock;
use metashrew_support::utils::consensus_decode;

use alkanes_runtime::{
  declare_alkane, message::MessageDispatch, storage::StoragePointer, token::Token,
  runtime::AlkaneResponder
};

use alkanes_support::{
  id::AlkaneId,
  parcel::AlkaneTransfer, response::CallResponse,
  utils::overflow_error
};

use bitcoin::hashes::Hash;
use bitcoin::{Txid, Block, Transaction};

use anyhow::{anyhow, Result};
use std::io::Cursor;

mod bamboo_image;
use bamboo_image::BAMBOO_IMAGE;

const WIN_MULTIPLIER: u128 = 2;

const BAMBOO_ALKANE_ID: AlkaneId = AlkaneId {
  block: 0x2,
  tx: 0x533,
};

#[derive(Default)]
pub struct BambooRoll(());

impl AlkaneResponder for BambooRoll {}

#[derive(MessageDispatch)]
enum BambooRollMessage {
  #[opcode(0)]
  Initialize,

  #[opcode(42)]
  Donate,

  #[opcode(69)]
  Roll,

  #[opcode(99)]
  #[returns(String)]
  GetName,

  #[opcode(100)]
  #[returns(String)]
  GetSymbol,

  #[opcode(101)]
  #[returns(u128)]
  GetAvailableBamboo,
  
  #[opcode(1000)]
  #[returns(Vec<u8>)]
  GetData,
}

impl Token for BambooRoll {
  fn name(&self) -> String {
    return String::from("BAMBOO ROLL")
  }

  fn symbol(&self) -> String {
    return String::from("BROLL");
  }
}

impl BambooRoll {
  fn initialize(&self) -> Result<CallResponse> {
    self.observe_initialization()?;
    let context = self.context()?;

    let response = CallResponse::forward(&context.incoming_alkanes);
    Ok(response)
  }

  fn get_name(&self) -> Result<CallResponse> {
    let context = self.context()?;
    let mut response = CallResponse::forward(&context.incoming_alkanes);

    response.data = self.name().into_bytes();

    Ok(response)
  }

  fn get_symbol(&self) -> Result<CallResponse> {
    let context = self.context()?;
    let mut response = CallResponse::forward(&context.incoming_alkanes);

    response.data = self.symbol().into_bytes();

    Ok(response)
  }

  fn get_available_bamboo(&self) -> Result<CallResponse> {
    let context = self.context()?;
    let mut response = CallResponse::forward(&context.incoming_alkanes);

    response.data = self.available_bamboo().to_le_bytes().to_vec();

    Ok(response)
  }

  fn get_data(&self) -> Result<CallResponse> {
    let context = self.context()?;
    let mut response = CallResponse::forward(&context.incoming_alkanes);

    response.data = BAMBOO_IMAGE.to_vec();

    Ok(response)
  }

  fn donate(&self) -> Result<CallResponse> {
    let context = self.context()?;

    if context.incoming_alkanes.0.len() != 1 {
      return Err(anyhow!(
        "Incoming alkanes must be BAMBOO tokens"
      ));
    }

    let transfer = context.incoming_alkanes.0[0].clone();
    if transfer.id != BAMBOO_ALKANE_ID {
      return Err(anyhow!("Incoming alkane is not BAMBOO token"));
    }

    self.increase_available_bamboo(transfer.value)?;

    Ok(CallResponse::default())
  }

  fn roll(&self) -> Result<CallResponse> {
    let context = self.context()?;
    let txid = self.transaction_id()?;

    // Enforce one roll per transaction
    if self.has_tx_hash(&txid) {
      return Err(anyhow!("Transaction already used for roll"));
    }
    
    if context.incoming_alkanes.0.len() != 1 {
      return Err(anyhow!(
        "Incoming alkanes must be BAMBOO tokens"
      ));
    }

    let transfer = context.incoming_alkanes.0[0].clone();
    if transfer.id != BAMBOO_ALKANE_ID {
      return Err(anyhow!("Incoming alkane is not BAMBOO token"));
    }

    let available_bamboo = self.available_bamboo();
    if available_bamboo < transfer.value {
      return Err(anyhow!("Not enough BAMBOO available to roll. Have: {}, Need: {}", available_bamboo, transfer.value));
    }

    self.add_tx_hash(&txid)?;

    let multiplier = self.calculate_random_multiplier(&txid)?;

    if multiplier == 0 {
      self.increase_available_bamboo(transfer.value)?;
      Ok(CallResponse::default())
    } else {
      self.decrease_available_bamboo(transfer.value)?;

      let mut response = CallResponse::default();
      let win_amount = transfer.value.checked_mul(WIN_MULTIPLIER)
        .ok_or_else(|| anyhow!("Win amount calculation overflow"))?;

      response.alkanes.0.push(AlkaneTransfer {
        id: BAMBOO_ALKANE_ID,
        value: win_amount,
      }); 

      Ok(response)
    }
  }

  fn available_bamboo_pointer(&self) -> StoragePointer {
    StoragePointer::from_keyword("/available_bamboo")
  }

  fn available_bamboo(&self) -> u128 {
    self.available_bamboo_pointer().get_value::<u128>()
  }

  fn set_available_bamboo(&self, v: u128) {
    self.available_bamboo_pointer().set_value::<u128>(v);
  }

  fn increase_available_bamboo(&self, v: u128) -> Result<()> {
    self.set_available_bamboo(overflow_error(self.available_bamboo().checked_add(v))?);
    Ok(())
  }

  fn decrease_available_bamboo(&self, v: u128) -> Result<()> {
    self.set_available_bamboo(overflow_error(self.available_bamboo().checked_sub(v))?);
    Ok(())
  }

  fn calculate_random_multiplier(&self, txid: &Txid) -> Result<u128> {
    let block_hash = self.block_hash()?;
    let txid_bytes = txid.as_byte_array();

    let value = block_hash[31].wrapping_add(txid_bytes[31]);

    Ok(if value < 141 { 0 } else { 2 })
  }

  fn current_block(&self) -> Result<Block> {
    Ok(AuxpowBlock::parse(&mut Cursor::<Vec<u8>>::new(self.block()))?.to_consensus())
  }

  fn block_hash(&self) -> Result<Vec<u8>> {
    let hash = self.current_block()?.block_hash().as_byte_array().to_vec();
    Ok(hash)
  }

  fn transaction_id(&self) -> Result<Txid> {
    Ok(
      consensus_decode::<Transaction>(&mut std::io::Cursor::new(self.transaction()))?
        .compute_txid(),
    )
  }

  fn has_tx_hash(&self, txid: &Txid) -> bool {
    StoragePointer::from_keyword("/tx-hashes/")
      .select(&txid.as_byte_array().to_vec())
      .get_value::<u8>()
      == 1
  }

  fn add_tx_hash(&self, txid: &Txid) -> Result<()> {
    StoragePointer::from_keyword("/tx-hashes/")
      .select(&txid.as_byte_array().to_vec())
      .set_value::<u8>(0x01);

    Ok(())
  }
}

declare_alkane! {
  impl AlkaneResponder for BambooRoll {
    type Message = BambooRollMessage;
  }
}
