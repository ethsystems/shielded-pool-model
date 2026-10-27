//! Reviewed RPC mirrors. Source and exact region hashes: source/manifest.json.
//! Async wrappers are retained. Trait effect calls are synchronous because async traits fail.
//! Alloy ABI builders become typed Request values with a provider handle and contract address.
//! RPC effects are trait parameters. No ABI, transport, signer, or chain correctness is proved.
//! Errors retain category and opaque payload; diagnostic string construction is abstract.
//! Word is two u128 halves; Address is 20 bytes; bytes are Vec<u8>.
use vstd::prelude::*;
verus! {
#[derive(Clone, Copy)]
pub struct Word { pub hi: u128, pub lo: u128 }
pub type Address = [u8;20];
pub struct Receipt { pub tx_hash: Word, pub block_number: Option<u64>, pub gas_used: u64, pub success: bool }
pub struct TxReceipt { pub tx_hash: Word, pub block_number: u64, pub gas_used: u64, pub success: bool }
pub struct Attestation { pub leaf: Word, pub index: u64, pub attester: Address, pub issued_at: u64, pub expires_at: u64 }
pub struct Event { pub leaf: Word, pub attester: Address, pub issued_at: u64, pub expires_at: u64 }
pub enum Error { Contract(u64), Transaction(u64), Reverted, InvalidResponse, Signer(u64), Rpc(u64) }
pub enum Request {
 CommitmentRoot(u64,Address), CommitmentCount(u64,Address), Nullifier(u64,Address,Word), KnownRoot(u64,Address,Word), Supported(u64,Address,Address),
 AttestationRoot(u64,Address), AttestationCount(u64,Address), AttestationLeaf(u64,Address,u64), Authorized(u64,Address,Address), Balance(u64,Address,Address),
 Deposit(u64,Address,Vec<u8>,Word,Address,Word,Address,Vec<u8>),
 Transfer(u64,Address,Vec<u8>,[Word;2],[Word;2],Word,Vec<u8>),
 Withdraw(u64,Address,Vec<u8>,Word,Address,Word,Address,Word),
 AddAttester(u64,Address,Address), AddAttestation(u64,Address,Word,u64), AddToken(u64,Address,Address), Approve(u64,Address,Address,Word),
}
pub enum RequestView {

 CommitmentRoot(u64,Address), CommitmentCount(u64,Address), Nullifier(u64,Address,Word), KnownRoot(u64,Address,Word), Supported(u64,Address,Address),
 AttestationRoot(u64,Address), AttestationCount(u64,Address), AttestationLeaf(u64,Address,u64), Authorized(u64,Address,Address), Balance(u64,Address,Address),
 Deposit(u64,Address,Seq<u8>,Word,Address,Word,Address,Seq<u8>),
 Transfer(u64,Address,Seq<u8>,[Word;2],[Word;2],Word,Seq<u8>),
 Withdraw(u64,Address,Seq<u8>,Word,Address,Word,Address,Word),
 AddAttester(u64,Address,Address), AddAttestation(u64,Address,Word,u64), AddToken(u64,Address,Address), Approve(u64,Address,Address,Word),
}
impl Request {pub open spec fn view(&self) -> RequestView {match *self {Request::CommitmentRoot(f0,f1)=>RequestView::CommitmentRoot(f0,f1),Request::CommitmentCount(f0,f1)=>RequestView::CommitmentCount(f0,f1),Request::Nullifier(f0,f1,f2)=>RequestView::Nullifier(f0,f1,f2),Request::KnownRoot(f0,f1,f2)=>RequestView::KnownRoot(f0,f1,f2),Request::Supported(f0,f1,f2)=>RequestView::Supported(f0,f1,f2),Request::AttestationRoot(f0,f1)=>RequestView::AttestationRoot(f0,f1),Request::AttestationCount(f0,f1)=>RequestView::AttestationCount(f0,f1),Request::AttestationLeaf(f0,f1,f2)=>RequestView::AttestationLeaf(f0,f1,f2),Request::Authorized(f0,f1,f2)=>RequestView::Authorized(f0,f1,f2),Request::Balance(f0,f1,f2)=>RequestView::Balance(f0,f1,f2),Request::Deposit(f0,f1,f2,f3,f4,f5,f6,f7)=>RequestView::Deposit(f0,f1,f2@,f3,f4,f5,f6,f7@),Request::Transfer(f0,f1,f2,f3,f4,f5,f6)=>RequestView::Transfer(f0,f1,f2@,f3,f4,f5,f6@),Request::Withdraw(f0,f1,f2,f3,f4,f5,f6,f7)=>RequestView::Withdraw(f0,f1,f2@,f3,f4,f5,f6,f7),Request::AddAttester(f0,f1,f2)=>RequestView::AddAttester(f0,f1,f2),Request::AddAttestation(f0,f1,f2,f3)=>RequestView::AddAttestation(f0,f1,f2,f3),Request::AddToken(f0,f1,f2)=>RequestView::AddToken(f0,f1,f2),Request::Approve(f0,f1,f2,f3)=>RequestView::Approve(f0,f1,f2,f3)}}}
pub trait RpcApi {
 spec fn word(q: RequestView) -> Result<Word,u64>;
 spec fn boolean(q: RequestView) -> Result<bool,u64>;
 spec fn sent(q: RequestView) -> Result<u64,u64>;
 spec fn receipt(pending: u64) -> Result<Receipt,u64>;
 spec fn events(receipt: Receipt) -> Seq<Option<Event>>;
 fn call_word(q: Request) -> (r: Result<Word,u64>) ensures r == Self::word(q.view());
 fn call_bool(q: Request) -> (r: Result<bool,u64>) ensures r == Self::boolean(q.view());
 fn send(q: Request) -> (r: Result<u64,u64>) ensures r == Self::sent(q.view());
 fn get_receipt(pending: u64) -> (r: Result<Receipt,u64>) ensures r == Self::receipt(pending);
 fn decoded_logs(receipt: &Receipt) -> (r: Vec<Option<Event>>) ensures r@ == Self::events(*receipt);
}
pub trait Setup {
 spec fn signer(key: Seq<u8>) -> Result<Address,u64>;
 spec fn url(url: Seq<u8>) -> Result<u64,u64>;
 spec fn provider(signer: Address, url: u64) -> u64;
 fn parse_key(key: &Vec<u8>) -> (r: Result<Address,u64>) ensures r == Self::signer(key@);
 fn parse_url(url: &Vec<u8>) -> (r: Result<u64,u64>) ensures r == Self::url(url@);
 fn connect(signer: Address, url: u64) -> (r: u64) ensures r == Self::provider(signer,url);
}
pub struct EthereumRpc { pub provider: u64, pub shielded_pool: Address, pub attestation_registry: Address, pub signer_address: Address }
pub open spec fn fits64(w: Word) -> bool { w.hi == 0 && w.lo <= u64::MAX }
pub fn try64(w: Word) -> (r: Option<u64>)
 ensures (r is Some) == fits64(w), r is Some ==> r->Some_0 as int == w.lo as int,
{ if w.hi == 0 && w.lo <= u64::MAX as u128 { Some(w.lo as u64) } else { None } }
pub open spec fn converted(r: Receipt) -> TxReceipt { TxReceipt {tx_hash:r.tx_hash, block_number: if r.block_number is Some {r.block_number->Some_0} else {0}, gas_used:r.gas_used, success:r.success} }
pub fn convert_receipt(r: &Receipt) -> (v: TxReceipt) ensures v == converted(*r),
{ TxReceipt {tx_hash:r.tx_hash,block_number:r.block_number.unwrap_or(0),gas_used:r.gas_used,success:r.success} }
pub open spec fn word_result(r: Result<Word,u64>) -> Result<Word,Error> { match r {Ok(w)=>Ok(w), Err(e)=>Err(Error::Contract(e))} }
pub open spec fn bool_result(r: Result<bool,u64>) -> Result<bool,Error> { match r {Ok(w)=>Ok(w), Err(e)=>Err(Error::Contract(e))} }
pub open spec fn tx_result<A: RpcApi>(q: Request) -> Result<TxReceipt,Error> {
 match A::sent(q.view()) {Err(e)=>Err(Error::Transaction(e)), Ok(p)=>match A::receipt(p) {
 Err(e)=>Err(Error::Transaction(e)), Ok(r)=>if !r.success {Err(Error::Reverted)} else {Ok(converted(r))}}}
}
pub fn clone_bytes(b: &Vec<u8>) -> (r: Vec<u8>) ensures r@ == b@,
{ let mut r=Vec::new(); let mut i=0; while i < b.len() invariant i <= b.len(), r@ == b@.take(i as int), decreases b.len()-i,
 {r.push(b[i]); i+=1;} r }
pub struct DepositProof {pub proof: Vec<u8>}
pub struct TransferProof {pub proof: Vec<u8>}
pub struct WithdrawProof {pub proof: Vec<u8>}

pub open spec fn first_event(logs: Seq<Option<Event>>) -> Option<Event>
 decreases logs.len(),
{ if logs.len()==0 {None} else {match logs[0] {Some(e)=>Some(e),None=>first_event(logs.drop_first())}} }
pub open spec fn attestation(e: Event,index: u64) -> Attestation { Attestation {leaf:e.leaf,index,attester:e.attester,issued_at:e.issued_at,expires_at:e.expires_at} }
pub fn find_event(logs: &Vec<Option<Event>>, index: u64) -> (r: Option<Attestation>)
 ensures r == match first_event(logs@) {None=>None,Some(e)=>Some(attestation(e,index))},
{
 let mut i=0;
 proof {assert(logs@.skip(0) =~= logs@);}
 while i<logs.len()
 invariant i<=logs.len(), first_event(logs@) == first_event(logs@.skip(i as int)),
 decreases logs.len()-i,
 {
  match &logs[i] {
   Some(e)=>{return Some(Attestation {leaf:e.leaf,index,attester:e.attester,issued_at:e.issued_at,expires_at:e.expires_at});},
   None=>{}
  }
  proof {assert(logs@.skip(i as int).drop_first() =~= logs@.skip(i as int + 1));}
  i+=1;
 }
 None
}
pub open spec fn added<A: RpcApi>(q: Request, countq: Request) -> Result<(Attestation,TxReceipt),Error> {
 match A::word(countq.view()) {Err(e)=>Err(Error::Contract(e)),Ok(count)=>match A::sent(q.view()) {
 Err(e)=>Err(Error::Transaction(e)),Ok(p)=>match A::receipt(p) {Err(e)=>Err(Error::Transaction(e)),Ok(receipt)=>
 if !receipt.success {Err(Error::Reverted)} else {match first_event(A::events(receipt)) {
 None=>Err(Error::InvalidResponse),Some(e)=>Ok((attestation(e,count.lo as u64),converted(receipt)))}}}}}
}

impl EthereumRpc {
pub async fn new<S: Setup>(rpc_url: &Vec<u8>, private_key: &Vec<u8>, shielded_pool: Address, attestation_registry: Address) -> (r: Result<EthereumRpc,Error>)
 ensures r == match S::signer(private_key@) {Err(e)=>Err(Error::Signer(e)),Ok(signer)=>match S::url(rpc_url@) {Err(e)=>Err(Error::Rpc(e)),Ok(url)=>Ok(EthereumRpc {provider:S::provider(signer,url),shielded_pool,attestation_registry,signer_address:signer})}},
 // STRENGTH new
{
 let signer_address = match S::parse_key(private_key) {Ok(s)=>s,Err(e)=>return Err(Error::Signer(e))};
 let url = match S::parse_url(rpc_url) {Ok(u)=>u,Err(e)=>return Err(Error::Rpc(e))};
 let provider=S::connect(signer_address,url);
 Ok(EthereumRpc {provider,shielded_pool,attestation_registry,signer_address})
}

pub async fn get_commitment_root<A: RpcApi>(&self) -> (r: Result<Word,Error>)
 ensures r == word_result(A::word((Request::CommitmentRoot(self.provider,self.shielded_pool)).view())),
 // STRENGTH get_commitment_root
{
 let result = A::call_word(Request::CommitmentRoot(self.provider,self.shielded_pool));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn is_nullifier_spent<A: RpcApi>(&self, nullifier: Word) -> (r: Result<bool,Error>)
 ensures r == bool_result(A::boolean((Request::Nullifier(self.provider,self.shielded_pool,nullifier)).view())),
 // STRENGTH is_nullifier_spent
{
 let result = A::call_bool(Request::Nullifier(self.provider,self.shielded_pool,nullifier));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn is_known_root<A: RpcApi>(&self, root: Word) -> (r: Result<bool,Error>)
 ensures r == bool_result(A::boolean((Request::KnownRoot(self.provider,self.shielded_pool,root)).view())),
 // STRENGTH is_known_root
{
 let result = A::call_bool(Request::KnownRoot(self.provider,self.shielded_pool,root));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn is_token_supported<A: RpcApi>(&self, token: Address) -> (r: Result<bool,Error>)
 ensures r == bool_result(A::boolean((Request::Supported(self.provider,self.shielded_pool,token)).view())),
 // STRENGTH is_token_supported
{
 let result = A::call_bool(Request::Supported(self.provider,self.shielded_pool,token));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn get_attestation_root<A: RpcApi>(&self) -> (r: Result<Word,Error>)
 ensures r == word_result(A::word((Request::AttestationRoot(self.provider,self.attestation_registry)).view())),
 // STRENGTH get_attestation_root
{
 let result = A::call_word(Request::AttestationRoot(self.provider,self.attestation_registry));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn is_authorized_attester<A: RpcApi>(&self, attester: Address) -> (r: Result<bool,Error>)
 ensures r == bool_result(A::boolean((Request::Authorized(self.provider,self.attestation_registry,attester)).view())),
 // STRENGTH is_authorized_attester
{
 let result = A::call_bool(Request::Authorized(self.provider,self.attestation_registry,attester));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn get_token_balance<A: RpcApi>(&self, token: Address, account: Address) -> (r: Result<Word,Error>)
 ensures r == word_result(A::word((Request::Balance(self.provider,token,account)).view())),
 // STRENGTH get_token_balance
{
 let result = A::call_word(Request::Balance(self.provider,token,account));
 match result {Ok(value)=>Ok(value),Err(e)=>Err(Error::Contract(e))}
}

pub async fn get_commitment_count<A: RpcApi>(&self) -> (r: Result<u64,Error>)
 
 ensures r == match A::word((Request::CommitmentCount(self.provider,self.shielded_pool)).view()) {Err(e)=>Err(Error::Contract(e)),Ok(w)=>Ok(if fits64(w) {w.lo as u64} else {u64::MAX})},
 // STRENGTH get_commitment_count
{
 let result=match A::call_word(Request::CommitmentCount(self.provider,self.shielded_pool)) {Ok(w)=>w,Err(e)=>return Err(Error::Contract(e))};
 Ok(try64(result).unwrap_or(u64::MAX))
}

pub async fn get_attestation_count<A: RpcApi>(&self) -> (r: Result<u64,Error>)
 requires A::word((Request::AttestationCount(self.provider,self.attestation_registry)).view()) is Ok ==> fits64(A::word((Request::AttestationCount(self.provider,self.attestation_registry)).view())->Ok_0),
 ensures r == match A::word((Request::AttestationCount(self.provider,self.attestation_registry)).view()) {Err(e)=>Err(Error::Contract(e)),Ok(w)=>Ok(w.lo as u64)},
 // STRENGTH get_attestation_count
{
 let result=match A::call_word(Request::AttestationCount(self.provider,self.attestation_registry)) {Ok(w)=>w,Err(e)=>return Err(Error::Contract(e))};
 Ok(try64(result).unwrap())
}

pub async fn get_attestation_leaf<A: RpcApi>(&self, index: u64) -> (r: Result<Word,Error>)
 requires index < 1099511627776u64,
 ensures r == word_result(A::word((Request::AttestationLeaf(self.provider,self.attestation_registry,index)).view())),
 // STRENGTH get_attestation_leaf
{
 let index40 = if index < 1099511627776u64 {Some(index)} else {None};
 let result=A::call_word(Request::AttestationLeaf(self.provider,self.attestation_registry,index40.unwrap()));
 match result {Ok(w)=>Ok(w),Err(e)=>Err(Error::Contract(e))}
}

pub async fn deposit<A: RpcApi>(&self, proof: &DepositProof, commitment: Word, token: Address, amount: Word, funding_address: Address, encrypted_note: Vec<u8>) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::Deposit(self.provider,self.shielded_pool,proof.proof,commitment,token,amount,funding_address,encrypted_note)),
 // STRENGTH deposit
{
 let pending=match A::send(Request::Deposit(self.provider,self.shielded_pool,clone_bytes(&proof.proof),commitment,token,amount,funding_address,encrypted_note)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn transfer<A: RpcApi>(&self, proof: &TransferProof, nullifiers: [Word;2], commitments: [Word;2], root: Word, encrypted_notes: Vec<u8>) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::Transfer(self.provider,self.shielded_pool,proof.proof,nullifiers,commitments,root,encrypted_notes)),
 // STRENGTH transfer
{
 let pending=match A::send(Request::Transfer(self.provider,self.shielded_pool,clone_bytes(&proof.proof),nullifiers,commitments,root,encrypted_notes)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn withdraw<A: RpcApi>(&self, proof: &WithdrawProof, nullifier: Word, token: Address, amount: Word, recipient: Address, root: Word) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::Withdraw(self.provider,self.shielded_pool,proof.proof,nullifier,token,amount,recipient,root)),
 // STRENGTH withdraw
{
 let pending=match A::send(Request::Withdraw(self.provider,self.shielded_pool,clone_bytes(&proof.proof),nullifier,token,amount,recipient,root)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn add_attester<A: RpcApi>(&self, attester: Address) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::AddAttester(self.provider,self.attestation_registry,attester)),
 // STRENGTH add_attester
{
 let pending=match A::send(Request::AddAttester(self.provider,self.attestation_registry,attester)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn add_supported_token<A: RpcApi>(&self, token: Address) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::AddToken(self.provider,self.shielded_pool,token)),
 // STRENGTH add_supported_token
{
 let pending=match A::send(Request::AddToken(self.provider,self.shielded_pool,token)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn approve_token<A: RpcApi>(&self, token: Address, amount: Word) -> (r: Result<TxReceipt,Error>)
 ensures r == tx_result::<A>(Request::Approve(self.provider,token,self.shielded_pool,amount)),
 // STRENGTH approve_token
{
 let pending=match A::send(Request::Approve(self.provider,token,self.shielded_pool,amount)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 Ok(convert_receipt(&receipt))
}

pub async fn add_attestation<A: RpcApi>(&self, subject_pubkey_hash: Word, expires_at: u64) -> (r: Result<(Attestation,TxReceipt),Error>)
 requires A::word((Request::AttestationCount(self.provider,self.attestation_registry)).view()) is Ok ==> fits64(A::word((Request::AttestationCount(self.provider,self.attestation_registry)).view())->Ok_0),
 ensures r == added::<A>(Request::AddAttestation(self.provider,self.attestation_registry,subject_pubkey_hash,expires_at),Request::AttestationCount(self.provider,self.attestation_registry)),
 // STRENGTH add_attestation
{
 let index_before=match self.get_attestation_count::<A>().await {Ok(c)=>c,Err(e)=>return Err(e)};
 let pending=match A::send(Request::AddAttestation(self.provider,self.attestation_registry,subject_pubkey_hash,expires_at)) {Ok(p)=>p,Err(e)=>return Err(Error::Transaction(e))};
 let receipt=match A::get_receipt(pending) {Ok(r)=>r,Err(e)=>return Err(Error::Transaction(e))};
 if !receipt.success {return Err(Error::Reverted);}
 let logs=A::decoded_logs(&receipt);
 let event_data=match find_event(&logs,index_before) {Some(e)=>e,None=>return Err(Error::InvalidResponse)};
 Ok((event_data,convert_receipt(&receipt)))
}
}
fn main() {}
}
