//! Reviewed prover cores. Source regions: source/manifest.json; transformations: README.md.
//! Domain values use full-width records. Formatter/prover effects remain generic contracts.
//! Circuit argument construction is extracted; file/process lifecycle is modeled separately.
//! All witness fields are retained. Formatting requires the integer bounds read in prover_fmt.rs.
use vstd::prelude::*;
verus! {
#[derive(Clone,Copy)]
pub struct Amount { pub hi: u128, pub lo: u128 }
pub type Word = [u8;32];
pub type Address = [u8;20];
pub enum Error {InvalidAmount, InvalidTokens, Effect(u64)}
pub struct Note {pub token: Address,pub amount: Amount,pub owner_pubkey: Word,pub salt: Word}
pub struct MerkleProof {pub path: Vec<Word>,pub indices: Vec<u8>,pub leaf_index: u64,pub proof_length: usize}
pub struct DepositWitness {pub commitment: Word,pub token: Address,pub amount: Amount,pub funding_address: Address,pub attestation_root: Word,pub payload_hash: Word,pub spending_key: Word,pub owner_pubkey: Word,pub salt: Word,pub attester: Address,pub issued_at: u64,pub expires_at: u64,pub attestation_proof: MerkleProof}
pub struct TransferWitness {pub nullifiers: [Word;2],pub output_commitments: [Word;2],pub commitment_root: Word,pub payload_hash: Word,pub spending_key: Word,pub input_notes: [Note;2],pub output_notes: [Note;2],pub input_proofs: [MerkleProof;2]}
pub struct WithdrawWitness {pub nullifier: Word,pub token: Address,pub amount: Amount,pub recipient: Address,pub commitment_root: Word,pub spending_key: Word,pub note: Note,pub commitment_proof: MerkleProof}
pub struct DepositProof {pub proof: Vec<u8>,pub commitment: Word,pub token: Address,pub amount: Amount,pub funding_address: Address,pub attestation_root: Word,pub payload_hash: Word}
pub struct TransferProof {pub proof: Vec<u8>,pub nullifiers: [Word;2],pub output_commitments: [Word;2],pub commitment_root: Word,pub payload_hash: Word}
pub struct WithdrawProof {pub proof: Vec<u8>,pub nullifier: Word,pub token: Address,pub amount: Amount,pub recipient: Address,pub commitment_root: Word}
pub enum Circuit {Deposit,Transfer,Withdraw}
pub trait Effects {
 spec fn deposit_text(w: DepositWitness) -> Seq<u8>;
 spec fn transfer_text(w: TransferWitness) -> Seq<u8>;
 spec fn withdraw_text(w: WithdrawWitness) -> Seq<u8>;
 spec fn proof(circuit: Circuit, text: Seq<u8>) -> Result<Seq<u8>,u64>;
 fn format_deposit(w: &DepositWitness) -> (r: Vec<u8>) requires deposit_format_ok(*w), ensures r@ == Self::deposit_text(*w);
 fn format_transfer(w: &TransferWitness) -> (r: Vec<u8>) requires transfer_format_ok(*w), ensures r@ == Self::transfer_text(*w);
 fn format_withdraw(w: &WithdrawWitness) -> (r: Vec<u8>) requires withdraw_format_ok(*w), ensures r@ == Self::withdraw_text(*w);
 fn prove(circuit: Circuit,text: &Vec<u8>) -> (r: Result<Vec<u8>,u64>)
 ensures (r is Ok) == (Self::proof(circuit,text@) is Ok),
 r is Ok ==> r->Ok_0@ == Self::proof(circuit,text@)->Ok_0,
 r is Err ==> r->Err_0 == Self::proof(circuit,text@)->Err_0;
}
pub open spec fn deposit_valid(w: DepositWitness) -> bool { w.amount.hi == 0 && w.amount.lo > 0 }
pub fn validate_amount(w: &DepositWitness) -> (r: bool) ensures r == deposit_valid(*w),
 {w.amount.hi == 0 && w.amount.lo > 0}

pub open spec fn deposit_format_ok(w: DepositWitness) -> bool { w.issued_at <= i64::MAX && w.expires_at <= i64::MAX && w.attestation_proof.proof_length <= i64::MAX }
pub open spec fn transfer_format_ok(w: TransferWitness) -> bool {w.input_proofs[0].proof_length <= i64::MAX && w.input_proofs[1].proof_length <= i64::MAX}
pub open spec fn withdraw_format_ok(w: WithdrawWitness) -> bool {w.commitment_proof.proof_length <= i64::MAX}
pub open spec fn sum_ok(a: Amount,b: Amount) -> bool {a.hi==0 && b.hi==0 && a.lo+b.lo <= u128::MAX}
pub open spec fn transfer_amounts_valid(w: TransferWitness) -> bool {sum_ok(w.input_notes[0].amount,w.input_notes[1].amount) && sum_ok(w.output_notes[0].amount,w.output_notes[1].amount) && w.input_notes[0].amount.lo+w.input_notes[1].amount.lo == w.output_notes[0].amount.lo+w.output_notes[1].amount.lo}
pub open spec fn transfer_tokens_valid(w: TransferWitness) -> bool {w.input_notes[1].token@ == w.input_notes[0].token@ && w.output_notes[0].token@ == w.input_notes[0].token@ && w.output_notes[1].token@ == w.input_notes[0].token@}
pub fn checked_sum(a: Amount,b: Amount) -> (r: Option<u128>)
 ensures (r is Some) == sum_ok(a,b), r is Some ==> r->Some_0 == a.lo+b.lo,
 {if a.hi != 0 || b.hi != 0 {None} else {a.lo.checked_add(b.lo)}}
pub fn validate_amounts(w: &TransferWitness) -> (r: bool) ensures r == transfer_amounts_valid(*w),
 {match (checked_sum(w.input_notes[0].amount,w.input_notes[1].amount),checked_sum(w.output_notes[0].amount,w.output_notes[1].amount)) {(Some(a),Some(b))=>a==b,_=>false}}
pub fn address_eq(a: &Address,b: &Address) -> (r: bool) ensures r == (a@==b@),
 {let mut i=0;while i<20 invariant i<=20,forall|j:int| 0<=j<i ==> a@[j]==b@[j],decreases 20-i,
 {if a[i]!=b[i] {return false;}i+=1;}proof {assert(a@ =~= b@);}true}
pub fn validate_tokens(w: &TransferWitness) -> (r: bool) ensures r == transfer_tokens_valid(*w),
 {address_eq(&w.input_notes[1].token,&w.input_notes[0].token) && address_eq(&w.output_notes[0].token,&w.input_notes[0].token) && address_eq(&w.output_notes[1].token,&w.input_notes[0].token)}

pub fn copy_bytes(bytes: &[u8]) -> (r: Vec<u8>) ensures r@ == bytes@,
 {let mut r=Vec::new();let mut i=0;while i<bytes.len() invariant i<=bytes.len(),r@==bytes@.take(i as int),decreases bytes.len()-i,
 {r.push(bytes[i]);i+=1;}r}
pub fn append(out: &mut Vec<u8>, bytes: &[u8])
 ensures final(out)@ == old(out)@ + bytes@,
 {let ghost before=out@;let mut i=0;while i<bytes.len() invariant i<=bytes.len(),out@ == before + bytes@.take(i as int),decreases bytes.len()-i,
 {out.push(bytes[i]);i+=1;}}
pub struct Commands {pub nargo: Vec<Vec<u8>>, pub bb: Vec<Vec<u8>>}
pub open spec fn nargo_args() -> Seq<Seq<u8>> { seq![seq![101u8,120,101,99,117,116,101],seq![119u8,105,116,110,101,115,115]] }
pub open spec fn bb_args(target: Seq<u8>,circuit: Seq<u8>) -> Seq<Seq<u8>> {
 seq![seq![112u8,114,111,118,101],seq![45u8,98],target+seq![47u8]+circuit+seq![46u8,106,115,111,110],seq![45u8,119],target+seq![47u8,119,105,116,110,101,115,115,46,103,122],seq![45u8,45,119,114,105,116,101,95,118,107],seq![45u8,116],seq![101u8,118,109],seq![45u8,111],target+seq![47u8]]
}
pub open spec fn args_view(args: Vec<Vec<u8>>) -> Seq<Seq<u8>> {args@.map(|i:int,v:Vec<u8>| v@)}
pub async fn prove_deposit<E: Effects>(witness: &DepositWitness) -> (r: Result<DepositProof,Error>)
 requires (deposit_valid(*witness)) ==> deposit_format_ok(*witness),
 ensures !(deposit_valid(*witness)) ==> r is Err && r->Err_0 == Error::InvalidAmount,
 (deposit_valid(*witness)) ==> ((r is Ok) == (E::proof(Circuit::Deposit,E::deposit_text(*witness)) is Ok)),
 (deposit_valid(*witness)) && r is Err ==> r->Err_0 == Error::Effect(E::proof(Circuit::Deposit,E::deposit_text(*witness))->Err_0),
 r is Ok ==> r->Ok_0.proof@ == E::proof(Circuit::Deposit,E::deposit_text(*witness))->Ok_0,
 r is Ok ==> r->Ok_0.commitment == witness.commitment,
 r is Ok ==> r->Ok_0.token == witness.token,
 r is Ok ==> r->Ok_0.amount == witness.amount,
 r is Ok ==> r->Ok_0.funding_address == witness.funding_address,
 r is Ok ==> r->Ok_0.attestation_root == witness.attestation_root,
 r is Ok ==> r->Ok_0.payload_hash == witness.payload_hash,
 // STRENGTH prove_deposit
{
 if !validate_amount(witness) {return Err(Error::InvalidAmount);}
 let prover_toml=E::format_deposit(witness);
 let proof_bytes=match E::prove(Circuit::Deposit,&prover_toml) {Ok(b)=>b,Err(e)=>return Err(Error::Effect(e))};
 Ok(DepositProof {proof:proof_bytes,commitment:witness.commitment,token:witness.token,amount:witness.amount,funding_address:witness.funding_address,attestation_root:witness.attestation_root,payload_hash:witness.payload_hash})
}

pub async fn prove_transfer<E: Effects>(witness: &TransferWitness) -> (r: Result<TransferProof,Error>)
 requires (transfer_amounts_valid(*witness) && transfer_tokens_valid(*witness)) ==> transfer_format_ok(*witness),
 ensures !(transfer_amounts_valid(*witness) && transfer_tokens_valid(*witness)) ==> (r is Err && r->Err_0 == if !transfer_amounts_valid(*witness) {Error::InvalidAmount} else {Error::InvalidTokens}),
 (transfer_amounts_valid(*witness) && transfer_tokens_valid(*witness)) ==> ((r is Ok) == (E::proof(Circuit::Transfer,E::transfer_text(*witness)) is Ok)),
 (transfer_amounts_valid(*witness) && transfer_tokens_valid(*witness)) && r is Err ==> r->Err_0 == Error::Effect(E::proof(Circuit::Transfer,E::transfer_text(*witness))->Err_0),
 r is Ok ==> r->Ok_0.proof@ == E::proof(Circuit::Transfer,E::transfer_text(*witness))->Ok_0,
 r is Ok ==> r->Ok_0.nullifiers == witness.nullifiers,
 r is Ok ==> r->Ok_0.output_commitments == witness.output_commitments,
 r is Ok ==> r->Ok_0.commitment_root == witness.commitment_root,
 r is Ok ==> r->Ok_0.payload_hash == witness.payload_hash,
 // STRENGTH prove_transfer
{
 if !validate_amounts(witness) {return Err(Error::InvalidAmount);}
 if !validate_tokens(witness) {return Err(Error::InvalidTokens);}
 let prover_toml=E::format_transfer(witness);
 let proof_bytes=match E::prove(Circuit::Transfer,&prover_toml) {Ok(b)=>b,Err(e)=>return Err(Error::Effect(e))};
 Ok(TransferProof {proof:proof_bytes,nullifiers:witness.nullifiers,output_commitments:witness.output_commitments,commitment_root:witness.commitment_root,payload_hash:witness.payload_hash})
}

pub async fn prove_withdraw<E: Effects>(witness: &WithdrawWitness) -> (r: Result<WithdrawProof,Error>)
 requires (true) ==> withdraw_format_ok(*witness),
 ensures (true) ==> ((r is Ok) == (E::proof(Circuit::Withdraw,E::withdraw_text(*witness)) is Ok)),
 (true) && r is Err ==> r->Err_0 == Error::Effect(E::proof(Circuit::Withdraw,E::withdraw_text(*witness))->Err_0),
 r is Ok ==> r->Ok_0.proof@ == E::proof(Circuit::Withdraw,E::withdraw_text(*witness))->Ok_0,
 r is Ok ==> r->Ok_0.nullifier == witness.nullifier,
 r is Ok ==> r->Ok_0.token == witness.token,
 r is Ok ==> r->Ok_0.amount == witness.amount,
 r is Ok ==> r->Ok_0.recipient == witness.recipient,
 r is Ok ==> r->Ok_0.commitment_root == witness.commitment_root,
 // STRENGTH prove_withdraw
{
 
 let prover_toml=E::format_withdraw(witness);
 let proof_bytes=match E::prove(Circuit::Withdraw,&prover_toml) {Ok(b)=>b,Err(e)=>return Err(Error::Effect(e))};
 Ok(WithdrawProof {proof:proof_bytes,nullifier:witness.nullifier,token:witness.token,amount:witness.amount,recipient:witness.recipient,commitment_root:witness.commitment_root})
}

pub fn prove_circuit_args(target_display: &Vec<u8>, circuit_name: &Vec<u8>) -> (r: Commands)
 ensures args_view(r.nargo) == nargo_args(), args_view(r.bb) == bb_args(target_display@,circuit_name@),
 // STRENGTH prove_circuit_args
{
 let mut nargo=Vec::new();nargo.push(copy_bytes(&[101u8,120u8,101u8,99u8,117u8,116u8,101u8]));nargo.push(copy_bytes(&[119u8,105u8,116u8,110u8,101u8,115u8,115u8]));
 proof {assert(nargo@[0]@ == seq![101u8,120,101,99,117,116,101]); assert(nargo@[1]@ == seq![119u8,105,116,110,101,115,115]);}
 let mut bytecode=copy_bytes(target_display.as_slice());append(&mut bytecode,&[47u8]);append(&mut bytecode,circuit_name.as_slice());append(&mut bytecode,&[46u8,106u8,115u8,111u8,110u8]);
 let mut witness=copy_bytes(target_display.as_slice());append(&mut witness,&[47u8,119u8,105u8,116u8,110u8,101u8,115u8,115u8,46u8,103u8,122u8]);
 let mut output=copy_bytes(target_display.as_slice());append(&mut output,&[47u8]);
 let mut bb=Vec::new();bb.push(copy_bytes(&[112u8,114u8,111u8,118u8,101u8]));bb.push(copy_bytes(&[45u8,98u8]));bb.push(bytecode);bb.push(copy_bytes(&[45u8,119u8]));bb.push(witness);bb.push(copy_bytes(&[45u8,45u8,119u8,114u8,105u8,116u8,101u8,95u8,118u8,107u8]));bb.push(copy_bytes(&[45u8,116u8]));bb.push(copy_bytes(&[101u8,118u8,109u8]));bb.push(copy_bytes(&[45u8,111u8]));bb.push(output);
 proof {assert(bb@[0]@ =~= bb_args(target_display@,circuit_name@)[0]); assert(bb@[1]@ =~= bb_args(target_display@,circuit_name@)[1]); assert(bb@[2]@ =~= bb_args(target_display@,circuit_name@)[2]); assert(bb@[3]@ =~= bb_args(target_display@,circuit_name@)[3]); assert(bb@[4]@ =~= bb_args(target_display@,circuit_name@)[4]); assert(bb@[5]@ =~= bb_args(target_display@,circuit_name@)[5]); assert(bb@[6]@ =~= bb_args(target_display@,circuit_name@)[6]); assert(bb@[7]@ =~= bb_args(target_display@,circuit_name@)[7]); assert(bb@[8]@ =~= bb_args(target_display@,circuit_name@)[8]); assert(bb@[9]@ =~= bb_args(target_display@,circuit_name@)[9]);assert(args_view(nargo) =~= nargo_args()); assert(args_view(bb) =~= bb_args(target_display@,circuit_name@));}
 Commands {nargo,bb}
}

// Effect boundary for the complete prove_circuit control flow. Path values are opaque.
#[derive(Clone,Copy)]
pub enum Part {Manifest,Source,ProverToml,Target,Proof}
pub trait Paths {
 spec fn named(base: u64, name: Seq<u8>) -> u64;
 spec fn part(base: u64, part: Part) -> u64;
 spec fn display(path: u64) -> Seq<u8>;
 fn join_name(base: u64,name: &Vec<u8>) -> (r: u64) ensures r == Self::named(base,name@);
 fn join_part(base: u64,part: Part) -> (r: u64) ensures r == Self::part(base,part);
 fn display_path(path: u64) -> (r: Vec<u8>) ensures r@ == Self::display(path);
}
pub enum IoSpec {Create(u64),Copy(u64,u64),Canonical(u64),Symlink(u64,u64),Write(u64,Seq<u8>),Close(u64)}
pub enum Io {Create(u64),Copy(u64,u64),Canonical(u64),Symlink(u64,u64),Write(u64,Vec<u8>),Close(u64)}
impl Io {pub open spec fn view(&self)->IoSpec {match *self {
 Io::Create(p)=>IoSpec::Create(p),Io::Copy(a,b)=>IoSpec::Copy(a,b),Io::Canonical(p)=>IoSpec::Canonical(p),Io::Symlink(a,b)=>IoSpec::Symlink(a,b),Io::Write(p,b)=>IoSpec::Write(p,b@),Io::Close(p)=>IoSpec::Close(p)}}}
pub struct Output {pub success: bool,pub stderr: Vec<u8>}
pub trait Process {
 spec fn exists(path: u64) -> bool;
 spec fn temp(root: u64,prefix: Seq<u8>) -> Result<u64,u64>;
 spec fn io(op: IoSpec) -> Result<u64,u64>;
 spec fn output(binary: Seq<u8>,args: Seq<Seq<u8>>,cwd: u64,kill: bool) -> Result<(bool,Seq<u8>),u64>;
 spec fn read(path: u64) -> Result<Seq<u8>,u64>;
 fn path_exists(path: u64) -> (r: bool) ensures r == Self::exists(path);
 fn tempdir(root: u64,prefix: &Vec<u8>) -> (r: Result<u64,u64>) ensures r == Self::temp(root,prefix@);
 fn io_exec(op: Io) -> (r: Result<u64,u64>) ensures r == Self::io(op.view());
 fn run(binary: &Vec<u8>,args: &Vec<Vec<u8>>,cwd: u64,kill: bool) -> (r: Result<Output,u64>)
 ensures (r is Ok) == (Self::output(binary@,args_view(*args),cwd,kill) is Ok),
 r is Ok ==> r->Ok_0.success == Self::output(binary@,args_view(*args),cwd,kill)->Ok_0.0,
 r is Ok ==> r->Ok_0.stderr@ == Self::output(binary@,args_view(*args),cwd,kill)->Ok_0.1,
 r is Err ==> r->Err_0 == Self::output(binary@,args_view(*args),cwd,kill)->Err_0;
 fn read_file(path: u64) -> (r: Result<Vec<u8>,u64>)
 ensures (r is Ok) == (Self::read(path) is Ok),r is Ok ==> r->Ok_0@ == Self::read(path)->Ok_0,r is Err ==> r->Err_0 == Self::read(path)->Err_0;
}
pub enum ProcessError {NotFound,Io(u64),Witness(Seq<u8>),Generation(Seq<u8>)}
pub enum RunResult {Proof(Vec<u8>),Io(u64),NotFound,Witness(Vec<u8>),Generation(Vec<u8>)}
pub open spec fn run_view(r: RunResult) -> Result<Seq<u8>,ProcessError> {
 match r {RunResult::Proof(b)=>Ok(b@),RunResult::Io(e)=>Err(ProcessError::Io(e)),RunResult::NotFound=>Err(ProcessError::NotFound),RunResult::Witness(b)=>Err(ProcessError::Witness(b@)),RunResult::Generation(b)=>Err(ProcessError::Generation(b@))}
}
pub struct Settings {pub circuits_dir: u64,pub work_root: u64,pub nargo_binary: Vec<u8>,pub bb_binary: Vec<u8>}
pub open spec fn prefix() -> Seq<u8> {seq![115u8,104,105,101,108,100,101,100,45,112,111,111,108,45,112,114,111,118,101,45]}
pub open spec fn process_result<P: Paths,E: Process>(settings: Settings,circuit_name: Vec<u8>,prover_toml: Vec<u8>) -> Result<Seq<u8>,ProcessError> {
{let circuit_dir=P::named(settings.circuits_dir,circuit_name@); if !E::exists(circuit_dir) {Err(ProcessError::NotFound)} else {match E::temp(settings.work_root,prefix()) {Err(e)=>Err(ProcessError::Io(e)),Ok(work)=>{{let package_dir=P::named(work,circuit_name@); match E::io(IoSpec::Create(package_dir)) {Err(e)=>Err(ProcessError::Io(e)),Ok(_created)=>{match E::io(IoSpec::Copy(P::part(circuit_dir,Part::Manifest),P::part(package_dir,Part::Manifest))) {Err(e)=>Err(ProcessError::Io(e)),Ok(_copied)=>{match E::io(IoSpec::Canonical(P::part(circuit_dir,Part::Source))) {Err(e)=>Err(ProcessError::Io(e)),Ok(canonical)=>{match E::io(IoSpec::Symlink(canonical,P::part(package_dir,Part::Source))) {Err(e)=>Err(ProcessError::Io(e)),Ok(_linked)=>{match E::io(IoSpec::Write(P::part(package_dir,Part::ProverToml),prover_toml@)) {Err(e)=>Err(ProcessError::Io(e)),Ok(_written)=>{match E::output(settings.nargo_binary@,nargo_args(),package_dir,true) {Err(e)=>Err(ProcessError::Io(e)),Ok(nargo_status)=>{if !nargo_status.0 {Err(ProcessError::Witness(nargo_status.1))} else {{let target_dir=P::part(package_dir,Part::Target); match E::output(settings.bb_binary@,bb_args(P::display(target_dir),circuit_name@),package_dir,true) {Err(e)=>Err(ProcessError::Io(e)),Ok(bb_status)=>{if !bb_status.0 {Err(ProcessError::Generation(bb_status.1))} else {match E::read(P::part(target_dir,Part::Proof)) {Err(e)=>Err(ProcessError::Io(e)),Ok(proof)=>{match E::io(IoSpec::Close(work)) {Err(e)=>Err(ProcessError::Io(e)),Ok(_closed)=>{Ok(proof)}}}}}}}}}}}}}}}}}}}}}}}}}}
}
pub async fn prove_circuit<P: Paths,E: Process>(settings: &Settings,circuit_name: &Vec<u8>,prover_toml: &Vec<u8>) -> (r: RunResult)
 ensures run_view(r) == process_result::<P,E>(*settings,*circuit_name,*prover_toml),
 // STRENGTH prove_circuit
{
 let prefix_bytes=copy_bytes(&[115u8,104,105,101,108,100,101,100,45,112,111,111,108,45,112,114,111,118,101,45]);
let circuit_dir=P::join_name(settings.circuits_dir,circuit_name);
if !E::path_exists(circuit_dir) {return RunResult::NotFound;}
let work=match E::tempdir(settings.work_root,&prefix_bytes) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let package_dir=P::join_name(work,circuit_name);
let display=P::display_path(P::join_part(package_dir,Part::Target)); let commands=prove_circuit_args(&display,circuit_name);
let _created=match E::io_exec(Io::Create(package_dir)) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let _copied=match E::io_exec(Io::Copy(P::join_part(circuit_dir,Part::Manifest),P::join_part(package_dir,Part::Manifest))) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let canonical=match E::io_exec(Io::Canonical(P::join_part(circuit_dir,Part::Source))) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let _linked=match E::io_exec(Io::Symlink(canonical,P::join_part(package_dir,Part::Source))) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let _written=match E::io_exec(Io::Write(P::join_part(package_dir,Part::ProverToml),copy_bytes(prover_toml.as_slice()))) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let nargo_status=match E::run(&settings.nargo_binary,&commands.nargo,package_dir,true) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
if !nargo_status.success {return RunResult::Witness(nargo_status.stderr);}
let target_dir=P::join_part(package_dir,Part::Target);
let bb_status=match E::run(&settings.bb_binary,&commands.bb,package_dir,true) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
if !bb_status.success {return RunResult::Generation(bb_status.stderr);}
let proof=match E::read_file(P::join_part(target_dir,Part::Proof)) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
let _closed=match E::io_exec(Io::Close(work)) {Ok(v)=>v,Err(e)=>return RunResult::Io(e)};
RunResult::Proof(proof)
}
fn main() {}
}
