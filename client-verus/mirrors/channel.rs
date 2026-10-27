//! Reviewed channel cores. See source/manifest.json for exact source regions.
//! Locks and Arc become a sequential registry parameter or an opaque shared handle.
//! Key is a serialized SEC1 value; no curve/encoding/injectivity proof is claimed.
//! Receiver/send effects are trait methods. Scheduler, cancellation, fairness and liveness are outside the model.
use vstd::prelude::*;
verus! {
pub type Key = [u8;33];
pub struct Message { pub encrypted_note: Vec<u8>, pub commitment: [u8;32], pub recipient: Key }
pub enum Error { RecipientNotFound, ChannelClosed }
pub enum TryReceive { Message(Message), Empty, Disconnected }
pub trait Effects {
 spec fn pair(capacity: usize) -> (u64,u64);
 spec fn delivered(sender: u64, message: Message) -> bool;
 spec fn tried(receiver: u64) -> TryReceive;
 spec fn received(receiver: u64) -> Option<Message>;
 fn channel(capacity: usize) -> (r: (u64,u64)) ensures r == Self::pair(capacity);
 fn send(sender: u64, message: Message) -> (r: bool) ensures r == Self::delivered(sender,message);
 fn try_recv(receiver: u64) -> (r: TryReceive) ensures r == Self::tried(receiver);
 fn recv(receiver: u64) -> (r: Option<Message>) ensures r == Self::received(receiver);
}
pub trait RegistryApi: Sized {
 spec fn entries(&self) -> Map<Key,u64>;
 spec fn handle(&self) -> u64;
 fn empty() -> (r: Self) ensures r.entries() == Map::<Key,u64>::empty();
 fn insert(&mut self, key: Key, sender: u64)
 ensures final(self).entries() == old(self).entries().insert(key,sender), final(self).handle() == old(self).handle();
 fn remove(&mut self, key: Key)
 ensures final(self).entries() == old(self).entries().remove(key), final(self).handle() == old(self).handle();
 fn get(&self, key: Key) -> (r: Option<u64>)
 ensures r == if self.entries().contains_key(key) {Some(self.entries()[key])} else {None};
 fn shared_handle(&self) -> (r: u64) ensures r == self.handle();
}
pub struct Channel<R: RegistryApi> {pub viewing_pubkey: Key,pub receiver: u64,pub registry: R}
pub struct SystemChannel {pub viewing_pubkey: Key,pub receiver: u64,pub registry_handle: u64}
pub open spec fn sent<E: Effects>(entries: Map<Key,u64>, key: Key, m: Message) -> Result<(),Error> {
 if !entries.contains_key(key) {Err(Error::RecipientNotFound)} else if E::delivered(entries[key],m) {Ok(())} else {Err(Error::ChannelClosed)}
}
pub open spec fn nonblocking<E: Effects>(receiver: u64) -> Result<Option<Message>,Error> {
 match E::tried(receiver) {TryReceive::Message(m)=>Ok(Some(m)),TryReceive::Empty=>Ok(None),TryReceive::Disconnected=>Err(Error::ChannelClosed)}
}
pub open spec fn blocking<E: Effects>(receiver: u64) -> Result<Message,Error> {
 match E::received(receiver) {Some(m)=>Ok(m),None=>Err(Error::ChannelClosed)}
}
pub fn registry_clone<R: RegistryApi>(registry: &R) -> (r: R)
 ensures r.entries() == Map::<Key,u64>::empty(),
 // STRENGTH registry_clone
{R::empty()}

pub async fn registry_register<R: RegistryApi,E: Effects>(registry: &mut R, viewing_pubkey: Key) -> (r: Channel<R>)
 ensures final(registry).entries() == old(registry).entries().insert(viewing_pubkey,E::pair(100).0),
 r.viewing_pubkey == viewing_pubkey, r.receiver == E::pair(100).1, r.registry.entries() == Map::<Key,u64>::empty(),
 // STRENGTH registry_register
{
 let (tx,rx)=E::channel(100);
 let key=viewing_pubkey;
 registry.insert(key,tx);
 Channel {viewing_pubkey,receiver:rx,registry:registry_clone(registry)}
}

pub async fn registry_unregister<R: RegistryApi>(registry: &mut R, viewing_pubkey: Key)
 ensures final(registry).entries() == old(registry).entries().remove(viewing_pubkey),
 // STRENGTH registry_unregister
{
 let key=viewing_pubkey;
 registry.remove(key);
}

pub async fn registry_send_to<R: RegistryApi,E: Effects>(registry: &R, recipient_viewing_pubkey: Key, message: Message) -> (r: Result<(),Error>)
 ensures r == sent::<E>(registry.entries(),recipient_viewing_pubkey,message),
 // STRENGTH registry_send_to
{
 let key=recipient_viewing_pubkey;
 let sender=match registry.get(key) {Some(tx)=>tx,None=>return Err(Error::RecipientNotFound)};
 if E::send(sender,message) {Ok(())} else {Err(Error::ChannelClosed)}
}

pub fn channel_new<R: RegistryApi,E: Effects>(viewing_pubkey: Key, registry: R) -> (r: Channel<R>)
 ensures r.viewing_pubkey == viewing_pubkey, r.registry == registry, r.receiver == E::pair(1).1,
 // STRENGTH channel_new
{
 let (_,rx)=E::channel(1);
 Channel {viewing_pubkey,receiver:rx,registry}
}

pub async fn channel_send_note<R: RegistryApi,E: Effects>(channel: &Channel<R>, recipient_viewing_pubkey: Key, encrypted_note: Vec<u8>, commitment: [u8;32]) -> (r: Result<(),Error>)
 ensures r == sent::<E>(channel.registry.entries(),recipient_viewing_pubkey,Message {encrypted_note,commitment,recipient:recipient_viewing_pubkey}),
 // STRENGTH channel_send_note
{
 let message=Message {encrypted_note,commitment,recipient:recipient_viewing_pubkey};
 registry_send_to::<R,E>(&channel.registry,recipient_viewing_pubkey,message).await
}

pub async fn channel_receive_note<R: RegistryApi,E: Effects>(channel: &Channel<R>) -> (r: Result<Option<Message>,Error>)
 ensures r == nonblocking::<E>(channel.receiver),
 // STRENGTH channel_receive_note
{
 match E::try_recv(channel.receiver) {TryReceive::Message(message)=>Ok(Some(message)),TryReceive::Empty=>Ok(None),TryReceive::Disconnected=>Err(Error::ChannelClosed)}
}

pub async fn channel_receive_note_blocking<R: RegistryApi,E: Effects>(channel: &Channel<R>) -> (r: Result<Message,Error>)
 ensures r == blocking::<E>(channel.receiver),
 // STRENGTH channel_receive_note_blocking
{ E::recv(channel.receiver).ok_or(Error::ChannelClosed) }

pub async fn system_receive_note<E: Effects>(channel: &SystemChannel) -> (r: Result<Option<Message>,Error>)
 ensures r == nonblocking::<E>(channel.receiver),
 // STRENGTH system_receive_note
{
 match E::try_recv(channel.receiver) {TryReceive::Message(message)=>Ok(Some(message)),TryReceive::Empty=>Ok(None),TryReceive::Disconnected=>Err(Error::ChannelClosed)}
}

pub async fn system_receive_note_blocking<E: Effects>(channel: &SystemChannel) -> (r: Result<Message,Error>)
 ensures r == blocking::<E>(channel.receiver),
 // STRENGTH system_receive_note_blocking
{ E::recv(channel.receiver).ok_or(Error::ChannelClosed) }

pub async fn system_create_channel<R: RegistryApi,E: Effects>(registry: &mut R, viewing_pubkey: Key) -> (r: SystemChannel)
 ensures final(registry).entries() == old(registry).entries().insert(viewing_pubkey,E::pair(100).0),
 r.viewing_pubkey == viewing_pubkey, r.receiver == E::pair(100).1, r.registry_handle == old(registry).handle(),
 // STRENGTH system_create_channel
{
 let (tx,rx)=E::channel(100);
 let key=viewing_pubkey;
 registry.insert(key,tx);
 SystemChannel {viewing_pubkey,receiver:rx,registry_handle:registry.shared_handle()}
}

pub async fn system_send_note<R: RegistryApi,E: Effects>(registry: &R, recipient_viewing_pubkey: Key, encrypted_note: Vec<u8>, commitment: [u8;32]) -> (r: Result<(),Error>)
 ensures r == sent::<E>(registry.entries(),recipient_viewing_pubkey,Message {encrypted_note,commitment,recipient:recipient_viewing_pubkey}),
 // STRENGTH system_send_note
{
 let key=recipient_viewing_pubkey;
 let message=Message {encrypted_note,commitment,recipient:recipient_viewing_pubkey};
 let sender=match registry.get(key) {Some(tx)=>tx,None=>return Err(Error::RecipientNotFound)};
 if E::send(sender,message) {Ok(())} else {Err(Error::ChannelClosed)}
}

// Composition example: this models the ChannelRegistry API, not ChannelSystem.
pub async fn registered_channel_cannot_send<R: RegistryApi,E: Effects>(registry: &mut R, own_key: Key, recipient: Key, encrypted_note: Vec<u8>, commitment: [u8;32]) -> (r: Result<(),Error>)
 ensures r is Err && r->Err_0 == Error::RecipientNotFound,
 // STRENGTH registered_channel_cannot_send
{
 let channel=registry_register::<R,E>(registry,own_key).await;
 channel_send_note::<R,E>(&channel,recipient,encrypted_note,commitment).await
}
fn main() {}
}
