module SignedDH.Specification

open Comparse
open DY.Core
open DY.Lib

/// Protocol: Signed DH
/// Modeler: Théophile Wallez
/// Date: March 2025
///
/// Model features:
///  * attacker: active
///  * sessions: unbounded
///  * agents: unbounded
///  * compromises: long-term keys + ephemeral keys
///  * Attacker class: symbolic
///  * Primitives: DH, signature, KDF
///  * Properties: Authentication, Forward Secrecy
///
/// Analysis features:
///   * difficulty ratings: easy
///   * status: finished

/// This file contains the specification.
/// We start by defining types for participant states,
/// messages sent on the network,
/// signature inputs,
/// and protocol events.

/// Type for client state
[@@ with_bytes bytes]
type client_state =
  | ClientInitiateState:
    x_sk:bytes ->
    client_state
  | ClientFinishState:
    k_c:bytes ->
    client_state

/// generate a corresponding message format with Comparse
%splice [ps_client_state] (gen_parser (`client_state))
%splice [ps_client_state_is_well_formed] (gen_is_well_formed_lemma (`client_state))

/// and register it as a state type.
instance _: local_state client_state = {
  tag = "SignedDH.ClientState";
  format = mk_parseable_serializeable ps_client_state;
}

/// Type for server state
[@@ with_bytes bytes]
type server_state =
  | ServerFinishState:
    k_s:bytes ->
    server_state

/// generate a corresponding message format with Comparse
%splice [ps_server_state] (gen_parser (`server_state))
%splice [ps_server_state_is_well_formed] (gen_is_well_formed_lemma (`server_state))

/// and register it as a state type.
instance _: local_state server_state = {
  tag = "SignedDH.ServerState";
  format = mk_parseable_serializeable ps_server_state;
}

/// Type for client message sent on the network
[@@ with_bytes bytes]
type client_message = {
  x_pk: bytes;
}

/// generate a corresponding message format with Comparse.
%splice [ps_client_message] (gen_parser (`client_message))
%splice [ps_client_message_is_well_formed] (gen_is_well_formed_lemma (`client_message))
instance _: parseable_serializeable bytes client_message = mk_parseable_serializeable ps_client_message

/// Type for server message sent on the network
[@@ with_bytes bytes]
type server_message = {
  y_pk: bytes;
  sig: bytes;
}

/// generate a corresponding message format with Comparse.
%splice [ps_server_message] (gen_parser (`server_message))
%splice [ps_server_message_is_well_formed] (gen_is_well_formed_lemma (`server_message))
instance _: parseable_serializeable bytes server_message = mk_parseable_serializeable ps_server_message

/// Type for signature input
[@@ with_bytes bytes]
type sig_input = {
  x_pk: bytes;
  y_pk: bytes;
}

/// generate a corresponding message format with Comparse.
%splice [ps_sig_input] (gen_parser (`sig_input))
%splice [ps_sig_input_is_well_formed] (gen_is_well_formed_lemma (`sig_input))
instance _: parseable_serializeable bytes sig_input = mk_parseable_serializeable ps_sig_input

/// Type for protocol event (e.g. to state authentication property)
[@@ with_bytes bytes]
type signed_dh_event =
  | ClientInitiateEvent:
    client_sid:state_id ->
    x_pk:bytes ->
    signed_dh_event
  | ServerFinishEvent:
    server_sid:state_id ->
    x_pk:bytes ->
    y_pk:bytes ->
    k_s:bytes ->
    signed_dh_event
  | ClientFinishEvent:
    client_sid:state_id ->
    server:principal ->
    x_pk:bytes ->
    y_pk:bytes ->
    k_c:bytes ->
    signed_dh_event

/// generate a corresponding message format with Comparse
%splice [ps_signed_dh_event] (gen_parser (`signed_dh_event))

/// and register it as an event type.
instance _: event signed_dh_event = {
  tag = "SignedDH.Event";
  format = mk_parseable_serializeable ps_signed_dh_event;
}

/// The following is a proof artifact.

val client_ephemeral_key_label:
  principal -> state_id ->
  label
let client_ephemeral_key_label client sid =
  principal_tag_state_label client "SignedDH.ClientState" sid

val server_ephemeral_key_label:
  principal -> state_id ->
  label
let server_ephemeral_key_label server sid =
  principal_tag_state_label server "SignedDH.ServerState" sid

/// We now specify the protocol.

/// The protocol steps to generate long-term keys
/// and send public keys to other participants
/// belong to the standard library of DY*,
/// hence are not in this file.

/// Initiate the handshake with a server.

val client_initiate:
  client:principal ->
  traceful (state_id & timestamp)
let client_initiate client =
  // Generate ephemeral dh key
  let* client_sid = new_session_id client in
  let* x_sk = mk_rand (DhKey "SignedDH" empty) (client_ephemeral_key_label client client_sid) 32 in
  set_state client client_sid (ClientInitiateState x_sk);*

  // Trigger protocol event
  let x_pk = dh_pk x_sk in
  trigger_event client (ClientInitiateEvent client_sid x_pk);*

  // Send message
  let* msg_timestamp = send_msg (serialize client_message { x_pk }) in

  return (client_sid, msg_timestamp)

/// Receive a handshake request from a client,
/// and send a response.

val server_receive:
  server:principal -> private_keys_sid:state_id ->
  msg_ts:timestamp ->
  traceful (option (state_id & timestamp))
let server_receive server private_keys_sid msg_ts =
  // Retrieve client message
  let*? msg_bytes = recv_msg msg_ts in
  let*? msg: client_message = return (parse client_message msg_bytes) in
  let x_pk = msg.x_pk in

  // Generate ephemeral dh key and compute server key
  let* server_sid = new_session_id server in
  let* y_sk = mk_rand (DhKey "SignedDH" empty) (server_ephemeral_key_label server server_sid) 32 in
  let k_s = kdf_extract (dh y_sk x_pk) empty in
  set_state server server_sid (ServerFinishState k_s);*

  // Trigger protocol event
  let y_pk = dh_pk y_sk in
  trigger_event server (ServerFinishEvent server_sid x_pk y_pk k_s);*

  // Compute signature
  let*? my_sig_key = get_private_key server private_keys_sid (LongTermSigKey "SignedDH") in
  let* sig_nonce = mk_rand SigNonce secret 32 in
  let sig = sign my_sig_key sig_nonce (serialize sig_input { x_pk; y_pk; }) in

  // Send message
  let* msg_timestamp = send_msg (serialize server_message { y_pk; sig; }) in
  return (Some (server_sid, msg_timestamp))

/// Receive the response from a server,
/// and finish processing the handshake.

val client_finish:
  client:principal -> server:principal -> pki_sid:state_id ->
  msg_ts:timestamp -> client_sid:state_id ->
  traceful (option unit)
let client_finish client server pki_sid msg_timestamp client_sid =
  // Retrieve messsage server
  let*? msg_bytes = recv_msg msg_timestamp in
  let*? msg: server_message = return (parse server_message msg_bytes) in

  // Retrieve client initialization state
  let*? my_state: client_state = get_state client client_sid in
  guard_tr (ClientInitiateState? my_state);*?
  let ClientInitiateState x_sk = my_state in
  let x_pk = dh_pk x_sk in

  // Check signature
  let*? server_vk = get_public_key client pki_sid (LongTermSigKey "SignedDH") server in
  guard_tr (verify server_vk (serialize sig_input { x_pk; y_pk = msg.y_pk; }) msg.sig);*?

  // Compute and store client key
  let k_c = kdf_extract (dh x_sk msg.y_pk) empty in
  set_state client client_sid (ClientFinishState k_c);*

  // Trigger protocol event
  trigger_event client (ClientFinishEvent client_sid server x_pk msg.y_pk k_c);*

  return (Some ())
