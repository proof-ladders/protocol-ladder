module SignedDH.Theorem

open Comparse
open DY.Core
open DY.Lib
open SignedDH.Specification
open SignedDH.Proof

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

/// Authentication theorem for the client.

val client_auth:
  client:principal -> server:principal ->
  client_sid:state_id -> x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    // if the client finishes a handshake at time `client_ev_ts`
    event_triggered_at tr client_ev_ts client (ClientFinishEvent client_sid server x_pk y_pk k) /\
    trace_invariant tr
  )
  (ensures (
    // then either
    let tr_before_ev = prefix tr client_ev_ts in
    // the server finished a handshake with the client with the same parameters before time `client_ev_ts`
    (exists server_sid. event_triggered tr_before_ev server (ServerFinishEvent server_sid x_pk y_pk k)) \/
    // or the long-term signature key of the server was compromised before time `client_ev_ts`
    is_corrupt tr_before_ev (long_term_key_label server)
  ))
let client_auth client server client_sid x_pk y_pk k client_ev_ts tr = ()

/// Forward secrecy for the client.

val client_secrecy:
  client:principal -> server:principal ->
  client_sid:state_id -> x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    // if the attacker knows a key `k`
    attacker_knows tr k /\
    // which was derived from a handshake by a client at time `client_ev_ts`
    event_triggered_at tr client_ev_ts client (ClientFinishEvent client_sid server x_pk y_pk k) /\
    trace_invariant tr
  )
  (ensures (
    // then either
    let tr_before_ev = prefix tr client_ev_ts in
    // the server long-term signature key was compromised before time `client_ev_ts`
    is_corrupt tr_before_ev (long_term_key_label server) \/
    // the client ephemeral key was compromised
    is_corrupt tr (client_ephemeral_key_label client client_sid) \/
    (exists server_sid.
      event_triggered tr_before_ev server (ServerFinishEvent server_sid x_pk y_pk k) /\
      // the server ephemeral key was compromised (the two lines above specify the server session id)
      is_corrupt tr (server_ephemeral_key_label server server_sid)
    )
  ))
let client_secrecy client server client_sid x_pk y_pk k client_ev_ts tr =
  attacker_only_knows_publishable_values tr k

/// Secrecy for the server.
/// Note that the client is not authenticated by the server,
/// and it could be that the attacker initiated the handshake with the server
/// hence is able to derive the handshake key.
/// Therefore, we state secrecy for the server only when
/// a honest client indeed initiated a handshake with the server.

val server_secrecy:
  client:principal -> server:principal ->
  client_sid:state_id -> server_sid:state_id ->
  x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  server_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    // if the attacker knows a key `k`
    attacker_knows tr k /\
    // which was derived from a handshake by a server
    event_triggered tr server (ServerFinishEvent server_sid x_pk y_pk k) /\
    // and a client initiated this handshake with the same parameters
    event_triggered tr client (ClientInitiateEvent client_sid x_pk) /\
    trace_invariant tr
  )
  (ensures (
    // then either the client ephemeral key is compromised
    is_corrupt tr (client_ephemeral_key_label client client_sid) \/
    // or the server ephemeral key is compromised
    is_corrupt tr (server_ephemeral_key_label server server_sid)
  ))
let server_secrecy client server client_sid server_sid x_pk y_pk k client_ev_ts server_ev_ts tr =
  attacker_only_knows_publishable_values tr k
