module SignedDH.Theorem

open Comparse
open DY.Core
open DY.Lib
open SignedDH.Specification
open SignedDH.Proof

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val client_auth:
  client:principal -> server:principal ->
  client_sid:state_id -> x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    event_triggered_at tr client_ev_ts client (ClientFinishEvent client_sid server x_pk y_pk k) /\
    trace_invariant tr
  )
  (ensures (
    let tr_before_ev = prefix tr client_ev_ts in
    (exists server_sid. event_triggered tr_before_ev server (ServerFinishEvent server_sid x_pk y_pk k)) \/
    is_corrupt tr_before_ev (long_term_key_label server)
  ))
let client_auth client server client_sid x_pk y_pk k client_ev_ts tr = ()

val client_secrecy:
  client:principal -> server:principal ->
  client_sid:state_id -> x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    attacker_knows tr k /\
    event_triggered_at tr client_ev_ts client (ClientFinishEvent client_sid server x_pk y_pk k) /\
    trace_invariant tr
  )
  (ensures (
    let tr_before_ev = prefix tr client_ev_ts in
    is_corrupt tr_before_ev (long_term_key_label server) \/
    is_corrupt tr (client_ephemeral_key_label client client_sid) \/
    (exists server_sid.
      event_triggered tr_before_ev server (ServerFinishEvent server_sid x_pk y_pk k) /\
      is_corrupt tr (server_ephemeral_key_label server server_sid)
    )
  ))
let client_secrecy client server client_sid x_pk y_pk k client_ev_ts tr =
  attacker_only_knows_publishable_values tr k

val server_secrecy:
  client:principal -> server:principal ->
  client_sid:state_id -> server_sid:state_id ->
  x_pk:bytes -> y_pk:bytes -> k:bytes ->
  client_ev_ts:timestamp ->
  server_ev_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    attacker_knows tr k /\
    event_triggered tr client (ClientInitiateEvent client_sid x_pk) /\
    event_triggered tr server (ServerFinishEvent server_sid x_pk y_pk k) /\
    trace_invariant tr
  )
  (ensures (
    is_corrupt tr (client_ephemeral_key_label client client_sid) \/
    is_corrupt tr (server_ephemeral_key_label server server_sid)
  ))
let server_secrecy client server client_sid server_sid x_pk y_pk k client_ev_ts server_ev_ts tr =
  attacker_only_knows_publishable_values tr k
