module BasicHash.Theorem

open Comparse
open DY.Core
open DY.Lib
open BasicHash.Specification
open BasicHash.Proof

/// Authentication theorem of Basic Hash:

val auth_theorem:
  tag_id:principal -> reader_id:principal ->
  reader_ev_ts:timestamp -> nonce:bytes ->
  tr:trace ->
  Lemma
  (requires
    // if the reader accepted a nonce and tag at time `reader_ev_ts`
    event_triggered_at tr reader_ev_ts reader_id (ReaderAccept tag_id nonce) /\
    trace_invariant tr
  )
  (ensures (
    // then either:
    let tr_at_ev = prefix tr reader_ev_ts in
    // - the tag sent a corresponding nonce before time `reader_ev_ts`
    event_triggered tr_at_ev tag_id (TagSend nonce) \/
    // - the attacker compromised the reader before time `reader_ev_ts`
    is_corrupt tr_at_ev (principal_label reader_id) \/
    // - the attacker compromised the tag before time `reader_ev_ts`
    is_corrupt tr_at_ev (principal_label tag_id)
  ))
let auth_theorem tag_id reader_id reader_ev_ts nonce tr = ()
