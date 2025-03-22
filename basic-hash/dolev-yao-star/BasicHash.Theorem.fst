module BasicHash.Theorem

open Comparse
open DY.Core
open DY.Lib
open BasicHash.Specification
open BasicHash.Proof

val auth_theorem:
  tag_id:principal -> reader_id:principal ->
  reader_ev_ts:timestamp -> nonce:bytes ->
  tr:trace ->
  Lemma
  (requires
    event_triggered_at tr reader_ev_ts reader_id (ReaderAccept tag_id nonce) /\
    trace_invariant tr
  )
  (ensures (
    let tr_at_ev = prefix tr reader_ev_ts in
    event_triggered tr_at_ev tag_id (TagSend nonce) \/
    is_corrupt tr_at_ev (principal_label reader_id) \/
    is_corrupt tr_at_ev (principal_label tag_id)
  ))
let auth_theorem tag_id reader_id reader_ev_ts nonce tr = ()
