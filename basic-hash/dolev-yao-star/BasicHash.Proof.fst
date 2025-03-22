module BasicHash.Proof

open Comparse
open DY.Core
open DY.Lib
open BasicHash.Specification

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

#push-options "--ifuel 2"
let basic_hash_mac_pred {|crypto_usages|}: mac_crypto_predicate = {
  pred = (fun tr key_usg key msg -> (
    let MacKey _ usg_data = key_usg in
    match parse mac_key_usage_data usg_data with
    | None -> False
    | Some { usg_tag_id } -> (
      event_triggered tr usg_tag_id (TagSend msg)
    )
  ));
  pred_later = (fun tr1 tr2 key_usg key msg -> ());
}
#pop-options

let tag_state_predicate {|crypto_invariants|}: local_state_predicate tag_state = {
  pred = (fun tr me key_sid (st:tag_state) ->
    st.key `has_usage tr` (mac_key_usage me) /\
    is_knowable_by (principal_label me) tr st.key
  );
  pred_later = (fun tr1 tr2 me key_sid st -> ());
  pred_knowable = (fun tr me key_sid st ->
    assert(is_well_formed _ (is_knowable_by (principal_label me) tr) st)
  );
}

let reader_state_predicate {|crypto_invariants|}: local_state_predicate reader_state = {
  pred = (fun tr me key_sid (st:reader_state) ->
    st.key `has_usage tr` (mac_key_usage st.tag_id) /\
    bytes_invariant tr st.key /\
    get_label tr st.key `equivalent tr` (mac_key_label st.tag_id me)
  );
  pred_later = (fun tr1 tr2 me key_sid st -> ());
  pred_knowable = (fun tr me key_sid st ->
    assert(is_well_formed _ (is_knowable_by (principal_label me) tr) st)
  );
}

#push-options "--ifuel 1"
let basic_hash_event_predicate: event_predicate basic_hash_event =
  fun tr me ev -> (
    match ev with
    | TagSend nonce -> (
      True
    )
    | ReaderAccept tag_id nonce -> (
      event_triggered tr tag_id (TagSend nonce) \/
      is_corrupt tr (mac_key_label tag_id me)
    )
  )
#pop-options

instance _: crypto_usages = default_crypto_usages

let all_mac_preds = [
  ("BasicHash.MacKey", basic_hash_mac_pred);
]

instance _: crypto_invariants = {
  usages = default_crypto_usages;
  preds = {
    default_crypto_predicates with
    mac_pred = mk_mac_predicate all_mac_preds;
  }
}

let all_state_preds = [
  mk_local_state_tag_and_pred tag_state_predicate;
  mk_local_state_tag_and_pred reader_state_predicate;
]

let all_event_preds = [
  mk_event_tag_and_pred basic_hash_event_predicate;
]

instance _: protocol_invariants = {
  crypto_invs = _;
  trace_invs = {
    state_pred = mk_state_pred all_state_preds;
    event_pred = mk_event_pred all_event_preds;
  };
}

let _ = do_boilerplate mk_mac_predicate_correct all_mac_preds
let _ = do_boilerplate mk_state_pred_correct all_state_preds
let _ = do_boilerplate mk_event_pred_correct all_event_preds
let _ = enable_comparse_wf_lemmas_smtpats ()

val pair_tag_reader_proof:
  tag_id:principal -> reader_id:principal ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let _, tr_out = pair_tag_reader tag_id reader_id tr in
    trace_invariant tr_out
  ))
let pair_tag_reader_proof tag_id reader_id tr = ()

val tag_send_proof:
  tag_id:principal -> key_sid:state_id ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let _, tr_out = tag_send tag_id key_sid tr in
    trace_invariant tr_out
  ))
let tag_send_proof tag_id key_sid tr = ()

val reader_receive_proof:
  reader_id:principal -> key_sid:state_id -> msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let _, tr_out = reader_receive reader_id key_sid msg_ts tr in
    trace_invariant tr_out
  ))
let reader_receive_proof reader_id key_sid msg_ts tr = ()
