module SignedDH.Proof

open Comparse
open DY.Core
open DY.Lib
open SignedDH.Specification

#set-options "--fuel 0 --ifuel 0 --z3rlimit 25 --z3cliopt 'smt.qi.eager_threshold=100'"

let _ = enable_comparse_wf_lemmas_smtpats ()

#push-options "--ifuel 1"
let signed_dh_sign_pred {|crypto_usages|}: sign_crypto_predicate = {
  pred = (fun tr sk_usg vk msg -> (
    exists server. sk_usg == long_term_key_type_to_usage (LongTermSigKey "SignedDH") server /\ (
      match parse sig_input msg with
      | None -> False
      | Some { x_pk; y_pk; } -> (
        exists y_sk server_sid.
          y_pk == dh_pk y_sk /\
          get_label tr y_sk == server_ephemeral_key_label server server_sid /\
          event_triggered tr server (ServerFinishEvent server_sid x_pk y_pk (kdf_extract (dh y_sk x_pk) empty))
      )
    )
  ));
  pred_later = (fun tr1 tr2 sk_usg vk msg ->
    enable_bytes_well_formed_smtpats tr1
  );
}
#pop-options

#push-options "--ifuel 1"
let client_state_predicate {|crypto_invariants|}: local_state_predicate client_state = {
  pred = (fun tr me sid (st:client_state) ->
    match st with
    | ClientInitiateState x_sk -> (
      bytes_invariant tr x_sk /\
      get_label tr x_sk == client_ephemeral_key_label me sid /\
      x_sk `has_usage tr` (DhKey "SignedDH" empty)
    )
    | ClientFinishState k_c -> (
      bytes_invariant tr k_c /\
      get_label tr k_c `can_flow tr` client_ephemeral_key_label me sid
    )
  );
  pred_later = (fun tr1 tr2 me sid st -> ());
  pred_knowable = (fun tr me sid st -> ());
}
#pop-options

#push-options "--ifuel 1"
let server_state_predicate {|crypto_invariants|}: local_state_predicate server_state = {
  pred = (fun tr me sid (st:server_state) ->
    match st with
    | ServerFinishState k_s -> (
      bytes_invariant tr k_s /\
      get_label tr k_s `can_flow tr` server_ephemeral_key_label me sid
    )
  );
  pred_later = (fun tr1 tr2 me sid st -> ());
  pred_knowable = (fun tr me key_sid st -> ());
}
#pop-options

#push-options "--ifuel 1"
let signed_dh_event_predicate {|crypto_invariants|}: event_predicate signed_dh_event =
  fun tr me ev -> (
    match ev with
    | ClientInitiateEvent client_sid x_pk -> (
      bytes_invariant tr x_pk /\
      get_dh_label tr x_pk == (client_ephemeral_key_label me client_sid)
    )
    | ServerFinishEvent server_sid x_pk y_pk k_s -> (
      bytes_invariant tr k_s /\
      bytes_invariant tr x_pk /\
      get_label tr k_s == join (server_ephemeral_key_label me server_sid) (get_dh_label tr x_pk)
    )
    | ClientFinishEvent client_sid server x_pk y_pk k_c -> (
      (exists server_sid.
        event_triggered tr server (ServerFinishEvent server_sid x_pk y_pk k_c) /\
        bytes_invariant tr k_c /\
        get_label tr k_c == join (client_ephemeral_key_label me client_sid) (server_ephemeral_key_label server server_sid)
      ) \/
      is_corrupt tr (long_term_key_label server)
    )
  )
#pop-options

instance _: crypto_usages = default_crypto_usages

let all_sign_preds = [
  ("SignedDH", signed_dh_sign_pred);
]

instance _: crypto_invariants = {
  usages = default_crypto_usages;
  preds = {
    default_crypto_predicates with
    sign_pred = mk_sign_predicate all_sign_preds;
  }
}

let all_state_preds = [
  mk_local_state_tag_and_pred client_state_predicate;
  mk_local_state_tag_and_pred server_state_predicate;
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
]

let all_event_preds = [
  mk_event_tag_and_pred signed_dh_event_predicate;
]

instance _: protocol_invariants = {
  crypto_invs = _;
  trace_invs = {
    state_pred = mk_state_pred all_state_preds;
    event_pred = mk_event_pred all_event_preds;
  };
}

let _ = do_boilerplate mk_sign_predicate_correct all_sign_preds
let _ = do_boilerplate mk_state_pred_correct all_state_preds
let _ = do_boilerplate mk_event_pred_correct all_event_preds

val client_initiate_proof:
  client:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_initiate client tr in
    trace_invariant tr_out
  ))
let client_initiate_proof client tr = ()

val server_receive_proof:
  server:principal -> private_keys_sid:state_id ->
  msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = server_receive server private_keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let server_receive_proof server private_keys_sid msg_ts tr =
  assert(forall tr x_pk y_pk. {:pattern (bytes_invariant tr (serialize sig_input { x_pk; y_pk; }))}
    is_publishable tr x_pk /\ is_publishable tr y_pk ==> is_publishable tr (serialize sig_input { x_pk; y_pk; })
  )

val dh_shared_secret_lemma_smtpat:
  x:bytes -> y:bytes ->
  Lemma (dh x (dh_pk y) == dh y (dh_pk x))
  [SMTPat (dh x (dh_pk y));
   SMTPat (dh y (dh_pk x))]
let dh_shared_secret_lemma_smtpat x y =
  dh_shared_secret_lemma x y

val client_finish_proof:
  client:principal -> server:principal -> pki_sid:state_id ->
  msg_ts:timestamp -> client_sid:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_finish client server pki_sid msg_ts client_sid tr in
    trace_invariant tr_out
  ))
let client_finish_proof client server pki_sid msg_ts client_sid tr =
  allow_inversion client_state;
  allow_inversion server_message
