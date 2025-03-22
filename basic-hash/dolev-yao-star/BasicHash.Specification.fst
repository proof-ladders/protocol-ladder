module BasicHash.Specification

open Comparse
open DY.Core
open DY.Lib

[@@ with_bytes bytes]
type tag_state = {
  key: bytes;
}

%splice [ps_tag_state] (gen_parser (`tag_state))
%splice [ps_tag_state_is_well_formed] (gen_is_well_formed_lemma (`tag_state))

instance _: local_state tag_state = {
  tag = "BasicHash.TagState";
  format = mk_parseable_serializeable ps_tag_state;
}

[@@ with_bytes bytes]
type reader_state = {
  tag_id: principal;
  key: bytes;
}

%splice [ps_reader_state] (gen_parser (`reader_state))
%splice [ps_reader_state_is_well_formed] (gen_is_well_formed_lemma (`reader_state))

instance _: local_state reader_state = {
  tag = "BasicHash.ReaderState";
  format = mk_parseable_serializeable ps_reader_state;
}

type mac_key_usage_data = {
  usg_tag_id: principal;
}

%splice [ps_mac_key_usage_data] (gen_parser (`mac_key_usage_data))
%splice [ps_mac_key_usage_data_is_well_formed] (gen_is_well_formed_lemma (`mac_key_usage_data))
instance _: parseable_serializeable bytes mac_key_usage_data = mk_parseable_serializeable ps_mac_key_usage_data

val mac_key_usage: principal -> usage
let mac_key_usage tag_id =
  MacKey "BasicHash.MacKey" (serialize _ { usg_tag_id = tag_id })

val mac_key_label: principal -> principal -> label
let mac_key_label tag_id reader_id =
  join (principal_label tag_id) (principal_label reader_id)

[@@ with_bytes bytes]
type message = {
  nonce: bytes;
  tag: bytes;
}

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))
instance _: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

[@@ with_bytes bytes]
type basic_hash_event =
  | TagSend:
    nonce:bytes ->
    basic_hash_event
  | ReaderAccept:
    tag_id:principal ->
    nonce:bytes ->
    basic_hash_event

%splice [ps_basic_hash_event] (gen_parser (`basic_hash_event))

instance _: event basic_hash_event = {
  tag = "BasicHash.Event";
  format = mk_parseable_serializeable ps_basic_hash_event;
}

val pair_tag_reader:
  principal -> principal ->
  traceful (state_id & state_id)
let pair_tag_reader tag_id reader_id =
  let* key = mk_rand (mac_key_usage tag_id) (mac_key_label tag_id reader_id) 32 in

  let* tag_key_sid = new_session_id tag_id in
  set_state tag_id tag_key_sid ({ key } <: tag_state);*

  let* reader_key_sid = new_session_id reader_id in
  set_state reader_id reader_key_sid ({ tag_id; key } <: reader_state);*

  return (tag_key_sid, reader_key_sid)


val tag_send:
  principal -> state_id ->
  traceful (option timestamp)
let tag_send tag_id key_sid =
  let* nonce = mk_rand NoUsage public 32 in
  trigger_event tag_id (TagSend nonce);*
  let*? st: tag_state = get_state tag_id key_sid in
  let tag = mac_compute st.key nonce in
  let* msg_timestamp = send_msg (serialize _ { nonce; tag }) in
  return (Some msg_timestamp)

val reader_receive:
  principal -> state_id -> timestamp ->
  traceful (option unit)
let reader_receive reader_id key_sid msg_ts =
  let*? msg_bytes = recv_msg msg_ts in
  let*? msg = return (parse message msg_bytes) in
  let*? st: reader_state = get_state reader_id key_sid in
  guard_tr (mac_verify st.key msg.nonce msg.tag);*?
  trigger_event reader_id (ReaderAccept st.tag_id msg.nonce);*
  return (Some ())
