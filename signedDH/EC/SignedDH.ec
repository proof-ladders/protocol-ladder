require import AllCore FMap FSet Distr.
require import PROM.

require (*--*) GDH_NominalGroup UFCMA ProtRO.

(** Buckle Up! **)
(* Starting notes:
   - We (try to) follow Doreen and Paul's model as closely as possible
     while remaining precise.
   - Whenever the pen and paper definition takes adversarial input in
     the form of a public key, that is then used to look for the
     identity of the intended partner, we instead takes input as
     "either a handle or a public key". This makes our definition more
     precise (because we don't make an arbitrary choice when two
     honest parties generate the same key), but also slightly more
     complex.
     In order to align with Doreen and Paul's model, we prevent the
     adversary from presenting us with a public-key that is already
     associated with a registered server. (Their definition infers
     intent; we prefer to enforce that adversary actions match
     intent.)
   - We probably want signing to be expressed as a multi-forgery game.
     (TODO: figure this out.)
   - The NIKE is split out as Nominal Group with Gap-DH + RO. The
     entire scheme could be proved assuming an abstract NIKE (with
     m-CKS-heavy security), and that be constructed from NG + Gap-DH +
     RO.
*)

(** Handles to refer to servers and client instances **)
type s_handle, c_handle.

(** Types and operators for the DH group **)
type pdh, sdh, sskey.

op [lossless] dkp: (pdh * sdh) distr.
op shared_key: pdh -> sdh -> pdh.

axiom shared_keyC X x Y y:
     (X, x) \in dkp
  => (Y, y) \in dkp
  => shared_key X y = shared_key Y x.

op [lossless full uniform] dssk: sskey distr.

(** Instantiate the GapDH theory **)
clone import GDH_NominalGroup as GapDH with
  type pkey       <= pdh,
  type skey       <= sdh,
  type sskey      <= sskey,
  op   dkp        <= dkp,
  op   shared_key <= shared_key,
  op   dssk       <= dssk
proof *.
realize dkp_ll by exact: dkp_ll.
realize shared_keyC by exact: shared_keyC.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Additional types for the signature scheme **)
type pkey, skey, sig.

(** Instantiate the UFCMA theory **)
clone import UFCMA as Signature with
  type pkey   <= pkey,
  type skey   <= skey,
  type sig    <= sig,
  type msg    <= pdh * pdh
proof *.

(** Additional types for defining protocols,
    plus RO instantiation
**)
type client_state = { s_id: pkey;    (* The server's identity, as its public key *)
                      x_pk: pdh;     (* The client's ephemeral public key *)
                      x_sk: sdh   }. (* The client's ephemeral secret *)

clone import FullRO as H with
  type in_t    <= pdh * pdh * pdh * sig,
  type out_t   <= sskey,
  op   dout  _ <= dssk,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

(** Instantiate the ProtRO theory **)
clone import ProtRO as Security with
  type pkey         <= pkey,
  type skey         <= skey,
  type sskey        <= sskey,
  op   dssk         <= dssk,
  type client_state <= client_state,
  type msg1         <= pdh,
  type msg2         <= pdh * sig,
  type ro_in        <= pdh * pdh * pdh * sig,
  type ro_out       <= sskey,
  op   d_ro         <= Self.dssk
proof *.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Finally, we define the signed DH protocol **)
module SignedDH (S : SigScheme) (H : RO) : Prot = {
  proc gen() = {
    var kp;

    kp <@ S.keygen();
    return kp;
  }

  proc init(s_id) = {
    var x_pk, x_sk;

    (x_pk, x_sk) <$ dkp;
    return ({| s_id = s_id; x_pk = x_pk; x_sk = x_sk |}, x_pk);
  }

  proc resp(sk_s, x_pk) = {
    var y_pk, y_sk, s, ss, ks;

    (y_pk, y_sk) <$ dkp;
    s <@ S.sign(sk_s, (x_pk, y_pk));
    ss <- shared_key x_pk y_sk;
    ks <@ H.get(ss, x_pk, y_pk, s);
    return (ks, (y_pk, s));
  }

  proc recv(st, c) = {
    var y_pk, s, b, ss, kc;
    var r <- None;

    (y_pk, s) <- c;
    b <@ S.verify(s_id st, (x_pk st, y_pk), s);
    if (b) {
      ss <- shared_key y_pk (x_sk st);
      kc <@ H.get(ss, x_pk st, y_pk, s);
      r <- Some kc;
    }
    return r;
  }
}.
