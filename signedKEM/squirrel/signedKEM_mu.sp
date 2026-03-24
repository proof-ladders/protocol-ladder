(*
 * Protocol:	  Signed KEM
 * Modeler: 	  Luc Fontaine
 * Date:        March 2026
 *
 * Status: 	    Ongoing
 * 
 * attacker:    active
 * sessions:    unbounded ∞ 
 * agents:      unbounded ∞ 
 * compromises: long-term keys (LTK)
 * primitives:  signatures, KEM
 * properties:  auth
 * difficulty:  easy
 *

Verifies in under a second.
*) 


(*
=====================
Function Definitions
=====================
*)

include Core.


(* a public communication channel over the network.*)
channel c.


(* KEM types and functions*)
type kem_skey[serializable]
type kem_randomness[serializable]

abstract kem_pub : kem_skey -> message.
abstract encap_shared : kem_randomness -> message -> message
abstract encap_ct : kem_randomness -> message -> message.
abstract decap : message -> kem_skey -> message.

(* abstracts and axiom used to leak names of type message and 
   not kem_skey in the process Corrupt *)
abstract from_sk : kem_skey -> message.
abstract to_sk : message -> kem_skey.

axiom [any] conv_sk (k:kem_skey, mk:message):
   to_sk(from_sk(k)) = k && from_sk(to_sk(mk)) = mk.


(* KEM correctness *)
axiom [any]  encap_decap (r:kem_randomness, k:kem_skey):
 decap (encap_ct r (kem_pub k)) k = encap_shared r (kem_pub k).


(* Signature declaration and correctness *)
signature SIGsign, SIGverify, pk.

axiom [any] SIGsign_ax (m1,m2,k : message) :
  m1 = m2 => SIGverify(m1, SIGsign(m2,k), pk(k)).


(* long-term sig client key *)
name c_sign_sk : index -> message.

(* ephemerals for Client *)
name c_kem_sk : index -> index -> kem_skey.
name r_c : index -> index -> kem_randomness.

(* long term KEM server key *)
name s_kem_sk : index -> kem_skey.

(* ephemerals for Server  *)
name r_s : index -> index -> kem_randomness.



(*
=====================
Protocol model
=====================
*)

process Client (C, i:index) =
  
  in(c, s_kem_pk); (* receive some long term server public kem key *)

  (* KeyGen *)
  let c_kem_sk = c_kem_sk C i in
  let c_kem_pk = kem_pub c_kem_sk in

  (* KemEncaps *)
  let r_c = r_c C i in
  let c_ct = encap_ct r_c s_kem_pk in
  let c_ss1 = encap_shared r_c s_kem_pk in

  (* Signature of our kem_pk *)
  let sig = SIGsign(c_kem_pk, c_sign_sk C) in

  C1:out(c, <<c_kem_pk, sig>, c_ct>); 
  in (c, s_ct);
  let c_ss2 = decap s_ct c_kem_sk in
  let kc = <c_ss1, c_ss2> in
  C2: null.

process Server(S: index, j: index) =


  S1:in (c, c_sign_pk);
  in (c, mA);
  
  let c_kem_pk = fst(fst mA) in
  let sig = snd(fst mA) in
  let c_ct = snd mA in
  if SIGverify(c_kem_pk, sig, c_sign_pk) then
     let r_s = r_s S j  in
     let s_kem_sk = s_kem_sk S in
     let s_ss1 = decap c_ct s_kem_sk in
     let s_ct = encap_ct r_s c_kem_pk in
     let s_ss2 = encap_shared r_s c_kem_pk in
     let ks = <s_ss1, s_ss2> in
     S2:out(c, s_ct).


process corrupt_S (S:index) =
  out(c, from_sk( s_kem_sk S)).

process corrupt_C (C:index) = 
  out(c, c_sign_sk C).
process protocol = (
   (!_C !_i Client(C, i))
   | 
   (!_S !_j Server(S,j))
   |
   (!_S corrupt_S(S))
   |
   (!_C corrupt_C(C))
   ).

system default = protocol.



(*
=====================
Security queries
=====================
*)

(* This lemma is a weak authentication of c_kem_pk by some Server j *)
lemma [default] authentication (S,C,i,j:index):
  input@S1(S,j) = pk(c_sign_sk C)  (* signing pkey of c is authenticated by s*)
  => happens(S2(S,j))
  => cond@S2(S,j) (*Server verifies well some sig *)
  => not((corrupt_C(C)) < S2(S,j)) (* client didnt leak c_sign_sk before sending sig *)
  => (*then there exists a session i of client C and Session j of server S authenticate public signing key of C i *)
  (exists (i : index),
    happens(C1(C,i)) &&
    fst(fst(input@S2(S,j))) = kem_pub(c_kem_sk C i)).

Proof.
  intro Hin Hap Cond Hcor.
  rewrite /cond Hin in Cond.
  euf Cond.
  constraints.
  intro [k [HC1k Heqpk]].
  exists k.
  split.
  auto.
  auto.
Qed.
 

(* TODO : executability lemma,
          forward secrecy (will require the use of crypto which can be difficult 
          in unbounded sessions case),
          implicit authentication *)
