(*
 * Protocol:	Simplified ACME
 * Modeler: 	Luc Fontaine and Charlie Jacomme
 * Date:        March 2026
 *
 * Status: 	Finished
 * 
 * attacker:    active
 * sessions:    unbounded ∞ 
 * agents:      unbounded ∞ 
 * compromises: long-term keys (LTK)
 * primitives:  signatures
 * properties:  auth
 * difficulty:  medium
 *

Verifies in two seconds.
*)


(*
=====================
Function Definitions
=====================
*)


include Core.

(* Channels are abstracted once the protocol is defined in Squirrel,
   but it makes it more readable during process declaration *)

channel c.
channel c_auth.
channel c_authLE.



(* Signature declaration and security properties needed *)

signature SIGsign,SIGverify,pk.

axiom [any] SIGsign_ax (x,y,k : message) : x = y => SIGverify(x, SIGsign(y,k), pk(k)).

(* To prove authentication, we use UEO proerty on signature, which affirm that
 if  a signature done with some key sk is verified with some key opk then opk = pk(sk) *)


(* Possible improvement : 
In fact, UEO is defined for polynomial values, but by defining it like that in Squirrel
we assume it for all values, even exponential ones. To refine that axiom, 
the idea would be to rewrite it as a crypto game and use the crypto tactic instead. *)

axiom [any] SIGsign_UEO (m, m', opk, sk : message) :
      SIGverify(m', SIGsign(m, sk), opk) => opk = pk(sk).


(* adr of owner[index] *)

name adr : index -> message.

(*long-term signing keys *)

name o_sk : index -> message.

name le_sk : message

(* ephemeral for LE *)
name token : index -> message

(* Owner and LE actions *)

abstract approved : message.

abstract register : message -> message.

abstract DNS_Upd : message -> message -> message.
abstract dns_to_adr : message -> message.


axiom [any] to_adrsig (adr, sig : message) :
  dns_to_adr (DNS_Upd adr sig) = <adr, sig>.
(*
=====================
Protocol model
=====================
*)

(* Here we model only multi-session and not multi-user/both, that would be the same *)
process Owner (i:index) = 
  (* we receive some Let's Encrypt server public key *)
  in(c, le_pk);

  let o_pk = pk(o_sk i) in
  O1:out(c, register(adr i));
  
  in(c, mLE);
  let tk = fst mLE in
  let le_sig = snd mLE in
  if SIGverify(tk, le_sig, le_pk) then
    let o_sig = SIGsign(tk, o_sk i) in
    O2:out(c_auth, DNS_Upd (adr i)  o_sig);
    O3:out(c, <adr i, o_pk>);
    O4:in(c, approved).



process LetsEnc(j:index) =

   in(c, reg);
   let tk = token j in
   let le_sig = SIGsign(tk, le_sk) in

   LE1:out(c, <tk, le_sig>);

   in (c, upd);
   let Adr = fst upd in
   let o_pkS = snd upd in

   LE2:out(c_authLE, Adr);

   in(c_authLE, o_sig);
   if SIGverify(tk, o_sig, o_pkS) then
     LE3:out(c, approved).


process DNS (i:index) = 
  D1:in(c_auth, mO);

  in(c_authLE, upd_adr);
  let adr = fst (dns_to_adr mO) in
  let sig = snd (dns_to_adr mO) in

  if adr = upd_adr then
    D2:out(c_authLE, sig).

(* Corruption results in a leak of private key *)
process Corrupt_O(i:index) = 
  out(c, o_sk i).


process protocol = (
   (!_i Owner(i))
   | 
   (!_j LetsEnc(j))
   |
   (!_i DNS(i))
   |
   (!_i Corrupt_O(i))
).

system default = protocol.


(* Authenticated channels axioms *)
(* O2(i) -> D2 *)
(* This axiom is also saying that a DNS process is always linked to an Owner process. We can allow it because DNS process begins only when it receives a message in the authenticated channel *)
axiom auth_c_auth(i:index) :
  happens(D2(i)) =>
    O2(i) < D2(i) &&
    input@D1(i) = output@O2(i).

(* This axiom is stronger than the previous one,
   it represents the challenge/response between LE Server and DNS *)
(*  D2 -> LE3(j) *)
(* LE3(j) -> D2 *)

axiom auth_c_authLE (j : index) :
  happens(LE3(j)) => 
    exists i,
    (D2(i) < LE3(j)) && (* Then some DNS server happened before *)
    input@LE3(j) = output@D2(i) && input@D2 i = output@LE2 j .
   (* and each one is authenticated to the other *)


lemma [default] auth_owner_nocor (i, j : index) :
  (* if a session j from LE server receives an honest adr i *)
  Adr j@LE3(j) = adr i =>
  (* and LE(j) process ended correctly *)
  happens(LE3(j)) =>
  exec@LE3(j) =>
  (* and the owner i is not corrupted until verification from LE *)
  not(Corrupt_O(i) < LE3(j)) =>
  (* then o_pk seen by LE j is pk(o_sk i) *)
  o_pkS j@LE2(j) = pk(o_sk i).

Proof.

  intro Hadr Hhap Hex NoCor.
  (* We introduce all of our hypothesis *)
  have CondLE : cond@LE3(j).
  auto.  (* and deduce cond@LE3(j) from Hex *)
  rewrite /cond in CondLE.


  have [i' [Hord [HinLE3 HinD2]]] := auth_c_authLE j Hhap.
  have HD2 : happens(D2(i')) by constraints.
  have [HordO2 HinD1] := auth_c_auth i' HD2.
  (* We add hypothesis from our two axioms of authenticated channels *)

  rewrite /output /o_sig /tk in HinD1.
  have CondD : cond@D2(i').
  smt. (* deduction of Cond@D2(i') from Hord HD2 Hhap *)

  rewrite /cond /adr1 HinD1 to_adrsig HinD2 /output /Adr Hadr in CondD; simpl.
  have Heq : i' = i by auto; simpl.
  subst i', i.

  rewrite HinLE3 /output /sig HinD1 to_adrsig in CondLE; simpl.
  apply SIGsign_UEO in CondLE.
  auto.

Qed.




