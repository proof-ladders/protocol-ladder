(*
 * Protocol: SignedDH+KEM	 
 * Modeler: Luc Fontaine	  
 * Date: March 2026        
 *
 * Status: 	   
 * 
 * attacker:    active
 * sessions:     1
 * agents:       1
 * compromises: long-term keys (LTK)
 * primitives:  ROM, signatures, diffie-hellman, KEM
 * properties:  auth, forward secrecy
 * difficulty:  medium
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

(* DH abstraction, assumed broken *)
abstract exp : message -> message -> message.
abstract gen : message.

(* KEM correctness *)
axiom [any]  encap_decap (r:kem_randomness, k:kem_skey):
 decap (encap_ct r (kem_pub k)) k = encap_shared r (kem_pub k).

(* Associativity of exp function first applied on gen *)
axiom [any] exp_assoc (x:message, y: message):
  exp (exp gen x) y = exp (exp gen y) x.

(* signature declaration and correctness *)
signature SIGsign, SIGverify, pk.

axiom [any] SIGsign_ax (x,y,k : message) : x = y => SIGverify(x, SIGsign(y,k), pk(k)).

(* Hash *)
hash Hash.

name kHash : message.

(*------------------------------------------------------------------*)
(* pairs *)

lemma [any] pair_eq_pair (x,y,x',y':message) :
(<x,y> = <x',y'>) = (x = x' && y = y').
Proof.
  rewrite eq_iff; split; intro H.
  split.
  by apply f_apply fst in H.
  by apply f_apply snd in H.
  auto.
Qed.

(* long-term signing key *)
name s_sk : message.

(* ephemerals for Client *)
name z_sk : kem_skey.
abstract x_sk : message.

(* ephemerals for Server  *)
abstract y_sk : message.
name r_s : kem_randomness.
name r_s' : kem_randomness.

(* We do not assume any security on the DH part, we are doing the opposite
   assumptions on security of DH and KEM in the file signedDHKEM_CDH.sp *) 
(* This proof is thus correct under the hypothesis of a broken DH scheme *)

(*
=====================
Protocol model
=====================
*)

process Client  =
  
  in(c, s_pk);
  (* DH part *)
  let x_sk = x_sk  in
  let x_pk = exp gen x_sk in

  (* KEM part *)
  let z_sk = z_sk  in
  let z_pk = kem_pub z_sk in

  C1:out(c, <x_pk, z_pk>);

  in (c, mA);
  let y_pk = (fst(fst(mA))) in
  let sig = snd(fst mA) in 
  let ct = snd(mA) in
  if SIGverify(<<x_pk, y_pk>, <z_pk, ct>>, sig, s_pk) then
    let C_ss = decap ct z_sk in
    let gCS = exp y_pk x_sk in
    let kC = Hash(<gCS, C_ss>, kHash) in
    C2:null



process Server =
  in (c, xz_pk');

  let x_pk = fst xz_pk' in
  let z_pk = snd xz_pk' in
  let y_sk = y_sk in
  let y_pk = exp gen y_sk in
  let r_s = r_s in
  let ct =  
    if z_pk = (kem_pub z_sk) then 
        encap_ct r_s (kem_pub z_sk)
    else  encap_ct (r_s') z_pk 
  in
  let S_ss = encap_shared r_s z_pk in
  let sig = SIGsign(<<x_pk, y_pk>,<z_pk, ct>>, s_sk) in
  let gSC = exp x_pk y_sk in
  let kS = Hash(<gSC, S_ss>, kHash) in
  S1:out(c, <<y_pk, sig>, ct>).


process kdforacle (i:index) =
  in(c,x); O :
  out(c, Hash(x,kHash)).

process corrupt =
  out(c, s_sk ).

process protocol = (
   (Client)
   | 
   (Server)
   |
   (corrupt) 
   | 
  (!_O kdforacle(O))
).

system default = protocol.

(* CPA assumption on KEM is represented as a crypto game. *)

game CPA_kem = {
  rnd k : kem_skey;
  rnd r : kem_randomness;
  rnd s' : message;

  oracle pk = {
    return (kem_pub k)
  }
  oracle encaps_ct = {
    return (encap_ct r (kem_pub k)) 
  }

  oracle encaps_shared = {
    return diff((encap_shared r (kem_pub k)), s') 
  }
}.

(*
=====================
Security queries
=====================
*)

(*------------------------------------------------------------------*)
(* Agreement of Client holds whenever S has not been corrupted before C's execution *)

lemma [default] authentication:
  (* a client process terminated *)
  happens(C2) =>
   (* which received the right pk *) 
  input@C1 = pk(s_sk) &&
  (* from the server not corrupted before *)
  not (corrupt < C2) =>

   (* then, the SIGverify in C2 is equivalent to a matching of keys with
      some server session k. *)
  (cond@C2 <=> 
    S1 < C2 && 
    gCS @C2 = exp(exp gen (y_sk))  (x_sk) &&
    fst( fst((input@C2))) = exp gen  (y_sk) &&
    fst (input@S1) = exp gen (x_sk) &&
    snd (input@S1) = kem_pub (z_sk) &&
    snd (input@C2) = encap_ct r_s (kem_pub (z_sk)) &&
    SIGverify(<<exp gen (x_sk), exp gen (y_sk)>,
    <snd(input@S1), encap_ct(r_s) (snd(input@S1))>>, 
              snd(fst(input@C2)), 
              pk(s_sk ))).

Proof.
  (* The proof is the same than in the CDH file *)
  intro HC2 [Hon NoCor].
  split. 
   
  - intro Cond.
    rewrite /cond Hon in Cond. 
    euf Cond.
      auto.

     intro [Ord [Eqdh Eqkem]].
     simpl.
     have Eq2 :  y_pk @C2 = y_pk1 @S1.
      by apply f_apply snd in Eqdh; simpl.   
    apply f_apply fst in Eqdh; simpl.
    rewrite /gCS Eq2 /y_pk1 /y_sk1 /x_sk1 //=.
    smt.
    -intro [H1 [H2 H3 H4 H5 H6 H7]].
    auto.
Qed.



(* We have four lemma of secrecy, for the secrecy of the shared secret resulting from
   the kem and for the secrecy of the full key, Hash(sharedKEM, sharedDH).
   We prove it on Server and on Client side 
*)

name nfresh : message.

global lemma [set:default/left; equiv:default/left, default/left]
  S_ss_secret (t0 : timestamp[const],j :index [const]) :
  (* Server happened *)
  [S1 <= t0] ->
  (* and the j-th hash oracle query happened *)
  [O j <= t0] ->
  (* and Client sent public keys to the Server who received them*)
  [C1 < S1] ->
   [ input@S1 = output@C1 ]
  ->
  (* then the shared computed by the Server is indistinguishable from uniform *)
  equiv(
    frame@t0, 
      diff(S_ss@S1, nfresh)).
 
Proof.
  intro Hap1 Hap2 Hon Heq.
  rewrite /S_ss /r_s1 /z_pk1 Heq /output /z_pk /z_sk1; simpl.
  crypto CPA_kem (k:z_sk) (r:r_s).
Qed.



global lemma [set:default/left; equiv:default/left, default/left]
  kS_secret (t0 : timestamp[const]) :
  (* Server happened *)
  [S1 <= t0] ->
  (* and Client sent public keys to the Server who received them*)
  (* We can improve this, just assuming that the part of the input corresponding to dh is     equal to the honest one. *)
  [C1 < S1 && input@S1 = output@C1 ]
  ->
  (* then the full key computed by the Server is indistinguishable from uniform *)
  equiv(
    frame@t0, 
      diff(kS@S1, nfresh)).
Proof.
  intro Hap  [Hon NoCor]. 
  rewrite /kS.
  prf 1 => /=. 
  intro j H1 H2.
  have ? : O(j) <= t0.  
    case H1; 1,2: auto. 
  clear H1.     

   rewrite eq_sym in H2. 
   
  rewrite equiv (S_ss_secret t0 j); 1,2,3,4: auto.  
  apply f_apply snd in H2;simpl.
  by fresh H2.
  by fresh 1.
Qed.


global lemma [set:default/left; equiv:default/left, default/left]
  C_ss_secret (t0 : timestamp[const], j : index[const]) :
  (* Client happened *)
  [C2 <= t0] ->
  (* and the j-th hash oracle query happened *)
  [O j <= t0] ->
  (* the Server replied before Client ended, and the Client received it well formed *)
  [S1 < C2] ->
  [snd(input@C2) = encap_ct r_s (kem_pub z_sk)] ->
  (* then the shared computed by the Client is indistinguishable from uniform *)
  equiv(
    input@O j, gCS@C2, input@C2, output@S1,
    diff(C_ss@C2, nfresh)).
Proof.
  intro Hap1 Hap2 Hon Heq.
  rewrite /C_ss /z_sk1 /ct Heq encap_decap.
  crypto CPA_kem (k:z_sk) (r:r_s).
Qed.


global lemma [set:default/left; equiv:default/left, default/left]
  kC_secret (t0 : timestamp[const]) :
  (* Client happened *)
  [C2 <= t0] ->
  (* the Server replied before Client ended, and the Client received it well formed *)
  [S1 < C2 && snd(input@C2) = encap_ct r_s (kem_pub z_sk)] ->
  (* then the full key computed by the Client is indistinguishable from uniform *)
  equiv(
    frame@t0,
    diff(kC@C2, nfresh)).
Proof.
  intro Hap [Hon Heq].
  rewrite /kC.
  prf 1 => /=.
  intro j H1 H2.
  have ? : O(j) <= t0.
    case H1; 1,2: auto.
  clear H1.
  rewrite eq_sym in H2.
  rewrite equiv (C_ss_secret t0 j); 1,2,3,4: auto.
  apply f_apply snd in H2; simpl.
  by fresh H2.
  by fresh 1.
Qed.


(* Possible improvements : 
   executability lemma
   add multi sessions and multi agents in the process and in the proofs.
   The authentication lemma will still be sound.
   Warning : the usage of crypto might cause problems of type non-polynomial variables *)
