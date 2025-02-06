(* As specified in Boneh and Shoup's "Graduate Course in Applied Cryptography"
     https://toc.cryptobook.us/
   (Exercise 11.9 of version 0.6.)
*)
require import AllCore Distr.

(** A more mature proof would rely on libraries of definitions-generic
    definitions have a lot more parameters than what we'd like to
    expose a tutorial reader to.

    Instead, we inline (and specialise) the definitions we care about.
**)

(* Given sets of public keys, secret keys, plaintexts, DEM keys, KEM
   ciphertexts and DEM ciphertexts ... *)
type pkey, skey, pt, key, kct, dct.

(* ... and the uniform distribution over the DEM key space *)
op [lossless full uniform] dkey : key distr.


(** A KEM is a triple of (potentially probabilistic and stateful)
    algorithms:
**)
module type KEM = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey): key * kct
  proc dec(sk : skey, k : kct): key option
}.

(** A CPA adversary against the KEM is an algorithm: **)
module type KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, c : kct): bool
}.

(** And we define the advantage of a CPA adversary A against a KEM E
    as
      `|   Pr[KEM_CPA_Exp(E, A).run(false) @ &m: res]
         - Pr[KEM_CPA_Exp(E, A).run(true) @ &m: res]  |
    where KEM_CPA_Exp is the experiment:
**)
module KEM_CPA_Exp (E : KEM) (A : KEM_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, k0, k1, k, c, r;

    (pk, sk) <@ E.keygen();
    (k0, c) <@ E.enc(pk);
    k1 <$ dkey;
    k <- if b then k1 else k0;
    r <@ A.distinguish(pk, k, c);
    return r;
  }
}.

(** A DEM is a pair of algorithms: **)
module type DEM = {
  (* We force key generation to be sampling in `dkey` *)
  proc enc(k : key, m : pt): dct
  proc dec(k : key, c : dct): pt
}.

(** A passive/eavesdropping DEM adversary is a pair of algorithms: **)
module type DEM_PAS_Adv = {
  proc choose(): pt * pt
  proc distinguish(c : dct): bool
}.

(** And we define the advantage of a passive adversary A against a DEM
    as
      `|   Pr[DEM_PAS_Exp(E, A).run(false) @ &m: res]
         - Pr[DEM_PAS_Exp(E, A).run(true) @ &m: res]  |
    where DEM_PAS_Exp is the experiment:
**)
module DEM_PAS_Exp (E : DEM) (A : DEM_PAS_Adv) = {
  proc run(b : bool) = {
    var k, m0, m1, c, r;

    k <$ dkey;
    (m0, m1) <@ A.choose();
    c <@ E.enc(k, if b then m1 else m0);
    r <@ A.distinguish(c);
    return r;
  }
}.

(** We have defined our assumptions, we can now define our
    constructive goal.

    A public key encryption scheme (with structured ciphertexts!) is a
    triple of algorithms:
**)
module type PKE = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey, m : pt): kct * dct
  proc dec(sk : skey, c : kct * dct): pt option
}.

(** A CPA adversary against a PKE is a pair of algorithms: **)
module type PKE_CPA_Adv = {
  proc choose(pk : pkey): pt * pt
  proc distinguish(c : kct * dct): bool
}.

(** The advantage of a CPA adversary A against a PKE E is
      `|   Pr[PKE_CPA_Exp(E, A).run(false) @ &m: res]
         - Pr[PKE_CPA_Exp(E, A).run(true) @ &m: res]  |
    where PKE_CPA_Exp is the experiment:
**)
module PKE_CPA_Exp (E : PKE) (A : PKE_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, c, r, m0, m1;

    (pk, sk) <@ E.keygen();
    (m0, m1) <@ A.choose(pk);
    c <@ E.enc(pk, if b then m1 else m0);
    r <@ A.distinguish(c);
    return r;
  }
}.

(* (* Note: instead of defining a specialised notion of PKE with
      structured ciphertexts, we could have obtained very similar
      definitions by _instantiating_ a library definition.

      However, note that the humongous variety of ways in which CPA
      security for PKEs can be expressed makes developing such a
      library a tricky proposition.
   *)
require PKE.
clone PKE as KEM_Based_PKE with
  type pkey <= pkey,
  type skey <= skey,
  type plaintext <= pt,
  type ciphertext <= kct * dct.

print KEM_Based_PKE.Scheme.
*)

(** Finally, we can define our KEM/DEM composition **)
module KEMDEM (E_kem : KEM) (E_s : DEM): PKE = {
  proc keygen = E_kem.keygen

  proc enc(pk : pkey, m : pt): kct * dct = {
    var k, kc, c;

    (k, kc) <@ E_kem.enc(pk);
    c <@ E_s.enc(k, m);
    return (kc, c);
  }

  proc dec(sk : skey, c : kct * dct): pt option = {
    var kc, dc, r, k, m;

    (kc, dc) <- c;
    r <- None;
    k <@ E_kem.dec(sk, kc);
    if (k <> None) {
      m <@ E_s.dec(oget k, dc);
      r <- Some m;
    }
    return r;
  }
}.


(*** And we prove its security: there exist reductions B_kem_0(E_s),
       B_kem_1(E_s) and B_s(E_kem) such that ...
***)
module B_kem_0 (E_s : DEM) (A : PKE_CPA_Adv) = {
  proc distinguish(pk : pkey, k : key, c: kct) = {
    var m0, m1, c', r;

    (m0, m1) <@ A.choose(pk);
    c' <@ E_s.enc(k, m0);
    r <@ A.distinguish(c, c');
    return r;
  }
}.

module B_kem_1 (E_s : DEM) (A : PKE_CPA_Adv) = {
  proc distinguish(pk : pkey, k : key, c: kct) = {
    var m0, m1, c', r;

    (m0, m1) <@ A.choose(pk);
    c' <@ E_s.enc(k, m1);
    r <@ A.distinguish(c, c');
    return r;
  }
}.

module B_s (E_kem : KEM) (A : PKE_CPA_Adv) = {
  var pk : pkey

  proc choose() = {
    var sk, m0, m1;

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    return (m0, m1);
  }

  proc distinguish(c : dct) = {
    var k0, kc, r;

    (k0, kc) <@ E_kem.enc(pk);
    r <@ A.distinguish(kc, c);
    return r;
  }
}.

section.
(* For every KEM E_kem *)
declare module E_kem <: KEM { -B_s }.
(* For every DEM E_s *)
declare module E_s   <: DEM { -B_s, -E_kem }.
(* and for every CPA adversary against the PKE KEMDEM(E_kem, E_s) *)
declare module A     <: PKE_CPA_Adv { -B_s, -E_kem, -E_s }.
(* we have
        Adv^{CPA}_{KEMDEM(E_kem, E_s)}(A)
     <=   Adv^{CPA}_{E_kem}(B_kem_0(E_s, A))
        + Adv^{CPA}_{E_kem}(B_kem_1(E_s, A))
        + Adv^{PAS}_{E_s}(B_s(E_kem, A))
*)

(* The pen and paper proof would use an intermediate game Game1, which
   is roughly the PKE CPA experiment, but where the DEM encryption is
   carried out using a random key, instead of one obtained from KEM
   encapsulation.

   It is clearly at distance Adv^{CPA}_{E_kem} from the PKE CPA
   experiment on KEMDEM with the same parameter b. (Hop1 and Hop3.)

   The distance between Game1 with b = 0 and Game1 with b = 1 is
   clearly exactly Adv^{PAS}_{E_s}. (Hop2.)

   Defining Game1 is unnecessary for the EasyCrypt proof itself, but
   helps present it in game-based style.
*)
local module Game1 = {
  proc run(b : bool) = {
    var pk, sk, m0, m1, k0, k1, kc, c, r;

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    (k0, kc) <@ E_kem.enc(pk);
    k1 <$ dkey;
    c <@ E_s.enc(k1, if b then m1 else m0);
    r <@ A.distinguish(kc, c);
    return r;
  }
}.

local lemma pke_0_kem_0 &m:
    Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
  = Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res].
proof.
(* We prove the equality by proving that the procedures are
   equivalent; we do *that* by proving that their body is equivalent
*)
byequiv=> //; proc.
(* We inline the reduction to make the PKE adversary appear on the
   right *)
inline {2} ^r<@.
wp; call (: true). (* if the adversary runs with similar views of the
                      system (state of A, inputs), then they must end
                      with similar views of the system (output) *)
(* We inline the KEM/DEM's encryption to make encapsulation and DEM
   encryption appear *)
inline {1} ^c<@.
wp; call (: true). (* same on DEM encryption-it's abstract! treated
                      the same as an adversary in our logic *)
(* We need to align the KEM encapsulation calls and adversary runs;
   fortunately, we know they are independent. *)
swap {1} ^pk0<- -1. swap {1} -1 -2.
(* We then have a sequence of equivalent calls *)
wp; call (: true).
(* interrupted by a one-sided random sampling-a key we do not use *)
wp; rnd {2}.
wp; call (: true).
wp; call (: true).
by auto.
qed.

local lemma kem_1_game1_0 &m:
    Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res]
  = Pr[Game1.run(false) @ &m: res].
proof.
(* Once we know how to do the proof, we can automate more of it *)
byequiv=> //; proc.
inline {1} ^r<@.
swap {1} ^pk0<- -3. swap {1} ^c0<- & +1 @^pk0<- & +1.
sim.
call (: true); wp.
conseq (: ={k1, k0, pk, sk, m1, m0, glob E_s, glob A}
       /\ c{1} = kc{2})=> //.
by sim.
qed.

local lemma Hop1 &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
   - Pr[Game1.run(false) @ &m: res] |
 = `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
    - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |.
proof. by rewrite (pke_0_kem_0 &m) -(kem_1_game1_0 &m). qed.

local lemma Hop2 &m:
  `| Pr[Game1.run(false) @ &m: res]
   - Pr[Game1.run(true) @ &m: res] |
  = `| Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
     - Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |.
proof.
(* With enough faith, one can shortcut named lemmas *)
have ->: Pr[Game1.run(false) @ &m: res]
       = Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res].
+ byequiv=> //; proc.
  inline {2} ^r<@.
  swap {2} ^c0<- & +1 -2. swap {2} ^k<$ 2.
  inline {2} 1.
  by sim.
have -> //: Pr[Game1.run(true) @ &m: res]
          = Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res].
byequiv=> //; proc.
swap {2} ^k<$ 1.
inline {2} ^r<@.
swap {2} ^c0<- & +1 -3.
inline {2} 1.
by sim.
qed.

local lemma Hop3 &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]
   - Pr[Game1.run(true) @ &m: res] |
 = `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res]
    - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res] |.
proof.
have ->: Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]
       = Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res].
+ byequiv=> //; proc.
  inline *.
  swap {1} ^pk0<- -1. swap {1} 5 -2.
  wp; call (: true).
  wp; call (: true).
  wp; call (: true).
  wp; rnd {2}; call (: true).
  by wp; call (: true).
have -> /#: Pr[Game1.run(true) @ &m: res]
          = Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res].
byequiv=> //; proc.
inline *.
swap {2} ^pk0<- -3. swap {2} 8 -5.
sim.
wp; call (: true).
wp; rnd.
wp; call (: true).
wp; call (: true).
by wp; call (: true).
qed.

(* We can finally conclude! *)
lemma security_of_kem_dem &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
   - Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]|
  <= `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |
   + `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res] |
   + `| Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
      - Pr[DEM_PAS_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |.
proof. smt(Hop1 Hop2 Hop3). qed.

end section.

print security_of_kem_dem.
