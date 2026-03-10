require import AllCore Real FMap FSet Distr.
require import PROM.

require (*--*) StdOrder.
(*---*) import StdOrder.RealOrder.

require (*--*) St_CDH_abstract SUFCMA UATPaKE.

(** Buckle Up! **)
(* Starting notes:
   - We (try to) follow Doreen and Paul's model as closely as possible
     while remaining precise.
   - Therefore, we stick to the presentation of Signed DH as involving
     nominal groups with St-CDH in the ROM. A slightly more idiomatic
     EasyCrypt approach (enabling more reuse) would be to consider
     instead a signed NIKE (assuming m-CKS-heavy security on a simple
     NIKE), then showing that that can be constructed, in the ROM,
     from a Nominal Group in which Strong CDH is hard.
*)

(** Types and operators for the DH group **)
type pdh, sdh, sskey.

op g: pdh.
op [lossless] dsk: sdh distr.
op (^): pdh -> sdh -> pdh.

axiom shared_keyC x y:
     x \in dsk
  => y \in dsk
  => (g ^ x) ^ y = (g ^ y) ^ x.

op [lossless full uniform] dssk: sskey distr.

(** Instantiate the St-CDH theory **)
clone import St_CDH_abstract as StCDH with
  type pkey <= pdh,
  type skey <= sdh,
  op   g    <= g,
  op   dsk  <= dsk,
  op   (^)  <= (^)
proof *.
realize dsk_ll by exact: dsk_ll.
realize shared_keyC by exact: shared_keyC.

(** Additional types for the signature scheme **)
type pkey, skey, sig.

(** Instantiate the SUFCMA theory **)
clone import SUFCMA as Signature with
  type pkey   <= pkey,
  type skey   <= skey,
  type sig    <= sig,
  type msg    <= pdh * pdh
proof *.

(** Additional types for defining protocols,
    plus RO instantiation
**)
type client_state = {
  pk: pkey;     (* The server's identity, as its public key *)
  epk: pdh;     (* The client's ephemeral public key *)
  esk: sdh      (* The client's ephemeral secret *)
}.

clone import FullRO as H with
  type in_t    <= pdh * pdh * pdh,
  type out_t   <= sskey,
  op   dout  _ <= dssk,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

(** Instantiate the UATPaKE theory
    Note: this builds the ROM in   **)
clone import UATPaKE as Security with
  type pkey         <= pkey,
  type skey         <= skey,
  type sskey        <= sskey,
  op   dssk         <= dssk,
  type client_state <= client_state,
  type msg1         <= pdh,
  type msg2         <= pdh * sig,
  type ro_in        <= pdh * pdh * pdh,
  type ro_out       <= sskey,
  op   d_ro         <= Self.dssk
proof *.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Finally, we define the signed DH protocol **)
module SignedDH (S : SigScheme) (H : RO) : UATPaKE = {
  proc gen() = {
    var kp;

    kp <@ S.keygen();
    return kp;
  }

  proc init(pk) = {
    var x_sk;

    x_sk <$ dsk;
    return ({| pk = pk; epk = g ^ x_sk; esk = x_sk |}, g ^ x_sk);
  }

  proc resp(sk_s, x_pk) = {
    var y_sk, s, ks;

    y_sk <$ dsk;
    s <@ S.sign(sk_s, (x_pk, g ^ y_sk));
    ks <@ H.get(x_pk, g ^ y_sk, x_pk ^ y_sk);
    return (ks, (g ^ y_sk, s));
  }

  proc recv(st, c) = {
    var y_pk, s, b, kc;
    var r <- None;

    (y_pk, s) <- c;
    b <@ S.verify(st.`pk, (st.`epk,  y_pk), s);
    if (b) {
      kc <@ H.get(st.`epk, y_pk, y_pk ^ st.`esk);
      r <- Some kc;
    }
    return r;
  }
}.

module B1 (S : SigScheme) (A : Adv_UATPaKE_RO) (O : CMA_Oracles) = {
  var b_ror : bool

  var halt_bad : bool

  var n : int
  var m : int
  
  var p_map : (int, int) fmap
  var i_map : (int, pdh) fmap
  var r_map : (int option * int, (pdh * sig) fset) fmap

  var pk_map : (int, pkey) fmap
  var c_map : (int, client_state) fmap
  
  var q : int fset
  var ich : int fset
  var rch : int fset
  var xp : int fset
  var cr : int fset
  
  module Oracles = {
    proc gen(): pkey = {
      var pk, bad;

      if (!halt_bad) {
        m <- m + 1;
        pk <@ O.gen();
        (* The reduction fails if:
           1. the adversary predicts an honest public key before it is
              generated; OR
           2. two servers generate the same public key.
        *)
        bad <-    has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map
               \/ rng pk_map pk;
        pk_map.[m] <- pk;
        if (bad) {
          halt_bad <- true;
          pk <- witness;
        }
      }  else {
        pk <- witness;
      }
     
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (!halt_bad /\ 0 < j <= m) {
        r <@ O.corrupt(j);
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, c, x, jo;

      if (!halt_bad) {
        n <- n + 1;
        x <$ dsk;
        c <- g ^ x;
        st <- {| pk = pk; epk = c; esk = x; |};
        c_map.[n] <- st;
        jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
        if (jo is Some j) {
          p_map.[n] <- j;
          i_map.[n] <- c;
        }
      } else {
        c <- witness;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, h, y, sig;
      var r <- None;

      if (!halt_bad /\ 0 < j <= m) {
        y <$ dsk;
        h <- g ^ y;
        sig <@ O.sign(j, (c, h));
        k <@ RO.get(c, h, c ^ y);
        c' <- (h, oget sig);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, jo, bo, b;
      var ko <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          jo <- find (fun _ pk_j=> pk_j = st_i.`pk) pk_map;
          if (jo is Some j) {
            bo <@ O.verify(j, (st_i.`epk, h), sig);
            b <- odflt false bo;
          } else {
            (* If the adversary gives us a key that is not registered
               as honest, we just simulate stuff:
               1. It is impossible for it to trigger the iffy case
                  below (because p_map.[i] would necessarily be
                  set); and
               2. The only way the adversary could trigger the iffy
                  case below on the same value later is to get the same
                  public key registered honestly, which halts the game-so
                  we would still not break the invariant)
            *)
            b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          }
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            halt_bad <- true;
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h(x) = {
      var r;

      if (!halt_bad) {
        r <@ RO.get(x);
      } else {
        r <- witness;
      }
      return r;
    }
  }

  proc forge() = {
    var b';

    RO.init();

    halt_bad <- false;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    c_map <- empty;

    b' <@ A(Oracles).distinguish();
  }
}.

module B1_0 (S : SigScheme) (A : Adv_UATPaKE_RO) (O : CMA_Oracles) = {
  proc forge() = {
    B1.b_ror <- false;
    B1(S, A, O).forge();
  }
}.

module B1_1 (S : SigScheme) (A : Adv_UATPaKE_RO) (O : CMA_Oracles) = {
  proc forge() = {
    B1.b_ror <- true;
    B1(S, A, O).forge();
  }
}.

module B2 (S : SigScheme) (A : Adv_UATPaKE_RO) (O : St_CDH_Oracles) = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var h_map : (pdh option * pdh * pdh, sskey) fmap

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var k, ko, b;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        b <@ O.ddh(x, y, z);
        if (has (fun _ c=> c = x) i_map /\ b) {
          k <@ h'(x, y);
          ko <- Some k;
        } else {
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }
      
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var pk, x;
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        pk <- (oget c_map.[i]).`pk;
        x <@ O.corrupt_1(i);
        r <- Some {| pk = pk; epk = g ^ oget x; esk = oget x |};
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c;

      n <- n + 1;
      c <@ O.gen_1();
      st <- {| pk = pk; epk = c; esk = witness; |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        y <- witness; (* silence a warning: all paths that use y define it first *)
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          h <@ O.gen_2();
        } else {
          y <$ dsk;
          h <- g ^ y;
        }
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          k <@ h'(c, h);
        } else {
          k <@ RO.get(c, h, c ^ y);
        }
        c' <- (h, sig);
        io <- find (fun i j' => j' = j /\ i_map.[i] = Some c) p_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
               empty set, we read undefined entries as the empty set
               here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            (* Spec says "Stop" *)
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc solve() = {
    var b';

    RO.init();

    b_ror <- witness;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    h_map <- empty;

    b' <@ A(Oracles).distinguish();
  }
}.

section.
declare module S <: SigScheme { -Exp_b, -SUFCMA, -RO, -B1, -B2 }.
declare module A <: Adv_UATPaKE_RO { -Exp_b, -SUFCMA, -RO, -B1, -B2, -S }.

local module Game0_b = {
  (* Inline and add (non-operational) infrastructure for early halting *)
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var halt_bad: bool

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      if (!halt_bad) {
        m <- m + 1;
        (pk, sk) <@ S.keygen();
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      } else {
        pk <- witness;
      }
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (!halt_bad /\ 0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, x, c;

      if (!halt_bad) {
        n <- n + 1;
        x <$ dsk;
        c <- g ^ x;
        st <- {| pk = pk; epk = c; esk = x |};
        c_map.[n] <- st;
        jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
        if (jo is Some j) {
          p_map.[n] <- j;
          i_map.[n] <- c;
        }
      } else {
        c <- witness;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (!halt_bad /\ 0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c, h, c ^ y);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h(x) = {
      var r;

      if (!halt_bad) {
        r <@ RO.get(x);
      } else {
        r <- witness;
      }
      return r;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    halt_bad <- false;
    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b' /\ !halt_bad;
  }
}.

(* Pen and paper says "Stop"; we can't stop because our
   reductions *must* be black-box. We execute the adversary,
   we do not simulate them: so we can't interrupt them
   either. This is where the infrastructure we added in Hop
   0 comes in: we set a flag that silences oracles and
   causes the adversary to lose.
*)
local module Game1_b = {
  (* Halt if the adversary predicts an honest public key before it is
     generated *)
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game0_b [-run]

  var bad_1: bool
  var bad_2: bool
  var bad_3: bool

  module Oracles = {
    include Game0_b.Oracles [-gen]

    proc gen(): pkey = {
      var sk, pk;
 
      if (!halt_bad) {
        m <- m + 1;
        (pk, sk) <@ S.keygen();
        (* bad_1: the adversary predicts a public key later generated
           honestly *)
        bad_1 <- bad_1 \/ has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map;
        (* bad_2: two honest servers generate the same public key *)
        bad_2 <- bad_2 \/ rng pk_map pk;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
        if (bad_1 \/ bad_2) {
          halt_bad <- true;
          pk <- witness;
        }
      } else {
        pk <- witness;
      }
      
      return pk;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    halt_bad <- false;
    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b' /\ !halt_bad;
  }
}.

local module Game2_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game0_b [-run]
  include var Game1_b [-run]

  module Oracles = {
    include Game1_b.Oracles [-receive]

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            halt_bad <- true;
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    halt_bad <- false;
    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b' /\ !halt_bad;
  }
}.

(** We now successively state and prove claims about consecutive games
    in the sequence. We sometimes introduce intermediate modules as
    proof artefacts to enable formal reasoning.
**)

(* Hop 0: The distance between Game0(false) and Game0(true) is exactly
          the advantage of A in distinguishing the real and ideal
          experiments
*)
local lemma Hop0 &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m: res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true ) @ &m: res] |
  = `|  Pr[Game0_b.run(false) @ &m: res]
      - Pr[Game0_b.run(true ) @ &m: res] |.
proof.
have ^ + -> - -> //:
  forall b, Pr[Exp_b(SignedDH(S), RO, A).run(b) @ &m: res]
          = Pr[Game0_b.run(b) @ &m: res].
move=> b; byequiv (: ={glob A, glob S, arg} ==> ={res})=> //.
proc.
(* The calls are equivalent due to equality on a bunch of variables *)
call (: ={glob Exp_b(SignedDH(S), RO)} /\ !Game0_b.halt_bad{2}); last first.
(* The invariant holds initially and allows us to conclude *)
+ by inline *; auto.
(* The invariant is preserved by all oracles *)
+ proc; rcondt {2} ^if; 1:by auto.
  by inline *; auto; call (: true); auto.
+ by proc; inline *; auto=> />.
+ by proc; inline *; auto=> />.
+ proc; rcondt {2} ^if; 1:by auto.
  conseq (: ={glob Exp_b(SignedDH(S), RO), c})=> //.
  by inline *; sim; auto.
+ proc; inline *; sp; if; auto.
  conseq (: ={glob Exp_b(SignedDH(S), RO), k, c'})=> //.
  sim; auto.
  by call (: true); auto.
+ proc; sp; if; auto; sp; if; auto.
  inline {1} 1.
  conseq (: ={glob Exp_b(SignedDH(S), RO), ko})=> //.
  by sim; auto.
+ conseq (: _ ==> ={glob RO, res})=> //.
  proc *; inline {2} 1; rcondt {2} ^if; 1:by auto.
  by sim.
qed.

(** Hop 1: Game 0 and Game 1 are equivalent (regardless of the value
    of the challenge bit) unless (and until) the gen oracle outputs a
    public key that was already used by the adversary (bad_1) OR one
    that was already honestly generated (bad_2).

    bad_1 happens with a probability bounded by the guessing entropy
    of the distribution induced on public keys by key generation.

    bad_2 is the probability of collision in taking q_gen samples from
    that same distributions.
**)
local lemma Hop1 (b : bool) &m:
  `|Pr[Game0_b.run(b) @ &m: res] - Pr[Game1_b.run(b) @ &m: res]|
  <= Pr[Game1_b.run(b) @ &m: Game1_b.bad_1] + Pr[Game1_b.run(b) @ &m: Game1_b.bad_2].
(* This aborts the proof - we simply use the statement as a section heading. *)
abort.

(* This is an equivalence up to failure, which places some constraints
   on the adversary, namely:
   - that it cannot use non-termination as a behaviour to distinguish; and
   - (later) that it cannot use the number of queries it makes as a
     behaviour to distinguish.
   The latter could be pushed into the proof; the former is not (yet?)
   supported by the logics.
*)
(* For all oracles that terminate, the adversary terminates *)
declare axiom A_ll (O <: UATPaKE_RO_Oracles {-A}):
     islossless O.gen
  => islossless O.corrupt
  => islossless O.expose
  => islossless O.init
  => islossless O.respond
  => islossless O.receive
  => islossless O.h
  => islossless A(O).distinguish.

declare axiom S_keygen_ll: islossless S.keygen.
declare axiom S_sign_ll: islossless S.sign.
declare axiom S_verify_ll: islossless S.verify.

(* To get absolute values, we must make the event appear on the left.
   Why? Because we make the failure immediately visible to the
   adversary and change the behaviour of the oracles after it; so the
   adversary on the right could in theory do extremely weird things,
   including giving up.

   The logic gives us this:

     Pr[Game0: res] <= Pr[Game1: res] + Pr[Game1: bad]

   If the adversary gives up in Game 1 when bad happens (and the games
   are equivalent otherwise) then it is easy to see that

     |Pr[Game0: res] - Pr[Game1: res]| = Pr[Game1: res] - Pr[Game0: res]

   This makes us sad. We become a lot less sad if we can also show that

     Pr[Game0: bad] = Pr[Game1: bad]

   But this requires being able to refer to the bad event before the
   hop. So each up to bad hop becomes two half-hops: one "free" hop
   where we just log that the bad event happens; and the actual
   meaningful hop where we change the oracles' behaviour after bad
   happens.
*)
local module Game05_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game0_b [-run]
  include var Game1_b [-run]

  module Oracles = {
    include Game0_b.Oracles [-gen]

    proc gen(): pkey = {
      var sk, pk;
 
      if (!halt_bad) {
        m <- m + 1;
        (pk, sk) <@ S.keygen();
        (* we need to guard this so we can keep bad1 and bad2
           individually synchronised... may have been easier to deal
           with them one by one...
        *)
        if (!bad_1 /\ !bad_2) {
          bad_1 <- has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map;
          bad_2 <- rng pk_map pk;
        }
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      } else {
        pk <- witness;
      }
      
      return pk;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    halt_bad <- false;
    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b' /\ !halt_bad;
  }
}.

local lemma Hop0_bad (b : bool) &m:
  Pr[Game0_b.run(b) @ &m: res] = Pr[Game05_b.run(b) @ &m: res].
proof.
byequiv (: ={glob A, glob S, b} ==> ={res})=> //.
by proc; sim.
qed.

local lemma Hop1 (b : bool) &m:
  `|Pr[Game0_b.run(b) @ &m: res] - Pr[Game1_b.run(b) @ &m: res]|
  <= Pr[Game1_b.run(b) @ &m: Game1_b.bad_1] + Pr[Game1_b.run(b) @ &m: Game1_b.bad_2].
proof.
rewrite Hop0_bad.
apply: (ler_trans Pr[Game1_b.run(b) @ &m: Game1_b.bad_1 \/ Game1_b.bad_2]); last first.
+ rewrite Pr [mu_or]; smt(ge0_mu).
byequiv (: ={glob A, glob S, b} ==> _): (Game1_b.bad_1 \/ Game1_b.bad_2)=> [||/#] //.
proc.
(* And now we lift the reasoning up to bad to the oracles the
   adversary has access to. Because we're in manual mode, and the
   semantics of `equiv` imply equitermination, we *must* also show that
   everything terminates once bad has occurred (we can no longer rely on
   the relational reasoning to guarantee thise once the programs are out
   of sync). In addition, and perhaps obviously, we must prove that
   the bad even can never unhappen once it has happened.  Keep in mind
   that it is simply a property of the state (here, the value of a
   boolean variable), and that the state can be modified
   programmatically. It isn't some external, untouchable truth. *)
call (: Game1_b.bad_1 \/ Game1_b.bad_2 (* the bad event *)
      (* The invariant that holds until bad happens *)
      , ={glob Exp_b, glob S, glob RO, Game0_b.halt_bad, Game1_b.bad_1, Game1_b.bad_2}
     /\ !Game0_b.halt_bad{2}
      (* the invariant that holds after bad happens *)
      , ={Game1_b.bad_1, Game1_b.bad_2} /\ Game0_b.halt_bad{2}).
(* Goal 1: the adversary terminates if its oracles terminate. See above. *)
+ exact: A_ll.
(* Goal i.0: if bad does not hold, and the non-bad invariant holds
   initially, then executing the oracles leads us to memories that are
   such that the correct invariant holds (depending on whether bad
   happened during the oracles' execution *)
+ by proc; if; auto; call (: true); auto=> /> /#.
(* Goal i.1: the left-hand side oracle terminates and preserves bad *)
+ move=> &2 bad; proc; if; auto.
  call S_keygen_ll; auto=> />.
  by case: bad.
(* Goal i.2: the right-hand side oracle terminates and preserves bad *)
+ move=> &1; proc; if; auto.
  by call S_keygen_ll; auto=> />.
(* Do those three again for all oracles *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; proc; if; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ by move=> &1; proc; if; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ move=> &1; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  exact: S_verify_ll.
+ move=> &1; conseq (: true); proc; islossless.
  exact: S_verify_ll.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; conseq (: true); proc; islossless.
+ by move=> &1; conseq (: true); proc; islossless.
(* Finally, show that the invariant implies what we wanted (and that
   the program's preamble establishes the invariant) *)
by inline; auto=> /> /#.
qed.

(** Hop 2: Game 1 and Game 2 are equivalent unless (and until) the
    adversary successfully triggers bad_3 in Game 2.
**)
local module Game15_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game0_b [-run]
  include var Game1_b [-run]

  module Oracles = {
    include Game2_b.Oracles [-receive]

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (!halt_bad /\ 0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            if (Exp_b.b_ror) {
              k <$ dssk;
              ko <- Some k;
            }
            Exp_b.ich <- Exp_b.ich `|` fset1 i;
          }
        }
      }
      return ko;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    halt_bad <- false;
    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b' /\ !halt_bad;
  }
}.

local lemma Hop1_bad (b : bool) &m:
  Pr[Game1_b.run(b) @ &m: res] = Pr[Game15_b.run(b) @ &m: res].
proof.
byequiv (: ={glob A, glob S, b} ==> ={res})=> //.
by proc; sim.
qed.

local lemma Hop2 b &m:
  `|Pr[Game1_b.run(b) @ &m: res] - Pr[Game2_b.run(b) @ &m: res]|
  <= Pr[Game2_b.run(b) @ &m: Game1_b.bad_3].
proof.
rewrite (Hop1_bad b &m).
byequiv (: ={glob A, glob S, b} ==> _): Game1_b.bad_3=> [||/#] //.
proc.
call (: Game1_b.bad_3 (* the bad event *)
      (* The invariant that holds until bad happens *)
      , ={glob Exp_b, glob S, glob RO, Game0_b.halt_bad, Game1_b.bad_1, Game1_b.bad_2, Game1_b.bad_3}
     /\ !Game1_b.bad_3{1}
      (* the invariant that holds after bad happens *)
      , ={Game1_b.bad_3} /\ Game0_b.halt_bad{2}).
(* Goal 1: the adversary terminates if its oracles terminate. See above. *)
+ exact: A_ll.
(* Goal i.0: if bad does not hold, and the non-bad invariant holds
   initially, then executing the oracles leads us to memories that are
   such that the correct invariant holds (depending on whether bad
   happened during the oracles' execution *)
+ by proc; if; auto; call (: true); auto.
(* Goal i.1: the left-hand side oracle terminates and preserves bad *)
+ move=> &2 bad; proc; if; auto.
  by call S_keygen_ll; auto=> />; rewrite bad.
(* Goal i.2: the right-hand side oracle terminates and preserves bad *)
+ move=> &1; proc; if; auto.
  by call S_keygen_ll; auto=> />.
(* Do those three again for all oracles *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; proc; if; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ by move=> &1; proc; if; auto=> />.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ move=> &1; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
(* And again *)
+ proc; sp; if; auto.
  sp; if; 1,3:auto.
  seq 2 2: (={glob Exp_b, glob S, glob RO, Game0_b.halt_bad, Game1_b.bad_1, Game1_b.bad_2, Game1_b.bad_3, i, c, ch, h, sig, b, ko, st_i}
         /\ ko{1} = None
         /\ (Game1_b.bad_3 => Game0_b.halt_bad){2}).
  + by call (: true); auto.
  if; 1:auto; last first.
  + rcondf {1} 1; 1:by auto=> /#.
    rcondf {2} 1; 1:by auto=> /#.
    by auto=> /> /#.
  seq 2 2: (={glob Exp_b, glob S, glob RO, Game0_b.halt_bad, Game1_b.bad_1, Game1_b.bad_2, Game1_b.bad_3, i, c, ch, h, sig, b, ko, st_i, k}
         /\ (Game1_b.bad_3 => Game0_b.halt_bad){2}).
  + by wp; call (: ={glob RO}); auto.
  if; 1,3:by auto=> /> /#.
  by sp; if; auto.
+ move=> &2 bad; rewrite bad.
  proc; sp; if; auto; sp; if; auto=> />.
  seq 3: true 1%r 1%r 0%r _ (Game1_b.bad_3 /\ Game0_b.halt_bad{2})=> //.
  + by conseq (: _ ==> true)=> />.
  + by islossless; exact: S_verify_ll.
  + if; 2:by auto=> />.
    by sp; conseq (: _ ==> true)=> />; islossless.
+ move=> &2; proc.
  rcondf 2; 1:by auto=> />.
  by auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, Game1_b.bad_3, res})=> //.
  by sim.
+ by move=> &2 bad; conseq (: true); proc; islossless.
+ by move=> &1; conseq (: true); proc; islossless.
(* Finally, show that the invariant implies what we wanted (and that
   the program's preamble establishes the invariant) *)
by inline; auto=> /> /#.
qed.

(** Reduction for Hop 2: If bad_2 happens, then we can extract a
    forgery, regardless of the challenge bit.
**)
local lemma Reduction1 b &m:
     B1.b_ror{m} = b
  => Pr[Game2_b.run(b) @ &m: Game1_b.bad_3]
     <= Pr[SUFCMA(S, B1(S, A)).run() @ &m: res].
abort.

(* We'd need to prove the same thing twice (once for each b) if we
   prove it directly on probabilities. But we can be a bit more clever
   by going one level down.
*)
local equiv Reduction1_equiv:
  Game2_b.run ~ SUFCMA(S, B1(S, A)).run:
       ={glob A, glob S, glob RO}
    /\ b{1} = B1.b_ror{2}
    ==> Game1_b.bad_3{1} => res{2}.
(** This says, if we have two memories that agree on the globals of A,
    S and RO and such that the value of the b argument is equal to the
    value of the B1.b_ror global variable in the right memory, then the
    two programs have the same probability of terminating, and we can
    couple the randomness in both programs so that the bad_3 flag being
    set implies that the right hand side program outputs true.
**)
proof.
proc.
inline {2} 7.
(** The invariant here must guarantee that the executions are and stay in sync
    *and* that they preserve the postcondition: if bad happens on the
    left, then the reduction wins.
**)
call (: (** Equivalences **)
        ={glob RO, glob S}
     /\ ={halt_bad}(Game0_b, B1)
     /\ ={m, n, q, ich, rch, xp, cr, pk_map, p_map, i_map, r_map, c_map, b_ror}(Exp_b, B1)
     /\ ={cr, pk_map, sk_map}(Exp_b, SUFCMA)
     /\ (B1.m = SUFCMA.n){2}
     /\ (B1.pk_map = SUFCMA.pk_map){2}
        (** One-sided invariants **)
     /\ (0 <= B1.m){2}
     /\ (0 <= B1.n){2}
     /\ (forall j, B1.pk_map.[j] <> None <=> 0 < j <= B1.m){2}
     /\ (forall i, B1.c_map.[i] <> None <=> 0 < i <= B1.n){2}
     /\ (forall i j,
              B1.p_map.[i] = Some j
           => exists st,
                   B1.c_map.[i] = Some st
                /\ B1.pk_map.[j] = Some st.`pk){2}
     /\ (   !Game1_b.bad_2
         => forall j j' pk,
                 Exp_b.pk_map.[j] = Some pk
              => Exp_b.pk_map.[j'] = Some pk
              => j = j'){1}
     /\ (Game1_b.bad_1 => Game0_b.halt_bad){1}
     /\ (Game1_b.bad_2 => Game0_b.halt_bad){1}
     /\ (Game1_b.bad_3 => Game0_b.halt_bad){1}
        (** THE CRUX **)
     /\ (Game1_b.bad_3{1} => SUFCMA.win{2})); last first.
+ by inline *; auto=> />; smt(emptyE in_fset0).
+ proc; if; 1,3:by auto.
  inline {2} 2; auto; call (: true).
  by auto=> /> &1 &2; smt(get_setE).
+ proc; sp 1 1; if; 1,3:by auto.
  by inline {2} 1; rcondt {2} 3; auto.
+ by proc; auto.
+ proc; if; 1,3:by auto.
  auto=> /> &1 &2 ge0_SUFn ge0_B1n.
  move=> dom_pk dom_c partnering + + + + + not_halted.
  rewrite not_halted=> /> + nbad1 nbad2 nbad3 esk _.
  rewrite nbad2=> /= inj_pk.
  smt(find_some get_setE).
+ conseq (: ={glob RO, glob S, res}
         /\ ={halt_bad}(Game0_b, B1)
         /\ ={m, n, q, ich, rch, xp, cr, p_map, i_map, r_map, pk_map, c_map, b_ror}(Exp_b, B1)
         /\ ={cr, pk_map, sk_map}(Exp_b, SUFCMA))=> |>.
  proc; sp; if; 1,3:by auto.
  inline {2} 3; rcondt {2} 6; 1:by auto.
  sim.
  auto; call (: ={glob RO}); 1:by sim.
  by auto; call (: true); auto.
+ proc; sp; if; 1,3:by auto.
  sp; if; 1,3:by auto.
  exlim (find (fun _ pk_j=> pk_j = st_i.`pk) B1.pk_map){2}.
  elim.
  + match None {2} 3; 1:by auto=> /> &0 -> + ->> ->>.
    (** Since the public key `i` is speaking with is not registered
        yet (`find _ B1.pk_map = None`), it *must* be that
        `B1.p_map.[i] = None`. Therefore, the final conditional
        simplifies out and we cannot forge in this run.
    **)
    rcondf {1} 4.
    + move=> &1; conseq (: Exp_b.p_map.[i] = None ==> Exp_b.p_map.[i] = None)=> //>.
      (* LORD THIS IS UGLY *)
      + move=> /> &2 /eq_sym not_found_pk.
        case _: (B1.c_map.[i]{1})=> [/#|/>].
        move=> st_i0 /> cmap_i0 + + ->> <<-.
        move=> _ _ _ _ partnering _ _ _ _ _ _ _ _ _ _.
        case _: (B1.p_map.[i]{1})=> [/#|/>].
        move=> j; rewrite -negP=> /partnering=> - [] [].
        move=> pk0 epk0 esk0 []; rewrite cmap_i0=> />.
        case: (findP (fun _ pk_j=> pk_j = pk0) SUFCMA.pk_map{1}); last first.
        + by rewrite not_found_pk.
        move=> _ /(_ j); rewrite domE.
        by case: (SUFCMA.pk_map.[j]{1}).
      by auto.
    rcondf {2} 5.
    + move=> &1; conseq (: B1.p_map.[i] = None ==> B1.p_map.[i] = None)=> //>.
      (* LORD THIS IS UGLY *)
      + move=> /> &2 /eq_sym not_found_pk.
        case _: (B1.c_map.[i]{2})=> [/#|/>].
        move=> st_i0 /> cmap_i0 + + ->> <<-.
        move=> _ _ _ _ partnering _ _ _ _ _ _ _ _ _ _.
        case _: (B1.p_map.[i]{2})=> [/#|/>].
        move=> j; rewrite -negP=> /partnering=> - [] [].
        move=> pk0 epk0 esk0 []; rewrite cmap_i0=> />.
        case: (findP (fun _ pk_j=> pk_j = pk0) SUFCMA.pk_map{2}); last first.
        + by rewrite not_found_pk.
        move=> _ /(_ j); rewrite domE.
        by case: (SUFCMA.pk_map.[j]{2}).
      by auto.
    seq 2 3: (#pre /\ ={h, sig, b}).
    + by call (: true); auto=> /> /#.
    if; 1,3:by auto.
    by wp; call (: ={glob RO}); auto.
  move=> j; match Some {2} 3.
  + by auto=> /> &0 + + ->> ->> - <- /#.
  inline {2} 4.
  rcondt {2} 8.
  + auto=> /> &0 + + ->> ->> - ^ jP <- @/get_as_Some /=.
    have /#: SUFCMA.pk_map.[j]{0} <> None.
    by move: jP=> /eq_sym /find_some /> ->.
  sp; seq 1 1: (={c_map, q, m, n, ich, rch, xp, cr, pk_map, p_map, i_map, r_map, b_ror}(Exp_b, B1)
             /\ ={cr, pk_map, sk_map}(Exp_b, SUFCMA)
             /\ ={halt_bad}(Game0_b, B1)
             /\ ={glob RO, glob S}
             /\ ={st_i, ko, i, c, ch, h, sig}
             /\ b{1} = b0{2}
             /\ ko{1} = None
             /\ find (fun _ pk_j=> pk_j = st_i{2}.`pk) B1.pk_map{2} = Some j
             /\ j0{2} = j
             /\ (h, s){2} = c{2}
             /\ m{2} = (st_i.`epk, h){2}
             /\ B1.c_map.[i]{2} = Some st_i{2}
             /\ 0 <= B1.m{2}
             /\ 0 <= B1.n{2}
             /\ (forall j, B1.pk_map.[j] <> None <=> 0 < j <= B1.m){2}
             /\ (forall j, B1.c_map.[j] <> None <=> 0 < j <= B1.n){2}
             /\ (forall j i,
                      B1.p_map.[j] = Some i
                   => exists st, B1.c_map.[j] = Some st /\ B1.pk_map.[i] = Some st.`pk){2}
             /\ (   !Game1_b.bad_2
                 => forall i i' pk,
                         Exp_b.pk_map.[i] = Some pk
                      => Exp_b.pk_map.[i'] = Some pk
                      => i = i'){1}
             /\ (B1.pk_map = SUFCMA.pk_map){2}
             /\ (B1.m = SUFCMA.n){2}
             /\ (Game1_b.bad_1 => Game0_b.halt_bad){1}
             /\ (Game1_b.bad_2 => Game0_b.halt_bad){1}
             /\ (Game1_b.bad_3 => Game0_b.halt_bad){1}
             /\ (Game1_b.bad_3{1} => SUFCMA.win{2})
             /\ !Game0_b.halt_bad{1}
             /\ 0 < i{1} <= Exp_b.n{1}
             /\ c{1} \notin odflt fset0 Exp_b.r_map.[Exp_b.p_map.[i], i]{1}).
  + call (: true); auto=> /> &1.
    by move=> &2 + qR /> - ^ /eq_sym + <- /> - /find_some @/get_as_Some /#.
  swap {2} 2 -1.
  seq 0 4: (={c_map, q, m, n, ich, rch, xp, cr, pk_map, p_map, i_map, r_map, b_ror}(Exp_b, B1)
         /\ ={cr, pk_map, sk_map}(Exp_b, SUFCMA)
         /\ ={halt_bad}(Game0_b, B1)
         /\ ={glob RO, glob S}
         /\ ={st_i, ko, i, c, ch, b, h, sig}
         /\ ko{1} = None
         /\ find (fun _ pk_j=> pk_j = st_i{2}.`pk) B1.pk_map{2} = Some j
         /\ j0{2} = j
         /\ (h, s){2} = c{2}
         /\ m{2} = (st_i.`epk, h){2}
         /\ B1.c_map.[i]{2} = Some st_i{2}
         /\ 0 <= B1.m{2}
         /\ 0 <= B1.n{2}
         /\ (forall j, B1.pk_map.[j] <> None <=> 0 < j <= B1.m){2}
         /\ (forall j, B1.c_map.[j] <> None <=> 0 < j <= B1.n){2}
         /\ (forall j i,
                  B1.p_map.[j] = Some i
               => exists st,
                       B1.c_map.[j] = Some st
                    /\ B1.pk_map.[i] = Some st.`pk){2}
         /\ (   !Game1_b.bad_2
             => forall i i' pk,
                     Exp_b.pk_map.[i] = Some pk
                  => Exp_b.pk_map.[i'] = Some pk
                  => i = i'){1}
         /\ (B1.pk_map = SUFCMA.pk_map){2}
         /\ (B1.m = SUFCMA.n){2}
         /\ (Game1_b.bad_1 => Game0_b.halt_bad){1}
         /\ (Game1_b.bad_2 => Game0_b.halt_bad){1}
         /\ (Game1_b.bad_3 => Game0_b.halt_bad){1}
         /\ (Game1_b.bad_3{1} => SUFCMA.win{2})
         /\ !Game0_b.halt_bad{1}
         /\ 0 < i{1} <= Exp_b.n{1}
         /\ c{1} \notin odflt fset0 Exp_b.r_map.[Exp_b.p_map.[i], i]{1}
         /\ ((   Game1_b.bad_3{1}
              \/ ((j0 \notin SUFCMA.cr /\ (j0, m, s) \notin SUFCMA.q /\ b){2})) => SUFCMA.win{2})).
  + by auto=> />.
  if=> //; last first.
  + rcondf {1} 1; 1:by auto.
    rcondf {2} 1; 1:by auto.
    by auto.
  seq 1 1: (#pre /\ ={k}); first by conseq />; sim.
  sp; if=> //.
  sp; wp.
  conseq (: _ ==> ={ko}).
  + auto=> |> &1 &2 [] |> [] |>.
    case: (Game1_b.bad_2{1})=> |>.
    case _: (B1.p_map.[i]{2})=> |>.
    move=> j1 + nbad2 /find_some [] |>.
    case: (st_i{2})=> |> pk_j1 epk_i esk_i p_i_j1 pk_j0_pk_j1 c_i.
    move=> SUFCMA_ge0_n ge0_B1_n dom_pk dom_p /(_ _ _ p_i_j1).
    rewrite c_i=> |> pk_j1_pk_j1 /(_ _ _ _ pk_j1_pk_j1 pk_j0_pk_j1)=> |>.
    move=> nbad1 gt0_i gei_B1n hs_notin_rmap + has_b _ _ gt0_j0 gej0_SUFCMA_n j0_notin_cr.
    rewrite j0_notin_cr has_b /=.
    admit. (* We need to show and keep that the SUFCMA query log
              contains all messages sent by honest servers. We cannot
              be processing one of those right now, given path
              conditions. (More invariants.) *)
admitted.

local lemma Reduction1_0 &m:
  Pr[Game2_b.run(false) @ &m: Game1_b.bad_3]
  <= Pr[SUFCMA(S, B1_0(S, A)).run() @ &m: res].
proof.
byequiv (: ={glob A, glob S, glob RO} /\ !b{1} ==> Game1_b.bad_3{1} => res{2})=> //.
proc *.
transitivity {2}
  { B1.b_ror <- false;
    r <@ SUFCMA(S, B1(S, A)).run(); }
  (={glob A, glob S, glob RO} /\ !b{1} ==> Game1_b.bad_3{1} => r{2})
  (={glob A, glob S, glob RO} ==> ={r})=> [/#|/>||].
+ by call Reduction1_equiv; auto=> />.
+ inline *; swap {2} 7 -6.
  by sim.
qed.

local lemma Reduction1_1 &m:
  Pr[Game2_b.run(true) @ &m: Game1_b.bad_3]
  <= Pr[SUFCMA(S, B1_1(S, A)).run() @ &m: res].
proof.
byequiv (: ={glob A, glob S, glob RO} /\ b{1} ==> Game1_b.bad_3{1} => res{2})=> //.
proc *.
transitivity {2}
  { B1.b_ror <- true;
    r <@ SUFCMA(S, B1(S, A)).run(); }
  (={glob A, glob S, glob RO} /\ b{1} ==> Game1_b.bad_3{1} => r{2})
  (={glob A, glob S, glob RO} ==> ={r})=> [/#|/>||].
+ by call Reduction1_equiv; auto=> />.
+ inline *; swap {2} 7 -6.
  by sim.
qed.

local module Game3_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]

  var h_map : (pdh option * pdh * pdh, sskey) fmap

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var io, st_i, k, ko;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        io <- find (fun _ c=> c = x) i_map;
        if (io is Some i) {
          st_i <- oget c_map.[i];
          if (z = y ^ st_i.`esk) {
            k <@ h'(x, y);
            ko <- Some k;
          }
        }
        if (ko is None) {
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }
      
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Here, we don't stop; we just don't actually register the key and move on *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c, x;

      n <- n + 1;
      x <$ dsk;
      c <- g ^ x;
      st <- {| pk = pk; epk = c; esk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        if (has (fun i c' => c' = c) i_map) {
          k <@ h'(c, h);
        } else {
          k <@ RO.get(c, h, c ^ y);
        }
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_2 <- true;
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    h_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

op p: real.
local lemma Hop3 b &m:
  `|Pr[Game2_b.run(b) @ &m: res] - Pr[Game3_b.run(b) @ &m: res]|
  <= p.
admitted.

local lemma Reduction &m:
  `|Pr[Game3_b.run(false) @ &m: res] - Pr[Game3_b.run(true) @ &m: res]|
  <= Pr[St_CDH(B2(S,A)).run() @ &m: res].
proof. admitted.

local lemma Security_of_SignedDH &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m : res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true) @ &m : res]|
  <=   Pr[Game1_b.run(true) @ &m: Game1_b.bad_1]
     + Pr[Game1_b.run(true) @ &m: Game1_b.bad_2]  
     + Pr[Game1_b.run(false) @ &m: Game1_b.bad_1]
     + Pr[Game1_b.run(false) @ &m: Game1_b.bad_2]  
     + Pr[SUFCMA(S, B1_0(S, A)).run() @ &m: res]
     + Pr[SUFCMA(S, B1_1(S, A)).run() @ &m: res]
     + 2%r * p
     + Pr[St_CDH(B2(S,A)).run() @ &m: res].
proof.
smt(Hop0 Hop1 Hop2 Reduction1_0 Reduction1_1 Hop3 Reduction).
qed.
end section.
