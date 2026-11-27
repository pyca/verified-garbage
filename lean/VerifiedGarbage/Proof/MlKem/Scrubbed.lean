module

public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.Zeroize
public import VerifiedGarbage.Proof.Framework.PublicOut
public import VerifiedGarbage.Proof.Zeroize.Wiped
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM leaving `scratch` wiped, on every target

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` (key
generation, encapsulation, with `H(ek)` given or not, and decapsulation)
meets its contract and leaves the first `w` bytes of `scratch` zero and the
others unchanged (`Zeroize.WipedBy`): the contracts `keyGenContract`, …
here, which are those of `Spec/MlKem/` with a stronger clause on `scratch`,
written as the postconditions without one (`keyGenPost`, …) with it added
(`wipe4`, `wipe5`, `wipe6`: `scratch` is the last argument of each). Every
target's implementation is proven against them. They imply the contracts of
`Spec/MlKem/` (`keyGen_spec`, …), and, `w` being a constant of the code, that
what is left in `scratch` is public (`keyGen_public`, …).

Each target's `callWipe` zeroes all of `scratch` once the function's code
returns (but x86-64's, which zeroes only what that code may write), so the
clause follows from the bytes it zeroes (`keyGen_wiped`, …:
`WipedBy.of_zeros`). Each function as emitted, with its cleanup, has three
theorems in its target's files: that it meets the contract here
(`keyGen_wiped`, …), and what follows, that it meets the one of `Spec/MlKem/`
and that what it leaves in `scratch` is public (`keyGen_public`, …).
-/

@[expose] public section

namespace VG.Proof.MlKem.Scrubbed

open VG.Spec.MlKem (Outcome leakRho)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Zeroize (WipedBy)

/-! ## Buffers with a prefix wiped -/

/-- The first `w` of the `len` bytes at `p` are zero, and the others unchanged. -/
abbrev Wiped (w : Nat) (m m' : Mem) (p : Addr) (len : Nat) : Prop :=
  WipedBy (fun i => decide (i < w)) m m' p len

/-- A buffer wiped in one memory on return is in another that agrees on it. -/
theorem wiped_congr {w : Nat} {m m₁ m₂ : Mem} {p : Addr} {len : Nat}
    (hb : ∀ a, Region.Contains ⟨p, len⟩ a 1 → m₁ a = m₂ a) (h : Wiped w m m₁ p len) :
    Wiped w m m₂ p len :=
  h.congr (fun _ _ => rfl) fun i hi => (hb _ (by
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := Nat.mod_le i (2 ^ 64)
    omega_using [this, hi])).symm

/-! ## Postconditions with `scratch`, the last argument, wiped -/

/-- A postcondition of four pointers. -/
abbrev Post4 : Type := Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- A postcondition of five pointers. -/
abbrev Post5 : Type := Addr → Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- A postcondition of six pointers. -/
abbrev Post6 : Type := Addr → Addr → Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- `P`, and the first `w` of the `len` bytes at the last argument zero, the others unchanged. -/
def wipe4 (w len : Nat) (P : Post4) : Post4 := fun a b c d m m' r =>
  P a b c d m m' r ∧ Wiped w m m' d len

/-- `P`, and the first `w` of the `len` bytes at the last argument zero, the others unchanged. -/
def wipe5 (w len : Nat) (P : Post5) : Post5 := fun a b c d e m m' r =>
  P a b c d e m m' r ∧ Wiped w m m' e len

/-- `P`, and the first `w` of the `len` bytes at the last argument zero, the others unchanged. -/
def wipe6 (w len : Nat) (P : Post6) : Post6 := fun a b c d e f m m' r =>
  P a b c d e f m m' r ∧ Wiped w m m' f len

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- With the `len` bytes at the last argument zero, `wipe4`. -/
theorem wiped4 (len : Nat) (P : Post4) : ∀ vs m m' x, vs.length = 4 →
    Curry.apply [.addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr] (wipe4 len len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
  exact ⟨h, .of_zeros hz⟩

/-- With the `len` bytes at the last argument zero, `wipe5`. -/
theorem wiped5 (len : Nat) (P : Post5) : ∀ vs m m' x, vs.length = 5 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (wipe5 len len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
  exact ⟨h, .of_zeros hz⟩

/-- With the `len` bytes at the last argument zero, `wipe6`. -/
theorem wiped6 (len : Nat) (P : Post6) : ∀ vs m m' x, vs.length = 6 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (wipe6 len len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
  exact ⟨h, .of_zeros hz⟩

/-! ## What is left in `scratch` -/

/-- `F` at the arguments `vs`. -/
theorem apply4 {α : Type} (F : Addr → Addr → Addr → Addr → α) :
    ∀ vs, Curry.apply [.addr, .addr, .addr, .addr] F vs =
    F (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0)
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ => rfl

/-- `F` at the arguments `vs`. -/
theorem apply5 {α : Type} (F : Addr → Addr → Addr → Addr → Addr → α) :
    ∀ vs, Curry.apply [.addr, .addr, .addr, .addr, .addr] F vs =
    F (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0) (vs.getD 4 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- `F` at the arguments `vs`. -/
theorem apply6 {α : Type} (F : Addr → Addr → Addr → Addr → Addr → Addr → α) :
    ∀ vs, Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] F vs =
    F (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0) (vs.getD 4 0) (vs.getD 5 0)
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- The bytes of `scratch` on entry, as `PublicOut.given` gives them. -/
theorem given4 (len : Nat) (vs : List (BitVec 64)) (m : Mem) :
    Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr]
      (fun _ _ _ s m => Spec.Zeroize.left m s len) vs m =
      Spec.Zeroize.left m (vs.getD 3 0) len :=
  congrFun (apply4 _ vs) m

/-- The bytes of `scratch` on return, as `PublicOut.out` gives them. -/
theorem out4 {n : Nat} (len : Nat) (vs : List (BitVec 64)) (m m' : Mem) (r : BitVec n) :
    Curry.apply (α := Mem → Mem → BitVec n → List Nat) [.addr, .addr, .addr, .addr]
      (fun _ _ _ s _ m' _ => Spec.Zeroize.left m' s len) vs m m' r = Spec.Zeroize.left m' (vs.getD 3 0) len :=
  congrFun (congrFun (congrFun (apply4 (α := Mem → Mem → BitVec n → List Nat) _ vs) m) m') r

/-- The bytes of `scratch` on entry, as `PublicOut.given` gives them. -/
theorem given5 (len : Nat) (vs : List (BitVec 64)) (m : Mem) :
    Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr]
      (fun _ _ _ _ s m => Spec.Zeroize.left m s len) vs m =
      Spec.Zeroize.left m (vs.getD 4 0) len :=
  congrFun (apply5 _ vs) m

/-- The bytes of `scratch` on return, as `PublicOut.out` gives them. -/
theorem out5 {n : Nat} (len : Nat) (vs : List (BitVec 64)) (m m' : Mem) (r : BitVec n) :
    Curry.apply (α := Mem → Mem → BitVec n → List Nat) [.addr, .addr, .addr, .addr, .addr]
      (fun _ _ _ _ s _ m' _ => Spec.Zeroize.left m' s len) vs m m' r = Spec.Zeroize.left m' (vs.getD 4 0) len :=
  congrFun (congrFun (congrFun (apply5 (α := Mem → Mem → BitVec n → List Nat) _ vs) m) m') r

/-- The bytes of `scratch` on entry, as `PublicOut.given` gives them. -/
theorem given6 (len : Nat) (vs : List (BitVec 64)) (m : Mem) :
    Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr]
      (fun _ _ _ _ _ s m => Spec.Zeroize.left m s len) vs m =
      Spec.Zeroize.left m (vs.getD 5 0) len :=
  congrFun (apply6 _ vs) m

/-- The bytes of `scratch` on return, as `PublicOut.out` gives them. -/
theorem out6 {n : Nat} (len : Nat) (vs : List (BitVec 64)) (m m' : Mem) (r : BitVec n) :
    Curry.apply (α := Mem → Mem → BitVec n → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr]
      (fun _ _ _ _ _ s _ m' _ => Spec.Zeroize.left m' s len) vs m m' r = Spec.Zeroize.left m' (vs.getD 5 0) len :=
  congrFun (congrFun (congrFun (apply6 (α := Mem → Mem → BitVec n → List Nat) _ vs) m) m') r

/-- What code leaves in the `len` bytes at `scr`, an argument, is public, if it
leaves the first `w` of them zero and the others unchanged. -/
theorem publicOut_of_wiped {T : Target} {c : Prog T.isa} {A : Abi T.isa} {sig : Sig} {o : PublicOut sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post post' : sig.Post A.ptrBits}
    {writeArgs : Bool} {stack : Nat} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (w len : Nat) (scr : List (BitVec 64) → Addr)
    (h : Verified T c (sig.contract A pre post' writeArgs stack leak))
    (hg : ∀ vs m, Curry.apply _ (o.given A.ptrBits) vs m = Spec.Zeroize.left m (scr vs) len)
    (ho : ∀ vs m m' r, Curry.apply _ (o.out A.ptrBits) vs m m' r = Spec.Zeroize.left m' (scr vs) len)
    (hp : ∀ vs m m' r, Curry.apply _ post' vs m m' r → Wiped w m m' (scr vs) len) :
    o.Of A c (sig.contract A pre post writeArgs stack leak) :=
  PublicOut.of_post h fun _ _ _ _ _ _ _ _ _ hgiven h₁ h₂ =>
    (ho _ _ _ _).trans (((hp _ _ _ _ h₁).left (hp _ _ _ _ h₂)
      ((hg _ _).symm.trans (hgiven.trans (hg _ _)))).trans (ho _ _ _ _).symm)

/-! ## The contracts of the functions' bodies

Each function is its body, `vg_mlkem*_<function>_body`, an internal
function, followed by `callWipe`. Every target's implementation of a body
is proven against its contract here (`keyGenBodyContract`, …), which is
that of `Spec/MlKem/` without its clause on `scratch`: the body does not
leave `scratch` scrubbed. -/

/-- The contract of `vg_mlkem768_keygen_body`: `Spec.MlKem.keyGenContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def keyGenBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem768 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1184, bytesAt m' dk 2400))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem768 (bytesAt m seed 32)))

/-- The contract of `vg_mlkem768_encaps_h_body`: `Spec.MlKem.encapsHContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsHBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1184))
    (post := fun ek _h msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- The contract of `vg_mlkem768_encaps_body`: `Spec.MlKem.encapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- The contract of `vg_mlkem768_decaps_body`: `Spec.MlKem.decapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def decapsBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem768 iters (bytesAt m dk 2400)
          (bytesAt m ct 1088)) r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem768 (bytesAt m dk 2400)))

/-- The contract of `vg_mlkem1024_keygen_body`: `Spec.MlKem1024.keyGenContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def keyGen1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem1024 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1568, bytesAt m' dk 3168))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem1024 (bytesAt m seed 32)))

/-- The contract of `vg_mlkem1024_encaps_h_body`: `Spec.MlKem1024.encapsHContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsH1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1568))
    (post := fun ek _h msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- The contract of `vg_mlkem1024_encaps_body`: `Spec.MlKem1024.encapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encaps1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- The contract of `vg_mlkem1024_decaps_body`: `Spec.MlKem1024.decapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def decaps1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m dk 3168)
          (bytesAt m ct 1568)) r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem1024 (bytesAt m dk 3168)))

/-! ## ML-KEM-768 -/

/-- `Spec.MlKem.keyGenContract`'s postcondition without its clause on
`scratch`. -/
def keyGenPost (pb : Nat) : Spec.MlKem.keyGenSig.Post pb := fun seed ek dk _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem768 iters (bytesAt m seed 32)
      (bytesAt m (seed + 32) 32)) r
    (bytesAt m' ek 1184, bytesAt m' dk 2400)

/-- `keyGenPost`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def keyGenContract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 32768) : Contract M :=
  Spec.MlKem.keyGenSig.contract A
    (post := wipe4 w 32768 (keyGenPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem768 (bytesAt m seed 32)))

/-- `Spec.MlKem.keyGenApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def keyGenApi (w : Nat := 32768) : Api :=
  { Spec.MlKem.keyGenApi with contracts := some fun A stack => keyGenContract A stack w }

/-- `keyGenContract` implies `Spec.MlKem.keyGenContract`. -/
theorem keyGen_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (keyGenContract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (keyGenContract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem.keyGenContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem.keyGenContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem keyGen_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (keyGenContract A stack w) rb) :
    Spec.MlKem.keyGenOut.Of A c (Spec.MlKem.keyGenContract A stack) := by
  unfold Spec.MlKem.keyGenOut
  refine publicOut_of_wiped w 32768 (fun vs => vs.getD 3 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given4 32768
  · dsimp only; exact out4 32768
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply4 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem.encapsHContract`'s postcondition without its clause on
`scratch`. -/
def encapsHPost (pb : Nat) : Spec.MlKem.encapsHSig.Post pb := fun ek _h msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1088)

/-- `encapsHPost`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def encapsHContract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 32768) : Contract M :=
  Spec.MlKem.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1184))
    (post := wipe6 w 32768 (encapsHPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- `Spec.MlKem.encapsHApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def encapsHApi (w : Nat := 32768) : Api :=
  { Spec.MlKem.encapsHApi with contracts := some fun A stack => encapsHContract A stack w }

/-- `encapsHContract` implies `Spec.MlKem.encapsHContract`. -/
theorem encapsH_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsHContract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (encapsHContract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem.encapsHContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem.encapsHContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem encapsH_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsHContract A stack w) rb) :
    Spec.MlKem.encapsHOut.Of A c (Spec.MlKem.encapsHContract A stack) := by
  unfold Spec.MlKem.encapsHOut
  refine publicOut_of_wiped w 32768 (fun vs => vs.getD 5 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given6 32768
  · dsimp only; exact out6 32768
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply6 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem.encapsContract`'s postcondition without its clause on
`scratch`. -/
def encapsPost (pb : Nat) : Spec.MlKem.encapsSig.Post pb := fun ek msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1088)

/-- `encapsPost`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def encapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 32768) : Contract M :=
  Spec.MlKem.encapsSig.contract A
    (post := wipe5 w 32768 (encapsPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- `Spec.MlKem.encapsApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def encapsApi (w : Nat := 32768) : Api :=
  { Spec.MlKem.encapsApi with contracts := some fun A stack => encapsContract A stack w }

/-- `encapsContract` implies `Spec.MlKem.encapsContract`. -/
theorem encaps_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsContract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (encapsContract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem.encapsContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem.encapsContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem encaps_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsContract A stack w) rb) :
    Spec.MlKem.encapsOut.Of A c (Spec.MlKem.encapsContract A stack) := by
  unfold Spec.MlKem.encapsOut
  refine publicOut_of_wiped w 32768 (fun vs => vs.getD 4 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given5 32768
  · dsimp only; exact out5 32768
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply5 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem.decapsContract`'s postcondition without its clause on
`scratch`. -/
def decapsPost (pb : Nat) : Spec.MlKem.decapsSig.Post pb := fun dk ct key _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem768 iters (bytesAt m dk 2400)
      (bytesAt m ct 1088)) r (bytesAt m' key 32)

/-- `decapsPost`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def decapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 32768) : Contract M :=
  Spec.MlKem.decapsSig.contract A
    (post := wipe4 w 32768 (decapsPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem768 (bytesAt m dk 2400)))

/-- `Spec.MlKem.decapsApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def decapsApi (w : Nat := 32768) : Api :=
  { Spec.MlKem.decapsApi with contracts := some fun A stack => decapsContract A stack w }

/-- `decapsContract` implies `Spec.MlKem.decapsContract`. -/
theorem decaps_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (decapsContract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (decapsContract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem.decapsContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem.decapsContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem decaps_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (decapsContract A stack w) rb) :
    Spec.MlKem.decapsOut.Of A c (Spec.MlKem.decapsContract A stack) := by
  unfold Spec.MlKem.decapsOut
  refine publicOut_of_wiped w 32768 (fun vs => vs.getD 3 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given4 32768
  · dsimp only; exact out4 32768
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply4 _ vs) m) m') r).mp h).2

/-! ## ML-KEM-1024 -/

/-- `Spec.MlKem1024.keyGenContract`'s postcondition without its clause on
`scratch`. -/
def keyGen1024Post (pb : Nat) : Spec.MlKem1024.keyGenSig.Post pb := fun seed ek dk _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem1024 iters (bytesAt m seed 32)
      (bytesAt m (seed + 32) 32)) r
    (bytesAt m' ek 1568, bytesAt m' dk 3168)

/-- `keyGen1024Post`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def keyGen1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 49152) : Contract M :=
  Spec.MlKem1024.keyGenSig.contract A
    (post := wipe4 w 49152 (keyGen1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem1024 (bytesAt m seed 32)))

/-- `Spec.MlKem1024.keyGenApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def keyGen1024Api (w : Nat := 49152) : Api :=
  { Spec.MlKem1024.keyGenApi with contracts := some fun A stack => keyGen1024Contract A stack w }

/-- `keyGen1024Contract` implies `Spec.MlKem1024.keyGenContract`. -/
theorem keyGen1024_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (keyGen1024Contract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (keyGen1024Contract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem1024.keyGenContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem1024.keyGenContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem keyGen1024_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (keyGen1024Contract A stack w) rb) :
    Spec.MlKem1024.keyGenOut.Of A c (Spec.MlKem1024.keyGenContract A stack) := by
  unfold Spec.MlKem1024.keyGenOut
  refine publicOut_of_wiped w 49152 (fun vs => vs.getD 3 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given4 49152
  · dsimp only; exact out4 49152
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply4 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem1024.encapsHContract`'s postcondition without its clause on
`scratch`. -/
def encapsH1024Post (pb : Nat) : Spec.MlKem1024.encapsHSig.Post pb := fun ek _h msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1568)

/-- `encapsH1024Post`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def encapsH1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 49152) : Contract M :=
  Spec.MlKem1024.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1568))
    (post := wipe6 w 49152 (encapsH1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- `Spec.MlKem1024.encapsHApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def encapsH1024Api (w : Nat := 49152) : Api :=
  { Spec.MlKem1024.encapsHApi with contracts := some fun A stack => encapsH1024Contract A stack w }

/-- `encapsH1024Contract` implies `Spec.MlKem1024.encapsHContract`. -/
theorem encapsH1024_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsH1024Contract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (encapsH1024Contract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem1024.encapsHContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem1024.encapsHContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem encapsH1024_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encapsH1024Contract A stack w) rb) :
    Spec.MlKem1024.encapsHOut.Of A c (Spec.MlKem1024.encapsHContract A stack) := by
  unfold Spec.MlKem1024.encapsHOut
  refine publicOut_of_wiped w 49152 (fun vs => vs.getD 5 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given6 49152
  · dsimp only; exact out6 49152
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply6 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem1024.encapsContract`'s postcondition without its clause on
`scratch`. -/
def encaps1024Post (pb : Nat) : Spec.MlKem1024.encapsSig.Post pb := fun ek msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1568)

/-- `encaps1024Post`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def encaps1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 49152) : Contract M :=
  Spec.MlKem1024.encapsSig.contract A
    (post := wipe5 w 49152 (encaps1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- `Spec.MlKem1024.encapsApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def encaps1024Api (w : Nat := 49152) : Api :=
  { Spec.MlKem1024.encapsApi with contracts := some fun A stack => encaps1024Contract A stack w }

/-- `encaps1024Contract` implies `Spec.MlKem1024.encapsContract`. -/
theorem encaps1024_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encaps1024Contract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (encaps1024Contract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem1024.encapsContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem1024.encapsContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem encaps1024_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (encaps1024Contract A stack w) rb) :
    Spec.MlKem1024.encapsOut.Of A c (Spec.MlKem1024.encapsContract A stack) := by
  unfold Spec.MlKem1024.encapsOut
  refine publicOut_of_wiped w 49152 (fun vs => vs.getD 4 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given5 49152
  · dsimp only; exact out5 49152
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply5 _ vs) m) m') r).mp h).2

/-- `Spec.MlKem1024.decapsContract`'s postcondition without its clause on
`scratch`. -/
def decaps1024Post (pb : Nat) : Spec.MlKem1024.decapsSig.Post pb := fun dk ct key _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m dk 3168)
      (bytesAt m ct 1568)) r (bytesAt m' key 32)

/-- `decaps1024Post`, and the first `w` bytes of `scratch` zero on return, the others unchanged. -/
def decaps1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) (w : Nat := 49152) : Contract M :=
  Spec.MlKem1024.decapsSig.contract A
    (post := wipe4 w 49152 (decaps1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem1024 (bytesAt m dk 3168)))

/-- `Spec.MlKem1024.decapsApi` with that contract: the forms that clean up a function's code
take an `Api`. -/
def decaps1024Api (w : Nat := 49152) : Api :=
  { Spec.MlKem1024.decapsApi with contracts := some fun A stack => decaps1024Contract A stack w }

/-- `decaps1024Contract` implies `Spec.MlKem1024.decapsContract`. -/
theorem decaps1024_spec {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (decaps1024Contract A stack w) rb)
    (hR : (T.noResidue.elim False fun R => R c (decaps1024Contract A stack w) rb) →
      T.noResidue.elim False fun R => R c (Spec.MlKem1024.decapsContract A stack) rb) :
    VerifiedScrubbed T c (Spec.MlKem1024.decapsContract A stack) rb :=
  h.post_mono hR fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.scrubbed⟩

/-- What is left in `scratch` is public. -/
theorem decaps1024_public {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w rb : Nat}
    (h : VerifiedScrubbed T c (decaps1024Contract A stack w) rb) :
    Spec.MlKem1024.decapsOut.Of A c (Spec.MlKem1024.decapsContract A stack) := by
  unfold Spec.MlKem1024.decapsOut
  refine publicOut_of_wiped w 49152 (fun vs => vs.getD 3 0) h.verified ?_ ?_ ?_
  · dsimp only; exact given4 49152
  · dsimp only; exact out4 49152
  · exact fun vs m m' r h => ((congrFun (congrFun (congrFun (apply4 _ vs) m) m') r).mp h).2

/-! ## From the bytes `callWipe` zeroes

Each in the form `Verified.callWipe'` takes (`hwiped`), with all of
`scratch` zeroed. -/

theorem keyGen_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.keyGenSig.words pb).length →
    Curry.apply (Spec.MlKem.keyGenSig.words pb) (keyGenPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.keyGenSig.words pb) (wipe4 32768 32768 (keyGenPost pb)) vs m m' x :=
  wiped4 32768 (keyGenPost pb)

theorem encapsH_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.encapsHSig.words pb).length →
    Curry.apply (Spec.MlKem.encapsHSig.words pb) (encapsHPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.encapsHSig.words pb) (wipe6 32768 32768 (encapsHPost pb)) vs m m' x :=
  wiped6 32768 (encapsHPost pb)

theorem encaps_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.encapsSig.words pb).length →
    Curry.apply (Spec.MlKem.encapsSig.words pb) (encapsPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.encapsSig.words pb) (wipe5 32768 32768 (encapsPost pb)) vs m m' x :=
  wiped5 32768 (encapsPost pb)

theorem decaps_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.decapsSig.words pb).length →
    Curry.apply (Spec.MlKem.decapsSig.words pb) (decapsPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.decapsSig.words pb) (wipe4 32768 32768 (decapsPost pb)) vs m m' x :=
  wiped4 32768 (decapsPost pb)

theorem keyGen1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.keyGenSig.words pb).length →
    Curry.apply (Spec.MlKem1024.keyGenSig.words pb) (keyGen1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.keyGenSig.words pb) (wipe4 49152 49152 (keyGen1024Post pb)) vs m m' x :=
  wiped4 49152 (keyGen1024Post pb)

theorem encapsH1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.encapsHSig.words pb).length →
    Curry.apply (Spec.MlKem1024.encapsHSig.words pb) (encapsH1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.encapsHSig.words pb) (wipe6 49152 49152 (encapsH1024Post pb)) vs m m' x :=
  wiped6 49152 (encapsH1024Post pb)

theorem encaps1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.encapsSig.words pb).length →
    Curry.apply (Spec.MlKem1024.encapsSig.words pb) (encaps1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.encapsSig.words pb) (wipe5 49152 49152 (encaps1024Post pb)) vs m m' x :=
  wiped5 49152 (encaps1024Post pb)

theorem decaps1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.decapsSig.words pb).length →
    Curry.apply (Spec.MlKem1024.decapsSig.words pb) (decaps1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.decapsSig.words pb) (wipe4 49152 49152 (decaps1024Post pb)) vs m m' x :=
  wiped4 49152 (decaps1024Post pb)

end VG.Proof.MlKem.Scrubbed
