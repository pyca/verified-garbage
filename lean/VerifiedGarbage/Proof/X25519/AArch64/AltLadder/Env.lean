module

import VerifiedGarbage.Proof.X25519.AArch64.Alt.Add
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sub
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sqr
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Cmadd
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mux
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul

/-! # The `_alt` field operations on slots, in `GF(p)`

Each operation of `Alt` on the slots of `Field` (`offset`), as an update of
the slots' values in `GF(p)` (`env`), and which slots hold values below
`2·p` (`Bel`), which the additions and subtractions need of their inputs. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.AArch64 VG.Proof.X25519 VG.Proof.Ed25519.AArch64 VG.Proof.X25519.AArch64.Alt
open VG.Impl.Ed25519.AArch64 (Slot offset)
open VG.Spec.X25519 (P)

/-- `2·p`. -/
abbrev P2 : Nat := 2 ^ 256 - 38

/-- The slots `S` hold values below `2·p`. -/
def Bel (m : Mem) (base : Addr) (S : Slot → Bool) : Prop :=
  ∀ i, S i = true → fe m base (offset i) < P2

variable {large : Bool}

theorem altRange (i : Slot) (h : i.val ≤ 13) : AltRange (offset i) large :=
  ⟨by simp only [offset]; omega, by simp only [offset]; omega,
    by have := workSize_ge large; simp only [offset]; omega⟩

theorem apart (i j : Slot) (h : i ≠ j) : offset i + 32 ≤ offset j ∨ offset j + 32 ≤ offset i := by
  have : i.val ≠ j.val := fun e => h (Fin.ext e)
  simp only [offset]; omega

theorem sameOrApart (i j : Slot) : SameOrApart (offset i) (offset j) := by
  by_cases h : i = j
  · exact .inl (by rw [h])
  · exact .inr (apart _ _ h)

/-- An operation writing slot `o` changes no other slot. -/
theorem env_upd {base : Addr} {o : Slot} {s t : State} (h : AltOp base (offset o) s t) :
    env t.mem base = Function.update (env s.mem base) o (env t.mem base o) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp only [Function.update_self]
  · rw [Function.update_of_ne hi]
    simp only [env, F]
    exact congrArg toFe (h.mem.fe (apart i o hi) (by simp only [offset]; omega))

theorem bel_upd {base : Addr} {o : Slot} {s t : State} {S : Slot → Bool} (h : AltOp base (offset o) s t)
    (hb : Bel s.mem base S) (b : Bool) (ho : b = true → fe t.mem base (offset o) < P2) :
    Bel t.mem base (Function.update S o b) := by
  intro i hi
  by_cases e : i = o
  · subst e; rw [Function.update_self] at hi; exact ho hi
  · rw [Function.update_of_ne e] at hi
    rw [h.mem.fe (apart i o e) (by simp only [offset]; omega)]
    exact hb i hi

theorem mod_of_add_mul {c a q : Nat} (h : c + P * q = a) : c % P = a % P := by
  rw [← h, Nat.add_mul_mod_self_left]

theorem mulE {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0) :
    WP isa (.block (Impl.X25519.AArch64.Alt.mul4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧ fe t.mem base (offset o) < P2 ∧
      env t.mem base = Function.update (env s.mem base) o (env s.mem base a * env s.mem base b) :=
  WP.mono (mul4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz) fun t ⟨h, hl, q, e⟩ =>
    ⟨h, hl, (env_upd h).trans (congrArg _ (toFe_mul (mod_of_add_mul (q := q) (by
      simp only [P]; exact e))))⟩

theorem sqrE {base : Addr} {s : State} (hs : Scr s base large) (o a : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hz : s.gpr .x17 = 0) :
    WP isa (.block (Impl.X25519.AArch64.Alt.sqr4 (offset o) (offset a))) s fun t =>
      AltOp base (offset o) s t ∧ fe t.mem base (offset o) < P2 ∧
      env t.mem base = Function.update (env s.mem base) o (env s.mem base a * env s.mem base a) :=
  WP.mono (sqr4_ok hs (altRange o ho) (altRange a ha) hz) fun t ⟨h, hl, q, e⟩ =>
    ⟨h, hl, (env_upd h).trans (congrArg _ (toFe_mul (mod_of_add_mul (q := q) (by
      simp only [P]; exact e))))⟩

theorem addE {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0)
    (hla : fe s.mem base (offset a) < P2) (hlb : fe s.mem base (offset b) < P2) :
    WP isa (.block (Impl.X25519.AArch64.Alt.addTwice4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧
      env t.mem base = Function.update (env s.mem base) o (env s.mem base a + env s.mem base b) :=
  WP.mono (addTwice4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz (by simp only [P2] at hla hlb; omega))
    fun t ⟨h, k, _, e⟩ => ⟨h, (env_upd h).trans (congrArg _ (toFe_add (mod_of_add_mul (q := 2 * k)
      (by simp only [P]; omega))))⟩

/-- `addE`, with only `b` below `2·p`: the sum is below `2²⁵⁷ − 38` still. -/
theorem addE1 {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0)
    (hlb : fe s.mem base (offset b) < P2) :
    WP isa (.block (Impl.X25519.AArch64.Alt.addTwice4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧
      env t.mem base = Function.update (env s.mem base) o (env s.mem base a + env s.mem base b) :=
  have hla : fe s.mem base (offset a) < 2 ^ 256 := VG.Proof.Ed25519.Word64.val4_lt _ _ _ _
  WP.mono (addTwice4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz (by simp only [P2] at hlb; omega))
    fun t ⟨h, k, _, e⟩ => ⟨h, (env_upd h).trans (congrArg _ (toFe_add (mod_of_add_mul (q := 2 * k)
      (by simp only [P]; omega))))⟩

theorem subE {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0)
    (hlb : fe s.mem base (offset b) < P2) :
    WP isa (.block (Impl.X25519.AArch64.Alt.subTwice4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧
      env t.mem base = Function.update (env s.mem base) o (env s.mem base a - env s.mem base b) :=
  WP.mono (subTwice4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz hlb)
    fun t ⟨h, k, _, e⟩ => ⟨h, (env_upd h).trans (congrArg _ (toFe_sub (by
      rw [e, Nat.add_mod, show (2 ^ 256 - 38) * k = P * (2 * k) by simp only [P]; omega,
        Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod])))⟩

theorem fe_lt (m : Mem) (base : Addr) (d : Nat) : fe m base d < 2 ^ 256 :=
  VG.Proof.Ed25519.Word64.val4_lt _ _ _ _

theorem cmaddE {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0) (h1 : (s.gpr .x1).toNat = 121666) :
    WP isa (.block (Impl.X25519.AArch64.Alt.cmadd4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧ fe t.mem base (offset o) < P2 ∧
      env t.mem base = Function.update (env s.mem base) o
        (toFe 121666 * env s.mem base a + env s.mem base b) := by
  have la := fe_lt s.mem base (offset a)
  have lb := fe_lt s.mem base (offset b)
  refine WP.mono (cmadd4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz (by rw [h1]; omega))
    fun t ⟨h, hl, q, e⟩ => ⟨h, hl, (env_upd h).trans (congrArg _ ?_)⟩
  rw [h1] at e
  simp only [env, F]
  rw [← toFe_mul (a := 121666) (b := fe s.mem base (offset a)) rfl]
  exact toFe_add (mod_of_add_mul (q := q) (by simp only [P]; exact e))

theorem cmadd4E {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) (hz : s.gpr .x17 = 0) (h1 : (s.gpr .x1).toNat = 4) :
    WP isa (.block (Impl.X25519.AArch64.Alt.cmadd4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧ fe t.mem base (offset o) < P2 ∧
      env t.mem base = Function.update (env s.mem base) o
        (toFe 4 * env s.mem base a + env s.mem base b) := by
  have la := fe_lt s.mem base (offset a)
  have lb := fe_lt s.mem base (offset b)
  refine WP.mono (cmadd4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) hz (by rw [h1]; omega))
    fun t ⟨h, hl, q, e⟩ => ⟨h, hl, (env_upd h).trans (congrArg _ ?_)⟩
  rw [h1] at e
  simp only [env, F]
  rw [← toFe_mul (a := 4) (b := fe s.mem base (offset a)) rfl]
  exact toFe_add (mod_of_add_mul (q := q) (by simp only [P]; exact e))

theorem muxE {base : Addr} {s : State} (hs : Scr s base large) (o a b : Slot) (ho : o.val ≤ 13)
    (ha : a.val ≤ 13) (hb : b.val ≤ 13) :
    WP isa (.block (Impl.X25519.AArch64.Alt.mux4 (offset o) (offset a) (offset b))) s fun t =>
      AltOp base (offset o) s t ∧ t.zf = s.zf ∧
      fe t.mem base (offset o) = (if s.zf then fe s.mem base (offset b) else fe s.mem base (offset a)) ∧
      env t.mem base = Function.update (env s.mem base) o
        (if s.zf then env s.mem base b else env s.mem base a) :=
  WP.mono (mux4_ok hs (altRange o ho) (altRange a ha) (altRange b hb) (sameOrApart o a)
    (sameOrApart o b)) fun t ⟨h, z, e⟩ => ⟨h, z, e, (env_upd h).trans (congrArg _ (by
      simp only [env, F]; rw [e]; cases s.zf <;> rfl))⟩

end VG.Proof.X25519.AArch64.AltLadder
