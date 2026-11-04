module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifySpec
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifySpec
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS verification on AArch64: constant time, the public data

The pointers, the lengths, the bytes of `n` and `e` and the precomputed
values are public (`PubV`, from `verifyPrecomputedTableContract.pub`); the
digest and the signature are secret. Two runs with the same public data as an
anchor `a` (`E`) are related at each point of the code by what correctness
says there; a failed check of the modulus' first byte returns 0
(`vfail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.AArch64 (pins_nil)
open VG.Proof.RsaPss.AArch64.Sgn (fb bytesAt_cons)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, the bytes of `n` and `e`, and the precomputed values. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  a1 : (stackArg s 1).setWidth 32 = (stackArg a 1).setWidth 32
  args : ∀ i < 8, i ≠ 1 → stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x0) (a.gpr .x1).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem PubV.refl (s : State) : PubV s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

/-- An entry state with the anchor's public data. -/
def E (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := PreV tsH tsG K s ∧ PubV a s

/-- `J` at a point of the code, from an entry state with the anchor `a`'s
public data. -/
def At (tsH tsG : List FnTable) (K : Nat) (J : State → State → Prop) (a t : State) : Prop :=
  ∃ s, E tsH tsG K a s ∧ J s t

/-- The first byte of `n`. -/
abbrev nxV (s : State) : Nat := (s.mem (s.gpr .x0)).toNat

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem scr : scr s = scr a := h.2.args 2 (by decide) (by decide)

theorem k : (s.gpr .x1).toNat = (a.gpr .x1).toNat := by rw [h.gpr (r := .x1) (by decide)]

theorem n0 : s.mem (s.gpr .x0) = a.mem (a.gpr .x0) := by
  have hk := h.1.k1
  have e1 := h.gpr (r := .x1) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x0) (k := (s.gpr .x1).toNat) (by omega),
    bytesAt_cons a.mem (a.gpr .x0) (k := (a.gpr .x1).toNat) (by rw [← e1]; omega)] at this
  exact (List.cons.inj this).1

theorem nx : nxV s = nxV a := congrArg BitVec.toNat h.n0

theorem any : anyV s = anyV a := by rw [anyV, anyV, h.2.a1]

theorem sLen : sLenV s = sLenV a := by rw [sLenV, sLenV, h.any, h.2.args 0 (by decide) (by decide)]

end E

/-! ## A failed check -/

/-- 0 returned. -/
theorem vfail_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u) :
    RelCT isa (Two Φ) verifyFail (Two fun a t => t.sp = fb a) :=
  two_post (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by
      obtain ⟨_, e₁, m₁⟩ := hΦ a s₁ h₁
      obtain ⟨_, e₂, m₂⟩ := hΦ a s₂ h₂
      rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb]) (by taint_decide))
    fun a u h => by
      obtain ⟨s, e, m⟩ := hΦ a u h
      exact WP.mono (fail_ok m) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]

end VG.Proof.RsaPss.AArch64.Vfy
