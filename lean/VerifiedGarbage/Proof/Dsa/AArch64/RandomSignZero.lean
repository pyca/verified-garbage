module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run

/-! Zero the signature output on all randomized-signing failure paths. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.WriteBytes (writeW8_apply)

structure RandomZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x12, .x9] s t
  r10 : t.gpr .x12 = out + BitVec.ofNat 64 j
  r11 : t.gpr .x9 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_zeroOut_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa RandomSign.zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x12, .x9, .x0] s t := by
  unfold RandomSign.zeroOut
  refine WP.seq (WP.mono (WP.keep [.x12, .x9, .x0] (Q := fun t => t.gpr .x12 = op ∧
      t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x0 = 0 ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (show Random.oOut % 8 = 0 ∧ Random.oOut < 32768 by decide),
      exec_ldrSp (show Random.oOutLen % 8 = 0 ∧ Random.oOutLen < 32768 by decide), hsp, hs.ld (d := Random.oOut) (by decide),
      hs.ld (d := Random.oOutLen) (by decide), hO, hK]) rfl rfl rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := k) hk' hk1 (RandomZeroInv s₁ op k) ?_
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩ hcx) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j hj t hI hcount
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.wr, k₁.wr]; exact hout j hj
  have hax' : (t.gpr .x0).setWidth 8 = 0 := by rw [hI.keep.gpr .x0 (by decide), hax]; rfl
  have hp : BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x12, .x9] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .x12 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .x9 = BitVec.ofNat 64 (k - (j + 1)))
      (by brun [hI.r10, hI.r11, hst, hax', hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl)
      rfl rfl rfl) fun t' ⟨⟨hm, hsi', hcx'⟩, k'⟩ => ?_
  refine ⟨⟨(hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)
  · rw [hcx', hcount]
    exact hp.symm

end VG.Proof.Dsa.AArch64
