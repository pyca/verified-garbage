module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! Zero the signature output on all randomized-signing failure paths. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
open VG.WriteBytes (writeW8_apply)

structure RandomZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.r10, .r11] s t
  r10 : t.gpr .r10 = out + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_zeroOut_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa RandomSign.zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.r10, .r11, .rax] s t := by
  unfold RandomSign.zeroOut
  refine WP.seq (WP.mono (WP.keep [.r10, .r11, .rax] (Q := fun t => t.gpr .r10 = op ∧
      t.gpr .r11 = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [random_ea_sp, hsp, hs.ld (d := Random.oOut) (by decide),
      hs.ld (d := Random.oOutLen) (by decide), hO, hK]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega) (RandomZeroInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j _ hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .r10 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = BitVec.ofNat 64 (k - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = k))) (by
    xrun [State.ea, hI.r10, hI.r11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ k - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

end VG.Proof.Dsa.X86_64
