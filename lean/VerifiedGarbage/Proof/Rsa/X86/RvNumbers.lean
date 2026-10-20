module

public import VerifiedGarbage.Proof.Rsa.X86.RvLoads
import VerifiedGarbage.Proof.Rsa.X86.RvProduct
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvSkip
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.TCB.X86.Target

/-! # Exact exponent product and the positive-even precondition for recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

def product (g : CallGeometry) (m : Mem) : Nat := inputValue g m 2 * inputValue g m 1
def GoOn (p : Nat) : Prop := ¬(p < 2 ∨ (p - 1) % 2 = 1)
instance (p : Nat) : Decidable (GoOn p) := inferInstanceAs (Decidable (¬(p < 2 ∨ (p - 1) % 2 = 1)))

theorem numbers_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.numbers s fun t =>
      KS g.toGeo s (fun _ => inputValue g s.mem 0) [aN]
        (fun _ => 2 * (product g s.mem / 2)) [wM] (fun _ => 0) [] t ∧
      t.zf = some (decide (GoOn (product g s.mem))) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.numbers
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok h len) fun s1 h1 => ?_)
  have arg : CallArgument s1 g.B g.Z 7 (BitVec.ofNat 32 ((g.args 7).toNat)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      h1.argument (h.arguments 7 (by decide)) (h.stageApart (by decide))
  refine WP.seq (WP.mono (prod_ok h1 arg (h.inputPositive 1) (h.inputBound 1) (h.inputBound 2)
    (inputValue_lt g s.mem 1) (inputValue_lt g s.mem 2)) fun s2 h2 => ?_)
  unfold VG.Impl.Rsa.X86.RecoverRt.skipBits
  refine WP.seq (WP.block_append (WP.mono (h2.bitOf_W (j := wM) (sl := sBit) (by simp) (by decide))
    fun s3 ⟨h3, _⟩ => ?_))
  refine WP.mono (h3.clrLow_W (j := wM) (by simp) (by decide)) fun s4 ⟨h4, _⟩ => ?_
  simp only [AWp, upd_self] at h4
  refine WP.seq (WP.mono (h4.subWrap_W (o := wT) (a := wZ) (b := wM)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by decide)) fun s5 ⟨h5, borrow⟩ => ?_)
  have flag : (s5.gpr .ebx).toNat = b2n (decide (0 < 2 * (product g s.mem / 2))) := by
    simp only [upd_self, upd_ne _ _ (by decide : wZ ≠ wM), upd_ne _ _ (by decide : wZ ≠ wMod),
      AW1, upd_ne _ _ (by decide : wZ ≠ wD), upd_ne _ _ (by decide : wZ ≠ wE)] at borrow
    exact borrow
  refine WP.mono (h5.skipTest_ok (by simp) (by rw [upd_self]; omega)
    (by rw [flag]; exact VG.Proof.Rsa.b2n_le _)) fun t ⟨hout, zt⟩ => ?_
  refine ⟨hout.mono (fun j hj => ⟨hj, rfl⟩) ?_ (by simp), ?_⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨by simp, by rw [upd_ne _ _ (by decide : wM ≠ wT), upd_self]; rfl⟩
  · simp only [upd_self] at zt
    rw [flag] at zt
    have valid : (product g s.mem % 2 = 1 ∧ b2n (decide (0 < 2 * (product g s.mem / 2))) = 1) ↔
        GoOn (product g s.mem) := by
      simp only [b2n, GoOn, decide_eq_true_eq]
      split <;> omega
    change t.zf = some (decide (product g s.mem % 2 = 1 ∧
      b2n (decide (0 < 2 * (product g s.mem / 2))) = 1)) at zt
    simpa only [valid] using zt

end VG.Proof.Rsa.X86.Recover
