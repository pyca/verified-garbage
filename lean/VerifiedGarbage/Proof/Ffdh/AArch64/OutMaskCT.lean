module

public import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# FFDH on AArch64: a number stored masked by its range, in constant time

Runs whose data have the same public part (`FD.pub`) and the same output
leak the same through `outMask` (`outMask_ct`), whatever the number: its
comparisons run over all the words, and it is stored masked, without a
branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

namespace OutMask

/-- A stage of some run's data with the public part `a.1`, the output at `a.2`, and some number. -/
def OnO (S : FD → Addr → Nat → State → Prop) (a : FD × Addr) (t : State) : Prop :=
  ∃ D z, D.pub = a.1 ∧ S D a.2 z t

theorem ono_post {S T : FD → Addr → Nat → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (OnO S)) c fun _ _ => True)
    (hw : ∀ D op z t, S D op z t → WP isa c t fun u => T D op z u ∧ KX t u) :
    RelCT isa (Two (OnO S)) c (Two (OnO T)) :=
  two_post hct fun _ _ ⟨D, z, hD, h⟩ => WP.mono (hw D _ z _ h) fun _ h => ⟨D, z, hD, h.1⟩

/-- `outMask`. -/
theorem outMask_ct : RelCT isa (Two (OnO O3)) (seqs outMask) (Two (OnO O6)) := by
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (OnO O4))
    (ono_post (two_map (fun a : FD × Addr => a.1.ws) (fun a s h => by
        obtain ⟨D, z, hD, ⟨mi, hI, _⟩, _⟩ := h; rw [← hD]; exact hI.goodW1)
      (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)))
      fun _ _ _ _ h => o3_o4 h) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (OnO O5)) (RelCT.block_append (l₁ := finBlk1) (l₂ := finBlk2)
    (RelCT.seq
      (two_piece (Ψ := fun (a : FD × Addr) t =>
          (t.gpr .x0 = FD.G a.1 ∧ t.gpr .x8 = off (FD.G a.1) (slot a.1.w aY) ∧ t.gpr .x5 = a.1.B) ∧
            ∃ D z, D.pub = a.1 ∧ WP isa (.block finBlk2) t (O5 D a.2 z)) [.x0]
        (pins_x0B (fun a : FD × Addr => FD.G a.1) fun a s h => by
          obtain ⟨D, z, hD, ⟨mi, hI, _⟩, _⟩ := h; rw [← hD]; exact hI.2.1.x0) (by taint_decide)
        fun a s ⟨D, z, hD, h⟩ => WP.mono (o4_fin1 h) fun u ⟨h₁, h₂⟩ => ⟨by rw [← hD]; exact h₁, D, z, hD, h₂⟩)
      (two_piece [.x0, .x5, .x8] (pins_of (fun (a : FD × Addr) r => if r = .x0 then FD.G a.1 else
          if r = .x5 then a.1.B else off (FD.G a.1) (slot a.1.w aY)) fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1.1
        · exact h.1.2.2
        · exact h.1.2.1) (by taint_decide) fun a s ⟨_, D, z, hD, h⟩ => WP.mono h fun _ h => ⟨D, z, hD, h⟩))) ?_)
  rw [seqs_one]
  exact ono_post (two_taint [.x1, .x8, .x9]
    (pins_of (fun (a : FD × Addr) r => if r = .x1 then a.2 + BitVec.ofNat 64 a.1.k else if r = .x8 then
        off (FD.G a.1) (slot a.1.w aY) else BitVec.ofNat 64 a.1.k) fun a s h r hr => by
      obtain ⟨D, z, hD, h⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [← hD]
      rcases hr with rfl | rfl | rfl
      · exact h.2.2.1
      · exact h.2.1
      · exact h.2.2.2.1) (by taint_decide)) fun _ _ _ _ h => o5_o6 h

end OutMask

end VG.Proof.Ffdh.AArch64
