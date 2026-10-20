module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFreshCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFreshCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Load the selected generator candidate from the persistent frame and evaluate it -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.Rsa.AArch64

def GeneratorBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  (∃ W, GeneratorMemory p W s) ∧ p.len = len

theorem generatorInput_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (.block generatorInput) s (GeneratorFreshBefore len p) := by
  obtain ⟨W, hm⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (generatorInput_ok hm.layout R hm.base hm.input (hm.parent.st (d := 272) (by decide)))
    fun t ⟨hd, hp, hf, hk⟩ => ?_
  have ff : Frm p.B [(272, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  exact ⟨⟨hm.parent.congr hk.wr, hd,
      hm.pParent.congrK (InScr.of_frm ff bound) hk, h.2⟩, hp,
    hm.hParent.congrK (InScr.of_frm ff bound) hk,
    hm.eParent.congrK (InScr.of_frm ff bound) hk,
    fun i hi => by rw [hk.wr]; exact hm.gWrite i hi⟩

theorem generatorInput_ct (len : Nat) :
    RelCT isa (Two (GeneratorBefore len)) (.block generatorInput)
      (Two (GeneratorFreshBefore len)) := by
  unfold generatorInput
  apply RelCT.block_append (M := isa) (l₁ := [.ldrSp .x0 40, .ldrSp .x3 168])
    (l₂ := [.str .x .x3 .x0 Field.g.offset])
  apply pin_ct [] [.x0] (fun p : GeneratorPlan => fun _ => p.B)
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_ (by taint_decide) ?_
  · intro p s h
    obtain ⟨W, hm⟩ := h.1
    obtain ⟨V, R⟩ := hm.rep
    have hv : s.mem.readW (p.F + BitVec.ofNat 64 40) 64 = p.B := (R.fr 5 (by decide)).trans hm.base
    have step : WP isa (.block [.ldrSp .x0 40, .ldrSp .x3 168]) s (fun t => t.gpr .x0 = p.B) := by
      brun [exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 168) (by decide),
        hm.layout.sp, hm.layout.ld (d := 40) (n := 8) (by decide),
        hm.layout.ld (d := 168) (n := 8) (by decide), hv]
    exact WP.mono step fun t ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ht
  · intro p s h
    apply WP.seq_iff.mpr
    exact (WP.block_append_iff (M := isa)
      (l₁ := [.ldrSp .x0 40, .ldrSp .x3 168])
      (l₂ := [.str .x .x3 .x0 Field.g.offset])).mp (generatorInput_ready h)

theorem generatorEvaluate_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorEvaluate M.mm len)
      (fun _ _ => True) := by
  unfold generatorEvaluate
  exact RelCT.seq (generatorInput_ct len) (generatorPowerFresh_ct M len hl)

end VG.Proof.Dsa.AArch64.Generation
