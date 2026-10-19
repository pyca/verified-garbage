module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFreshCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFreshCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Load the selected generator candidate from the persistent frame and evaluate it -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.Rsa.X86_64

def GeneratorBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  (∃ W, GeneratorMemory p W s) ∧ p.len = len

theorem generatorInput_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (.block generatorInput) s (GeneratorFreshBefore len p) := by
  obtain ⟨W, hm⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (generatorInput_ok hm.layout R hm.base hm.input (hm.parent.st (by decide)))
    fun t ⟨hd, hp, hf, hk⟩ => ?_
  have ff : Frm p.B [(272, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  exact ⟨⟨hm.parent.congr hk.2.2, hd,
      hm.pParent.congrK (InScr.of_frm ff bound) hk, h.2⟩, hp,
    hm.hParent.congrK (InScr.of_frm ff bound) hk,
    hm.eParent.congrK (InScr.of_frm ff bound) hk,
    fun i hi => by rw [hk.2.2]; exact hm.gWrite i hi⟩

theorem generatorInput_ct (len : Nat) :
    RelCT isa (Two (GeneratorBefore len)) (.block generatorInput)
      (Two (GeneratorFreshBefore len)) := by
  unfold generatorInput
  apply RelCT.block_append (M := isa) (l₁ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))])
    (l₂ := [.store (Core.field .g) .rax])
  apply pin_ct [.rsp] [.rdi] (fun p _ => p.B) ?_ (by taint_decide) ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain ⟨Ws, hs⟩ := hs.1
    obtain ⟨Wt, ht⟩ := ht.1
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    obtain ⟨W, hm⟩ := h.1
    obtain ⟨V, R⟩ := hm.rep
    have ld := hm.layout.ld (d := 40) (by decide)
    have ld168 := hm.layout.ld (d := 168) (by decide)
    have hv := R.slot (d := 40) (k := 5) rfl (by decide) hm.base
    have step : WP isa (.block [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))]) s
        (fun t => t.gpr .rdi = p.B) := by
      xrun [VG.Proof.RsaOaep.X86_64.ea_sp, hm.layout.rsp, ld, ld168, hv]
    exact WP.mono step fun t ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ht
  · intro p s h
    apply WP.seq_iff.mpr
    exact (WP.block_append_iff (M := isa)
      (l₁ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))])
      (l₂ := [.store (Core.field .g) .rax])).mp (generatorInput_ready h)

theorem generatorEvaluate_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorEvaluate Sq.mm M.mm len)
      (fun _ _ => True) := by
  unfold generatorEvaluate
  exact RelCT.seq (generatorInput_ct len) (generatorPowerFresh_ct M Sq len hl)

end VG.Proof.Dsa.X86_64.Generation
