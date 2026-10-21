module

public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Framework.Offset

/-! # Return the existing validity flag and restore the calling convention -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Ecdsa.Verify.X86_64 (KeyOk)

/-- The finish is the same flag conversion and register restore used elsewhere. -/
theorem finish_eq (c : Cfg) : Impl.EcKey.Validate.X86_64.finish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++ Spill.restoreCode .rdi Cfg.saved) := rfl

/-- No new arithmetic: reuse the flag-bit and register-restore proofs. -/
theorem finish_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ s : State} {g : Reg → BitVec 64}
    (F : Front c s₀ g s) :
    WP isa (.block (Impl.EcKey.Validate.X86_64.finish c)) s fun s' =>
      (s'.gpr .rax).setWidth 32 = (if KeyOk c s₀ then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) := by
  have hsz : size = 8192 := rfl
  have hF : c.sl FLAG + 8 ≤ size := by
    have := sl_le c hc.n10 (i := FLAG) (by decide)
    have := hc.n0
    omega
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok F.scr hF) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := (F.scr.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have saved₂ : Spill.Saved s₂.mem (s₂.gpr .rdi) g Cfg.saved := by
    rw [hs₂.rdi, k₂.2.1, k₁.2.1]; exact F.saved
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₂ (by decide)
    (fun p hp => ?_) saved₂) fun s₃ ⟨saved₃, kept₃, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₂.rdi]
    exact ⟨_, List.mem_append_right _ hs₂.wr, Offset.contains_base _ (by omega) (by omega)⟩
  · refine ⟨?_, fun r hr => (saved₃ r hr).trans (F.original r hr)⟩
    rw [kept₃ .rax (by decide), e₂, e₁, F.flag]
    simpa only [mask, decide_eq_true_eq] using (mask_bit (decide (KeyOk c s₀)))

end VG.Proof.EcKey.Validate.X86_64
