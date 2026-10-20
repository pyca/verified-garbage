module
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState

import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem

def setup (out : Nat) : List Instr := ptrTo .x0 .x28 out ++ vconsts ++
  [.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 32 0, .movz .x .x12 0 0]

theorem setup_ok {s : State} {out : Nat} (ho : out < 65536) (O : Nat → BitVec 32) :
    WP isa (.block (setup out)) s
      (LoopInv s (s.gpr .x28 + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") O 0) := by
  unfold setup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono_syms (wp_ptrTo' (d := .x0) (b := .x28) (s := s)
    (Q := fun s' => Only [.x0] s s' ∧ s'.gpr .x0 = s.gpr .x28 + BitVec.ofNat 64 out)
    (by decide) ho (fun _ hk hx => ⟨hk,hx⟩)) ?_
  intro s₁ h₁ sy₁
  rw [WP.block_append_iff]
  refine WP.mono_syms (Ntt.vconsts_ok s₁) ?_
  intro s₂ ⟨k₂,m₂,c₂,_⟩ sy₂
  refine WP.mono (WP.keepV (Q := fun s₃ => Only [.x3,.x11,.x12] s₂ s₃ ∧
    s₃.gpr .x3 = s₂.syms "VG_MLKEM_GAMMA" ∧ s₃.gpr .x11 = BitVec.ofNat 64 32 ∧ s₃.gpr .x12 = 0)
    (by rfl) (wp_x (by rfl) fun s₃ k₃ e₃ => wp_movz fun s₄ k₄ e₄ =>
      wp_movz fun s₅ k₅ e₅ => wp_nil ⟨((k₃.trans k₄).trans k₅).mono,
        by rw [k₅.get .x3,k₄.get .x3,e₃], by rw [k₅.get .x11,e₄]; rfl, by rw [e₅]; rfl⟩))
    fun s₃ ⟨⟨k₃,e₃,e11,e12⟩,v₃⟩ => ?_
  have hm : s₃.mem = s.mem := k₃.mem.trans (m₂.trans h₁.1.mem)
  refine ⟨((h₁.1.keep.trans k₂).trans k₃.keep).mono,
    by rw [hm]; exact Frame.refl _ _, ⟨by rw [v₃]; exact c₂.q,by rw [v₃]; exact c₂.m⟩,
    ?_, ?_, e12, ?_, ?_⟩
  · rw [k₃.get .x0,k₂.get .x0,h₁.2]; exact (BitVec.add_zero _).symm
  · rw [e₃,sy₂,sy₁]; exact (BitVec.add_zero _).symm
  · rw [e11]; rfl
  · rw [hm]; exact CoeffsUpTo.zero _

end VG.Proof.MlKem.AArch64.Dot
