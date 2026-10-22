module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! # Track the scratch counter through P-224's nested public loops -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64

def decompressT (len : Nat) : VG.X86_64.Taint.T where
  regs := .ofList [.rdi, .rsi, .rdx, .rsp]
  flags := false
  lens := [2 * len + 1, 8192]
  bases := [(.rdx, 1, 0)]

theorem decompress_agree {C : Spec.Weierstrass.Curve}
    {root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C} {s₁ s₂ : State}
    (h₁ : (decompressContract C root).pre s₁) (h₂ : (decompressContract C root).pre s₂)
    (hp : (decompressContract C root).pub s₁ s₂) :
    VG.X86_64.Taint.Agree (decompressT C.len) s₁ s₂ := by
  obtain ⟨hsp, hout, hpk, hws⟩ := hp
  have hr : VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) s₁ s₂ := by
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
    · exact hsp
  have wf (s : State) (h : (decompressContract C root).pre s) : VG.X86_64.Taint.Wf (decompressT C.len) s := by
    obtain ⟨_, hwr, _, _, hd, _, _, hfit, _⟩ := h
    constructor
    · intro _
      rw [hwr]
      refine ⟨.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil), ?_, ?_⟩
      · refine .cons ?_ (.cons (by simp) .nil)
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hd
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · dsimp; omega
        · change 8192 ≤ 2 ^ 64; decide
    · intro p hp
      obtain rfl := List.mem_singleton.mp hp
      simp only [VG.X86_64.Taint.region, hwr, List.getD_cons_succ, List.getD_cons_zero]
      exact (BitVec.add_zero _).symm

  refine ⟨hr.rf, ?_, wf s₁ h₁, wf s₂ h₂, ?_, ?_, hr.lo, hr.xr⟩
  · intro _
    rw [h₁.2.1, h₂.2.1, hout, hws]
  · intro sl h; cases h
  · intro sl h; cases h

end VG.Proof.EcKey.Compressed.X86_64
