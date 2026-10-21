module

import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Crypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.AesGcm.AArch64.Tail
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Tail
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt

/-!
# AES-GCM on AArch64: `Tail.cryptAlT` is constant time

Untrusted: everything here is checked by Lean. As `cryptAl_rel`: the code
between the calls by the taint analysis, from the registers the correctness
proofs pin, `x26` (the length of the text) among them for `crTailT`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.Tail
open VG.Spec.Gcm (Block)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `cryptAlT`: `cryptAl_rel`, with the same length of the text in `x26`. -/
theorem cryptAlT_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ R P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ R P D n σ₂) (hP : P % 16 = 0)
    (h26 : k₁ .x26 = k₂ .x26) :
    RelCT isa (Eq2 σ₁ σ₂) (cryptAlT v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k R P D n σ) {m' : Mem},
      Frame (crFrame St W D n) σ.mem m' → ciphOf m' Ctx R = ciphOf σ.mem Ctx R :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data) h.rounds
  have m₁ := h₁.mid (icb := 0) hP
  have m₂ := h₂.mid (icb := 0) hP
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x22, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x22, h₂.x22,
        h₁.x23, h₂.x23, h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (crArgs_ok L m₁) (crArgs_ok L m₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x22, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x22, b₂.1.x22, b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2T_ok L b₁.1 b₁.2) (crSeg2T_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  have e₁ := d₁.kept .x26 (by decide)
  have e₂ := d₂.kept .x26 (by decide)
  exact rel_taint [.x20, .x23, .x24, .x26] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24, e₁, e₂, h26]) ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcm.AArch64
