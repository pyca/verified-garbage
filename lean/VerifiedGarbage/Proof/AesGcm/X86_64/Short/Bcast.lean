module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame

import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM's short path on x86-64: the constants in every lane

Untrusted: everything here is checked by Lean. `bcast_ok`: lane 0 of a
register in its four lanes; `pow4c_ok`: the mask and the reduction constant
in every lane of `zmm0` and `zmm1`, as `powers` and `powersP` leave them.
Apart from the algebra of `Pow.lean`, which `powersP` does not need.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64

/-- Lane 0 of `r` in its four lanes. -/
theorem bcast_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1), .zop (.vshufi32x4 r r r 0x44)]) s fun t =>
      (∀ l < 4, t.zlane r l = s.xmm r) ∧ ZFrame [r] s t := by
  refine WP.mono (WP.zframe (rs := [r]) (by simp [vecDst, VOp.dst?, ZOp.dst])
    (Q := fun t => ∀ l < 4, t.zlane r l = s.xmm r) ?_) fun t h => h
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [VOp.exec, zlane_zbin, zlane_vshufi32x4 _ _ _ _ _ _ hl, ite_true]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals simp only [VG.Proof.Gcm.X86_64.StitchZ.shuf44_0, VG.Proof.Gcm.X86_64.StitchZ.shuf44_1,
    VG.Proof.Gcm.X86_64.StitchZ.shuf44_2, VG.Proof.Gcm.X86_64.StitchZ.shuf44_3]
  all_goals simp [State.lane, State.zlane, State.setV]

/-- The mask and the reduction constant in every lane of `zmm0` and `zmm1`. -/
theorem pow4c_ok (s : State) :
    WP isa (.block (([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] : List Instr) ++
        ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr))) s fun t =>
      (∀ l < 4, t.zlane .xmm0 l = s.xmm .xmm0) ∧ (∀ l < 4, t.zlane .xmm1 l = s.xmm .xmm1) ∧
      ZFrame [.xmm0, .xmm1] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (bcast_ok .xmm0 s) fun t₁ ⟨b₁, f₁⟩ => WP.mono (bcast_ok .xmm1 t₁) fun t ⟨b, f⟩ => ⟨fun l hl => ?_,
    fun l hl => ?_, (f₁.mono (rs' := [.xmm0, .xmm1]) (by simp)).trans (f.mono (by simp))⟩
  · rw [f.zlane _ (by decide) l hl, b₁ l hl]
  · rw [b l hl]
    have := f₁.zlane .xmm1 (by decide) 0 (by decide)
    simpa [State.zlane, State.lane] using this

end VG.Proof.AesGcm.X86_64.Short
