module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvChunk
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvBatch
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Tactic.NormNum

/-!
# RSA's inverse by divsteps on x86-64: a batch's divsteps

`bWords`, 59 divsteps in four packed chunks on the window (`Chunk.pchunkC_ok`),
from `~d` in `rbx` and the low words of `f` and `g` at the window's words 0
and 8, leaves `d` and the matrix of `msteps 59` in `rbx`, `r9`–`r12`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Rsa.X86_64.Chunk
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem bWords_ok {s : State} {W : Addr} {size : Nat} (hs : CScr s W size) (h24 : 24 ≤ size)
    {T0 : Divstep.MSt} (f0 : T0.f % 2 = 1) (hd : |T0.d| ≤ 2 ^ 30) (c₁ : ChunkAt W 0 64 true T0 s) :
    WP isa (.block VG.Impl.Rsa.X86_64.Keys.Inv.bWords) s fun t =>
      t.gpr .rbx = BitVec.ofInt 64 (Divstep.msteps 59 T0).d ∧
      t.gpr .r9 = BitVec.ofInt 64 (Divstep.msteps 59 T0).u ∧
      t.gpr .r10 = BitVec.ofInt 64 (Divstep.msteps 59 T0).v ∧
      t.gpr .r11 = BitVec.ofInt 64 (Divstep.msteps 59 T0).q ∧
      t.gpr .r12 = BitVec.ofInt 64 (Divstep.msteps 59 T0).r ∧
      Outside W 0 24 s.mem t.mem ∧
      KeepRegs [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13] s t := by
  have odd : ∀ k, (Divstep.msteps k T0).f % 2 = 1 := Divstep.msteps_f_odd f0
  have dd : ∀ k, |(Divstep.msteps k T0).d| ≤ 2 ^ 30 + 2 * k := fun k => by
    have := Divstep.msteps_d T0 k
    omega_arith
  have hT : 0 + 24 ≤ size := by omega
  rw [VG.Impl.Rsa.X86_64.Keys.Inv.bWords]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pchunkC_ok hs (n := 15) (K := 64) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT f0 (by have := dd 0; norm_num at this ⊢; omega_arith) c₁)
    fun s₂ ⟨d₂, u₂, v₂, q₂, r₂, w₂, k₂, o₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  obtain ⟨f₂, g₂⟩ := w₂ rfl
  rw [WP.block_append_iff]
  refine WP.mono (pchunkC_ok hs₂ (n := 15) (K := 49) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 15) (by have := dd 15; norm_num at this ⊢; omega_arith)
    ⟨d₂, f₂, g₂, fun h => absurd h (by decide), fun _ => ⟨u₂, v₂, q₂, r₂⟩⟩)
    fun s₃ ⟨d₃, u₃, v₃, q₃, r₃, w₃, k₃, o₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain ⟨f₃, g₃⟩ := w₃ rfl
  rw [← Divstep.msteps_add] at d₃ u₃ v₃ q₃ r₃ f₃ g₃
  rw [WP.block_append_iff]
  refine WP.mono (pchunkC_ok hs₃ (n := 15) (K := 34) (first := false) (last := false) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 30) (by have := dd 30; norm_num at this ⊢; omega_arith)
    ⟨d₃, f₃, g₃, fun h => absurd h (by decide), fun _ => ⟨u₃, v₃, q₃, r₃⟩⟩)
    fun s₄ ⟨d₄, u₄, v₄, q₄, r₄, w₄, k₄, o₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain ⟨f₄, g₄⟩ := w₄ rfl
  rw [← Divstep.msteps_add] at d₄ u₄ v₄ q₄ r₄ f₄ g₄
  rw [WP.block_append_iff]
  refine WP.mono (pchunkC_ok hs₄ (n := 14) (K := 19) (first := false) (last := true) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ hT (odd 45) (by have := dd 45; norm_num at this ⊢; omega_arith)
    ⟨d₄, f₄, g₄, fun h => absurd h (by decide), fun _ => ⟨u₄, v₄, q₄, r₄⟩⟩)
    fun s₅ ⟨d₅, u₅, v₅, q₅, r₅, _, k₅, o₅⟩ => ?_
  rw [← Divstep.msteps_add] at d₅ u₅ v₅ q₅ r₅
  refine WP.mono (notRbx_ok s₅) fun t ⟨b, k⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b, d₅, BitVec.not_not]
  · rw [k.1 _ (by decide), u₅]
  · rw [k.1 _ (by decide), v₅]
  · rw [k.1 _ (by decide), q₅]
  · rw [k.1 _ (by decide), r₅]
  · rw [k.2.1]
    exact ((o₂.trans o₃).trans o₄).trans o₅
  · exact (((k₂.trans k₃).trans k₄).trans k₅).trans ((Keeps.regs k).mono (by decide))

end VG.Proof.Rsa.X86_64.InvB
