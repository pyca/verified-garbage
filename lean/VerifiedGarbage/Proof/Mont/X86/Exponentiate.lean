module
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.EncodeBase
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete runtime-modulus exponentiation on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

theorem exponentiate_ok {n size m expWords : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 1 < expWords) (hen : expWords ≤ 2 * n)
    (hsteps : 32 * expWords < 2 ^ 32)
    (hone : wordsVal s.mem base (slot n 3) n = 1)
    (hr2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (exponentiate n expWords) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) expWords % m ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Keeps powerClob s t := by
  have cn : contextBytes n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  unfold exponentiate
  refine WP.seq (WP.mono (encodeBase_ok h hone hr2) fun s₂ ⟨c₂, Y₂, B₂, Oenc, Kenc⟩ => ?_)
  have E₂ : val32 s₂.mem base (slot n 8) expWords = val32 s.mem base (slot n 8) expWords :=
    encodeRanges_val32 Oenc (by decide) hen (by decide) (by decide) (by decide) (by decide) cn
  have O₂ : wordsVal s₂.mem base (slot n 3) n = 1 := by
    rw [wordsVal_eq_val32, encodeRanges_val32 Oenc (by decide) (Nat.le_refl _)
      (by decide) (by decide) (by decide) (by decide) cn, ← wordsVal_eq_val32, hone]
  refine WP.seq (wp_movS rfl fun s₃ u₃ _ => WP.block_nil ?_)
  have c₃ : Context n m base size s₃ := ⟨c₂.scr.of_keeps u₃.keeps (by decide), c₂.size_le,
    u₃.mem ▸ c₂.modulus, c₂.gt_one, u₃.mem ▸ c₂.inverse⟩
  refine WP.seq (WP.mono (exponentLoop_ok c₃ he hen (u₃.mem ▸ Y₂) (u₃.mem ▸ B₂) hsteps u₃.gpr)
    fun s₄ I => ?_)
  have O₄ : wordsVal s₄.mem base (slot n 3) n = 1 := by
    rw [exponentRanges_one I.mem cn, u₃.mem, O₂]
  refine WP.mono (context_mul_ok I.context (o := 6) (a := 6) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [O₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := wordsVal s₄.mem base (slot n 6) n)
      (out := wordsVal t.mem base (slot n 6) n) h.coprime
      (by rw [I.finished, Nat.mod_mod]) (by rw [Vt, O₄])
    rw [Nat.mod_eq_of_lt ltt, Nat.mod_mod, u₃.mem, E₂] at v
    exact v
  · have enc : Outs base (exponentRanges n expWords) s.mem s₂.mem := Oenc.mono (by
      intro r hr
      simp only [encodeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [exponentRanges, productRanges])
    have o₃ : Outs base (exponentRanges n expWords) s₂.mem s₃.mem := u₃.mem ▸ Outs.refl _ _ _
    exact ((enc.trans o₃).trans I.mem).trans (exponentRanges_op Kt (.inr rfl))
  · exact (((Kenc.mono (by decide)).widen u₃.keeps).trans I.keeps).trans
      ((OpKeep.keeps Kt).mono (by decide))

end VG.Proof.Mont.X86.Dynamic
