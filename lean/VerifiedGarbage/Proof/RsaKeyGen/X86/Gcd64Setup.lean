module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
/-! # Establish the native GCD workspace from a paired remainder and exponent -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Gcd64Input.lean`, which only this module imported.
section

/-! # Store complete register pairs into the native GCD input banks -/

section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem remainderInput_ok {s : State} {base : Addr} {size : Nat}
    (scratch : Scr s base size) (fit : 168 ≤ size) :
    WP isa (.block remainderInput) s fun t =>
      val32 t.mem base 160 2 = Mod64.pair (s.gpr .ecx) (s.gpr .ebx) ∧
      Outside base 160 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold remainderInput
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, val32_write_pair, B.other .eax (by decide), A.gpr, B.gpr, A.other .ebx (by decide)]
  · rw [B.mem, A.mem] at O
    exact O

theorem exponentInput_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (fit : 184 ≤ size) (sourceFit : offset + 8 ≤ size) :
    WP isa (.block (exponentInput offset)) s fun t =>
      val32 t.mem base 176 2 = Mod64.exponentValue s.mem base offset ∧
      Outside base 176 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold exponentInput
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  refine wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, val32_write_pair, B.other .eax (by decide), A.gpr, B.gpr, A.mem]
    rfl
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Gcd64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem setup_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (space : 400 ≤ size) (fit : offset + 8 ≤ size)
    (apart : offset + 8 ≤ 160 ∨ 168 ≤ offset) :
    WP isa (.block (setup offset)) s fun t =>
      Ws t base size 2 15 ∧ num t.mem base 2 0 = Mod64.pair (s.gpr .ecx) (s.gpr .ebx) ∧
      num t.mem base 2 1 = Mod64.exponentValue s.mem base offset ∧
      Outside base 160 24 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold setup
  refine WP.block_append (WP.mono (remainderInput_ok scratch (by omega)) fun a ⟨R, Oa, Ka⟩ => ?_)
  refine WP.mono (exponentInput_ok (scratch.of_keeps Ka (by decide)) (by omega) fit)
    fun t ⟨E, Ot, Kt⟩ => ?_
  have K := Ka.trans Kt
  have exponent : Mod64.exponentValue a.mem base offset = Mod64.exponentValue s.mem base offset := by
    change w32 a.mem base offset + 2 ^ 32 * w32 a.mem base (offset + 4) = _
    rw [Oa.w32 (d := offset) (by omega) (by have := scratch.nowrap; omega),
      Oa.w32 (d := offset + 4) (by omega) (by have := scratch.nowrap; omega)]
    rfl
  refine ⟨⟨scratch.of_keeps K (by decide), space, by decide, by decide⟩, ?_, E.trans exponent,
    (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), K⟩
  change val32 t.mem base 160 2 = _
  rw [Ot.val32 (by decide) (by decide)]
  exact R

end VG.Proof.RsaKeyGen.X86.Gcd64
