import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
import VerifiedGarbage.Proof.Ocb.Stretch

/-!
# AES-OCB on x86-64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf ror_mask sel_mask shl3 bit_bottom)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt)

theorem sel_mask' (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b then 1 else 0))) = if b then x' else x := sel_mask x x' b

theorem bit_bottom0 {v : Nat} (hv : v < 64) :
    BitVec.ofNat 64 v &&& BitVec.signExtend 64 (1 : BitVec 32) = if v.testBit 0 then 1 else 0 := by
  have := bit_bottom hv 0
  rwa [BitVec.ushiftRight_zero] at this

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .rax ++ s'.gpr .rdx ++ s'.gpr .rcx = shlIf (v.testBit k) a (s.gpr .rax ++ s.gpr .rdx ++ s.gpr .rcx) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hm : 0#64 - ((BitVec.ofNat 64 v >>> k) &&& BitVec.signExtend 64 (1 : BitVec 32)) =
      0#64 - (if v.testBit k then 1 else 0) := by rw [bit_bottom hv]
  have c1 : 1 ≤ 64 - a ∧ 64 - a ≤ 63 := ⟨by omega, by omega⟩
  by_cases hk : k = 0
  · subst hk
    refine ⟨_, by orun [stage, hbx, c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, bit_bottom0 hv, ror_mask _ ha ha', sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl
  · have ck : 1 ≤ k ∧ k ≤ 63 := ⟨by omega, by omega⟩
    refine ⟨_, by orun [stage, hbx, hk, c1, ck, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, hm, ror_mask _ ha ha', sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl

end VG.Proof.AesOcb.X86_64
