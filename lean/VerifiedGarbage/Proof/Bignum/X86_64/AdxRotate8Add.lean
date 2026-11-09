module
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-! Adding input blocks and their separately retained overflow. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax = 0 ∧ t.cf = some false ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem capture_ok (s : State) {c : Bool} (hc : s.cf = some c) (hz : s.gpr .rax = 0) :
    WP isa (.block [.adcx .rax (.reg .rax)]) s fun t =>
      t.cf = some false ∧ (t.gpr .rax).toNat = c.toNat ∧ Keeps [.rax] s t := by
  refine WP.mono (adcx_ok s (src := .reg .rax) rfl (fun _ h => nomatch h) hc)
    fun t ⟨ct, hct, _, et, kt⟩ => ?_
  rw [hz] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at et
  have hb := Bool.toNat_le c
  have z : ct = false := Bool.toNat_eq_zero.mp (by omega_using [et, hb])
  subst z
  refine ⟨hct, ?_, kt⟩
  simpa using et

end VG.Proof.Bignum.X86_64.AdxRotate8
