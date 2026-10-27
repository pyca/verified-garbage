module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc

import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-! # Room on the stack for the nested parameter-generation frames -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem outer_stack_room {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) : 296 ≤ (u.gpr .rsp).toNat := by
  rw [hg]
  change 296 ≤ (s.gpr .rsp - BitVec.ofNat 64 48).toNat
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  omega

end VG.Proof.Dsa.X86_64.Generation
