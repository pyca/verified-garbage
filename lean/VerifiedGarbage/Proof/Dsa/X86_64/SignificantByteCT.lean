module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks

import VerifiedGarbage.Proof.Dsa.X86_64.Significant
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.Checks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Significant
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Timing of one public modulus-width scan byte -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ScanBytePublic where
  pointer : Addr
  remaining : Nat
  found : Nat × Byte
  value : Byte

def ScanBytePre (p : ScanBytePublic) (s : State) : Prop :=
  s.gpr .rsi = p.pointer ∧ s.gpr .rcx = BitVec.ofNat 64 p.remaining ∧
  s.gpr .r8 = BitVec.ofNat 64 p.found.1 ∧ s.gpr .r9 = p.found.2.zeroExtend 64 ∧
  s.mem p.pointer = p.value ∧ InRegions (s.rd ++ s.wr) p.pointer 1 ∧ p.found.1 < 2 ^ 64

def ScanChoosePre (p : ScanBytePublic) (s : State) : Prop :=
  s.gpr .rsi = p.pointer ∧ s.gpr .rcx = BitVec.ofNat 64 p.remaining ∧
  s.gpr .r8 = BitVec.ofNat 64 p.found.1 ∧ s.gpr .r9 = p.found.2.zeroExtend 64 ∧
  s.gpr .rax = p.value.zeroExtend 64 ∧ s.zf = some (decide (p.found.1 = 0))

theorem significantChoose_ct : RelCT isa (Two ScanChoosePre) Checks.significantChoose (fun _ _ => True) := by
  unfold Checks.significantChoose
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.2.2.2, ht.2.2.2.2.2]) ?_ ?_
  · exact two_taint [.rax, .rcx]
      (pins_of (fun p r => if r = .rax then p.value.zeroExtend 64 else BitVec.ofNat 64 p.remaining) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.2.2.2.1
        · exact h.1.2.1)) (by taint_decide)
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)

theorem significantByte_ct : RelCT isa (Two ScanBytePre) Checks.significantByte (fun _ _ => True) := by
  unfold Checks.significantByte seqs
  refine RelCT.seq (two_piece (Ψ := ScanChoosePre) [.rsi, .r8]
    (pins_of (fun p r => if r = .rsi then p.pointer else BitVec.ofNat 64 p.found.1) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hsi, hcx, h8, h9, hm, hr, hf⟩
    refine WP.mono (WP.keep [.rax, .r8] (Q := fun t =>
      t.gpr .rax = p.value.zeroExtend 64 ∧ t.zf = some (decide (p.found.1 = 0)) ∧
      t.gpr .r8 = BitVec.ofNat 64 p.found.1) ?_ rfl)
      fun t ⟨⟨ha, hz, ht8⟩, hk⟩ => ⟨(hk.gpr (by decide)).trans hsi,
        (hk.gpr (by decide)).trans hcx, ht8, (hk.gpr (by decide)).trans h9, ha, hz⟩
    xrun [State.ea, at0, hsi, h8, hm, hr, BitVec.and_self, ofNat_beq_zero hf,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  refine RelCT.seq (two_post (Ψ := fun (p : ScanBytePublic) t =>
    t.gpr .rsi = p.pointer ∧ t.gpr .rcx = BitVec.ofNat 64 p.remaining) significantChoose_ct ?_) ?_
  · intro p s ⟨hsi, hcx, h8, h9, ha, hz⟩
    exact WP.mono (significantChoose_ok h8 h9 ha hcx hz) fun t ⟨_, _, _, hk⟩ =>
      ⟨(hk.gpr (by decide)).trans hsi, (hk.gpr (by decide)).trans hcx⟩
  · exact two_taint [.rsi, .rcx]
      (pins_of (fun p r => if r = .rsi then p.pointer else BitVec.ofNat 64 p.remaining) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
