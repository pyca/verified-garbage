module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIGeometry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Input buffers and stack arguments survive the saved-register prologue -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def savedBase (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 48

theorem generation_incoming_address (s : State) (j : Nat) :
    off (generationBase s) (352 + 8 * j) = stackArgAddr s j := by
  simp only [generationBase, off, stackArgAddr, BitVec.ofNat_add, BitVec.ofNat_mul]
  bv_omega

theorem allocated_rsp {s u : State} (hg : u.gpr = (allocState 48 s).gpr) :
    (allocState 296 u).gpr .rsp = generationBase s := by
  change u.gpr .rsp - BitVec.ofNat 64 296 = _
  rw [hg]
  change s.gpr .rsp - BitVec.ofNat 64 48 - BitVec.ofNat 64 296 = _
  simp only [BitVec.sub_sub, generationBase]
  rfl

theorem saved_frame_sub (s : State) :
    Region.Sub ⟨savedBase s, 48⟩ (below (s.gpr .rsp) 472) :=
  Offset.sub_below _ (by decide) (by decide)

theorem allocated_tape {s u : State} (h : GenerationABI s)
    (hr : u.rd = s.rd) (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem)
    (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩)
    (stack : (below (s.gpr .rsp) 472).Disjoint ⟨ptr, len.toNat⟩)
    (hin : (⟨ptr, len.toNat⟩ : Region) ∈ s.rd) :
    GenerationTapeMemory (tapeOf h ptr len bound arena stack) (allocState 296 u) where
  cover := by
    intro a n ha
    simp only [tapeOf, bytesAt_length, InRegions, List.mem_singleton] at ha
    obtain ⟨r, rfl, ha⟩ := ha
    exact ⟨_, List.mem_append_left _ (hr.symm ▸ hin), ha⟩
  bytes := by
    change Spec.Rsa.bytesAt u.mem ptr (Spec.Rsa.bytesAt s.mem ptr len.toNat).length = _
    rw [bytesAt_length]
    apply VG.Proof.Dsa.Generation.frame_bytesAt hf
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact (stack.sub_left (saved_frame_sub s)).symm
    · exact Nat.le_of_lt len.isLt

end VG.Proof.Dsa.X86_64.Generation
