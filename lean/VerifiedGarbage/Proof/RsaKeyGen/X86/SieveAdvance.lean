module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvanceMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSaveHit
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCursor
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCount
import VerifiedGarbage.Proof.Mont.Words32

/-! # The complete sieve transition records a hit and advances one static entry -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

def advancedMem (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) : Mem :=
  ((m.writeW (off (p.setWidth 64) 16) (BitVec.ofNat 32 hit.toNat)).writeW
    (off (p.setWidth 64) 8) (m.readW (off (p.setWidth 64) 8) 32 + 8)).writeW
      (off (p.setWidth 64) 12) (BitVec.ofNat 32 (nextCount q hit))

theorem advance_ok {p : BitVec 32} {s : State} (C : StackContext p s)
    {q : Nat} (positive : 0 < q) (bound : q < 2 ^ 32) (hit : Bool)
    (count : s.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q)
    (result : s.gpr .eax = BitVec.ofNat 32 hit.toNat) :
    WP isa (.block (advance stackSlots)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextCount q hit) ∧ t.mem = advancedMem p s.mem q hit ∧
      Outside (p.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t ∧ StackContext p t ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q hit) == 0#32) := by
  unfold advance
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (saveHit_ok C) fun a ⟨mask, Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (WP.mono (advanceCursor_ok Ca) fun b ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  have cursor : a.mem.readW (off (p.setWidth 64) 8) 32 = s.mem.readW (off (p.setWidth 64) 8) 32 :=
    BitVec.eq_of_toNat_eq (Oa.w32 (d := 8) (by decide) (by decide))
  have countB : b.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q :=
    (BitVec.eq_of_toNat_eq (Ob.w32 (d := 12) (by decide) (by decide))).trans
      ((BitVec.eq_of_toNat_eq (Oa.w32 (d := 12) (by decide) (by decide))).trans count)
  have maskB : b.gpr .ecx = BitVec.ofNat 32 hit.toNat - 1 := by
    rw [Kb.1 .ecx (by decide), mask, result]
  refine WP.mono (advanceCount_ok Cb positive bound hit countB maskB) fun t ⟨V, Mc, Oc, Kc, Ct, Z⟩ => ?_
  refine ⟨V, ?_, ?_, ((Ka.mono (by decide)).widen Kb).widen Kc, Ct, Z⟩
  · unfold advancedMem
    rw [Mc, Mb, cursor, Ma, result]
  · exact ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans
      (Oc.mono (by decide) (by decide))

end VG.Proof.RsaKeyGen.X86.Sieve
