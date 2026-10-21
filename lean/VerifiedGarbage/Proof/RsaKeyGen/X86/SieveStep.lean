module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvanceMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveTrial
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # One sieve iteration advances its public cursor and records exact divisibility -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def dividesAt (c i : Nat) : Bool := decide (c % tabEntry i = 0)

theorem StateAt.step {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) (positive : 0 < q) (bound : q < 2 ^ 32) :
    WP isa (step stackSlots) s fun t =>
      StateAt g c (i + 1) (nextCount q (dividesAt c i)) t ∧
      t.mem.readW (off (g.sp.setWidth 64) 16) 32 = BitVec.ofNat 32 (dividesAt c i).toNat ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q (dividesAt c i)) == 0#32) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Sieve.step
  apply WP.assoc
  refine WP.seq (WP.mono (H.trial v index) fun a ⟨result, M, K, Ca⟩ => ?_)
  refine WP.mono (advance_ok Ca positive bound (dividesAt c i) (by rw [M]; exact H.count) result)
    fun t ⟨_, Mt, O, Kt, _, Z⟩ => ?_
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by rw [M] at O; exact O
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := K.widen Kt
  have mem : t.mem = advancedMem g.sp s.mem q (dividesAt c i) := by rw [Mt, M]
  refine ⟨⟨H.context.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_, ?_, ?_⟩, ?_, Z, outside, keep⟩
  · rw [mem, advancedMem_candidate]; exact H.candidate
  · rw [mem, advancedMem_ending]; exact H.ending
  · rw [mem, advancedMem_cursor, H.cursor]
    unfold Geometry.cursor
    rw [BitVec.add_assoc]
    change g.table + (BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 8) = _
    rw [← BitVec.ofNat_add]
    congr 2 <;> omega
  · rw [mem, advancedMem_count]
  · rw [mem, advancedMem_hit]

end VG.Proof.RsaKeyGen.X86.Sieve
