module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvance
import VerifiedGarbage.Proof.Framework.Offset

/-! # Stack metadata after one sieve iteration -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Proof.Mont

theorem stack_write_ne {m : Mem} {p : BitVec 32} {a b : Nat} {value : BitVec 32}
    (apart : b + 4 ≤ a ∨ a + 4 ≤ b) (aFit : a + 4 ≤ 20) (bFit : b + 4 ≤ 20) :
    (m.writeW (off (p.setWidth 64) a) value).readW (off (p.setWidth 64) b) 32 =
      m.readW (off (p.setWidth 64) b) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ apart (by omega) (by omega)) (by decide)

theorem advancedMem_candidate (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 0) 32 = m.readW (off (p.setWidth 64) 0) 32 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]

theorem advancedMem_ending (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 4) 32 = m.readW (off (p.setWidth 64) 4) 32 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]

theorem advancedMem_cursor (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 8) 32 = m.readW (off (p.setWidth 64) 8) 32 + 8 := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

theorem advancedMem_count (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 (nextCount q hit) :=
  Mem.readW_writeW_self32 _ _ _

theorem advancedMem_hit (p : BitVec 32) (m : Mem) (q : Nat) (hit : Bool) :
    (advancedMem p m q hit).readW (off (p.setWidth 64) 16) 32 = BitVec.ofNat 32 hit.toNat := by
  unfold advancedMem
  rw [stack_write_ne (by decide) (by decide) (by decide),
    stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Sieve
