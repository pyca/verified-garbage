module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MillerRabin
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Check the complete padded draw before reading any witness byte. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem tape_check {s : State} {base : Addr} {bytes remaining drawBytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (bound : remaining < 2 ^ 32) (drawBound : drawBytes < 2 ^ 32)
    (value : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining) :
    WP isa (.block (tapeCheck drawBytes)) s fun t =>
      t.cf = some (decide (remaining < drawBytes)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  have fit : witnessRemaining + 4 ≤ bytes := Nat.le_trans (by decide : witnessRemaining + 4 ≤ 40960) capacity
  unfold tapeCheck
  refine wp_movS (readSrc_sc scr (d := witnessRemaining) (by omega)) fun a A _ =>
    wp_cmpi fun t T carry _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [carry, A.gpr, value, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt drawBound]

end VG.Proof.Dsa.X86.Generation
