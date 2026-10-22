module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.WitnessTape
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! Consume exactly one padded draw and retain the next cursor. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem remember_draw {s : State} {base : Addr} {bytes remaining drawBytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : drawBytes ≤ remaining) (bound : remaining < 2 ^ 32)
    (value : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining) :
    WP isa (.block (rememberDraw drawBytes)) s fun t =>
      t.mem = (s.mem.writeW (off base witnessCursor) (s.gpr .esi)).writeW
        (off base witnessRemaining) (BitVec.ofNat 32 (remaining - drawBytes)) ∧
      Keeps [.eax] s t := by
  have cursorFit : witnessCursor + 4 ≤ bytes := Nat.le_trans (by decide : witnessCursor + 4 ≤ 40960) capacity
  have remainingFit : witnessRemaining + 4 ≤ bytes := Nat.le_trans (by decide : witnessRemaining + 4 ≤ 40960) capacity
  unfold rememberDraw
  refine wp_storeS (scr.ea (d := witnessCursor) (by omega)) (scr.write cursorFit) fun a A => ?_
  have Sa := scr.of_keeps (A.keeps []) (by decide)
  have remaining : a.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining := by
    rw [A.mem, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : witnessCursor + 4 ≤ witnessRemaining))
      (by decide) (by decide)) (by decide), value]
  refine wp_movS (readSrc_sc Sa (d := witnessRemaining) (by omega)) fun b B _ =>
    wp_subS rfl fun c C _ => ?_
  have Kc : Keeps [.eax] s c := ((A.keeps _).trans B.keeps).trans C.keeps
  have Sc := scr.of_keeps Kc (by decide)
  refine wp_storeS (Sc.ea (d := witnessRemaining) (by omega)) (Sc.write remainingFit) fun t T => WP.block_nil ?_
  refine ⟨?_, Kc.trans (T.keeps _)⟩
  rw [T.mem, C.gpr, B.gpr, remaining, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) room,
    C.mem, B.mem, A.mem]

end VG.Proof.Dsa.X86.Generation
