module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Save the current schoolbook multiplier without touching the operands -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem wideMultiplier_ok {s : State} {base : Addr} {bytes a i mult : Nat}
    (hs : Scr s base bytes)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : a + 4 * i + 4 ≤ bytes) (hm : mult + 4 ≤ bytes) :
    WP isa (.block [.mov .eax (.mem (at_ .ebp a)), .store (sc mult) .eax]) s fun t =>
      w32 t.mem base mult = w32 s.mem base (a + 4 * i) ∧
      Outside base mult 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  refine wp_movS (readSrc_regAt hs hp (by omega)) fun u U _ => ?_
  have Hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (Hu.ea (by omega)) (Hu.write hm) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, U.keeps.trans (T.keeps _)⟩
  · rw [T.mem, w32_write_self, U.gpr, show 4 * i + a = a + 4 * i by omega]
  · rw [T.mem, U.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.Bignum.X86
