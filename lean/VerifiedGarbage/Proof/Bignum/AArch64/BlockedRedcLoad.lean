module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Load a full accumulator block without changing memory or flags. -/
theorem asLoad_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.asLoad) s fun t =>
      ((∀ i < 8, accumulator t i = word s.mem B (eT + 8 * i)) ∧
       t.mem = s.mem ∧ t.c = s.c) ∧
      Keep VG.Impl.Bignum.AArch64.BlockedRedc.aa s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep VG.Impl.Bignum.AArch64.BlockedRedc.aa ?_ (by decide) (by decide) (by decide)
  have hcode : VG.Impl.Bignum.AArch64.BlockedRedc.asLoad =
    [ld .x19 .x8 0, ld .x20 .x8 8, ld .x21 .x8 16, ld .x22 .x8 24, ld .x23 .x8 32, ld .x24 .x8 40, ld .x25 .x8 48, ld .x26 .x8 56] := rfl
  brun [hcode,
    h8, hs.ld (show eT + 8 ≤ Z by omega), hld 0 (by decide), hld 1 (by decide), hld 2 (by decide), hld 3 (by decide),
    hld 4 (by decide), hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Load the seven resident modulus words; word zero remains in memory. -/
theorem nsLoad_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN) (hN : eN + 64 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad) s fun t =>
      ((∀ i < 8, operand t (word s.mem B eN) i = word s.mem B (eN + 8 * i)) ∧
       t.mem = s.mem ∧ t.c = s.c) ∧
      Keep VG.Impl.Bignum.AArch64.BlockedRedc.nn s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eN + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep VG.Impl.Bignum.AArch64.BlockedRedc.nn ?_ (by decide) (by decide) (by decide)
  have hcode : VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad =
    [ld .x2 .x17 8, ld .x3 .x17 16, ld .x4 .x17 24, ld .x5 .x17 32, ld .x6 .x17 40, ld .x9 .x17 48, ld .x11 .x17 56] := rfl
  brun [hcode,
    h17, hld 1 (by decide), hld 2 (by decide), hld 3 (by decide),
    hld 4 (by decide), hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

end VG.Proof.Bignum.AArch64.BlockedRedc
