module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

def loadAccumulator : List Instr :=
  VG.Impl.Bignum.AArch64.BlockedRedc.aa.zipIdx.map fun (r,i) => ld r .x16 (8*i)

theorem loadAccumulator_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block loadAccumulator) s fun t =>
      ((∀ i < 8, accumulator t i = word s.mem B (eT + 8 * i)) ∧
       t.mem = s.mem ∧ t.c = s.c) ∧
      Keep VG.Impl.Bignum.AArch64.BlockedRedc.aa s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep VG.Impl.Bignum.AArch64.BlockedRedc.aa ?_ (by decide) (by decide) (by decide)
  have hcode : loadAccumulator =
    [ld .x19 .x16 0, ld .x20 .x16 8, ld .x21 .x16 16, ld .x22 .x16 24,
     ld .x23 .x16 32, ld .x24 .x16 40, ld .x25 .x16 48, ld .x26 .x16 56] := rfl
  brun [hcode, h16, hs.ld (show eT + 8 ≤ Z by omega), hld 0 (by decide),
    hld 1 (by decide), hld 2 (by decide), hld 3 (by decide), hld 4 (by decide),
    hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem clearCarry_ok {s : State} (h7 : s.gpr .x7 = 0) :
    WP isa (.block [.adds .x .x1 .x7 .x7]) s fun t =>
      (t.c = false ∧ t.mem = s.mem) ∧ Keep [.x1] s t := by
  refine WP.keep [.x1] ?_ rfl rfl rfl
  brun [h7]

end VG.Proof.Bignum.AArch64.ProductEight
