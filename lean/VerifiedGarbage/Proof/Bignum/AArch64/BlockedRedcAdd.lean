import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Add the next eight input words to the resident accumulator. -/
theorem addMemory_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false)) s fun t =>
      (t.c = chainCarry (accumulator s) (fun i => word s.mem B (eT + 8 * i)) false 8 ∧
       (∀ i < 8, t.gpr VG.Impl.Bignum.AArch64.BlockedRedc.aa[i]! =
         addCarry (accumulator s i) (word s.mem B (eT + 8 * i))
           (chainCarry (accumulator s) (fun j => word s.mem B (eT + 8 * j)) false i)) ∧
       t.mem = s.mem) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ [.x13]) s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega)
  refine WP.keep (c := .block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false)) (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ [.x13]) ?_
    (by decide) (by decide) (by decide)
  have hcode : VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false =
    [ld .x13 .x16 0, .adds .x .x19 .x19 .x13, ld .x13 .x16 8, .adcs .x .x20 .x20 .x13, ld .x13 .x16 16, .adcs .x .x21 .x21 .x13, ld .x13 .x16 24, .adcs .x .x22 .x22 .x13, ld .x13 .x16 32, .adcs .x .x23 .x23 .x13, ld .x13 .x16 40, .adcs .x .x24 .x24 .x13, ld .x13 .x16 48, .adcs .x .x25 .x25 .x13, ld .x13 .x16 56, .adcs .x .x26 .x26 .x13] := rfl
  brun [hcode,
    h16, hs.ld (show eT + 8 ≤ Z by omega), hld 1 (by decide), hld 2 (by decide),
    hld 3 (by decide), hld 4 (by decide), hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

end VG.Proof.Bignum.AArch64.BlockedRedc
