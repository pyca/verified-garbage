module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastCancel
import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev cancelRegs := VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
  VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ [.x1, .x27]

structure CancelInv (s : State) (B : Addr) (eQ eN j : Nat) (t : State) : Prop where
  value : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0 →
    2 ^ (64 * j) * blockValue (accumulator t) =
    blockValue (accumulator s) + wv t.mem B eQ j * blockValue (operand s (word s.mem B eN))
  frame : Outside B eQ (8 * j) s.mem t.mem
  keep : Keep cancelRegs s t


theorem cancelStep_ok {s t : State} {B : Addr} {Z eQ eN j : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hN : eN + 8 ≤ Z)
    (hQN : eQ + 64 ≤ eN ∨ eN + 8 ≤ eQ)
    (hj : j < 8) (hI : CancelInv s B eQ eN j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.cancel j)) t
      fun u => CancelInv s B eQ eN (j + 1) u := by
  have hnw := hs.nowrap
  have hn := hI.frame.word (d := eN) (by omega) (by omega)
  have hop := (keep_operand hI.keep (by decide) (word t.mem B eN)).trans
    (congrArg (operand s) hn)
  have hopV := congrArg blockValue hop
  refine WP.mono (BlockedRedcFast.cancelRow_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x8 (by decide)).trans h8)
    ((hI.keep.gpr .x17 (by decide)).trans h17)
    ((hI.keep.gpr .x7 (by decide)).trans h7)
    (by omega) hN hj (by omega)) fun u ⟨hv, hm, ku⟩ => ?_
  have hmem := (congrArg (fun m : Mem => wv m B eQ (j + 1)) hm).trans
    (wv_writeW_top t.mem B eQ j (t.gpr .x19 * t.gpr .x15) (by omega))
  refine ⟨?_, ?_, (hI.keep.trans ku).mono (by decide)⟩
  · intro hinv
    have hinv' : ((word t.mem B eN).toNat * (t.gpr .x15).toNat + 1) % 2 ^ 64 = 0 := by
      exact (congrArg (fun a : Nat => (a * (t.gpr .x15).toNat + 1) % 2 ^ 64)
        (congrArg BitVec.toNat hn)).trans
          ((congrArg (fun b : Nat => ((word s.mem B eN).toNat * b + 1) % 2 ^ 64)
            (congrArg BitVec.toNat (hI.keep.gpr .x15 (by decide)))).trans hinv)
    obtain ⟨hv0, hc⟩ := hv hinv'
    have hz : u.c.toNat = 0 := congrArg Bool.toNat hc
    have hv' : 2 ^ 64 * blockValue (accumulator u) =
        blockValue (accumulator t) + (t.gpr .x19 * t.gpr .x15).toNat *
          blockValue (operand s (word s.mem B eN)) := by
      have he : blockValue (accumulator u) + (2 ^ 64) ^ 8 * u.c.toNat =
          blockValue (accumulator u) :=
        (congrArg (fun z => blockValue (accumulator u) + (2 ^ 64) ^ 8 * z) hz).trans
          ((congrArg (blockValue (accumulator u) + ·) (Nat.mul_zero ((2 ^ 64) ^ 8))).trans
            (Nat.add_zero _))
      exact (congrArg (2 ^ 64 * ·) he.symm).trans (hv0.trans
        (congrArg (fun n => blockValue (accumulator t) +
          (t.gpr .x19 * t.gpr .x15).toNat * n) hopV))
    have hstep := cancel_step (hI.value hinv) hv'
    exact (congrArg (· * blockValue (accumulator u)) (pow64_succ j)).trans
      (hstep.trans (congrArg (fun q => blockValue (accumulator s) +
        q * blockValue (operand s (word s.mem B eN))) hmem.symm))
  · have ho := writeW_outside t.mem B (t.gpr .x19 * t.gpr .x15)
      (d := eQ + 8 * j) (by omega)
    have hm' : Outside B (eQ + 8 * j) 8 t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)
    exact (hI.frame.mono (by omega) (by omega)).trans (hm'.mono (by omega) (by omega))


theorem cancelPrefix_ok {s : State} {B : Addr} {Z eQ eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hN : eN + 8 ≤ Z)
    (hQN : eQ + 64 ≤ eN ∨ eN + 8 ≤ eQ)
    (hk : k ≤ 8) :
    WP isa (.block ((List.range k).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.cancel)) s
      fun t => CancelInv s B eQ eN k t := by
  induction k with
  | zero =>
    apply WP.block_nil
    refine ⟨?_, Outside.refl _ _ _ _, Keep.refl _ _⟩
    intro _
    exact (Nat.one_mul _).trans ((Nat.add_zero _).symm.trans
      (congrArg (blockValue (accumulator s) + ·)
        (Nat.zero_mul (blockValue (operand s (word s.mem B eN)))).symm))
  | succ k ih =>
    rewrite [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    exact WP.mono (ih (by omega)) fun t hI =>
      cancelStep_ok hs h8 h17 h7 hQ hN hQN (by omega) hI

end VG.Proof.Bignum.AArch64.BlockedRedc
