module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev blockRegs := VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nn ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt ++
  [.x1, .x27, .x16]

def tailBlock : List Instr := VG.Impl.Bignum.AArch64.BlockedRedc.addMemory false ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad ++
  (List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.tail

/-- One full block column loads each input block once, adds all eight
coefficient products, and stores the low block. -/
theorem tailBlock_ok {s : State} {B : Addr} {Z eQ eT eN : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h7 : s.gpr .x7 = 0) (hQ : eQ + 64 ≤ Z) (hT : eT + 64 ≤ Z)
    (hN : eN + 64 ≤ Z) (hQT : eQ + 64 ≤ eT ∨ eT + 64 ≤ eQ)
    (hNT : eN + 64 ≤ eT ∨ eT + 64 ≤ eN) :
    WP isa (.block tailBlock) s fun t =>
      wv t.mem B eT 8 + (2 ^ 64) ^ 8 * blockValue (accumulator t) =
        blockValue (accumulator s) + wv s.mem B eT 8 + wv s.mem B eQ 8 * wv s.mem B eN 8 ∧
      t.c = false ∧ t.gpr .x16 = off B (eT + 64) ∧
      Outside B eT 64 s.mem t.mem ∧ Keep blockRegs s t := by
  rewrite [tailBlock, List.append_assoc]
  apply WP.block_append
  refine WP.mono (addMemory_value hs h16 hT) fun a ⟨⟨hav, ham⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (nsLoad_ok (hs.congr ka.wr) ((ka.gpr .x17 (by decide)).trans h17) hN)
    fun d ⟨⟨hdn, hdm, hdc⟩, kd⟩ => ?_
  have kad := ka.trans kd
  have dm := hdm.trans ham
  have hacc := congrArg blockValue (keep_accumulator kd (by decide))
  have hcarry := congrArg Bool.toNat hdc
  have hdval : blockValue (accumulator d) + (2 ^ 64) ^ 8 * d.c.toNat =
      blockValue (accumulator s) + wv s.mem B eT 8 :=
    ((congrArg (· + (2 ^ 64) ^ 8 * d.c.toNat) hacc).trans
      (congrArg (fun c => blockValue (accumulator a) + (2 ^ 64) ^ 8 * c) hcarry)).trans hav
  have hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  have hx := Nat.lt_of_lt_of_le (wv_lt s.mem B eT 8) (Nat.le_of_eq hr)
  refine WP.mono (tailTile_ok (hs.congr kad.wr)
    ((kad.gpr .x8 (by decide)).trans h8) ((kad.gpr .x16 (by decide)).trans h16)
    ((kad.gpr .x17 (by decide)).trans h17) ((kad.gpr .x7 (by decide)).trans h7)
    hQ hT (by omega) hQT (by omega) hdval (blockValue_lt _) hx)
    fun t ⟨hI, hc⟩ => ?_
  have n0 := congrArg (fun m : Mem => word m B eN) hdm
  have hn : blockValue (operand d (word d.mem B eN)) = wv s.mem B eN 8 :=
    (congrArg (fun n => blockValue (operand d n)) n0).trans
      ((blockValue_congr hdn).trans ((blockValue_words a.mem B eN).trans
        (congrArg (fun m : Mem => wv m B eN 8) ham)))
  have hq := congrArg (fun m : Mem => wv m B eQ 8) dm
  have hv : wv t.mem B eT 8 + (2 ^ 64) ^ 8 *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
      blockValue (accumulator d) + (2 ^ 64) ^ 8 * d.c.toNat +
        wv d.mem B eQ 8 * blockValue (operand d (word d.mem B eN)) :=
    (congrArg (fun r => wv t.mem B eT 8 + r *
    (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat)) hr.symm).trans hI.value
  have hplain := zero_carry_value (congrArg Bool.toNat hc) hv
  have hprod := (congrArg (· * blockValue (operand d (word d.mem B eN))) hq).trans
    (congrArg (wv s.mem B eQ 8 * ·) hn)
  refine ⟨?_, hc, hI.ptr, ?_, (kad.trans hI.keep).mono (by decide)⟩
  · exact hplain.trans ((congrArg (· + wv d.mem B eQ 8 *
      blockValue (operand d (word d.mem B eN))) hdval).trans
        (congrArg (blockValue (accumulator s) + wv s.mem B eT 8 + ·) hprod))
  · intro x hx
    exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) dm)

end VG.Proof.Bignum.AArch64.BlockedRedc
