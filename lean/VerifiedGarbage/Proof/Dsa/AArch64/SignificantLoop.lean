module

public import VerifiedGarbage.Proof.Dsa.AArch64.Significant
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Complete actual-width scanning for DSA's public moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def scanFinish (found : Nat × Byte) (bs : List Byte) : Nat × Byte :=
  if found.1 = 0 then VG.Proof.Dsa.significant bs else found

theorem scanFinish_step (found : Nat × Byte) (b : Byte) (bs : List Byte) :
    scanFinish (scanNext found (bs.length + 1) b) bs = scanFinish found (b :: bs) := by
  by_cases hf : found.1 = 0
  · by_cases hb : b = 0
    · subst b
      have hnext : scanNext found (bs.length + 1) 0 = found := ite_eq_right (by simp)
      rw [hnext]
      unfold scanFinish
      rw [ite_eq_left hf, ite_eq_left hf, VG.Proof.Dsa.significant, ite_eq_left rfl]
    · have hnext : scanNext found (bs.length + 1) b = (bs.length + 1, b) := ite_eq_left ⟨hf, hb⟩
      rw [hnext, scanFinish, scanFinish, ite_eq_left hf,
        VG.Proof.Dsa.significant, ite_eq_right hb]
      exact ite_eq_right (Nat.succ_ne_zero _)
  · have hnext : scanNext found (bs.length + 1) b = found := ite_eq_right (fun h => hf h.1)
    rw [hnext, scanFinish, scanFinish, ite_eq_right hf, ite_eq_right hf]

theorem scanNext_bounds {found : Nat × Byte} {n : Nat} (b : Byte)
    (hf : found.1 < 2 ^ 64) (hn : n < 2 ^ 64) (hn1 : 0 < n)
    (hzero : found.1 = 0 → found.2 = 0) :
    (scanNext found n b).1 < 2 ^ 64 ∧
    ((scanNext found n b).1 = 0 → (scanNext found n b).2 = 0) := by
  unfold scanNext
  split
  · exact ⟨hn, fun h => by dsimp only at h; omega⟩
  · exact ⟨hf, hzero⟩

theorem scanFinish_nil {found : Nat × Byte} (hz : found.1 = 0 → found.2 = 0) :
    scanFinish found [] = found := by
  unfold scanFinish
  split
  · rename_i h
    apply Prod.ext
    · exact h.symm
    · exact (hz h).symm
  · rfl

structure ScanState (s : State) (B : Addr) (Z : Nat) (p : Addr) (bs : List Byte)
    (found : Nat × Byte) : Prop where
  pointer : s.gpr .x1 = p
  remaining : s.gpr .x2 = BitVec.ofNat 64 bs.length
  width : s.gpr .x8 = BitVec.ofNat 64 found.1
  head : s.gpr .x9 = found.2.zeroExtend 64
  source : Src s B Z p bs
  bound : found.1 < 2 ^ 64
  zero : found.1 = 0 → found.2 = 0

/-- The scan loop's result, with its memory and register frame. -/
theorem significantLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte} {found : Nat × Byte}
    (h : ScanState s B Z p bs found) (hn : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop Checks.significantByte (.nonzero .x .x2)) s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (scanFinish found bs).1 ∧
      t.gpr .x9 = (scanFinish found bs).2.zeroExtend 64 ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x9, .x1, .x2] s t := by
  let target := scanFinish found bs
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte) (first : Nat × Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ ScanState t B Z ptr rest first ∧
    scanFinish first rest = target ∧ t.mem = s.mem ∧ Keep [.x3, .x8, .x9, .x1, .x2] s t
  refine WP.loop (M := isa) (body := Checks.significantByte) (c := .nonzero .x .x2) Inv ?_ bs.length s ?_
  · intro n u ⟨ptr, rest, first, hlen, hpos, hbnd, hu, htarget, hum, hku⟩
    cases rest with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b rest =>
      have hr : InRegions (u.rd ++ u.wr) ptr 1 := by simpa using hu.source.rd 0 (by simp)
      have hbyte : u.mem ptr = b := by
        have e := hu.source.val 0 (by simp)
        change u.mem (ptr + 0) = b at e
        exact (congrArg u.mem (BitVec.add_zero ptr)).symm.trans e
      refine WP.mono (significantByte_ok hu.pointer hu.remaining hu.width hu.head hr hu.bound
        (by simp) (by omega)) fun t ⟨htp, htl, ht8, ht9, htm, hkt⟩ => ?_
      rw [hbyte] at ht8 ht9
      have hbounds := scanNext_bounds b hu.bound (show (b :: rest).length < 2 ^ 64 by omega)
        (by simp) hu.zero
      have ht : ScanState t B Z (ptr + 1) rest (scanNext first (rest.length + 1) b) :=
        ⟨htp, by simpa only [List.length_cons, Nat.add_sub_cancel] using htl,
          ht8, ht9, source_tail (hu.source.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
          hbounds.1, hbounds.2⟩
      have htarget' := (scanFinish_step first b rest).trans htarget
      have hk := (hku.trans hkt).mono (show ∀ r ∈
        [Reg.x3, Reg.x8, Reg.x9, Reg.x1, Reg.x2] ++ [Reg.x3, Reg.x8, Reg.x9, Reg.x1, Reg.x2],
        r ∈ [Reg.x3, Reg.x8, Reg.x9, Reg.x1, Reg.x2] by decide)
      by_cases he : rest.length = 0
      · left
        have hnil : scanFinish (scanNext first (rest.length + 1) b) rest =
            scanNext first (rest.length + 1) b :=
          (congrArg (scanFinish (scanNext first (rest.length + 1) b))
            (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil ht.zero)
        have hresult := hnil.symm.trans htarget'
        refine ⟨?_, ?_, ?_, htm.trans hum, hk⟩
        · rw [eval_nonzero, htl, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          simp only [List.length_cons, Nat.add_sub_cancel, he, ne_eq, not_true_eq_false, decide_false]
        · exact ht.width.trans (congrArg (fun x : Nat × Byte => BitVec.ofNat 64 x.1) hresult)
        · exact ht.head.trans (congrArg (fun x : Nat × Byte => x.2.zeroExtend 64) hresult)
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega,
          ptr + 1, rest, _, rfl, by omega, by simp only [List.length_cons] at hlen; omega,
          ht, htarget', htm.trans hum, hk⟩
        rw [eval_nonzero, htl, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [List.length_cons, Nat.add_sub_cancel, he, ne_eq, not_false_eq_true, decide_true]
  · exact ⟨p, bs, found, rfl, hn, h64, h, rfl, rfl, Keep.refl _ _⟩

/-- Scan a nonempty modulus buffer, including any leading zero padding. -/
theorem significant_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hsi : s.gpr .x1 = p) (hcx : s.gpr .x2 = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (hn : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa Checks.significant s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .x9 = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x9, .x1, .x2] s t := by
  unfold Checks.significant seqs
  refine WP.seq (WP.mono (WP.keep [.x8, .x9] (Q := fun u =>
    u.gpr .x8 = 0 ∧ u.gpr .x9 = 0 ∧ u.mem = s.mem) (by brun) (by decide) (by decide)
    (by decide +kernel))
    fun u ⟨⟨hu8, hu9, hum⟩, hku⟩ => ?_)
  have hu : ScanState u B Z p bs (0, 0) :=
    ⟨(hku.gpr .x1 (by decide)).trans hsi, (hku.gpr .x2 (by decide)).trans hcx, hu8, hu9,
      hs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku, by decide, fun _ => rfl⟩
  refine WP.mono (significantLoop_ok hu hn h64) fun t ⟨ht8, ht9, htm, hkt⟩ =>
    ⟨ht8, ht9, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
