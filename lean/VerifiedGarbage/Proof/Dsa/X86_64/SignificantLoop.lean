module

public import VerifiedGarbage.Proof.Dsa.X86_64.Significant
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual

/-! # Complete actual-width scanning for DSA's public moduli -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
  pointer : s.gpr .rsi = p
  remaining : s.gpr .rcx = BitVec.ofNat 64 bs.length
  width : s.gpr .r8 = BitVec.ofNat 64 found.1
  head : s.gpr .r9 = found.2.zeroExtend 64
  source : Src s B Z p bs
  bound : found.1 < 2 ^ 64
  zero : found.1 = 0 → found.2 = 0

/-- The scan loop's result, with its memory and register frame. -/
theorem significantLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte} {found : Nat × Byte}
    (h : ScanState s B Z p bs found) (hn : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop Checks.significantByte .ne) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (scanFinish found bs).1 ∧
      t.gpr .r9 = (scanFinish found bs).2.zeroExtend 64 ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .r9, .rsi, .rcx] s t := by
  let target := scanFinish found bs
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte) (first : Nat × Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ ScanState t B Z ptr rest first ∧
    scanFinish first rest = target ∧ t.mem = s.mem ∧ Keep [.rax, .r8, .r9, .rsi, .rcx] s t
  refine WP.loop (M := isa) (body := Checks.significantByte) (c := .ne) Inv ?_ bs.length s ?_
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
        (by simp) (by omega)) fun t ⟨htp, htl, ht8, ht9, htz, htm, hkt⟩ => ?_
      rw [hbyte] at ht8 ht9
      have hbounds := scanNext_bounds b hu.bound (show (b :: rest).length < 2 ^ 64 by omega)
        (by simp) hu.zero
      have ht : ScanState t B Z (ptr + 1) rest (scanNext first (rest.length + 1) b) :=
        ⟨htp, by simpa only [List.length_cons, Nat.add_sub_cancel] using htl,
          ht8, ht9, source_tail (hu.source.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
          hbounds.1, hbounds.2⟩
      have htarget' := (scanFinish_step first b rest).trans htarget
      have hk := (hku.trans hkt).mono (show ∀ r ∈
        [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx] ++ [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx],
        r ∈ [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx] by decide)
      by_cases he : rest.length = 0
      · left
        have hnil : scanFinish (scanNext first (rest.length + 1) b) rest =
            scanNext first (rest.length + 1) b :=
          (congrArg (scanFinish (scanNext first (rest.length + 1) b))
            (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil ht.zero)
        have hresult := hnil.symm.trans htarget'
        refine ⟨?_, ?_, ?_, htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
        · exact ht.width.trans (congrArg (fun x : Nat × Byte => BitVec.ofNat 64 x.1) hresult)
        · exact ht.head.trans (congrArg (fun x : Nat × Byte => x.2.zeroExtend 64) hresult)
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega,
          ptr + 1, rest, _, rfl, by omega, by simp only [List.length_cons] at hlen; omega,
          ht, htarget', htm.trans hum, hk⟩
        change VG.X86_64.eval .ne t = some true
        simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he,
          decide_false, Option.map_some, Bool.not_false]
  · exact ⟨p, bs, found, rfl, hn, h64, h, rfl, rfl, Keep.refl _ _⟩

/-- Scan a nonempty modulus buffer, including any leading zero padding. -/
theorem significant_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (hn : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa Checks.significant s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .r9 = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .r9, .rsi, .rcx] s t := by
  unfold Checks.significant seqs
  refine WP.seq (WP.mono (WP.keep [.r8, .r9] (Q := fun u =>
    u.gpr .r8 = 0 ∧ u.gpr .r9 = 0 ∧ u.mem = s.mem) (by xrun) rfl)
    fun u ⟨⟨hu8, hu9, hum⟩, hku⟩ => ?_)
  have hu : ScanState u B Z p bs (0, 0) :=
    ⟨(hku.gpr (by decide)).trans hsi, (hku.gpr (by decide)).trans hcx, hu8, hu9,
      hs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku, by decide, fun _ => rfl⟩
  refine WP.mono (significantLoop_ok hu hn h64) fun t ⟨ht8, ht9, htm, hkt⟩ =>
    ⟨ht8, ht9, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
