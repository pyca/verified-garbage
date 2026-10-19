module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignificantByteCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.AArch64.Significant
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantByteCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Significant
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time width scanning with respect to public modulus bytes -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def scanFound (bs : List Byte) : Nat → Nat × Byte
  | 0 => (0, 0)
  | j + 1 => scanNext (scanFound bs j) (bs.length - j) (bs.getD j 0)

theorem scanFound_bound (bs : List Byte) (j : Nat) : (scanFound bs j).1 ≤ bs.length := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    unfold scanFound scanNext
    split
    · exact Nat.sub_le _ _
    · exact ih

structure ScanPublic where
  base : Addr
  extent : Nat
  pointer : Addr
  bytes : List Byte

def ScanPre (p : ScanPublic) (s : State) : Prop :=
  s.gpr .x1 = p.pointer ∧ s.gpr .x9 = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.base p.extent p.pointer p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

def ScanLoop (p : ScanPublic) (j : Nat) (s : State) : Prop :=
  s.gpr .x1 = p.pointer + BitVec.ofNat 64 j ∧
  s.gpr .x9 = BitVec.ofNat 64 (p.bytes.length - j) ∧
  s.gpr .x8 = BitVec.ofNat 64 (scanFound p.bytes j).1 ∧
  s.gpr .x10 = (scanFound p.bytes j).2.zeroExtend 64 ∧
  Src s p.base p.extent p.pointer p.bytes ∧ p.bytes.length < 2 ^ 64

theorem scanLoop_byte {p : ScanPublic} {j : Nat} {s : State}
    (hj : j < p.bytes.length) (h : ScanLoop p j s) :
    ScanBytePre ⟨p.pointer + BitVec.ofNat 64 j, p.bytes.length - j,
      scanFound p.bytes j, p.bytes.getD j 0⟩ s := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    (h.2.2.2.2.1.val j hj).trans (by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]),
    h.2.2.2.2.1.rd j hj, Nat.lt_of_le_of_lt (scanFound_bound _ _) h.2.2.2.2.2⟩

theorem scanLoop_step {p : ScanPublic} {j : Nat} {s : State}
    (hj : j < p.bytes.length) (h : ScanLoop p j s) :
    WP isa Checks.significantByte s fun t =>
      isa.eval (.nonzero .x .x9) t = some (decide (j + 1 < p.bytes.length)) ∧ ScanLoop p (j + 1) t := by
  have hb := scanLoop_byte hj h
  refine WP.mono (significantByte_ok (remaining := p.bytes.length - j) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.2.1
    hb.2.2.2.2.2.2 (by omega) (by have := h.2.2.2.2.2; omega))
    fun t ⟨hsi, hcx, h8, h9, hz, hm, hk⟩ => ?_
  have hbyte := hb.2.2.2.2.1
  have hpos : p.pointer + BitVec.ofNat 64 j + 1 = p.pointer + BitVec.ofNat 64 (j + 1) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  refine ⟨?_, hsi.trans hpos, ?_, ?_, ?_, h.2.2.2.2.1.congrK ?_ hk, h.2.2.2.2.2⟩
  · change some (!(t.gpr .x9 == (0#64))) = _
    simp only [hz]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    by_cases he : p.bytes.length - j = 1
    · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, decide_eq_true_eq, false_iff]
      omega
    · simp only [he, decide_false, Bool.not_false, decide_eq_true_eq, true_iff]
      omega
  · rw [hcx, show p.bytes.length - j - 1 = p.bytes.length - (j + 1) by omega]
  · rw [h8, hbyte]; rfl
  · rw [h9, hbyte]; rfl
  · rw [hm]; exact InScr.refl _ _ _

theorem significantLoop_ct :
    RelCT isa (Two fun p s => 0 < p.bytes.length ∧ ScanLoop p 0 s)
      (.loop Checks.significantByte (.nonzero .x .x9)) (fun _ _ => True) := by
  have hct := two_map (Φ := fun (p : ScanPublic × Nat) s => p.2 < p.1.bytes.length ∧ ScanLoop p.1 p.2 s) (fun (p : ScanPublic × Nat) =>
      (⟨p.1.pointer + BitVec.ofNat 64 p.2, p.1.bytes.length - p.2,
        scanFound p.1.bytes p.2, p.1.bytes.getD p.2 0⟩ : ScanBytePublic))
    (fun p s h => scanLoop_byte h.1 h.2) significantByte_ct
  refine (two_loop (Φ := ScanLoop) (Ψ := fun _ _ => True) (fun p => p.bytes.length) hct ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p j s hj hs
  exact WP.mono (scanLoop_step hj hs) fun t ⟨hz, ht⟩ => ⟨hz, fun _ => ht, fun _ => trivial⟩

theorem significant_ct : RelCT isa (Two ScanPre) Checks.significant (fun _ _ => True) := by
  unfold Checks.significant seqs
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.bytes.length ∧ ScanLoop p 0 s) []
    (by intro p s t hs ht r hr; cases hr) (by taint_decide) ?_) significantLoop_ct
  intro p s ⟨hsi, hcx, hsrc, h1, h64⟩
  refine WP.mono (WP.keep [.x8, .x10] (Q := fun t => t.gpr .x8 = 0 ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨h8, h9, hm⟩, hk⟩ => ?_
  refine ⟨h1, ?_, ?_, h8, h9, hsrc.congrK ?_ hk, h64⟩
  · simpa using (hk.gpr .x1 (by decide)).trans hsi
  · simpa using (hk.gpr .x9 (by decide)).trans hcx
  · rw [hm]; exact InScr.refl _ _ _

end VG.Proof.Dsa.AArch64
