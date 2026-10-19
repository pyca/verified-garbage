module

public import VerifiedGarbage.Proof.Dsa.X86_64.SignificantByteCT
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Significant
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantByteCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.RsaPss
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Significant
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.RsaPss

/-! # Constant-time width scanning with respect to public modulus bytes -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  s.gpr .rsi = p.pointer ∧ s.gpr .rcx = BitVec.ofNat 64 p.bytes.length ∧
  Src s p.base p.extent p.pointer p.bytes ∧ 0 < p.bytes.length ∧ p.bytes.length < 2 ^ 64

def ScanLoop (p : ScanPublic) (j : Nat) (s : State) : Prop :=
  s.gpr .rsi = p.pointer + BitVec.ofNat 64 j ∧
  s.gpr .rcx = BitVec.ofNat 64 (p.bytes.length - j) ∧
  s.gpr .r8 = BitVec.ofNat 64 (scanFound p.bytes j).1 ∧
  s.gpr .r9 = (scanFound p.bytes j).2.zeroExtend 64 ∧
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
      isa.eval .ne t = some (decide (j + 1 < p.bytes.length)) ∧ ScanLoop p (j + 1) t := by
  have hb := scanLoop_byte hj h
  refine WP.mono (significantByte_ok (remaining := p.bytes.length - j) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.2.1
    hb.2.2.2.2.2.2 (by omega) (by have := h.2.2.2.2.2; omega))
    fun t ⟨hsi, hcx, h8, h9, hz, hm, hk⟩ => ?_
  have hbyte := hb.2.2.2.2.1
  have hpos : p.pointer + BitVec.ofNat 64 j + 1 = p.pointer + BitVec.ofNat 64 (j + 1) := by
    rw [BitVec.add_assoc, ofNat_add_one]
  refine ⟨?_, hsi.trans hpos, ?_, ?_, ?_, h.2.2.2.2.1.congrK ?_ hk, h.2.2.2.2.2⟩
  · change VG.X86_64.eval .ne t = _
    simp only [VG.X86_64.eval, hz, Option.map_some]
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
      (.loop Checks.significantByte .ne) (fun _ _ => True) := by
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
  refine WP.mono (WP.keep [.r8, .r9] (Q := fun t => t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun t ⟨⟨h8, h9, hm⟩, hk⟩ => ?_
  refine ⟨h1, ?_, ?_, h8, h9, hsrc.congrK ?_ hk, h64⟩
  · simpa using (hk.gpr (show Reg.rsi ∉ _ by decide)).trans hsi
  · simpa using (hk.gpr (show Reg.rcx ∉ _ by decide)).trans hcx
  · rw [hm]; exact InScr.refl _ _ _

end VG.Proof.Dsa.X86_64
