module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.TCB.Arm.Isa

/-! One scan step advances only past a public zero byte before the last byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def ScanStepPost (src : BitVec 32) (bs : List Byte) (s t : State) : Prop :=
  t.gpr .r3 = (bs.getD 0 0).setWidth 32 ∧ t.mem = s.mem ∧
    if bs.getD 0 0 = 0 ∧ 1 < bs.length then
      t.gpr .r4 = src + 1 ∧ t.gpr .r6 = BitVec.ofNat 32 (bs.length - 1) ∧ t.z = false
    else t.gpr .r4 = src ∧ t.gpr .r6 = BitVec.ofNat 32 bs.length ∧ t.z = true

theorem scanStep_ok (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (source : Octets base src len bs s) (positive : 0 < bs.length) (fits : bs.length < 2 ^ 32)
    (ptr : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 bs.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep s fun t =>
      ScanStepPost src bs s t ∧ Rest [.r3, .r4, .r6, .r11] s t := by
  refine withRest [.r3, .r4, .r6, .r11] ?_ (by
    intro r hr i hi
    have checked : (instrs VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep).all (fun i => !(clobbers i r)) = true := by
      cases r <;> try decide +kernel
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.scanStep, WP.seq_iff]
  refine WP.mono (scanRead_ok s source positive ptr) ?_
  rintro u ⟨⟨byte, zeroU, memU⟩, restU⟩
  have ptrU := (restU.gpr .r4 (by simp)).trans ptr
  have countU := (restU.gpr .r6 (by simp)).trans count
  by_cases headZero : bs.getD 0 0 = 0
  · refine WP.ite true (by change some u.z = some true; rw [zeroU, decide_eq_true headZero]) ?_ (by intro hf; cases hf)
    intro _
    rw [WP.seq_iff]
    refine WP.mono (scanCount_ok u positive fits countU) ?_
    rintro v ⟨⟨zeroV, memV⟩, restV⟩
    have ptrV := (restV.gpr .r4 (by simp)).trans ptrU
    have countV := (restV.gpr .r6 (by simp)).trans countU
    have byteV := (restV.gpr .r3 (by simp)).trans byte
    by_cases last : bs.length = 1
    · refine WP.ite false (by change some (!v.z) = some false; rw [zeroV, decide_eq_true last]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (scanStop_ok v) ?_
      rintro t ⟨⟨zeroT, memT⟩, restT⟩
      refine ⟨(restT.gpr .r3 (by simp)).trans byteV, memT.trans (memV.trans memU), ?_⟩
      rw [ite_eq_right (by omega : ¬(bs.getD 0 0 = 0 ∧ 1 < bs.length))]
      exact ⟨(restT.gpr .r4 (by simp)).trans ptrV, (restT.gpr .r6 (by simp)).trans countV, zeroT⟩
    · refine WP.ite true (by change some (!v.z) = some true; rw [zeroV, decide_eq_false last]; rfl) ?_ (by intro hf; cases hf)
      intro _
      refine WP.mono (scanAdvance_ok v positive countV) ?_
      rintro t ⟨⟨ptrT, countT, zeroT, memT⟩, restT⟩
      refine ⟨(restT.gpr .r3 (by simp)).trans byteV, memT.trans (memV.trans memU), ?_⟩
      rw [ite_eq_left (show bs.getD 0 0 = 0 ∧ 1 < bs.length from ⟨headZero, by omega⟩)]
      exact ⟨by rw [ptrT, ptrV], countT, zeroT⟩
  · refine WP.ite false (by change some u.z = some false; rw [zeroU, decide_eq_false headZero]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (scanStop_ok u) ?_
    rintro t ⟨⟨zeroT, memT⟩, restT⟩
    refine ⟨(restT.gpr .r3 (by simp)).trans byte, memT.trans memU, ?_⟩
    rw [ite_eq_right (fun h => headZero h.1)]
    exact ⟨(restT.gpr .r4 (by simp)).trans ptrU, (restT.gpr .r6 (by simp)).trans countU, zeroT⟩

end VG.Proof.Ffdh.Arm
