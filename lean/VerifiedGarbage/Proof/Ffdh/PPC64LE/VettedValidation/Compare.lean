module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! Byte comparison leaves all five domain arguments and the saved link register intact. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE VG.WriteBytes
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ)

def compareRegs : List Reg := [.r0, .r8, .r9, .r10, .r11]

theorem compare_ok {s : State} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (hc : s.gpr .r4 = BitVec.ofNat 64 n)
    (hr1 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 j) 1)
    (hr2 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 j) 1) :
    WP isa VG.Impl.Ffdh.PPC64LE.VettedValidation.compare s fun t => Only compareRegs s t ∧
      (t.gpr .r10 = 0 ↔ Spec.Rsa.bytesAt s.mem (s.gpr .r3) n = Spec.Rsa.bytesAt s.mem (s.gpr .r8) n) := by
  let A := Spec.Rsa.bytesAt s.mem (s.gpr .r3) n
  let B := Spec.Rsa.bytesAt s.mem (s.gpr .r8) n
  unfold VG.Impl.Ffdh.PPC64LE.VettedValidation.compare
  refine WP.seq (wp_addi fun u oU count => wp_li (by decide) fun v oV zero => wp_nil ?_)
  have zero : v.gpr .r10 = 0 := by rw [zero]; rfl
  have count : v.gpr .r9 = BitVec.ofNat 64 n := by
    rw [oV.get .r9, count, hc, BitVec.add_zero]
  have initial : Only compareRegs s v := (oU.trans oV).mono
  refine WP.mono (wp_countdown (cnt := .r9) hn' hn
    (fun i t => Only compareRegs s t ∧
      (∃ c : Byte, t.gpr .r10 = c.setWidth 64 ∧ (c = 0 ↔ A.take i = B.take i)) ∧
      t.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 i) ?_
    ⟨initial, ⟨0, by rw [zero]; rfl, by simp⟩, by rw [oV.get .r8, oU.get .r8]; simp⟩ count)
    (fun t ⟨only, ⟨c, value, equal⟩, _⟩ => ⟨only, ?_⟩)
  · intro i hi t ⟨o, ⟨c, ec, hcz⟩, ptr⟩ counter
    have index : t.gpr .r4 - t.gpr .r9 = BitVec.ofNat 64 i := by
      rw [o.get .r4, hc, counter]
      have sum : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - i) + BitVec.ofNat 64 i := by
        rw [← BitVec.ofNat_add]
        congr 1
        omega
      rw [sum, BitVec.add_comm, BitVec.add_sub_cancel]
    unfold compareByte
    refine wp_sub fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => ?_
    have addr : t₂.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 i := by
      rw [e₂, e₁, o₁.get .r3, o.get .r3, index]
    have readA : InRegions (t₂.rd ++ t₂.wr) (t₂.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [addr, o₂.rd, o₂.wr, o₁.rd, o₁.wr, o.rd, o.wr, BitVec.add_zero]
      exact hr1 i hi
    refine wp_lbz rfl readA fun t₃ o₃ e₃ => ?_
    have readB : InRegions (t₃.rd ++ t₃.wr) (t₃.gpr .r8 + BitVec.ofNat 64 0) 1 := by
      rw [o₃.get .r8, o₂.get .r8, o₁.get .r8, ptr,
        o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr, o.rd, o.wr, BitVec.add_zero]
      exact hr2 i hi
    refine wp_lbz rfl readB fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ =>
      wp_or fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_subi fun t₈ o₈ e₈ => wp_nil ?_
    have step : Only compareRegs t t₈ :=
      (((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).mono
    let a := s.mem (s.gpr .r3 + BitVec.ofNat 64 i)
    let b := s.mem (s.gpr .r8 + BitVec.ofNat 64 i)
    have ha : t₄.gpr .r0 = a.setWidth 64 := by
      rw [o₄.get .r0, e₃, addr, o₂.mem, o₁.mem, o.mem, BitVec.add_zero]
    have hb : t₄.gpr .r11 = b.setWidth 64 := by
      rw [e₄, o₃.get .r8, o₂.get .r8, o₁.get .r8, ptr,
        o₃.mem, o₂.mem, o₁.mem, o.mem, BitVec.add_zero]
    refine ⟨⟨(o.trans step).mono, ⟨c ||| (a ^^^ b), ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [o₈.get .r10, o₇.get .r10, e₆, e₅, o₅.get .r10, ha, hb,
        o₄.get .r10, o₃.get .r10, o₂.get .r10, o₁.get .r10, ec,
        BitVec.setWidth_or, BitVec.setWidth_xor]
    · have equal : (c ||| (a ^^^ b) = 0) ↔ c = 0 ∧ a = b := by
        simp [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
      rw [equal, hcz, bytesAt_take_succ _ _ hi, bytesAt_take_succ _ _ hi,
        snoc_eq_iff (by simp [bytesAt_length])]
    · rw [o₈.get .r8, e₇, o₆.get .r8, o₅.get .r8, o₄.get .r8,
        o₃.get .r8, o₂.get .r8, o₁.get .r8, ptr, ofNat_succ']
    · rw [e₈, o₇.get .r9, o₆.get .r9, o₅.get .r9, o₄.get .r9,
        o₃.get .r9, o₂.get .r9, o₁.get .r9]
  · rw [value]
    rw [List.take_of_length_le (by simp [A, bytesAt_length]),
      List.take_of_length_le (by simp [B, bytesAt_length])] at equal
    rw [← equal]
    constructor
    · intro h
      bv_omega
    · intro h
      rw [h]
      rfl

end VG.Proof.Ffdh.PPC64LE.VettedValidation
