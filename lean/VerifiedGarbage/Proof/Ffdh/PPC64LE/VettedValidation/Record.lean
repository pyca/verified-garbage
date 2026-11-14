module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.State
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! ### `Ffdh.PPC64LE.VettedValidation.Blocks`, which only this module used -/

section

/-! Register-only width checking and constant-table address setup. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem header_ok {s : State} {src : Addr} {k : Nat} {dom : List Byte}
    (h : Context src k dom s) (g : Group) (fit : g.len < 2 ^ 15) :
    WP isa (.block [.subi .r0 .r5 g.len]) s fun t =>
      (t.gpr .r0 = 0 ↔ g.len = k) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_subi (h := by omega_using [fit])
    (fun t o value => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨?_, o.mem,
      (show Keep [.r0] s t from ⟨o.gpr, o.rd, o.wr⟩).mono (by decide)⟩)
  rw [value, h.width]
  have hk : k < 2 ^ 64 := by have := h.upper; omega_using [this]
  constructor
  · intro zero
    change BitVec.ofNat 64 k - BitVec.ofNat 64 g.len = 0#64 at zero
    have same := congrArg (fun x : BitVec 64 => x + BitVec.ofNat 64 g.len) zero
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at same
    have hn := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
      Nat.mod_eq_of_lt (show g.len < 2 ^ 64 by omega_using [fit])] at hn
    exact hn.symm
  · intro same
    rw [same, BitVec.sub_self]
    rfl

theorem args_ok {s : State} {table : Addr} {offset : Nat}
    (sym : s.syms tableSym = table) (fit : offset + 8 < 2 ^ 15) :
    WP isa (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) s fun t =>
      t.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.r8] (Q := fun t =>
    t.gpr .r8 = table + BitVec.ofNat 64 (offset + 8) ∧ t.mem = s.mem) ?_ rfl rfl) ?_
  · crun [sym, fit]
  · rintro t ⟨⟨ptr, mem⟩, rest⟩
    exact ⟨ptr, mem, rest.mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end

/-! ### `Ffdh.PPC64LE.VettedValidation.Compare`, which only this module used -/

section

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
        omega_using [hi]
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

end

end


/-! An exact comparison of the supplied p/g[/q] encoding, after the public width check. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem recordPrefix {s : State} {ptr : Addr} {g : Group} {n : Nat}
    (h : RecordAt ptr g s) (size : n ≤ 3 * g.len) :
    Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) n = g.domain.take n := by
  have take := VG.Proof.MlKem.bytesAt_take s.mem (ptr + BitVec.ofNat 64 8) size
  change (Spec.Rsa.bytesAt s.mem _ (3 * g.len)).take n = Spec.Rsa.bytesAt s.mem _ n at take
  rw [h.bytes] at take
  exact take.symm

theorem compare_record {s : State} {src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context src k dom s) (g : Group) (sym : s.syms tableSym = table)
    (data : RecordAt (table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 < 2 ^ 15) (width : g.len = k) :
    WP isa (.seq (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)])
      VG.Impl.Ffdh.PPC64LE.VettedValidation.compare) s fun t =>
      (t.gpr .r10 = 0 ↔ dom = g.domain.take dom.length) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  have size : dom.length ≤ 3 * g.len := by rw [width]; rcases h.shape with hh | hh <;> omega_arith
  have positive : 0 < dom.length := by rcases h.shape with hh | hh <;> have := h.lower <;> omega_arith
  have small : dom.length < 2 ^ 64 := by rcases h.shape with hh | hh <;> have := h.upper <;> omega_arith
  have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 8 =
      table + BitVec.ofNat 64 (offset + 8) := by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [WP.seq_iff]
  refine WP.mono (args_ok sym fit) ?_
  rintro u ⟨source, memU, restU⟩
  refine WP.mono (compare_ok positive small
    ((restU.gpr (r := .r4) (by decide)).trans h.length) ?_ ?_) ?_
  · intro j hj
    rw [restU.gpr (r := .r3) (by decide), h.source, restU.2.1, restU.2.2]
    exact CallLay.inRegions_sub h.read (off := j) (l := 1) (by omega_arith) small
  · intro j hj
    rw [source, restU.2.1, restU.2.2, ← ptr]
    exact CallLay.inRegions_sub data.read (off := j) (l := 1) (by omega_arith)
      (by have := data.lenFit; omega_arith)
  · rintro t ⟨only, result⟩
    refine ⟨?_, only.mem.trans memU, keep_trans restU
      (show Keep clobbers u t from ⟨only.gpr, only.rd, only.wr⟩)⟩
    rw [restU.gpr (r := .r3) (by decide), h.source, source, memU, h.bytes] at result
    have ref := recordPrefix data size
    rw [ptr] at ref
    rw [ref] at result
    exact result

theorem record_ok {s : State} {src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context src k dom s) (g : Group) (sym : s.syms tableSym = table)
    (data : RecordAt (table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 < 2 ^ 15) :
    WP isa (record g offset) s fun t =>
      (t.gpr .r10 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  rw [record, WP.seq_iff]
  refine WP.mono_syms (header_ok h g data.lenFit) ?_
  rintro u ⟨zero, memU, restU⟩ symU
  refine WP.mono (WP.ite (Q := fun v : State =>
    (v.gpr .r10 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧
    v.mem = u.mem ∧ Keep clobbers u v) (decide (g.len = k)) ?_ ?_ ?_) ?_
  · rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq, decide_eq_true_eq] using zero)
  · intro hit
    have width := of_decide_eq_true hit
    refine WP.mono (compare_record (h.after memU restU) g (by rw [symU]; exact sym)
      (data.after memU restU) fit width) ?_
    rintro v ⟨result, mem, rest⟩
    exact ⟨by simpa only [width, true_and] using result, mem, rest⟩
  · intro miss
    have width := of_decide_eq_false miss
    exact VG.Proof.RsaPkcs1Sig.PPC64LE.wp_li (by decide) fun v o value =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨by rw [value]; simp [width], o.mem,
        (show Keep [.r10] u v from ⟨o.gpr, o.rd, o.wr⟩).mono (by decide)⟩
  · rintro t ⟨result, memT, restT⟩
    exact ⟨result, memT.trans memU, keep_trans restU restT⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation
