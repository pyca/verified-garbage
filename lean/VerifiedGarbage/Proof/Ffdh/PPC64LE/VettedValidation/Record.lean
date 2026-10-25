module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Blocks
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Compare
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

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
  have size : dom.length ≤ 3 * g.len := by rw [width]; rcases h.shape with hh | hh <;> omega
  have positive : 0 < dom.length := by rcases h.shape with hh | hh <;> have := h.lower <;> omega
  have small : dom.length < 2 ^ 64 := by rcases h.shape with hh | hh <;> have := h.upper <;> omega
  have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 8 =
      table + BitVec.ofNat 64 (offset + 8) := by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [WP.seq_iff]
  refine WP.mono (args_ok sym fit) ?_
  rintro u ⟨source, memU, restU⟩
  refine WP.mono (compare_ok positive small
    ((restU.gpr (r := .r4) (by decide)).trans h.length) ?_ ?_) ?_
  · intro j hj
    rw [restU.gpr (r := .r3) (by decide), h.source, restU.2.1, restU.2.2]
    exact CallLay.inRegions_sub h.read (off := j) (l := 1) (by omega) small
  · intro j hj
    rw [source, restU.2.1, restU.2.2, ← ptr]
    exact CallLay.inRegions_sub data.read (off := j) (l := 1) (by omega)
      (by have := data.lenFit; omega)
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
