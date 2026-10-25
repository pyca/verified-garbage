module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Blocks
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Compare
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! Exact full-encoding comparison, including the generator and optional subgroup order. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem recordPrefix {s : State} {ptr : Addr} {g : Group} {n : Nat}
    (h : RecordAt ptr g s) (size : n ≤ 3 * g.len) :
    Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) n = g.domain.take n := by
  have take := VG.Proof.MlKem.bytesAt_take s.mem (ptr + BitVec.ofNat 64 8) size
  change (Spec.Rsa.bytesAt s.mem _ (3 * g.len)).take n = Spec.Rsa.bytesAt s.mem _ n at take
  rw [h.bytes] at take
  exact take.symm

theorem compare_record {base src sp table : BitVec 32} {k offset : Nat} {dom : List Byte} {s : State}
    (h : Context base src sp table k dom s) (g : Group)
    (data : RecordAt (byteAddr table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 + 3 * g.len ≤ 17744) (width : g.len = k) :
    WP isa (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86.compare) s fun t =>
      (t.gpr .ebp = 0 ↔ dom = g.domain.take dom.length) ∧ t.mem = s.mem ∧ Keeps clobbers s t := by
  have size : dom.length ≤ 3 * g.len := by rw [width]; rcases h.shape with hh | hh <;> omega
  have positive : 0 < dom.length := by rcases h.shape with hh | hh <;> have := h.lower <;> omega
  have small : dom.length < 2 ^ 32 := by rcases h.shape with hh | hh <;> have := h.upper <;> omega
  have ptr : (byteAddr table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 8 =
      byteAddr (table + BitVec.ofNat 32 (offset + 8)) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact (addr_eq (by have := h.tableFits; omega)).symm
  have refRead := CallLay.inRegions_sub data.read (off := 0) (l := dom.length)
    (by omega) (by have := data.lenFit; omega)
  simp only [BitVec.add_zero, ptr] at refRead
  rw [WP.seq_iff]
  refine WP.mono (args_ok h) ?_
  rintro u ⟨first, second, count, memU, restU⟩
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.compare_ok u positive small h.sourceFits ?_ ?_ ?_
    first second count) ?_
  · have ht : table.toNat + (offset + 8) < 2 ^ 32 := by have := h.tableFits; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset + 8 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt ht]
    have := h.tableFits
    omega
  · rw [restU.2.1, restU.2.2]; exact h.read
  · rw [restU.2.1, restU.2.2]; exact refRead
  · rintro t ⟨result, memT, restT⟩
    refine ⟨?_, memT.trans memU, restU.trans (restT.mono (by decide))⟩
    rw [memU, h.bytes] at result
    have ref := recordPrefix data size
    rw [ptr] at ref
    rw [ref] at result
    exact result

theorem record_ok {base src sp table : BitVec 32} {k offset : Nat} {dom : List Byte} {s : State}
    (h : Context base src sp table k dom s) (g : Group)
    (data : RecordAt (byteAddr table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 + 3 * g.len ≤ 17744) :
    WP isa (record g offset) s fun t =>
      t.zf = some (decide (g.len = k ∧ dom = g.domain.take dom.length)) ∧
      t.mem = s.mem ∧ Keeps clobbers s t := by
  rw [record, WP.seq_iff]
  refine WP.mono (header_ok h g data.lenFit) ?_
  rintro u ⟨zero, memU, restU⟩
  have choice : WP isa (.ite .e (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86.compare)
      (.block [.mov .ebp (.imm 1)])) u fun v =>
      (v.gpr .ebp = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧
      v.mem = u.mem ∧ Keeps clobbers u v := by
    apply WP.ite (decide (g.len = k)) (by simpa only [isa, eval] using zero)
    · intro hit
      have width := of_decide_eq_true hit
      refine WP.mono (compare_record (h.after memU restU) g (data.after memU restU) fit width) ?_
      rintro t ⟨result, mem, rest⟩
      exact ⟨by simpa only [width, true_and] using result, mem, rest⟩
    · intro miss
      exact wp_movi fun t T => WP.block_nil ⟨by rw [T.gpr]; simp [of_decide_eq_false miss],
        T.mem, T.keeps.mono (by decide)⟩
  rw [WP.seq_iff]
  refine WP.mono choice ?_
  rintro v ⟨result, memV, restV⟩
  refine WP.mono (test_ok v) ?_
  rintro t ⟨zeroT, memT, restT⟩
  refine ⟨?_, memT.trans (memV.trans memU), (restU.trans restV).trans restT⟩
  rw [zeroT]
  congr 1
  exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq, decide_eq_true_eq] using result)

end VG.Proof.Ffdh.X86.VettedValidation
