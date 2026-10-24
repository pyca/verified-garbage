module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Blocks
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.CallLay

/-! Reuse the verified word/byte comparison loop on the complete public encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups
open VG.Proof.RsaPkcs1Sig.X86_64 (EqBytes)

theorem eqBytes_iff (m : Mem) (a b : Addr) (n : Nat) :
    EqBytes m a b n ↔ Spec.Rsa.bytesAt m a n = Spec.Rsa.bytesAt m b n := by
  constructor
  · intro h
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
      simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using h i hi
  · intro h i hi
    have same := congrArg (fun bs : List Byte => bs[i]?.getD 0) h
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] using same

theorem recordPrefix {s : State} {ptr : Addr} {g : Group} {n : Nat}
    (h : RecordAt ptr g s) (size : n ≤ 3 * g.len) :
    Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) n = g.domain.take n := by
  have take := VG.Proof.MlKem.bytesAt_take s.mem (ptr + BitVec.ofNat 64 8) size
  change (Spec.Rsa.bytesAt s.mem _ (3 * g.len)).take n = Spec.Rsa.bytesAt s.mem _ n at take
  rw [h.bytes] at take
  exact take.symm

theorem compare_ok {s : State} {base src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context base src k dom s) (g : Group) (sym : s.syms tableSym = table)
    (record : RecordAt (table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 < 2 ^ 31) (width : g.len = k) :
    WP isa (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86_64.compare) s fun t =>
      (t.gpr .rdx = 0 ↔ dom = g.domain.take dom.length) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  have size : dom.length ≤ 3 * g.len := by rw [width]; rcases h.shape with hh | hh <;> omega
  have positive : 0 < dom.length := by rcases h.shape with hh | hh <;> have := h.lower <;> omega
  have small : dom.length < 2 ^ 64 := by rcases h.shape with hh | hh <;> have := h.upper <;> omega
  have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 8 =
      table + BitVec.ofNat 64 (offset + 8) := by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have read := CallLay.inRegions_sub record.read (off := 0) (l := dom.length)
    (by omega) (by have := record.lenFit; omega)
  simp only [BitVec.add_zero, ptr] at read
  rw [WP.seq_iff]
  refine WP.mono (args_ok h sym fit) ?_
  rintro u ⟨source, length, memU, restU⟩
  have input : InRegions (u.rd ++ u.wr) (u.gpr .rdi) dom.length := by
    rw [restU.gpr (r := .rdi) (by decide), h.source, restU.2.1, restU.2.2]
    exact h.read
  have reference : InRegions (u.rd ++ u.wr) (u.gpr .rsi) dom.length := by
    rw [source, restU.2.1, restU.2.2]
    exact read
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.compare_ok
    (by rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]) positive ⟨input, reference⟩) ?_
  rintro t ⟨restT, memT, result⟩
  refine ⟨?_, memT.trans memU, (restU.trans (restT.mono (rs' := clobbers) (by decide))).mono (by
    intro r hr; simpa only [List.mem_append, or_self] using hr)⟩
  rw [restU.gpr (r := .rdi) (by decide), h.source, source, memU, eqBytes_iff, h.bytes] at result
  have ref := recordPrefix record size
  rw [ptr] at ref
  rw [ref] at result
  exact result

end VG.Proof.Ffdh.X86_64.VettedValidation
