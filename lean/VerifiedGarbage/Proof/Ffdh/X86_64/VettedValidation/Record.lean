module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare

import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.CallLay
/-! One public record leaves the equality flag for its full p/g/q encoding. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/VettedValidation/Blocks.lean`, which only this module imported.
section

/-! Short public controls and table-address setup for each recognition record. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem header_ok {s : State} {base src : Addr} {k : Nat} {dom : List Byte}
    (h : Context base src k dom s) (g : Group) (fit : g.len < 2 ^ 31) :
    WP isa (.block (header g)) s fun t =>
      t.zf = some (decide (g.len = k)) ∧ t.gpr .rdx = 1 ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.zf = some (decide (g.len = k)) ∧ t.gpr .rdx = 1 ∧ t.mem = s.mem) ?_ rfl) ?_
  · xrun [header, ea_at, h.baseReg, h.readWidth, h.width, sx_ofNat fit,
      VG.Proof.Bignum.X86_64.ofNat_sub_beq (j := k) (N := g.len) (by have := h.upper; omega) (by omega)]
    simp only [eq_comm]
  · rintro t ⟨⟨zero, value, mem⟩, rest⟩
    exact ⟨zero, value, mem, rest.mono (by decide)⟩

theorem args_ok {s : State} {base src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context base src k dom s) (sym : s.syms tableSym = table)
    (fit : offset + 8 < 2 ^ 31) :
    WP isa (.block (compareArgs offset)) s fun t =>
      t.gpr .rsi = table + BitVec.ofNat 64 (offset + 8) ∧
      t.gpr .rcx = BitVec.ofNat 64 dom.length ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = table + BitVec.ofNat 64 (offset + 8) ∧
    t.gpr .rcx = BitVec.ofNat 64 dom.length ∧ t.mem = s.mem) ?_ rfl) ?_
  · xrun [compareArgs, sym, sx_ofNat fit, ea_at, h.baseReg, h.readLength, h.length]
  · rintro t ⟨⟨ptr, length, mem⟩, rest⟩
    exact ⟨ptr, length, mem, rest.mono (by decide)⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun t =>
      t.zf = some (s.gpr .rdx == 0) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (s.gpr .rdx == 0) ∧ t.mem = s.mem) (by xrun [BitVec.and_self]) rfl) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨zero, mem, rest.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/VettedValidation/Compare.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem keep_trans {s t u : State} (a : Keep clobbers s t) (b : Keep clobbers t u) :
    Keep clobbers s u :=
  (a.trans b).mono (by intro r hr; simpa only [List.mem_append, or_self] using hr)

theorem record_ok {s : State} {base src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context base src k dom s) (g : Group) (sym : s.syms tableSym = table)
    (data : RecordAt (table + BitVec.ofNat 64 offset) g s)
    (fit : offset + 8 < 2 ^ 31) :
    WP isa (record g offset) s fun t =>
      t.zf = some (decide (g.len = k ∧ dom = g.domain.take dom.length)) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  rw [record, WP.seq_iff]
  refine WP.mono_syms (header_ok h g data.lenFit) ?_
  rintro u ⟨zero, one, memU, restU⟩ symU
  have hu := h.after memU restU
  have dataU := data.after memU restU
  have choice : WP isa (.ite .e
      (.seq (.block (compareArgs offset)) VG.Impl.RsaPkcs1Sig.X86_64.compare) (.block [])) u
      (fun v => (v.gpr .rdx = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧
        v.mem = u.mem ∧ Keep clobbers u v) := by
    apply WP.ite (decide (g.len = k)) (by simpa only [eval] using zero)
    · intro hit
      have width := of_decide_eq_true hit
      refine WP.mono (compare_ok hu g (by rw [symU]; exact sym) dataU fit width) ?_
      rintro v ⟨result, mem, rest⟩
      exact ⟨by simpa only [width, true_and] using result, mem, rest⟩
    · intro miss
      have width := of_decide_eq_false miss
      refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
      rw [one]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, width, false_and]
  rw [WP.seq_iff]
  refine WP.mono choice ?_
  rintro v ⟨result, memV, restV⟩
  refine WP.mono (test_ok v) ?_
  rintro t ⟨zeroT, memT, restT⟩
  refine ⟨?_, memT.trans (memV.trans memU), keep_trans restU (keep_trans restV restT)⟩
  rw [zeroT]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using result

end VG.Proof.Ffdh.X86_64.VettedValidation
