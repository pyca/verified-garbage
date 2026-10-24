module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Compare
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! One public record leaves the equality flag for its full p/g/q encoding. -/

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
