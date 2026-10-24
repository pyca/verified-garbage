module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Record
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! The finite scan returns the same recognition result as the shared pure table. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem return_ok (s : State) (n : Nat) (fit : n < 2 ^ 32) :
    WP isa (.block [.mov32 .rax (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 n ∧ t.mem = s.mem) ?_ rfl) ?_
  · have wide : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
    xrun [wide]
  · rintro t ⟨⟨value, mem⟩, rest⟩
    exact ⟨value, mem, rest.mono (by decide)⟩

theorem scan_ok {base src table : Addr} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat) (s : State)
    (h : Context base src k dom s) (sym : s.syms tableSym = table)
    (data : TableAt (table + BitVec.ofNat 64 offset) gs s)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744) :
    WP isa (scan gs offset) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (recognizeList gs k dom) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  induction gs generalizing offset s with
  | nil => exact return_ok s 0 (by decide)
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    rw [scan, WP.seq_iff]
    refine WP.mono_syms (record_ok h g sym data.1 (by rw [total] at fit; omega)) ?_
    rintro u ⟨zero, memU, restU⟩ symU
    refine WP.ite (decide (g.len = k ∧ dom = g.domain.take dom.length))
      (by simpa only [eval] using zero) ?_ ?_
    · intro hit
      refine WP.mono (return_ok u g.bits data.1.bitsFit) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_left (of_decide_eq_true hit)] using value,
        memT.trans memU, keep_trans restU restT⟩
    · intro miss
      have tail := (data.after memU restU).2
      have ptr : (table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
          table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        congr 2
        omega
      rw [ptr] at tail
      refine WP.mono (ih (offset + 8 + 3 * g.len) u (h.after memU restU)
        (by rw [symU]; exact sym) tail (by rw [total] at fit; omega)) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_right (of_decide_eq_false miss)] using value,
        memT.trans memU, keep_trans restU restT⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
