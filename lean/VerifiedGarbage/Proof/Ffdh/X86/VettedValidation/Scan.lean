module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Record
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! The finite scan returns the same recognition result as the shared pure table. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem return_ok (s : State) (n : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 n ∧ t.mem = s.mem ∧ Keeps clobbers s t := by
  exact wp_movi fun t T => WP.block_nil ⟨T.gpr, T.mem, T.keeps.mono (by decide)⟩

theorem scan_ok {base src sp table : BitVec 32} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat) (s : State)
    (h : Context base src sp table k dom s)
    (data : TableAt (byteAddr table + BitVec.ofNat 64 offset) gs s)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744) :
    WP isa (scan gs offset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (recognizeList gs k dom) ∧
      t.mem = s.mem ∧ Keeps clobbers s t := by
  induction gs generalizing offset s with
  | nil => exact return_ok s 0
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    rw [scan, WP.seq_iff]
    refine WP.mono (record_ok h g data.1 (by rw [total] at fit; omega)) ?_
    rintro u ⟨zero, memU, restU⟩
    refine WP.ite (decide (g.len = k ∧ dom = g.domain.take dom.length))
      (by simpa only [isa, eval] using zero) ?_ ?_
    · intro hit
      refine WP.mono (return_ok u g.bits) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_left (of_decide_eq_true hit)] using value,
        memT.trans memU, restU.trans restT⟩
    · intro miss
      have tail := (data.after memU restU).2
      have ptr : (byteAddr table + BitVec.ofNat 64 offset) + BitVec.ofNat 64 (8 + 3 * g.len) =
          byteAddr table + BitVec.ofNat 64 (offset + 8 + 3 * g.len) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        congr 2
        omega
      rw [ptr] at tail
      refine WP.mono (ih (offset + 8 + 3 * g.len) u (h.after memU restU)
        tail (by rw [total] at fit; omega)) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_right (of_decide_eq_false miss)] using value,
        memT.trans memU, restU.trans restT⟩

end VG.Proof.Ffdh.X86.VettedValidation
