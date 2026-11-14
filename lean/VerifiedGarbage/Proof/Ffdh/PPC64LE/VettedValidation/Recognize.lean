module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Record
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! ### `Ffdh.PPC64LE.VettedValidation.Scan`, which only this module used -/

section

/-! The finite scan returns the same recognition result as the shared pure table. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem return_ok (s : State) (n : Nat) (fit : n < 2 ^ 15) :
    WP isa (.block [.li .r8 n]) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  exact VG.Proof.RsaPkcs1Sig.PPC64LE.wp_li fit fun t o value =>
    VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨value, o.mem,
      (show Keep [.r8] s t from ⟨o.gpr, o.rd, o.wr⟩).mono (by decide)⟩

theorem scan_ok {src table : Addr} {k : Nat} {dom : List Byte}
    (gs : List Group) (offset : Nat) (s : State)
    (h : Context src k dom s) (sym : s.syms tableSym = table)
    (data : TableAt (table + BitVec.ofNat 64 offset) gs s)
    (fit : offset + (gs.flatMap Group.bytes).length ≤ 17744) :
    WP isa (scan gs offset) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (recognizeList gs k dom) ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  induction gs generalizing offset s with
  | nil => exact return_ok s 0 (by decide)
  | cons g gs ih =>
    have total : ((g :: gs).flatMap Group.bytes).length =
        8 + 3 * g.len + (gs.flatMap Group.bytes).length := by
      rw [List.flatMap_cons, List.length_append, VG.Proof.Ffdh.VettedTableFacts.groupBytes_length]
    rw [scan, WP.seq_iff]
    refine WP.mono_syms (record_ok h g sym data.1 (by rw [total] at fit; omega_arith)) ?_
    rintro u ⟨zero, memU, restU⟩ symU
    refine WP.ite (decide (g.len = k ∧ dom = g.domain.take dom.length))
      (by
        rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_zero]
        congr 1
        exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq, decide_eq_true_eq] using zero)) ?_ ?_
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
        omega_arith
      rw [ptr] at tail
      refine WP.mono (ih (offset + 8 + 3 * g.len) u (h.after memU restU)
        (by rw [symU]; exact sym) tail (by rw [total] at fit; omega_arith)) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa only [recognizeList, ite_eq_right (of_decide_eq_false miss)] using value,
        memT.trans memU, keep_trans restU restT⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation

end

end


/-! The read-only prefix restores LR and preserves the original domain arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

def allClobbers : List Reg := .r12 :: clobbers

def recognized (s : State) : BitVec 64 :=
  BitVec.ofNat 64 (recognizeList groups (s.gpr .r5).toNat (domain s))

structure Result (s t : State) : Prop where
  value : t.gpr .r8 = recognized s
  mem : t.mem = s.mem
  keep : Keep allClobbers s t
  lr : t.lr = s.lr

theorem recognize_ok {s : State} (h : contract.pre s) :
    WP isa recognize s fun t => Result s t := by
  have input := context h
  have table := consts_table (pre_plain h).2
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  rw [recognize, WP.seq_iff]
  refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
    (Q := fun u : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s u ∧ u.gpr .r12 = s.lr)
    (fun u o saved => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨o, saved⟩)) ?_
  rintro u ⟨only, saved⟩ symU
  rw [WP.seq_iff]
  refine WP.mono (scan_ok (src := s.gpr .r3) (table := s.syms tableSym)
    (k := (s.gpr .r5).toNat) (dom := domain s) groups 0 u ?_ ?_ ?_ fit) ?_
  · exact ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
      (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
      by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
  · rw [symU]
  · have after := table.after only.mem (show Keep [.r12] s u from ⟨only.gpr, only.rd, only.wr⟩)
    rw [symU] at *
    simpa only [BitVec.add_zero] using after
  · rintro v ⟨value, memV, restV⟩
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mtlr fun w regs memW rdW wrW spW lrW =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨by rw [regs, value]; rfl,
        memW.trans (memV.trans only.mem), ?_, by rw [lrW, restV.gpr (by decide), saved]⟩
    refine ⟨?_, rdW.trans (restV.2.1.trans only.rd), wrW.trans (restV.2.2.trans only.wr)⟩
    intro r hr
    rw [regs, restV.gpr (by intro hc; exact hr (List.mem_cons_of_mem _ hc)),
      only.gpr r (by simpa only [allClobbers, List.mem_cons, List.not_mem_nil, or_false] using
        (fun eq : r = .r12 => hr (by rw [eq]; exact List.mem_cons_self))) ]

end VG.Proof.Ffdh.PPC64LE.VettedValidation
