module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Scan
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts

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
