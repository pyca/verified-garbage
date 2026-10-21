module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! # Candidate sieve framing releases only the existing trial-divisor pattern -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.CandidateSieve

def Entry (g : Sieve.Geometry) (c : Nat) (s : State) : Prop :=
  Sieve.Context g c s ∧ s.gpr .edi + 256#32 = g.candidate ∧ s.syms TrialTable32.symbol = g.table

theorem setup_ready {g : Sieve.Geometry} {c : Nat} {s : State} (S : Entry g c s) :
    WP isa (.block setup) s (Sieve.Ready g c) := by
  unfold setup
  refine wp_addS rfl fun a A _ => WP.block_nil ?_
  refine ⟨?_, A.gpr.trans S.2.1, ?_⟩
  · refine ⟨S.1.stack.keep A.keeps (by decide), ?_, ?_, ?_, ?_⟩
    · intro i index; rw [A.keeps.2.1, A.keeps.2.2]; exact S.1.candidateRead i index
    · intro i index d mem; rw [A.keeps.2.1, A.keeps.2.2]; exact S.1.tableRead i index d mem
    · intro i index; rw [A.mem]; exact S.1.tableWords i index
    · rw [A.mem]; exact S.1.candidateValue
  · rw [A.syms]; exact S.2.2

theorem setup_trace {g : Sieve.Geometry} {c d : Nat} :
    RelCT isa (fun s t => Entry g c s ∧ Entry g d t) (.block setup)
      (fun s t => Sieve.Ready g c s ∧ Sieve.Ready g d t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block setup)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  exact ⟨(raw _ _ _ _ _ _ A E G).1, wp_result (setup_ready S) E, wp_result (setup_ready T) G⟩

theorem body_trace {g : Sieve.Geometry} (v : g.Valid) {c d : Nat} (pattern : Sieve.SamePattern g c d)
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Entry g c s ∧ Entry g d t) (body g.w)
      (VG.X86.Taint.Agree (τr [.esp])) := by
  unfold body
  exact RelCT.seq setup_trace (RelCT.seq (Sieve.body_trace v pattern length low candidateFar tableFar)
    (checkedBlockInvariant rfl rfl))

theorem code_trace {g : Sieve.Geometry} (v : g.Valid) {c d : Nat} (pattern : Sieve.SamePattern g c d)
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Entry g c (allocFrame 20 s) ∧ Entry g d (allocFrame 20 t))
      (code g.w) (fun _ _ => True) := by
  unfold code
  apply RelCT.frameAlloc
  refine (body_trace v pattern length low candidateFar tableFar).mono ?_ (fun _ _ _ => trivial)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.CandidateSieve
