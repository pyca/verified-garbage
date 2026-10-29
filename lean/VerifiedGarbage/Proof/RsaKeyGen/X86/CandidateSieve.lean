module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup

import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
/-! # Native sieve setup and cleanup preserve the workspace pointer and candidate -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveBody.lean`, which only this module imported.
section

/-! # The complete prepared sieve computes the specified compositeness filter -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem body_full_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body stackSlots g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate := by
  have run := WP.seq (WP.mono (setup_ok v C pointer length symbol low candidateFar tableFar)
    fun u ⟨U, F, K₀⟩ => WP.mono (loop_full_ok v U) fun t ⟨value, O, K, candidate⟩ =>
      (show t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
        Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
          t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate from by
        refine ⟨?_, F.trans (setupFrame_stack (outsideStack_frame O)), (K₀.mono (by decide)).trans K, candidate⟩
        rw [length, tableCount, VG.Proof.RsaKeyGen.trialPrefix_spec large] at value
        exact value))

  exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc run)) fun a H => WP.assoc H)

theorem body_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body stackSlots g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t :=
  WP.mono (body_full_ok v C pointer length symbol low candidateFar tableFar large)
    fun _ ⟨result, F, K, _⟩ => ⟨result, F, K⟩

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.CandidateSieve

theorem body_ok {g : Sieve.Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Sieve.Context g c s)
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (Sieve.setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold body setup
  refine WP.seq (wp_addS rfl fun a A _ => WP.block_nil ?_)
  have Ca : Sieve.Context g c a := by
    refine ⟨C.stack.keep A.keeps (by decide), ?_, ?_, ?_, ?_⟩
    · intro i index; rw [A.keeps.2.1, A.keeps.2.2]; exact C.candidateRead i index
    · intro i index d mem; rw [A.keeps.2.1, A.keeps.2.2]; exact C.tableRead i index d mem
    · intro i index; rw [A.mem]; exact C.tableWords i index
    · rw [A.mem]; exact C.candidateValue
  refine WP.seq (WP.mono (Sieve.body_full_ok v Ca (A.gpr.trans pointer) length
    (by rw [A.syms]; exact symbol) low candidateFar tableFar large) fun b ⟨result, F, Kb, saved⟩ => ?_)
  have Cb := Ca.stack.keep Kb (by decide)
  unfold restore
  refine wp_movS (v := g.candidate) (by
    change readSrc b (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some g.candidate
    rw [Cb.read 0 (by decide), saved]) fun d D _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t :=
    (((A.keeps.mono (by decide)).trans Kb).widen D.keeps).widen T.keeps
  have edi : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, D.gpr, ← pointer]
    change s.gpr .edi + 256#32 - 256#32 = s.gpr .edi
    exact BitVec.add_sub_cancel _ _
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
    refine ⟨?_, all.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact edi
    · exact all.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, K⟩
  · rw [T.other .eax (by decide), D.other .eax (by decide)]; exact result
  · rw [A.mem] at F
    rw [T.mem, D.mem]
    exact F

theorem code_ok {g : Sieve.Geometry} (v : g.Valid) {c : Nat} {s : State}
    (C : Sieve.Context g c (allocFrame 20 s)) (fit : 20 ≤ (s.gpr .esp).toNat)
    (pointer : s.gpr .edi + 256#32 = g.candidate) (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (code g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (Sieve.setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold code
  refine WP.frameAlloc (by decide) (by decide) (by decide) fit (NoSp.of_all (by rfl)) ?_
  refine WP.mono (body_ok v C (by rw [allocFrame_gpr _ _ (by decide)]; exact pointer)
    length symbol low candidateFar tableFar large) fun t ⟨result, F, K⟩ => ?_
  exact ⟨by rw [freed_gpr _ _ (by decide)]; exact result, F, FilterStack.freed_keeps K (by decide)⟩

end VG.Proof.RsaKeyGen.X86.CandidateSieve
