module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! # The complete prepared sieve computes the specified compositeness filter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem body_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) (large : 8161 < c) :
    WP isa (body stackSlots g.w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
      Frame (setupWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  have run := WP.seq (WP.mono (setup_ok v C pointer length symbol low candidateFar tableFar)
    fun u ⟨U, F, K₀⟩ => WP.mono (loop_ok v U) fun t ⟨value, O, K⟩ =>
      (show t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * g.w) c).toNat ∧
        Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t from by
        refine ⟨?_, F.trans (setupFrame_stack (outsideStack_frame O)), (K₀.mono (by decide)).trans K⟩
        rw [length, tableCount, VG.Proof.RsaKeyGen.trialPrefix_spec large] at value
        exact value))

  exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc run)) fun a H => WP.assoc H)

end VG.Proof.RsaKeyGen.X86.Sieve
