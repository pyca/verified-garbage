module

import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetupTiming
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup

/-! # The complete sieve preserves the candidate contract's timing distinction -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def Ready (g : Geometry) (c : Nat) (s : State) : Prop :=
  Context g c s ∧ s.gpr .edi = g.candidate ∧ s.syms TrialTable32.symbol = g.table

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Ready g c s ∧ Ready g d t)
      (body stackSlots g.w) (VG.X86.Taint.Agree (τr [.esp])) := by
  have setup : RelCT isa (fun s t => Ready g c s ∧ Ready g d t)
      (.seq (.block (candidateSlots stackSlots g.w))
        (.seq tableAddress (.block (tableSlots stackSlots g.w))))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
    intro s t tr ur u z ⟨⟨S, Ps, Ss⟩, ⟨T, Pt, St⟩⟩ E G
    have trace := (setup_trace v low _ _ _ _ _ _ ⟨S, T, Ps, Pt⟩ E G).1
    have U := wp_result (setup_ok v S Ps length Ss low candidateFar tableFar) E
    have Z := wp_result (setup_ok v T Pt length St low candidateFar tableFar) G
    exact ⟨trace, U.1, Z.1⟩
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              have R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

end VG.Proof.RsaKeyGen.X86.Sieve
