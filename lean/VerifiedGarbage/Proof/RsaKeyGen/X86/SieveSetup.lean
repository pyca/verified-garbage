module

import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveTableSlots
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! # The static-address prefix establishes all sieve-loop preconditions -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def setupWrites (g : Geometry) : List Region := [g.stackRegion, below g.sp 4]

theorem setupFrame_stack {g : Geometry} {m m' : Mem} (F : Frame [g.stackRegion] m m') :
    Frame (setupWrites g) m m' := by
  apply F.sub
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

theorem setupFrame_symbol {g : Geometry} {m m' : Mem} (F : Frame [below g.sp 4] m m') :
    Frame (setupWrites g) m m' := by
  apply F.sub
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

theorem setup_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) (length : g.limit = tableCount g.w)
    (symbol : s.syms TrialTable32.symbol = g.table) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    WP isa (.seq (.block (candidateSlots stackSlots g.w)) (.seq tableAddress (.block (tableSlots stackSlots g.w)))) s
      fun t => StateAt g c 0 g.limit t ∧ Frame (setupWrites g) s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  refine WP.seq (WP.mono_syms (candidateSlots_ok v C pointer) fun a ⟨A, Oa, Ka⟩ Sa => ?_)
  refine WP.seq (WP.mono (symFrame_ok TrialTable32.symbol a (by rw [A.context.stack.sp]; exact low)) fun b R => ?_)
  have B : CandidateReady g c b :=
    ⟨A.context.keepSymbol v R candidateFar tableFar,
      (symbol_stack_word A.context R low (by decide : 0 + 4 ≤ 20)).trans A.candidate,
      (symbol_stack_word A.context R low (by decide : 4 + 4 ≤ 20)).trans A.ending⟩
  have address : b.gpr .eax = g.table := by rw [R.addr, Sa]; exact symbol
  have symbolFrame : Frame [below g.sp 4] a.mem b.mem := by rw [← A.context.stack.sp]; exact R.frame
  have Kb : Keeps [.eax, .ecx] a b := ⟨R.gpr, R.rd, R.wr⟩
  refine WP.mono (tableSlots_ok v B length address) fun t ⟨T, Ot, Kt⟩ => ?_
  exact ⟨T, ((setupFrame_stack (outsideStack_frame Oa)).trans (setupFrame_symbol symbolFrame)).trans
    (setupFrame_stack (outsideStack_frame Ot)), ((Ka.mono (by decide)).trans Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.Sieve
