module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCandidateSlots
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! ### `RsaKeyGen.X86.SieveTableSlots`, which only this module used -/

section

/-! # Initialize the static cursor, public table length and hit word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem tableSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : CandidateReady g c s)
    (length : g.limit = tableCount g.w) (pointer : s.gpr .eax = g.table) :
    WP isa (.block (tableSlots stackSlots g.w)) s fun t =>
      StateAt g c 0 g.limit t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (slot 8) .eax] ++ ([.mov .eax (.imm (BitVec.ofNat 32 (tableCount g.w))),
    .store (slot 12) .eax] ++ [.mov .eax (.imm 0), .store (slot 16) .eax]))) s _
  refine WP.block_append (WP.mono (C.context.stack.store 8 (by decide) .eax) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (WP.mono (Ca.literal 12 (by decide) (BitVec.ofNat 32 (tableCount g.w)))
    fun b ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  refine WP.mono (Cb.literal 16 (by decide) 0#32) fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = ((s.mem.writeW (off (g.sp.setWidth 64) 8) g.table).writeW
      (off (g.sp.setWidth 64) 12) (BitVec.ofNat 32 g.limit)).writeW (off (g.sp.setWidth 64) 16) 0#32 := by
    rw [Mt, Mb, Ma, pointer, ← length]
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem :=
    ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := ((Ka.mono (by decide)).trans Kb).trans Kt
  refine ⟨⟨C.context.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_, ?_, ?_⟩, outside, keep⟩
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.candidate
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.ending
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    unfold Geometry.cursor
    rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Sieve

end

end


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
