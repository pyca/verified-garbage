module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryDerived

/-! # The initialized persistent frame contains all public pointers and lengths -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

def initialWords (args W : Nat → BitVec 32) : Nat → BitVec 32 :=
  frameUpdate (derivedWords (incomingWords args W incomingSlots) derivedSlots) 16 0

theorem entryInitialize_ok {base : Addr} {args W : Nat → BitVec 32} {s : State}
    (R : EntryArguments base args s) (words : FrameWords s.mem base W) :
    WP isa (.block (entryIncoming ++ entryDerived)) s fun t => EntryArguments base args t ∧
      FrameWords t.mem base (initialWords args W) ∧
      Frame [⟨base, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.block_append (WP.mono (entryIncomingList_ok incomingSlots R words (by
    intro pair hp
    simp only [incomingSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    fun a ⟨Ra, Wa, Oa, Ka⟩ => ?_)
  exact WP.mono (entryDerived_ok Ra Wa) fun _ ⟨Rt, Wt, Ot, Kt⟩ => ⟨Rt, Wt, Oa.trans Ot, Ka.trans Kt⟩

theorem initialWords_source (args W : Nat → BitVec 32) :
    initialWords args W 5 = args 10 ∧ initialWords args W 6 = args 0 ∧ initialWords args W 7 = args 1 ∧
    initialWords args W 8 = args 4 ∧ initialWords args W 9 = args 5 ∧ initialWords args W 11 = args 6 ∧
    initialWords args W 12 = args 7 ∧ initialWords args W 13 = args 8 ∧ initialWords args W 15 = args 9 ∧
    initialWords args W 17 = args 2 ∧ initialWords args W 18 = args 3 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem initialWords_derived (args W : Nat → BitVec 32) :
    initialWords args W 3 = args 10 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.wrappedSeed ∧
    initialWords args W 4 = args 10 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hashes ∧
    initialWords args W 14 = args 10 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash ∧
    initialWords args W 16 = 0 := ⟨rfl, rfl, rfl, rfl⟩
end VG.Proof.Dsa.X86.Generation
