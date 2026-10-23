module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # A nested prepared round retains the caller's length argument -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def lengthRegion (p : BitVec 32) : Region := ⟨(p + 24#32).setWidth 64, 4⟩

structure Caller (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop where
  sp : s.gpr .esp = p
  low : 80 ≤ p.toNat
  stackFar : (⟨g.W, g.L⟩ : Region).Disjoint (below p 80)
  lengthFar : (lengthRegion p).Disjoint ⟨g.W, g.L⟩
  lengthStackFar : (lengthRegion p).Disjoint (below p 80)
  readLen : readSrc s (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity)

theorem Caller.keepFrame {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (C : Caller g capacity p s) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem) : Caller g capacity p t := by
  have spT : t.gpr .esp = p := (K.1 .esp sp).trans C.sp
  refine ⟨spT, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  have same : readSrc t (.mem (at_ .esp 24)) = readSrc s (.mem (at_ .esp 24)) := by
    show t.load32 (t.ea (at_ .esp 24)) = s.load32 (s.ea (at_ .esp 24))
    have eaS : s.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [C.sp]
      rfl
    have eaT : t.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (t.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [spT]
      rfl
    simp only [State.load32, eaT, eaS, K.2.1, K.2.2]
    congr 1
    apply congrArg some
    apply F.readW (r := lengthRegion p) (Region.contains_self _ _) ?_ (by decide)
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact C.lengthFar
    · exact C.lengthStackFar
  exact same.trans C.readLen

theorem workspaceGlobalFrame {g : Geometry} {rs : List (Nat × Nat)} {m m' : Mem}
    (O : Outs g.W rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ g.L) :
    Frame [⟨g.W, g.L⟩] m m' := by
  intro x outside
  have nc := outside _ (List.mem_singleton_self _)
  have bound : g.L ≤ ofs g.W x := by
    by_contra bad
    apply nc
    change ofs g.W x + 1 ≤ g.L
    omega
  apply O
  intro r mem
  exact Or.inr (Nat.le_trans (fit r mem) bound)

theorem Caller.keepOuts {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (C : Caller g capacity p s) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    {rs : List (Nat × Nat)} (O : Outs g.W rs s.mem t.mem) (fit : ∀ r ∈ rs, r.1 + r.2 ≤ g.L) :
    Caller g capacity p t := by
  apply C.keepFrame K sp
  apply (workspaceGlobalFrame O fit).sub
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), fun _ h => h⟩

end VG.Proof.MillerRabin.X86
