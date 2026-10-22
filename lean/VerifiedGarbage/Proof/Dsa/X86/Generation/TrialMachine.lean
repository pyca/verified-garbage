module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialPrime
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialLoop
import VerifiedGarbage.Proof.Framework.Offset

/-! Frame values and candidate memory survive every trial-table step. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def trialLoopClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

structure TrialMachine (initial : State) (base : Addr) (size : Nat) (sp : BitVec 32)
    (values : Nat → BitVec 32) (s : State) : Prop where
  frame : TrialFrame sp s
  ws : Rt.Ws s base size
  apart : Region.Disjoint ⟨base, size⟩ ⟨sp.setWidth 64, 36⟩
  memory : Frame [⟨sp.setWidth 64, 36⟩] initial.mem s.mem
  keeps : Keeps trialLoopClob initial s
  slots : ∀ i < 9, trialSlot s.mem sp i = values i

namespace TrialMachine

theorem of_keeps {initial s t : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} {rs : List Reg}
    (h : TrialMachine initial base size sp values s) (K : Keeps rs s t)
    (regs : ∀ r ∈ rs, r ∈ trialLoopClob) (mem : t.mem = s.mem) :
    TrialMachine initial base size sp values t := by
  have K' := K.mono regs
  exact ⟨h.frame.keep K' (by decide), h.ws.of_keeps K', h.apart, mem ▸ h.memory,
    h.keeps.trans K', fun i hi => mem ▸ h.slots i hi⟩

theorem read {initial s : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    {i : Nat} (hi : i < 9) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp (4 * i))) = some (values i) := by
  rw [h.frame.read hi, h.slots i hi]

theorem word {initial s : State} {base : Addr} {size offset : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    (fit : offset + 4 ≤ size) :
    s.mem.readW (off base offset) 32 = initial.mem.readW (off base offset) 32 :=
  h.memory.readW (r := ⟨base, size⟩)
    (Offset.contains_base _ fit (by have := h.ws.nowrap; omega))
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.apart) (by decide)

theorem number {initial s : State} {base : Addr} {size offset n : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    (fit : offset + 4 * n ≤ size) :
    val32 s.mem base offset n = val32 initial.mem base offset n :=
  val32_congr fun j hj => congrArg BitVec.toNat (h.word (by omega))

theorem store {initial s : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    {i : Nat} (hi : i < 9) (r : Reg) :
    WP isa (.block [.store (VG.Impl.Mont.X86.at_ .esp (4 * i)) r]) s fun t =>
      TrialMachine initial base size sp (fun j => if j = i then s.gpr r else values j) t ∧
      Keeps [] s t := by
  refine WP.mono (h.frame.store hi r) ?_
  rintro t ⟨frame, K, mem, value, other⟩
  refine ⟨⟨frame, h.ws.of_keeps K, h.apart, h.memory.trans mem,
    h.keeps.trans (K.mono (by simp)), ?_⟩, K⟩
  intro j hj
  by_cases eq : j = i
  · subst j; simpa only [ite_true] using value
  · rw [ite_eq_right eq, other j hj eq, h.slots j hj]

end TrialMachine
end VG.Proof.Dsa.X86.Generation
