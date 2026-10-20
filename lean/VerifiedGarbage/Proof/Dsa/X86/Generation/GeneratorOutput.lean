module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorStore
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory

/-! # Publish a generator only after the computed value passes its range check -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorOutput_ok {s : State} {G : PrimeConfig} {frame : Addr}
    {words : Nat → BitVec 32} {parent : BitVec 32} {value : Nat}
    (R : PrimeReady G s) (F : SearchFrame s frame) (W : FrameWords s.mem frame words)
    (saved : words 5 = parent) (power : wordsVal s.mem G.base (slot G.n 6) G.n = value)
    (status : s.gpr .eax = if 1 < value then 1 else 3)
    (frameScratch : Region.Disjoint ⟨frame, frameBytes⟩ ⟨G.base, G.size⟩)
    (fit : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).toNat + G.len ≤ 2 ^ 32)
    (write : ∀ e k, e + k ≤ G.len → InRegions s.wr
      ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64 + BitVec.ofNat 64 e) k)
    (apart : Region.Disjoint
      ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64, G.len⟩ ⟨G.base, G.size⟩)
    (frameOutput : Region.Disjoint ⟨frame, frameBytes⟩
      ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64, G.len⟩) :
    WP isa (.seq (.block [.store (frameSlot 19) .eax]) (onSuccess (generatorStore G.len))) s fun t =>
      PrimeReady G t ∧ SearchFrame t frame ∧
      FrameWords t.mem frame (frameUpdate words 19 (if 1 < value then 1 else 3)) ∧
      (1 < value → Spec.Rsa.bytesAt t.mem
        ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64) G.len = Spec.Dsa.encodeBE G.len value) ∧
      Frame [⟨off frame 76, 4⟩,
        ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.g).setWidth 64, G.len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  refine WP.seq (WP.mono (frameStatusAx_ok F W) fun a ⟨Fa, Wa, Oa, Ka⟩ => ?_)
  rw [status] at Wa
  have frameA := sampleOutside_frame Oa (by decide)
  have scratchApart : ∀ r ∈ [⟨off frame 76, 4⟩], (⟨G.base, G.size⟩ : Region).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact frameScratch.symm.sub_right (Offset.sub_base _ (by unfold frameBytes; decide))
  have Ra := R.frame frameA scratchApart Ka (by decide) (by decide)
  have room : slot G.n 6 + 8 * G.n ≤ G.size := by
    have := slot_bound (n := G.n) (by decide : 6 < 9)
    have := R.context.size_le
    unfold stride at *
    omega
  have powerA : wordsVal a.mem G.base (slot G.n 6) G.n = value := by
    rw [sampleFrame_words frameA (by
      intro r hr
      exact (scratchApart r hr).sub_left (Offset.sub_base _ room))
      (by have := R.context.scr.nowrap; omega), power]
  refine onSuccess_ok Fa Wa ?_ ?_
  · intro b mem Kb good
    have accepted : 1 < value := by
      by_contra bad
      have : (3 : BitVec 32) = 1 := by simpa only [frameUpdate, ite_true, ite_eq_right bad] using good
      exact (by decide : (3 : BitVec 32) ≠ 1) this
    have Rb := Ra.frame (by rw [mem]; exact Frame.refl [] a.mem) (by simp) Kb (by decide) (by decide)
    have Fb := Fa.keeps Kb (by decide)
    have Wb : FrameWords b.mem frame (frameUpdate words 19 (if 1 < value then 1 else 3)) := by rw [mem]; exact Wa
    have parentB : b.mem.readW (off frame 20) 32 = parent := by
      rw [Wb 5 (by decide)]
      exact saved
    have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s b :=
      (Ka.mono (by decide)).trans (Kb.mono (by decide))
    refine WP.mono (generatorStore_ok Rb Fb parentB fit
      (by intro e k hk; rw [Ksb.2.2]; exact write e k hk) apart) fun t ⟨Rt, output, Ot, Kt⟩ => ?_
    rw [mem, powerA] at output
    have frameT := copyOutside_frame Ot
    have frameB : Frame [⟨off frame 76, 4⟩] s.mem b.mem := by rw [mem]; exact frameA
    exact ⟨Rt, Fb.keeps Kt (by decide), Wb.keep frameT (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact frameOutput), fun _ => output,
      (frameB.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans
        (frameT.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)), Ksb.trans Kt⟩
  · intro t mem Kt bad
    have rejected : ¬ 1 < value := by
      intro accepted
      apply bad
      simp only [frameUpdate, ite_true, ite_eq_left accepted]
    exact ⟨Ra.frame (by rw [mem]; exact Frame.refl [] a.mem) (by simp) Kt (by decide) (by decide),
      Fa.keeps Kt (by decide), by rw [mem]; exact Wa,
      fun h => (rejected h).elim, by rw [mem]; exact frameA.mono (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr; simp),
      (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
