module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorBody
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeSlice

/-! # One complete h-tape chunk advances the exact generator-search invariant -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generator_body_frame {P : GeneratorSearchPlan} {s t : Mem}
    (O : Frame [⟨P.core.base, P.core.size⟩, ⟨P.core.witness.setWidth 64, P.core.len⟩,
      ⟨off P.frame 76, 4⟩, ⟨(generatorOutputPointer P.parent).setWidth 64, P.core.len⟩] s t) :
    Frame P.changed s t := by
  apply O.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨P.core.base, P.core.size⟩, by simp [GeneratorSearchPlan.changed, generatorSearchWrites], fun _ h => h⟩
  · exact ⟨⟨P.core.witness.setWidth 64, P.core.len⟩, by simp [GeneratorSearchPlan.changed, generatorSearchWrites], fun _ h => h⟩
  · exact ⟨⟨P.frame, frameBytes⟩, by simp [GeneratorSearchPlan.changed, generatorSearchWrites],
      Offset.sub_base _ (by unfold frameBytes; decide)⟩
  · exact ⟨⟨(generatorOutputPointer P.parent).setWidth 64, P.core.len⟩, by simp [GeneratorSearchPlan.changed, generatorSearchWrites], fun _ h => h⟩

theorem generator_search_step {P : GeneratorSearchPlan} {expected : Option Nat} {initial : State}
    {used : Nat} {s t : State} {W : Nat → BitVec 32}
    (I : GeneratorInvariant P expected initial used s) (room : used + P.core.len ≤ P.tape.length)
    (rep : FrameWords s.mem P.frame W)
    (repT : FrameWords t.mem P.frame
      (frameUpdate (frameUpdate W 21 (W 11 + BitVec.ofNat 32 used)) 20 (BitVec.ofNat 32 (used + P.core.len))))
    (O : Outside P.frame 0 frameBytes s.mem t.mem) (K : Keeps [.eax, .ecx] s t) :
    WP isa (generatorBody P.core.len) t fun u => ∃ W', SearchFrame u P.frame ∧ FrameWords u.mem P.frame W' ∧
      (if W' 19 = 3 then GeneratorInvariant P expected initial (used + P.core.len) u
        else GeneratorFinished P expected initial u) := by
  obtain ⟨Wi, Ri, _, remaining, Oi, rd, wr⟩ := I
  have R := Ri.relabel rep
  let Wt := frameUpdate (frameUpdate W 21 (W 11 + BitVec.ofNat 32 used)) 20 (BitVec.ofNat 32 (used + P.core.len))
  have Rt : GeneratorSearchMemory P Wt t := R.control repT (by
    intro i _ hx
    have n20 : i ≠ 20 := by intro eq; subst i; simp at hx
    have n21 : i ≠ 21 := by intro eq; subst i; simp at hx
    simp only [Wt, frameUpdate, ite_eq_right n20, ite_eq_right n21]) O (Nat.le_refl _) K (by decide)
  have ptr : Wt 21 = P.tapePtr + BitVec.ofNat 32 used := by
    change W 11 + BitVec.ofNat 32 used = _
    rw [R.fixed 11 (by decide) (by decide), P.savedTape]
  have positive : 0 < P.core.len := by have := P.core.lenMin; omega
  have bytes : Spec.Rsa.bytesAt t.mem ((Wt 21).setWidth 64) P.core.len = (P.tape.drop used).take P.core.len := by
    rw [ptr, tape_slice P.tapeBounds room positive, Rt.tapeValue]
  refine WP.mono (generatorBody_ok P.layout Rt.prepared Rt.layout Rt.representation
    ((Rt.fixed 5 (by decide) (by decide)).trans P.savedParent) P.base
    (by rw [ptr]; exact tape_pointer_fit P.tapeBounds room positive)
    (by intro d hd; rw [ptr]; exact tape_slice_read P.tapeBounds room positive Rt.tapeRead hd)
    (by
      rw [ptr]
      exact (P.tapeSeparate ⟨P.core.base, P.core.size⟩ (by simp [generatorSearchWrites])).sub_left
        (tape_slice_sub P.tapeBounds room positive)) Rt.exponentRead Rt.outputWrite)
    fun u ⟨ready, Fu, Wu, output, Ou, Ku⟩ => ?_
  rw [bytes, Rt.exponentValue] at Wu output
  change FrameWords u.mem P.frame (frameUpdate Wt 19 (if P.accepts used then 1 else 3)) at Wu
  change P.accepts used → Spec.Rsa.bytesAt u.mem ((generatorOutputPointer P.parent).setWidth 64) P.core.len =
    Spec.Dsa.encodeBE P.core.len (P.value used) at output
  have frameU := generator_body_frame (P := P) Ou
  have Ru := Rt.frame ready.prepared Wu (by
    intro i _ hx
    have ne : i ≠ 19 := by intro eq; subst i; simp at hx
    simp only [frameUpdate, ite_eq_right ne]) frameU Ku (by decide)
  have whole := (Oi.trans (generator_search_frame O (Nat.le_refl _))).trans frameU
  have rdU := Ku.2.1.trans (K.2.1.trans rd)
  have wrU := Ku.2.2.trans (K.2.2.trans wr)
  refine ⟨_, Fu, Wu, ?_⟩
  by_cases good : P.accepts used
  · rw [show frameUpdate Wt 19 (if P.accepts used then 1 else 3) 19 = 1 by simp only [frameUpdate, ite_true, ite_eq_left good]]
    rw [ite_eq_right (by decide : (1 : BitVec 32) ≠ 3)]
    refine ⟨_, Ru, Or.inr ⟨P.value used, ?_, ?_, output good⟩, whole, rdU, wrU⟩
    · simp only [frameUpdate, ite_true, ite_eq_left good]
    · rw [P.remaining_step room, ite_eq_left good] at remaining
      exact remaining
  · rw [show frameUpdate Wt 19 (if P.accepts used then 1 else 3) 19 = 3 by simp only [frameUpdate, ite_true, ite_eq_right good], ite_eq_left rfl]
    refine ⟨_, Ru, ?_, ?_, whole, rdU, wrU⟩
    · rfl
    · rw [P.remaining_step room, ite_eq_right good] at remaining
      exact remaining
end VG.Proof.Dsa.X86.Generation
