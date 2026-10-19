module

public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Dsa.X86.HeaderFrame
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer

/-! # Installing a list of stack arguments into distinct persistent fields -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem saveArguments_ok (args : List (Nat × Field)) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (distinct : (args.map Prod.snd).Nodup)
    (inputs : ∀ a ∈ args, StackArgument s base size a.1) :
    WP isa (.block (Entry.saveArguments args)) s fun t =>
      (∀ a ∈ args, pointerValue base t (.input a.2) = stackValue s a.1) ∧
      (∀ f, f ∉ args.map Prod.snd → pointerValue base t (.input f) = pointerValue base s (.input f)) ∧
      Keeps [.eax] s t ∧ Outside base 8192 64 s.mem t.mem := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨by simp, by simp, Keeps.refl _ _, Outside.refl _ _ _ _⟩
  | cons a args ih =>
    have D : a.2 ∉ args.map Prod.snd ∧ (args.map Prod.snd).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    have A := inputs a List.mem_cons_self
    have B := VG.Proof.Dsa.X86.Layout.field_bounds a.2
    have hi : Layout.field a.2 + 4 ≤ 8256 := B.2
    change WP isa (.block (Entry.saveArgument a.1 a.2 ++ Entry.saveArguments args)) s _
    refine WP.block_append (WP.mono (saveArgument_ok a.2 hs hz A.readSrc) fun u ⟨V, K, O⟩ => ?_)
    have Oheader : Outside base 8192 64 s.mem u.mem := O.mono B.1 (by omega)
    have Owhole : Outside base 0 size s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
    refine WP.mono (ih (hs.of_keeps K (by decide)) D.2
      (fun b hb => (inputs b (List.mem_cons_of_mem _ hb)).keep K (by decide))) fun t ⟨Values, Other, Keep, Frame⟩ => ?_
    refine ⟨?_, ?_, K.trans Keep, Oheader.trans Frame⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [Other b.2 D.1, V]
      · rw [Values b hb]
        exact (inputs b (List.mem_cons_of_mem _ hb)).value_keep K (by decide) Owhole
    · intro f hf
      have H : f ≠ a.2 ∧ f ∉ args.map Prod.snd := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hf
      rw [Other f H.2]
      exact field_keep O H.1

end VG.Proof.Dsa.X86
