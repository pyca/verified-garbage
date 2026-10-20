module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory

/-! # The prime loop cannot modify its witness tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem PrimeReady.unchanged {G : PrimeConfig} {s t : State} {rs : List Reg} (R : PrimeReady G s)
    (mem : t.mem = s.mem) (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) : PrimeReady G t :=
  R.keep (by rw [mem]; exact Frame.refl _ _) K di sp

theorem PrimeFrame.tapeBytes {G : PrimeConfig} {s t : Mem} {start len : Nat}
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s t)
    (fits : start + len ≤ G.tapeLen) :
    Spec.Rsa.bytesAt t (off (G.tape.setWidth 64) start) len =
      Spec.Rsa.bytesAt s (off (G.tape.setWidth 64) start) len := by
  have sub := Offset.sub_base (G.tape.setWidth 64) fits
  apply drawFrame_bytes O ?_ (by have := G.tapeLen32; omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    exact (G.tapeScratch.sub_left sub).sub_right
      (Offset.sub_base _ (primeWrites_bound G.width G.flagRoom item hi))
  · obtain rfl := List.mem_singleton.mp hr
    exact G.tapeWitness.sub_left sub
end VG.Proof.Dsa.X86.Generation
