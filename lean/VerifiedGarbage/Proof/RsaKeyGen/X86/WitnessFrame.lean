module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry

/-! # Per-witness products retain the candidate's reusable prepared values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessMont
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def ranges (g : Geometry) : List (Nat × Nat) := montWrites g 6 ++ [(g.array 5, 4 * g.words)]

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega))
  intro r mem
  simp only [ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl | rfl | rfl <;>
    rcases mem with (rfl | rfl | rfl) | rfl <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega

theorem marker_preserve {g : Geometry} (v : g.Valid) {s t : Mem}
    (F : WorkspaceFrame g (ranges g) s t) :
    word t g.W (g.array 27 + 8 * g.w) = word s g.W (g.array 27 + 8 * g.w) := by
  apply F.read64 (by have := Prepared.paddedFit v (j := 27) (by decide); omega)
  intro r mem
  simp only [ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with (rfl | rfl | rfl) | rfl <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega

theorem data_keep {g : Geometry} (v : g.Valid) {s t : VG.X86.State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) (T : PreparedR2.Ready g c capacity p t)
    (F : WorkspaceFrame g (ranges g) s.mem t.mem) : Prepare.Data g c capacity p t :=
  ⟨T, (preserve v F (Or.inl rfl)).trans S.r2,
    (preserve v F (Or.inr (Or.inl rfl))).trans S.one,
    (preserve v F (Or.inr (Or.inr (Or.inl rfl)))).trans S.minusOne,
    (preserve v F (Or.inr (Or.inr (Or.inr rfl)))).trans S.exponent,
    (marker_preserve v F).trans S.marker, (F.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | rfl <;>
        exact Or.inl (by simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega))).trans S.stride⟩

theorem data_outside {g : Geometry} (v : g.Valid) {s t : VG.X86.State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) (O : Outside g.W (g.array 6) (4 * g.words) s.mem t.mem)
    {regs : List VG.X86.Reg} (K : VG.Proof.Mont.X86.Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) : Prepare.Data g c capacity p t := by
  have A := S.ready
  have outs := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs A.scratch.nowrap outs
  have T : PreparedR2.Ready g c capacity p t :=
    ⟨A.context.keepOutside K base O (v.arrayHeader _),
      A.modulus.keep v F
        (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 6; omega))
        (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide))),
      A.caller.keepOuts K sp outs
        (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide)),
      A.scratch.of_keeps K base sp⟩
  apply data_keep v S T
  exact WorkspaceFrame.of_outs A.scratch.nowrap (Outs.of_outside
    (O.mono (o' := g.array 6) (n' := 8 * (g.w + 2)) (Nat.le_refl _) (by unfold Geometry.words; omega)) (by simp [ranges, montWrites]))

end VG.Proof.RsaKeyGen.X86.WitnessMont
