module

public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.MillerRabin.Contract

/-! # The round's write footprint is within the reviewed compact contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

def roundWrites (g : Geometry) : List (Nat × Nat) :=
  [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8),
    (g.array 2, 16 * (g.w + 2)), (g.array 5, 16 * (g.w + 2)),
    (g.array 8, 8 * (g.w + 2)), (g.array 11, 128 * (g.w + 2))]

theorem roundFrame_keeps {g : Geometry} {capacity : Nat} {m m' : Mem}
    (length : g.L = 8 * capacity) (F : WorkspaceFrame g (roundWrites g) m m') :
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact g.W capacity g.w m m' := by
  intro i index header arrays table
  apply F i (by omega)
  intro r mem
  simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
  have h1 := header 1 (by decide)
  have h23 := header 23 (by decide)
  have h26 := header 26 (by decide)
  have h29 := header 29 (by decide)
  have h30 := header 30 (by decide)
  have a2 := arrays 2 (by decide)
  have a3 := arrays 3 (by decide)
  have a5 := arrays 5 (by decide)
  have a6 := arrays 6 (by decide)
  have a8 := arrays 8 (by decide)
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h23
  · exact h26
  · exact h29
  · exact h30
  · dsimp only
    unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes at *
    omega
  · dsimp only
    unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes at *
    omega
  · exact a8
  · change i < g.array 11 ∨ g.array 11 + 128 * (g.w + 2) ≤ i
    have endOffset : g.array 11 + 128 * (g.w + 2) = g.array 27 := by
      unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes
      omega
    rw [endOffset]
    exact table

end VG.Proof.MillerRabin.X86
