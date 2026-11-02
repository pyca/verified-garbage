module

public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # Montgomery's reviewed write footprint preserves prepared round data -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def montWrites (g : Geometry) (out : Nat) : List (Nat × Nat) :=
  [(g.array 2, 8 * (g.w + 2)), (g.array 3, 8 * (g.w + 2)), (g.array out, 8 * (g.w + 2))]

theorem montFrame {g : Geometry} {out capacity : Nat} {m m' : Mem}
    (length : g.L = 8 * capacity)
    (K : Proof.Rsa.Mont.Keeps g.W capacity g.w out m m') :
    WorkspaceFrame g (montWrites g out) m m' := by
  intro i hi apart
  apply K i (by omega)
  intro j mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact apart (g.array 2, 8 * (g.w + 2)) (by simp [montWrites])
  · exact apart (g.array 3, 8 * (g.w + 2)) (by simp [montWrites])
  · exact apart (g.array j, 8 * (g.w + 2)) (by simp [montWrites])

theorem Context.keepMont {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    (wr : t.wr = s.wr) (base : t.gpr .edi = s.gpr .edi) {out : Nat}
    (O : WorkspaceFrame g (montWrites g out) s.mem t.mem) : Context g t := by
  have hdr := v.headerFit
  have H : ∀ {d : Nat}, d + 4 ≤ 256 → w32 t.mem g.W d = w32 s.mem g.W d := by
    intro d fit
    apply congrArg BitVec.toNat
    apply O.read32 (by omega)
    intro r mem
    simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> exact Or.inl (Nat.le_trans fit (v.arrayHeader _))
  refine ⟨C.ws.of_wr wr, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, base]; exact C.base
  · rw [H (by decide)]; exact C.width
  · rw [H (by decide)]; exact C.stride
  · intro j index
    rw [H (by omega)]; exact C.pointers j index

theorem Modulus.keepMont {g : Geometry} (v : g.Valid) {c : Nat} {m m' : Mem}
    (M : Modulus g c m) {out : Nat} (notMod : 0 < out)
    (O : WorkspaceFrame g (montWrites g out) m m') : Modulus g c m' := by
  refine M.keep v O ?_ ?_
  · intro r mem
    simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader 2))
    · exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader 3))
    · exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader out))
  · intro r mem
    simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact Or.inl (g.arrayBefore (by decide : 0 < 2))
    · exact Or.inl (g.arrayBefore (by decide : 0 < 3))
    · exact Or.inl (g.arrayBefore notMod)

end VG.Proof.MillerRabin.X86
