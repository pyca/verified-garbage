module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset

/-! # Workspace-local frames allow calls to use their own stack -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

/-- Listed workspace ranges may change; callable operations separately
specify the frame of their stack writes. -/
def WorkspaceFrame (g : Geometry) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < g.L, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) → m' (off g.W i) = m (off g.W i)

theorem WorkspaceFrame.refl (g : Geometry) (rs : List (Nat × Nat)) (m : Mem) :
    WorkspaceFrame g rs m m := fun _ _ _ => rfl

theorem WorkspaceFrame.trans {g : Geometry} {rs : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}
    (a : WorkspaceFrame g rs m₁ m₂) (b : WorkspaceFrame g rs m₂ m₃) :
    WorkspaceFrame g rs m₁ m₃ := fun i hi hr => (b i hi hr).trans (a i hi hr)

theorem WorkspaceFrame.mono {g : Geometry} {rs rs' : List (Nat × Nat)} {m m' : Mem}
    (a : WorkspaceFrame g rs m m') (included : ∀ r ∈ rs, r ∈ rs') :
    WorkspaceFrame g rs' m m' := fun i hi hr => a i hi fun r mem => hr r (included r mem)

theorem WorkspaceFrame.cover {g : Geometry} {rs rs' : List (Nat × Nat)} {m m' : Mem}
    (a : WorkspaceFrame g rs m m')
    (included : ∀ r ∈ rs, ∃ R ∈ rs', R.1 ≤ r.1 ∧ r.1 + r.2 ≤ R.1 + R.2) :
    WorkspaceFrame g rs' m m' := by
  intro i hi outside
  apply a i hi
  intro r mem
  obtain ⟨R, known, lower, upper⟩ := included r mem
  have := outside R known
  omega

theorem WorkspaceFrame.of_outs {g : Geometry} {rs : List (Nat × Nat)} {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (a : Outs g.W rs m m') :
    WorkspaceFrame g rs m m' := by
  intro i hi hr
  apply a
  intro r mem
  rw [ofs_off0 g.W (by omega)]
  exact hr r mem

theorem WorkspaceFrame.read32 {g : Geometry} {rs : List (Nat × Nat)} {m m' : Mem}
    (a : WorkspaceFrame g rs m m') {d : Nat} (fit : d + 4 ≤ g.L)
    (apart : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply Mem.readW_congr
  intro i hi
  have step : off g.W d + BitVec.ofNat 64 i = off g.W (d + i) := by
    unfold off
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [step]
  apply a (d + i) (by omega)
  intro r mem
  have := apart r mem
  omega

theorem WorkspaceFrame.read64 {g : Geometry} {rs : List (Nat × Nat)} {m m' : Mem}
    (a : WorkspaceFrame g rs m m') {d : Nat} (fit : d + 8 ≤ g.L)
    (apart : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) :
    m'.readW (off g.W d) 64 = m.readW (off g.W d) 64 := by
  apply Mem.readW_congr
  intro i hi
  have step : off g.W d + BitVec.ofNat 64 i = off g.W (d + i) := by
    unfold off
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [step]
  apply a (d + i) (by omega)
  intro r mem
  have := apart r mem
  omega

theorem WorkspaceFrame.val32 {g : Geometry} {rs : List (Nat × Nat)} {m m' : Mem}
    (a : WorkspaceFrame g rs m m') {d n : Nat} (fit : d + 4 * n ≤ g.L)
    (apart : ∀ r ∈ rs, d + 4 * n ≤ r.1 ∨ r.1 + r.2 ≤ d) :
    val32 m' g.W d n = val32 m g.W d n := by
  apply val32_congr
  intro i hi
  apply congrArg BitVec.toNat
  apply a.read32 (by omega)
  intro r mem
  have := apart r mem
  omega

end VG.Proof.MillerRabin.X86
