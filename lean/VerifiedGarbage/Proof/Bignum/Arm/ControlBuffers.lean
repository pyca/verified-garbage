module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState

/-! # Preserve the public layout across writes to control slots and external buffers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (Layout wordAt wOf)

theorem outs_readW {m m' : Mem} {base : Addr} {ranges : List (Nat × Nat)}
    {d bits : Nat} (h : Outs base ranges m m')
    (sep : ∀ r ∈ ranges, d + bits / 8 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (fit : d + bits / 8 ≤ 2 ^ 64) : m'.readW (off base d) bits = m.readW (off base d) bits := by
  apply Mem.readW_congr
  intro i hi
  apply h
  intro r hr
  rw [ofs_off base (by omega)]
  have := sep r hr
  omega

theorem CrtLayoutState.of_header_eq {base : BitVec 32} {len w : Nat} {m m' : Mem}
    (h : CrtLayoutState base len w m) (eq : WorkspaceEq (State.addr base) 128 m m') :
    CrtLayoutState base len w m' := by
  have width := eq.width (by decide)
  refine ⟨?_, width.trans h.width⟩
  unfold Layout
  rw [width]
  refine ⟨h.layout.1, h.layout.2.1, h.layout.2.2.1, ?_⟩
  intro j hj
  unfold wordAt
  rw [eq.word (bits := 64) (by simp only [Proof.Rsa.Mont.arrWord]; omega)]
  exact h.layout.2.2.2 j hj

theorem control_buffers_header {base : Addr} {m m' : Mem} {ranges : List (Nat × Nat)}
    (h : Outs base ranges m m') (lower : ∀ r ∈ ranges, 128 ≤ r.1) : WorkspaceEq base 128 m m' := by
  refine ⟨fun d k hk => Mem.read_congr ?_⟩
  intro i hi
  apply h
  intro r hr
  rw [ofs_off base (by omega)]
  have := lower r hr
  omega

end VG.Proof.Bignum.Arm
