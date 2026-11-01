module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # The full exponent loop reveals only public exponent bytes and buffer dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem expBytes_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExpByteState ok base ep len w M1 x1 eb 0 s ∧
      ExpByteState ok base ep len w M2 x2 eb 0 t ∧ s.sp = t.sp) expBytes (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb.length ∧ 0 < k ∧
    ExpByteState ok base ep len w M1 x1 eb j s ∧ ExpByteState ok base ep len w M2 x2 eb j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq expBits (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have hj : j < eb.length := by omega
    have ct := relCT_keep_sp (expByte_ct (ok := ok) (base := base) (ep := ep + BitVec.ofNat 32 j)
      (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := pre eb j) (b := eb[j]) fit) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs.input hj, ht.input hj, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1⟩ := expByteState_step s hs hj
    obtain ⟨_, _, run2, next2, zero2⟩ := expByteState_step t ht hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ eb.length := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  exact (RelCT.loop I step eb.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.ConditionalExp
