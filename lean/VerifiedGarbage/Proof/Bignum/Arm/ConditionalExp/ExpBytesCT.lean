module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # The full exponent loop reveals only public exponent bytes and buffer dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

theorem expBytes_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb : List Byte}
    (K : TwoExp.Montgomery base len w Q regions) (ct : TwoExp.MontgomeryTiming K) (positive : 0 < eb.length)
    (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    RelCT isa (fun s t => (ExpByteState ok base ep len w M1 x1 eb 0 s ∧ Q s) ∧
      (ExpByteState ok base ep len w M2 x2 eb 0 t ∧ Q t) ∧ s.sp = t.sp) (expBytesWith K.op) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb.length ∧ 0 < k ∧
    (ExpByteState ok base ep len w M1 x1 eb j s ∧ Q s) ∧ (ExpByteState ok base ep len w M2 x2 eb j t ∧ Q t) ∧
      s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq (expBitsWith K.op) (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, ⟨hs, qs⟩, ⟨ht, qt⟩, sp⟩ := h
    have hj : j < eb.length := by omega_using [jk, hk]
    have ct' := relCT_keep_sp (expByte_ct (ok := ok) (base := base) (ep := ep + BitVec.ofNat 32 j)
      (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := pre eb j) (b := eb[j]) K ct) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct' s t tr1 tr2 u z ⟨⟨hs.input hj, qs⟩, ⟨ht.input hj, qt⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1⟩ := expByteState_step s K hs qs hj sepR
    obtain ⟨_, _, run2, next2, zero2⟩ := expByteState_step t K ht qt hj sepR
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
      exact ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], next1, next2, sp'⟩
  exact (RelCT.loop I step eb.length).mono
    (fun _ _ h => ⟨0, by omega_using [], positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.ConditionalExp
