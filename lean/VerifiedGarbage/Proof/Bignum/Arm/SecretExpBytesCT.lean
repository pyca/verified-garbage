module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpByteState
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpByteCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The private exponent loop reveals only public buffer dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem secretExpBytes_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (positive : 0 < eb1.length) (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => ExpByteState base ep len w M1 x1 eb1 0 s ∧
      ExpByteState base ep len w M2 x2 eb2 0 t ∧ s.sp = t.sp) secretExpBytes (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    ExpByteState base ep len w M1 x1 eb1 j s ∧ ExpByteState base ep len w M2 x2 eb2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq secretExpBits (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have hj : j < eb1.length := by omega
    have hj2 : j < eb2.length := by omega
    have ct := relCT_keep_sp (secretExpByte_ct (base := base) (ep := ep + BitVec.ofNat 32 j)
      (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E1 := pre eb1 j) (E2 := pre eb2 j) (b1 := eb1[j]) (b2 := eb2[j]) fit) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs.input hj, ht.input hj2, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1⟩ := secretExpByteState_step s hs hj
    obtain ⟨_, _, run2, next2, zero2⟩ := secretExpByteState_step t ht hj2
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2, length]
    · intro again
      have notLast : j + 1 ≠ eb1.length := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
