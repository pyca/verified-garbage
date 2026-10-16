module

public import VerifiedGarbage.Proof.Rsa.Arm.DivArgsCT
public import VerifiedGarbage.Proof.Rsa.Arm.DivShiftArray
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeftCT
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shifting the secret division registers reveals only public dimensions -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm

private def ShiftPublic (g : Geometry) (i : Fin 4) (s : State) : Prop :=
  s.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets i) ∧
  s.gpr .lr = BitVec.ofNat 32 (g.words i)

private theorem array_ct {g : Geometry} {i : Fin 4} :
    RelCT isa (fun s t => ShiftPublic g i s ∧ ShiftPublic g i t)
      VG.Impl.Bignum.Arm.shiftLeft (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨shiftLeft_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩

theorem quotientShift_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.seq (.block quotientArgs) VG.Impl.Bignum.Arm.shiftLeft) s (Context g) := by
  rw [WP.seq_iff]
  refine WP.mono (quotientArgs_ok h) ?_
  rintro u ⟨ptr, count, carry, _, ctx, _⟩
  exact WP.mono (shiftArray_ok ctx 0 (Or.inl rfl) ptr count (by rw [carry]; decide))
    (fun _ h => h.2.2.2.1)

theorem shift_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) shift (fun _ _ => True) := by
  have qwp (s : State) (h : Context g s) : WP isa (.block quotientArgs) s (ShiftPublic g 0) :=
    WP.mono (quotientArgs_ok h) (fun _ h => ⟨h.1, h.2.1⟩)
  have rwp (s : State) (h : Context g s) : WP isa (.block remainderArgs) s (ShiftPublic g 1) :=
    WP.mono (remainderArgs_ok h) (fun _ h => ⟨h.1, h.2.1⟩)
  have qct := (pair_posts (quotientArgs_ct (g := g)) qwp).seq (array_ct (i := 0))
  have rct := (pair_posts (remainderArgs_ct (g := g)) rwp).seq (array_ct (i := 1))
  exact ((pair_posts qct (fun _ h => quotientShift_ok h)).seq rct).assoc

end VG.Proof.Rsa.Arm.Div
