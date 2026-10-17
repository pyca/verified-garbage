module

public import VerifiedGarbage.Proof.Rsa.Arm.DivArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGeCT
public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The secret remainder comparison only controls masked selection -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm

theorem reduce_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) reduce (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 3) ∧
    s.gpr .r10 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
    s.gpr .r12 = g.base + BitVec.ofNat 32 (g.offsets 2) ∧
    s.gpr .r9 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
    s.gpr .r7 = BitVec.ofNat 32 (g.n + 1) ∧ s.gpr .lr = BitVec.ofNat 32 (g.n + 1)
  have wp (s : State) (h : Context g s) : WP isa (.block subtractArgs) s Q :=
    WP.mono (subtractArgs_ok h) (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1⟩)
  refine (pair_posts (subtractArgs_ct (g := g)) wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨subtractIfGe_ct s t tr1 tr2 u v trivial trivial ?_ e1 e2, trivial⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.2.2.2.1.trans h.2.2.2.2.2.1.symm
  · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  · exact h.1.2.1.trans h.2.2.1.symm
  · exact h.1.2.2.1.trans h.2.2.2.1.symm
  · exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm

end VG.Proof.Rsa.Arm.Div
