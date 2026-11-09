module

public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
meta import VerifiedGarbage.Proof.X448.X86_64.Inv
meta import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
meta import VerifiedGarbage.Proof.Ed448.Formulas
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import Mathlib.FieldTheory.Finite.Basic
meta import Mathlib.Tactic.NormNum.Prime
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectBase
import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectBase
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
meta import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister

/-! Verification lookups reveal only public scalar digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep)
open VG.Impl.X448.X86_64 (BITS)

/-- Compose timing proofs with the single-run facts established by correctness. -/
theorem seq_same {A B : State → Prop} {p q : Prog isa}
    (hp : RelCT isa (fun x y => A x ∧ A y) p (fun _ _ => True))
    (hw : ∀ s, A s → WP isa p s B)
    (hq : RelCT isa (fun x y => B x ∧ B y) q (fun _ _ => True)) :
    RelCT isa (fun x y => A x ∧ A y) (.seq p q) (fun _ _ => True) :=
  (hp.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).seq
    (hq.mono (fun _ _ h => h.2) (fun _ _ h => h))




structure JointTimingCtx (base : Addr) (S K : Nat) (s : State) : Prop where
  scr : Scr s base
  bs : Bits base BITS S s
  bk : Bits base KBITS K s
  d : E s.mem base 11 = Spec.Ed448.d
  z : E s.mem base 10 = 1
  p : Proof.Ed448.pt (E s.mem base) 0 1 2 = Spec.Ed448.identity

end VG.Proof.Ed448.X86_64.Window
