module
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
public import VerifiedGarbage.Proof.Framework.RelCT
public import Batteries.Logic

import VerifiedGarbage.Proof.Rsa.Arm.DivArgsCT
import VerifiedGarbage.Proof.Rsa.Arm.DivInit
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Rsa.Arm.Div
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Rsa.Arm.DivArgs
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasBody
import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectPrepare
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubBody
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGe
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Division initialization uses only public lengths and pointers -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm)

theorem init_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) init (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 1) ∧
    s.gpr .lr = BitVec.ofNat 32 (g.n + 1)
  have args : RelCT isa (fun s t => Context g s ∧ Context g t)
      (.block (remainderArgs ++ [.mov .r3 (.imm 0)])) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : Context g s) :
      WP isa (.block (remainderArgs ++ [.mov .r3 (.imm 0)])) s Q := by
    rw [WP.block_append_iff]
    refine WP.mono (remainderArgs_ok h) ?_
    rintro u ⟨ptr, count, _, _, _⟩
    refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
    exact ⟨(a.other .r0 (by decide)).trans ptr, (a.other .lr (by decide)).trans count⟩
  have clear : RelCT isa (fun s t => Context g s ∧ Context g t)
      (.seq (.block (remainderArgs ++ [.mov .r3 (.imm 0)])) VG.Impl.Bignum.Arm.zero)
      (fun _ _ => True) := by
    refine (pair_posts args wp).seq ?_
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨zero_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩
  exact ((pair_posts clear (fun _ h => clear_ok h)).seq initCount_ct).assoc

end VG.Proof.Rsa.Arm.Div
