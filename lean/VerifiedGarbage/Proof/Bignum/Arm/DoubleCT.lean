module

public import VerifiedGarbage.Proof.Bignum.Arm.DoubleProduct
public import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Double
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Modular doubling reveals only its public workspace layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

def DoubleReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop :=
  CoreReady base size out tmp a b mod acc n s ∧ w32 s.mem (State.addr base) a = 2

def DoubleInitReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop :=
  InitReady base size out tmp a b mod acc n s ∧ w32 s.mem (State.addr base) a = 2

theorem doubleCore_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat} (ht : tmp + 32 ≤ size) (hn : 0 < n) :
    RelCT isa (fun s t => DoubleReady base size out tmp a b mod acc n s ∧
      DoubleReady base size out tmp a b mod acc n t) doubleCore (fun _ _ => True) := by
  let P := DoubleReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) doubleProduct (fun _ _ => True) := by
    unfold doubleProduct
    have stage := (productStage_ct (base := base) (size := size) (tmp := tmp) (a := a)
      (b := b) (mod := mod) (acc := acc) (n := n) (i := 0) hn).mono
      (fun _ _ (h : P _ ∧ P _) => ⟨h.1.1.round.stage, h.2.1.round.stage⟩) (fun _ _ h => h)
    refine stage.seq ?_
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : P s) : WP isa doubleProduct s (FinishReady base size tmp out acc mod n) :=
    WP.mono (doubleProduct_ok s h.1 h.2) (fun _ h => h.2.1)
  exact (pair_posts ct wp).seq (montFinish_ct ht)

theorem doubleInit_ready {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (s : State) (h : DoubleInitReady base size out tmp a b mod acc n s) :
    WP isa montInit s (DoubleReady base size out tmp a b mod acc n) := by
  obtain ⟨inv, regs, inverse⟩ := h.1.secret
  refine WP.mono (montInit_ok s h.1.ctx regs h.1.operand inverse) ?_
  rintro t ⟨ready, outside, rest⟩
  have ctx := h.1.ctx
  have hn := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fit := ctx.aFits
  have accA := ctx.accA
  have tmpA := ctx.tmpA
  refine ⟨ready, ?_⟩
  rw [outs_word32 outside (d := a) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)]
  exact h.2

theorem doubleBody_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (ht : tmp + 32 ≤ size) (hn : 0 < n) :
    RelCT isa (fun s t => DoubleInitReady base size out tmp a b mod acc n s ∧
      DoubleInitReady base size out tmp a b mod acc n t) doubleBody (fun _ _ => True) := by
  let P := DoubleInitReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) montInit (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨is, rs, _⟩ := h.1.1.secret
    obtain ⟨it, rt, _⟩ := h.2.1.secret
    exact ⟨montInit_ct s t tr1 tr2 u v trivial trivial
      ⟨rs.tmpPtr.trans rt.tmpPtr.symm, rs.accPtr.trans rt.accPtr.symm, rs.count.trans rt.count.symm⟩ e1 e2, trivial⟩
  exact (pair_posts ct doubleInit_ready).seq (doubleCore_ct ht hn)

end VG.Proof.Bignum.Arm
