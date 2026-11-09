module

public import VerifiedGarbage.Impl.Ed25519.X86_64.FieldMemory
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide

/-! Exact extended-coordinate operations and the slots they preserve. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def fieldDest : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ | .mul2 o _ _
  | .sqr2 o _ => o

theorem evalOp_unchanged (op : FieldOp) (e : Env) (i : Slot) (hi : i ≠ fieldDest op) :
    evalOp op e i = e i := by
  cases op <;> exact Function.update_of_ne hi _ _

theorem evalOps_unchanged (ops : List FieldOp) (e : Env) (i : Slot)
    (hi : ∀ op ∈ ops, i ≠ fieldDest op) : evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change evalOps ops (evalOp op e) i = e i
    rw [ih (evalOp op e) (fun p hp => hi p (List.mem_cons_of_mem _ hp)), evalOp_unchanged op e i (hi op (by simp))]

theorem point_ops_high (ops : List FieldOp) (hops : ∀ op ∈ ops, (fieldDest op).val < 16)
    (e : Env) (i : Slot) (hi : 16 ≤ i.val) : evalOps ops e i = e i := by
  apply evalOps_unchanged
  intro op hop heq
  have h := hops op hop
  have := congrArg Fin.val heq
  omega

theorem constPoint_eval (p : Spec.Ed25519.Point) (e : Env) :
    point (evalOps (constPointOps p) e) 0 1 2 3 = p := by cases p; rfl

end VG.Proof.Ed25519.X86_64
