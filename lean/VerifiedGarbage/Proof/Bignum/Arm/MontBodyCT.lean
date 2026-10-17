module

public import VerifiedGarbage.Impl.Bignum.Arm.MontBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Constant-time complete Montgomery arithmetic, including initialization -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure InitReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop where
  ctx : RoundCtx s base size tmp a b mod acc n
  secret : ∃ inv, InitRegs s base out tmp a b mod acc n inv ∧
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0
  operand : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n

theorem montBody_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat} (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => InitReady base size out tmp a b mod acc n s ∧
      InitReady base size out tmp a b mod acc n t) montBody (fun _ _ => True) := by
  let P := InitReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) montInit (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨is, rs, _⟩ := h.1.secret
    obtain ⟨it, rt, _⟩ := h.2.secret
    exact ⟨montInit_ct s t tr1 tr2 u v trivial trivial
      ⟨rs.tmpPtr.trans rt.tmpPtr.symm, rs.accPtr.trans rt.accPtr.symm, rs.count.trans rt.count.symm⟩ e1 e2, trivial⟩
  have wp (s : State) (h : P s) : WP isa montInit s (CoreReady base size out tmp a b mod acc n) := by
    obtain ⟨inv, regs, inverse⟩ := h.secret
    exact WP.mono (montInit_ok s h.ctx regs h.operand inverse) (fun _ h => h.1)
  exact (pair_posts ct wp).seq (montCore_ct ht)

end VG.Proof.Bignum.Arm
