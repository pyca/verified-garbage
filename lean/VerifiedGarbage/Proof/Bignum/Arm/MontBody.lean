module

public import VerifiedGarbage.Impl.Bignum.Arm.MontBody
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Complete Montgomery arithmetic from pointers and a packed-word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem montBody_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (finish : CsubCtx s base size out acc mod tmp n)
    (regs : InitRegs s base out tmp a b mod acc n inv)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montBody s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) b n % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 32), (tmp + 16, 8), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [montBody, WP.seq_iff]
  refine WP.mono (montInit_ok s ctx regs hB hInv) ?_
  rintro u ⟨ready, outsideU, restU⟩
  obtain ⟨inverse, header, hinverse⟩ := ready.round.secret
  refine WP.mono (montCore_ok u ready.round.ctx (finish.congr restU.wr) header ready.round.ptr
    ready.outPtr ready.zero ready.round.operand hinverse) ?_
  rintro t ⟨bound, value, outsideT, restT⟩
  have nowrap := ctx.workspace.nowrap
  have old (d : Nat) (fits : d + 4 * n ≤ size)
      (sepA : d + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ d)
      (sepT : d + 4 * n ≤ tmp ∨ tmp + 32 ≤ d) :
      val32 u.mem (State.addr base) d n = val32 s.mem (State.addr base) d n :=
    outsideU.val32 (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepA
      · exact sepT) (by omega)
  have oldM := old mod ctx.mFits ctx.accM.symm ctx.tmpM.symm
  have oldA := old a ctx.aFits ctx.accA.symm ctx.tmpA.symm
  have oldB := old b ctx.bFits ctx.accB.symm ctx.tmpB.symm
  rw [oldM] at bound
  rw [oldM, oldA, oldB] at value
  exact ⟨bound, value, (outsideU.mono (by simp)).trans (outsideT.mono (by simp)), restU.trans restT⟩

end VG.Proof.Bignum.Arm
