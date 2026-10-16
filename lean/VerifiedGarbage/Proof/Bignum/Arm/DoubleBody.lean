module

public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete modular doubling from pointers and a packed-word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem doubleBody_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (finish : CsubCtx s base size out acc mod tmp n)
    (regs : InitRegs s base out tmp a b mod acc n inv)
    (two : w32 s.mem (State.addr base) a = 2)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa doubleBody s fun t =>
      val32 t.mem (State.addr base) out n =
        (2 * val32 s.mem (State.addr base) b n) % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 32), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [doubleBody, WP.seq_iff]
  refine WP.mono (montInit_ok s ctx regs hB hInv) ?_
  rintro u ⟨ready, outsideU, restU⟩
  have nowrap := ctx.workspace.nowrap
  have hn := ctx.count
  have afit := ctx.aFits
  have aAcc := ctx.accA
  have aTmp := ctx.tmpA
  have twoU : w32 u.mem (State.addr base) a = 2 := by
    rw [outs_word32 outsideU (d := a) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega), two]
  refine WP.mono (doubleCore_ok u ready (finish.congr restU.wr) twoU) ?_
  rintro t ⟨value, outsideT, restT⟩
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
  have oldB := old b ctx.bFits ctx.accB.symm ctx.tmpB.symm
  rw [oldM, oldB] at value
  exact ⟨value, (outsideU.mono (by simp)).trans (outsideT.mono (by simp)), restU.trans restT⟩

end VG.Proof.Bignum.Arm
