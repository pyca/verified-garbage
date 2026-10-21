module

public import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaalStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal

/-! One UMAAL iteration simulates a downward-write baseline iteration exactly. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRowUmaal
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16)

def stepNew (k : Nat) (n : State) : State :=
  { ((((n.setReg .r2 (inW k n)).setReg .r3 (accW k n)).setReg .r5 (accW k n)).setReg .r3
      (BitVec.ofNat 32 ((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat + (accW k n).toNat))).setReg
      .r11 (BitVec.ofNat 32 (((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat +
        (accW k n).toNat) / 2 ^ 32)) with
    mem := n.mem.writeW (State.addr (n.gpr .r0 + BitVec.ofNat 32 k))
      (BitVec.ofNat 32 ((inW k n).toNat * (n.gpr .r9).toNat + (n.gpr .r11).toNat + (accW k n).toNat)) }


-- `rowUEnd` itself is shared unchanged with the existing UMAAL row.

theorem stepU_exec (n : State)
    (hr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + 0#32)) 4)
    (ha : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + 4#32)) 4)
    (hw : InRegions n.wr (State.addr (n.gpr .r0 + 0#32)) 4) :
    execBlock isa DownRow.stepU n = some (stepNew 0 n,
      [.addr (State.addr (n.gpr .r12 + 0#32)), .addr (State.addr (n.gpr .r0 + 4#32)),
        .addr (State.addr (n.gpr .r0 + 0#32))]) := by
  simp only [DownRow.stepU, execBlock, isa, exec,
    show (0 < 4096) = True by decide, show (4 < 4096) = True by decide,
    ↓reduceIte, State.load32, State.store32, Op2.eval,
    gpr_setReg, reduceCtorEq, rd_setReg, wr_setReg, mem_setReg, hr, ha, hw, Option.map_some, addrs,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rfl

def advState (s : State) : State :=
  (subFlags ((s.setReg .r0 (s.gpr .r0 + 4)).setReg .r12 (s.gpr .r12 + 4)) (s.gpr .lr) 1).setReg .lr
    (s.gpr .lr - 1)

theorem advState_exec (s : State) : execBlock isa rowAdvance s = some (advState s, []) := by
  simp only [rowAdvance, execBlock, isa, exec, Op2.eval,
    Option.map_some, addrs, List.map_nil, List.append_nil]
  rfl

theorem advance_noFlags {a b : State} (h : NoFlags a b) :
    execBlock isa rowAdvance a = execBlock isa rowAdvance b := by
  obtain ⟨g, sp, m, rd, wr, u, sy⟩ := h
  cases a; cases b
  dsimp only at g sp m rd wr u sy
  subst g sp m rd wr u sy
  rfl

theorem body_sim {o n o' : State} {t : List Leak} {x : BitVec 32} (ag : Agree o n)
    (h1 : o.gpr .r1 = x &&& mask16) (h10 : o.gpr .r10 = x >>> 16) (h9 : o.gpr .r9 = mask16)
    (hx : n.gpr .r9 = x) (h : Exec isa DownRow.body o t o') :
    Exec isa DownRow.bodyU n t (advState (stepNew 0 n)) ∧
      endState (advState (stepNew 0 n)) = o' := by
  unfold DownRow.body at h
  obtain ⟨o₁, ts, ta, es, ea, rfl⟩ := seq_inv h
  change Exec isa (stepAt 0) o ts o₁ at es
  obtain ⟨rfl, rd, ra, wr, nf⟩ := step_fwd (k:=0) (by decide) h1 h10 h9 es
  have ea' := Exec.block_iff.mp ea
  rw [advance_noFlags nf, advState_exec] at ea'
  simp only [Option.some.injEq, Prod.mk.injEq] at ea'
  obtain ⟨rfl, rfl⟩ := ea'
  have r0 : o.gpr .r0 = n.gpr .r0 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have r12 : o.gpr .r12 = n.gpr .r12 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have nr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + 0#32)) 4 := by
    rw [←r12,←ag.rd,←ag.wr];exact rd
  have na : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + 4#32)) 4 := by
    rw [←r0,←ag.rd,←ag.wr];exact ra
  have nw : InRegions n.wr (State.addr (n.gpr .r0 + 0#32)) 4 := by
    rw [←r0,←ag.wr];exact wr
  have en := Exec.block_iff.mpr (stepU_exec n nr na nw)
  have en' := Exec.block_iff.mpr (advState_exec (stepNew 0 n))
  refine ⟨?_,?_⟩
  · exact (by simpa only [DownRow.bodyU,r0,r12] using Exec.seq en en')
  · have kept : ∀ r, r ≠ .r2 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → o.gpr r = n.gpr r := ag.gpr
    have r1 := kept .r1 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r8 := kept .r8 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r10 := kept .r10 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r11 := kept .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have rlr := kept .lr (by decide) (by decide) (by decide) (by decide) (by decide)
    subst hx
    have hn1 : n.gpr .r1 = n.gpr .r9 &&& mask16 := r1 ▸ h1
    have gs : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).gpr = s.gpr := fun _ _ _ => rfl
    have ms : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).mem = s.mem := fun _ _ _ => rfl
    refine NoFlags.eq ⟨funext fun r => ?_, ag.sp.symm, ?_, ag.rd.symm, ag.wr.symm, ag.unknowns.symm,
      ag.syms.symm⟩ ?_ ?_ ?_ ?_
    · cases r <;> simp only [endState, advState, stepNew, stepOld, stepSum, inW, accW, gs, gpr_setReg,
        reduceCtorEq, ↓reduceIte, ag.mem, r0, r1, r8, r10, r11, r12, rlr, h9, hn1]
    · simp only [endState, advState, stepNew, stepOld, stepSum, inW, accW, ms, mem_setReg, gpr_setReg,
        reduceCtorEq, ↓reduceIte, ag.mem, r0, r11, r12]
    all_goals simp only [endState, advState, subFlags, n_setReg, z_setReg, c_setReg, v_setReg,
      gpr_setReg, reduceCtorEq, ↓reduceIte, stepNew, stepOld, rlr]

theorem body_keeps {n : State} :
    (advState (stepNew 0 n)).gpr .r1 = n.gpr .r1 ∧
      (advState (stepNew 0 n)).gpr .r10 = n.gpr .r10 ∧
      (advState (stepNew 0 n)).gpr .r9 = n.gpr .r9 := by
  simp only [advState, stepNew, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, and_self]

end VG.Proof.Bignum.Arm.DownRowUmaal
