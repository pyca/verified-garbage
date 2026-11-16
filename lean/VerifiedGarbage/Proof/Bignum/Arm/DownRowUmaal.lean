module

public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Bignum.Arm.RowStep
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! ### `Bignum.Arm.DownRowUmaalBody`, which only this module used -/

section

/-! ### `Bignum.Arm.DownRowUmaalStep`, which only this module used -/

section

/-! Exact states and traces of the downward row's baseline step. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRowUmaal
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16)

def inW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 32
def accW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))) 32

def stepSum (k : Nat) (x : BitVec 32) (s : State) : Nat :=
  (inW k s).toNat*x.toNat+(s.gpr .r11).toNat+(accW k s).toNat

def stepAt (k : Nat) : Prog isa :=
  .seq (.block [.ldr .r2 .r12 k]) (.seq (.block rowProduct)
    (.seq (.block [.ldr .r5 .r0 (k+4)])
      (.seq (.block (addWord .r5 ++ addCarry)) (.block [.str .r3 .r0 k]))))

def stepOld (k : Nat) (x : BitVec 32) (s : State) : State :=
  { (((((((s.setReg .r2 (inW k s &&& mask16)).setReg .r6 (inW k s >>> 16)).setReg .r7
      ((x &&& mask16) * (inW k s >>> 16))).setReg .r5 (accW k s)).setReg .r4
      (BitVec.ofNat 32 (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32))).setReg
      .r3 (BitVec.ofNat 32 (stepSum k x s))).setReg .r11 (BitVec.ofNat 32 (stepSum k x s / 2 ^ 32))) with
    mem := s.mem.writeW (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) (BitVec.ofNat 32 (stepSum k x s)) }


theorem step_fwd {k : Nat} (hk : k + 4 < 4096) {x : BitVec 32} {s s' : State} {t : List Leak}
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (h : Exec isa (stepAt k) s t s') :
    t = [.addr (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))),
      .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k))] ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4 ∧
    NoFlags s' (stepOld k x s) := by
  unfold stepAt at h
  obtain ⟨s₁, t₁, r₁, e₁, h₁, rfl⟩ := seq_inv h
  obtain ⟨s₂, t₂, r₂, e₂, h₂, rfl⟩ := seq_inv h₁
  obtain ⟨s₃, t₃, r₃, e₃, h₃, rfl⟩ := seq_inv h₂
  obtain ⟨s₄, t₄, t₅, e₄, e₅, rfl⟩ := seq_inv h₃
  obtain ⟨hr₁, rfl, rfl⟩ := ldr_block (by omega_using [hk] : k < 4096) e₁
  -- `rowProduct`
  obtain p1 : (s.setReg .r2 (inW k s)).gpr .r1 = x &&& mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h1
  obtain p10 : (s.setReg .r2 (inW k s)).gpr .r10 = x >>> 16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h10
  obtain p9 : (s.setReg .r2 (inW k s)).gpr .r9 = mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h9
  obtain ⟨_, _, w₂, prod, f₂⟩ := rowProduct_ok _ x p1 p10 p9
  rw [(Exec.det w₂ e₂).2] at prod f₂
  obtain ⟨_, _, w₂', v2, v6, v7⟩ := rowProduct_regs (s.setReg .r2 (inW k s))
  rw [(Exec.det w₂' e₂).2] at v2 v6 v7
  obtain t₂0 : t₂ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₂)
  subst t₂0
  obtain g0 : s₂.gpr .r0 = s.gpr .r0 := by
    rw [f₂.regs .r0 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  have m₂ : s₂.mem = s.mem := f₂.mem
  -- the accumulator word
  obtain ⟨hr₃, rfl, rfl⟩ := ldr_block hk e₃
  -- `addWord r5 ++ addCarry`
  let s₃ := s₂.setReg .r5 (s₂.mem.readW (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 (k+4))) 32)
  obtain a3 : s₃.gpr .r5 = accW k s := by
    simp only [s₃, gpr_setReg, ↓reduceIte, g0, m₂, accW]
  obtain c3 : s₃.gpr .r11 = s.gpr .r11 := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs .r11 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  obtain p3 : (s₃.gpr .r3).toNat + (s₃.gpr .r4).toNat * 2 ^ 32 = (inW k s).toNat * x.toNat := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [prod, Nat.mul_comm]; simp only [gpr_setReg, ↓reduceIte]
  obtain hb := mac_bound (inW k s) x (accW k s) (s.gpr .r11)
  obtain ⟨_, _, w₄, ⟨lo, sumA, sumC⟩, f₄⟩ := rowMac_ok s₃ (by rw [p3, a3, c3]; omega_using [hb])
  rw [(Exec.det w₄ e₄).2] at sumA sumC f₄
  obtain t₄0 : t₄ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₄)
  subst t₄0
  obtain g40 : s₄.gpr .r0 = s.gpr .r0 := by
    rw [f₄.regs .r0 (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]; exact g0
  obtain ⟨hw₅, rfl, rfl⟩ := str_block (by omega_using [hk] : k < 4096) e₅
  obtain lo3 : s₄.gpr .r3 = BitVec.ofNat 32 (stepSum k x s) := by
    refine toNat_lo (hi := s₄.gpr .r11) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega_using []
  obtain hi11 : s₄.gpr .r11 = BitVec.ofNat 32 (stepSum k x s / 2 ^ 32) := by
    refine toNat_hi (lo := s₄.gpr .r3) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega_using []
  obtain hi4 : s₄.gpr .r4 = BitVec.ofNat 32
      (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32) := by
    refine toNat_hi (lo := lo) ?_
    rw [sumA, p3, a3]; simp
  obtain keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r11 →
      s₄.gpr r = s.gpr r := by
    intro r h2 h3 h4 h5 h6 h7 h11
    obtain e4 := f₄.regs r (by simp [h3, h4, h11])
    rw [e4]
    simp only [s₃, gpr_setReg, h5, ↓reduceIte]
    by_cases h8 : r = .r8
    · subst h8
      rw [VG.Arm.Exec.gpr (fun i hi => by revert i hi; decide) e₂]
      simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs r (by simp [h2, h3, h4, h5, h6, h7, h8])]
    simp only [gpr_setReg, h2, ↓reduceIte]
  obtain k5 : s₄.gpr .r5 = accW k s := by rw [f₄.regs _ (by decide)]; exact a3
  obtain k2 : s₄.gpr .r2 = inW k s &&& mask16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v2, p9]; simp only [gpr_setReg, ↓reduceIte]
  obtain k6 : s₄.gpr .r6 = inW k s >>> 16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v6]; simp only [gpr_setReg, ↓reduceIte]
  obtain k7 : s₄.gpr .r7 = (x &&& mask16) * (inW k s >>> 16) := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v7, p1]; simp only [gpr_setReg, ↓reduceIte]
  obtain wr₄ : s₄.wr = s.wr := by rw [f₄.wr]; exact f₂.wr
  refine ⟨by simp [g0, g40], hr₁, by rw [g0, f₂.rd, f₂.wr] at hr₃; exact hr₃, by rw [g40, wr₄] at hw₅; exact hw₅, ?_⟩
  refine ⟨funext fun r => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s₄.gpr r = _
    cases r <;> simp only [stepOld, gpr_setReg, reduceCtorEq, ↓reduceIte]
    all_goals first
      | exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact lo3
      | exact hi11
      | exact hi4
      | exact k5
      | exact k2
      | exact k6
      | exact k7
  · change s₄.sp = s.sp; rw [f₄.sp]; exact f₂.sp
  · change s₄.mem.writeW _ (s₄.gpr .r3) = _
    simp only [stepOld]
    rw [lo3, g40, f₄.mem]
    change s₂.mem.writeW _ _ = _
    rw [m₂]
  · change s₄.rd = s.rd; rw [f₄.rd]; exact f₂.rd
  · exact wr₄
  · change s₄.unknowns = s.unknowns; rw [f₄.unknowns]; exact f₂.unknowns
  · change s₄.syms = s.syms; rw [f₄.syms]; exact f₂.syms


end VG.Proof.Bignum.Arm.DownRowUmaal

end

end


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
  obtain ea' := Exec.block_iff.mp ea
  rw [advance_noFlags nf, advState_exec] at ea'
  simp only [Option.some.injEq, Prod.mk.injEq] at ea'
  obtain ⟨rfl, rfl⟩ := ea'
  obtain r0 : o.gpr .r0 = n.gpr .r0 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain r12 : o.gpr .r12 = n.gpr .r12 := ag.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain nr : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r12 + 0#32)) 4 := by
    rw [←r12,←ag.rd,←ag.wr];exact rd
  obtain na : InRegions (n.rd ++ n.wr) (State.addr (n.gpr .r0 + 4#32)) 4 := by
    rw [←r0,←ag.rd,←ag.wr];exact ra
  obtain nw : InRegions n.wr (State.addr (n.gpr .r0 + 0#32)) 4 := by
    rw [←r0,←ag.wr];exact wr
  obtain en := Exec.block_iff.mpr (stepU_exec n nr na nw)
  obtain en' := Exec.block_iff.mpr (advState_exec (stepNew 0 n))
  refine ⟨?_,?_⟩
  · exact (by simpa only [DownRow.bodyU,r0,r12] using Exec.seq en en')
  · have kept : ∀ r, r ≠ .r2 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r9 → o.gpr r = n.gpr r := ag.gpr
    obtain r1 := kept .r1 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain r8 := kept .r8 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain r10 := kept .r10 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain r11 := kept .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain rlr := kept .lr (by decide) (by decide) (by decide) (by decide) (by decide)
    subst hx
    obtain hn1 : n.gpr .r1 = n.gpr .r9 &&& mask16 := r1 ▸ h1
    obtain gs : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).gpr = s.gpr := fun _ _ _ => rfl
    obtain ms : ∀ (s : State) (a b : BitVec 32), (subFlags s a b).mem = s.mem := fun _ _ _ => rfl
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

end

end


/-! The UMAAL downward row has the baseline row's exact trace and final state. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRowUmaal
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16)

theorem loop_sim {x : BitVec 32} {o o' : State} {tr : List Leak}
    (h : Exec isa (.loop DownRow.body .ne) o tr o') :
    ∀ {n : State}, Agree o n → o.gpr .r1 = x &&& mask16 → o.gpr .r10 = x >>> 16 → o.gpr .r9 = mask16 →
      n.gpr .r9 = x → ∃ n', Exec isa (.loop DownRow.bodyU .ne) n tr n' ∧ endState n' = o' := by
  generalize hc : (Code.loop DownRow.body .ne : Prog isa) = c at h
  induction h with
  | icall | icallNext => cases hc
  | loopExit hb he =>
    cases hc
    intro n ag h1 h10 h9 hx
    obtain ⟨e, rfl⟩ := body_sim ag h1 h10 h9 hx hb
    exact ⟨_, .loopExit e (by simpa [isa, eval, endState, z_setReg] using he), rfl⟩
  | loopNext hb he _ _ ih =>
    cases hc
    intro n ag h1 h10 h9 hx
    obtain ⟨e, rfl⟩ := body_sim ag h1 h10 h9 hx hb
    obtain ⟨k1, k10, k9⟩ := body_keeps (n := n)
    obtain ⟨n', e', rfl⟩ := ih rfl (agree_endState _)
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [k1, ← ag.gpr .r1 (by decide)
        (by decide) (by decide) (by decide) (by decide), h1])
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte]; rw [k10, ← ag.gpr .r10 (by decide)
        (by decide) (by decide) (by decide) (by decide), h10])
      (by simp only [endState, gpr_setReg, reduceCtorEq, ↓reduceIte])
      (by rw [k9, hx])
    exact ⟨n', .loopNext e (by simpa [isa, eval, endState, z_setReg] using he) e', rfl⟩
  | block => cases hc
  | seq => cases hc
  | iteT => cases hc
  | iteF => cases hc
  | call => cases hc
  | frame => cases hc

/-! ## The rows -/

/-- `DownRow.coreU` runs as `DownRow.loop`, from a state where the scalar `x` is
split for `row`. -/
theorem coreU_sim {x : BitVec 32} {s s' : State} {t : List Leak}
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (h : Exec isa DownRow.loop s t s') : Exec isa DownRow.coreU s t s' := by
  let n := s.setReg .r9 (s.gpr .r1 ||| (s.gpr .r10 <<< 16))
  obtain ej : Exec isa (.block rowUJoin) s [] n := by
    refine Exec.block_iff.mpr ?_
    simp only [rowUJoin, execBlock, isa, reduceExec, Op2.eval, show (1 ≤ 16 ∧ 16 ≤ 31) = True by decide,
      ↓reduceIte, Option.map_some, addrs, List.map_nil, List.append_nil]
    rfl
  obtain hx : n.gpr .r9 = x := by
    simp only [n, gpr_setReg, ↓reduceIte, h1, h10]; exact join16 x
  obtain ag : Agree s n := ⟨fun r _ _ _ _ h9' => by simp only [n, gpr_setReg, h9', ↓reduceIte],
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨n', e', rfl⟩ := loop_sim h ag h1 h10 h9 hx
  obtain ee : Exec isa (.block rowUEnd) n' [] (endState n') := Exec.block_iff.mpr (rowUEnd_exec n')
  have := Exec.seq ej (Exec.seq e' ee)
  rwa [List.nil_append, List.append_nil] at this


theorem code_sim : Sim (M:=isa) DownRow.code DownRow.codeU := by
  intro s t s' h
  unfold DownRow.code at h
  obtain ⟨s₁,t₁,r₁,e₁,h₁,rfl⟩:=seq_inv h
  obtain ⟨s₂,t₂,t₃,e₂,e₃,rfl⟩:=seq_inv h₁
  obtain ⟨_,_,run,h1,h10,h9,_,_⟩:=rowSplit_ok s
  rw [(Exec.det run e₁).2] at h1 h10 h9
  exact .seq e₁ (.seq (coreU_sim h1 h10 h9 e₂) e₃)

theorem codeU_stack : FrameStack.armStack DownRow.codeU=0 := by
  rfl

end VG.Proof.Bignum.Arm.DownRowUmaal
