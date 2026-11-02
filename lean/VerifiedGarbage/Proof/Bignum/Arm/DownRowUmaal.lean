module

import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaalBody
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Framework.Arm.Reduce

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
  have ej : Exec isa (.block rowUJoin) s [] n := by
    refine Exec.block_iff.mpr ?_
    simp only [rowUJoin, execBlock, isa, reduceExec, Op2.eval, show (1 ≤ 16 ∧ 16 ≤ 31) = True by decide,
      ↓reduceIte, Option.map_some, addrs, List.map_nil, List.append_nil]
    rfl
  have hx : n.gpr .r9 = x := by
    simp only [n, gpr_setReg, ↓reduceIte, h1, h10]; exact join16 x
  have ag : Agree s n := ⟨fun r _ _ _ _ h9' => by simp only [n, gpr_setReg, h9', ↓reduceIte],
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨n', e', rfl⟩ := loop_sim h ag h1 h10 h9 hx
  have ee : Exec isa (.block rowUEnd) n' [] (endState n') := Exec.block_iff.mpr (rowUEnd_exec n')
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
