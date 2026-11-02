module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
import VerifiedGarbage.Proof.Bignum.Arm.MontCallArgsReady
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Constant time of a shared Montgomery operation in its caller frame -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

/-- Arguments access only the caller's stack word and the public header. -/
theorem montCallArgs_trace (s : State) {base : BitVec 32} {size o a b : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (write : InRegions s.wr (State.addr s.sp) 4)
    (ho : o < 8) (ha : a < 8) (hb : b < 8)
    {tr : List Leak} {u : State} (run : Exec isa (.block (MontCall.opArgs o a b)) s tr u) :
    tr = [.addr (State.addr s.sp), .addr (State.addr (base + BitVec.ofNat 32 48))] := by
  have immediate : ∀ j < 8, encodable (BitVec.ofNat 32 j) = true := by decide
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 48)) 4 := by
    rw [ptr, addr_add (by have := ws.nowrap; omega)]
    exact ws.read fit
  rw [Exec.block_iff] at run
  simp only [MontCall.opArgs, execBlock, isa, exec, Op2.eval,
    immediate o ho, immediate a ha, immediate b hb,
    show encodable (6 : BitVec 32) = true from rfl,
    show (0 < 256) = True by decide, show (0 < 4096) = True by decide,
    show (48 < 4096) = True by decide, show (1 ≤ 3 ∧ 3 ≤ 31) = True by decide,
    ↓reduceIte, State.store32, State.load32, gpr_setReg, reduceCtorEq,
    sp_setReg, mem_setReg, rd_setReg, wr_setReg, write, read,
    BitVec.add_zero, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Option.some.injEq, Prod.mk.injEq] at run
  simpa only [ptr] using run.2.symm

theorem CallInput.callEntry {base : BitVec 32} {len w o a b : Nat} {s : State}
    (h : CallInput base len w o a b s) : CallInput base len w o a b s.callEntry := by
  exact ⟨⟨h.workspace.nowrap, h.workspace.writable⟩, h.layout, h.width,
    (State.callEntry_gpr s (by decide)).trans h.ptr,
    (State.callEntry_gpr s (by decide)).trans h.outIndex,
    (State.callEntry_gpr s (by decide)).trans h.aIndex,
    h.bArg, h.inverse, h.operand, h.stackFit, h.argRead, h.stackWorkspace, h.stackArg⟩

theorem montCall_rawCall_ct (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (ct : RelCT isa (fun s t => CallInput base len w o a b s ∧
      CallInput base len w o a b t ∧ s.sp = t.sp) callee (fun _ _ => True)) :
    RelCT isa (fun s t => CallInput base len w o a b s ∧
      CallInput base len w o a b t ∧ s.sp = t.sp) (.call name callee) (fun _ _ => True) := by
  intro s t tr1 tr2 u v hp e1 e2
  cases e1 with
  | call p1 b1 q1 =>
    cases e2 with
    | call p2 b2 q2 =>
      rw [call_callEntry, Option.some.injEq] at p1 p2
      subst p1 p2
      obtain ⟨trace, _⟩ := ct _ _ _ _ _ _ ⟨hp.1.callEntry, hp.2.1.callEntry, hp.2.2⟩ b1 b2
      exact ⟨by simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using trace, trivial⟩

theorem montCallOp_ct (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (ct : RelCT isa (fun s t => CallInput base len w o a b s ∧
      CallInput base len w o a b t ∧ s.sp = t.sp) callee (fun _ _ => True))
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧
      CallStack base len s ∧ CallStack base len t ∧
      numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0 ∧ s.sp = t.sp)
      (MontCall.op name callee o a b) (fun s t => s.sp = t.sp) := by
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨hs, ht, cs, ctStack, boundS, boundT, sp⟩ := hp
  have fitS : 8 ≤ s.sp.toNat := by have := cs.fit; omega
  have fitT : 8 ≤ t.sp.toNat := by have := ctStack.fit; omega
  have fits : VG.Proof.Rsa.Mont.arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
  have size : 52 ≤ 8 * len := by simp only [VG.Proof.Rsa.Mont.arrAt, VG.Proof.Rsa.Mont.hdrBytes] at fits; omega
  unfold MontCall.op at e1 e2
  cases e1 with
  | seq f1 restore1 =>
    cases e2 with
    | seq f2 restore2 =>
      have frameSp := (Exec.sp f1).trans (sp.trans (Exec.sp f2).symm)
      obtain ⟨restoreTrace, finalSp⟩ := loadStack_ct .r0 0 _ _ _ _ _ _ frameSp restore1 restore2
      cases f1 with
      | frame p1 b1 q1 =>
        cases f2 with
        | frame p2 b2 q2 =>
          have allocS : isa.push (.alloc 8) s = some (allocated 8 s) := by
            simp only [isa, push, fitS]
            rfl
          have allocT : isa.push (.alloc 8) t = some (allocated 8 t) := by
            simp only [isa, push, fitT]
            rfl
          have eqS := Option.some.inj (allocS.symm.trans p1)
          have eqT := Option.some.inj (allocT.symm.trans p2)
          subst eqS eqT
          cases b1 with
          | seq args1 call1 =>
            cases b2 with
            | seq args2 call2 =>
              obtain ⟨_, s1, runS, inputS⟩ := montCallArgs_ready s hs cs ho ha hb boundS
              obtain ⟨_, t1, runT, inputT⟩ := montCallArgs_ready t ht ctStack ho ha hb boundT
              rw [(Exec.det runS args1).2] at inputS
              rw [(Exec.det runT args2).2] at inputT
              have argsSp : _ := (Exec.sp args1).trans
                ((show (allocated 8 s).sp = (allocated 8 t).sp by simp only [allocated, sp]).trans (Exec.sp args2).symm)
              obtain ⟨callTrace, _⟩ := montCall_rawCall_ct name callee ct _ _ _ _ _ _
                ⟨inputS, inputT, argsSp⟩ call1 call2
              have writeS : InRegions (allocated 8 s).wr (State.addr (allocated 8 s).sp) 4 :=
                ⟨⟨State.addr (allocated 8 s).sp, 8⟩, List.mem_cons_self, by
                  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
              have writeT : InRegions (allocated 8 t).wr (State.addr (allocated 8 t).sp) 4 :=
                ⟨⟨State.addr (allocated 8 t).sp, 8⟩, List.mem_cons_self, by
                  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
              have traceS := montCallArgs_trace (allocated 8 s)
                ⟨hs.workspace.nowrap, List.mem_cons_of_mem _ hs.workspace.writable⟩ size hs.ptr writeS ho.1 ha.1 hb.1 args1
              have traceT := montCallArgs_trace (allocated 8 t)
                ⟨ht.workspace.nowrap, List.mem_cons_of_mem _ ht.workspace.writable⟩ size ht.ptr writeT ho.1 ha.1 hb.1 args2
              exact ⟨by simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
                        rw [traceS, traceT, callTrace, restoreTrace]
                        simp only [allocated, sp], finalSp⟩

end VG.Proof.Bignum.Arm
