module

import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.MontContract
public import Batteries.Logic
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import Batteries.Logic
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFn
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
meta import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
meta import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! ### `Bignum.Arm.MontVerified`, which only this module used -/

section

/-! # Verified ARMv7 Montgomery multiplication against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- A minimal valid workspace: two-word numbers and modulus one. -/
def montSatWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def montSatMem : Mem := fun x =>
  if x = 0x8000 then 1 else
  let i := (x - 0x1000).toNat
  if i < 512 then (montSatWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

def montSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 1 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := montSatMem
  rd := [⟨0x8000, 4⟩]
  wr := [⟨0x1000, 512⟩]

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.MontCallFn`, which this module and modules that import it used -/

section

/-! # Callable Montgomery multiplication preserves the ARM procedure-call ABI -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Operand Keeps)

theorem montCallFn_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa MontCall.code s fun t => abiPreserved s t ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have eq := h.pushed_eq
  have framePush := FrameStack.pushed_frameA (rs := MontCall.savedRegs) h.stackFit
  unfold MontCall.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (call_entry_ok s h hb.1) ?_
  rintro u ⟨ready, memU, restU⟩
  rw [WP.seq_iff]
  have savedPush := call_push_saved s h.stackFit
  have stackRead : InRegions (u.rd ++ u.wr) (State.addr u.sp) 4 := by
    rw [restU.rd, restU.wr, restU.sp]
    refine ⟨⟨State.addr (callPushed s).sp, 40⟩, List.mem_append_right _ List.mem_cons_self, ?_⟩
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have stackSep : Region.Disjoint ⟨State.addr u.sp, 4⟩ ⟨State.addr base, 8 * len⟩ := by
    rw [restU.sp]
    exact h.stackWorkspace.sub_left (Region.sub_prefix (by decide))
  have savedBase : u.mem.readW (State.addr u.sp) 32 = base := by
    rw [memU, restU.sp]
    change (callPushed s).mem.readW (State.addr (s.sp - 40)) 32 = base
    simpa only [BitVec.add_zero] using (savedPush (.r0, 0) (by decide)).trans h.ptr
  have callReady : CallBodyReady base len w o a b u := ⟨ready, stackRead, stackSep, savedBase⟩
  have body := montCallArithmetic_ok u callReady ho ha hb
  refine WP.mono body ?_
  rintro v ⟨lt, value, keeps, frameBody, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 40 := restV.sp.trans restU.sp
  have wrV : v.wr = (callPushed s).wr := restV.wr.trans restU.wr
  rw [memU] at lt value keeps frameBody
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr callAllSaved := by
    rw [spV]
    have savedPush : Spill.Saved (callPushed s).mem (State.addr (s.sp - BitVec.ofNat 32 40)) s.gpr callAllSaved :=
      call_push_saved s h.stackFit
    exact savedPush.frame (lo := 0) (hi := 40) (by decide) frameBody (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace)
  have stackFit : v.sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega_using []
  have writable : (⟨State.addr v.sp, 40⟩ : Region) ∈ v.wr := by
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (call_restore_ok v s.gpr stackFit ⟨_, List.mem_append_right _ writable, Region.contains_self _ _⟩ saved) ?_
  rintro t ⟨restored, memT, restT⟩ ml ul hfl
  have spT : t.sp = s.sp - BitVec.ofNat 32 40 := restT.sp.trans spV
  have oldM := eq.number fits (by decide : 0 < 8)
  have oldA := eq.number fits ha.1
  have oldB := eq.number fits hb.1
  rw [oldM] at lt
  rw [oldM, oldA, oldB] at value
  have lostEq : WorkspaceEq (State.addr base) (8 * len) t.mem ml :=
    WorkspaceEq.of_frame (by omega_using [nowrap]) hfl (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    have member : r ∈ callCalleeSaved.map Prod.fst := by
      simpa only [callCalleeSaved, List.map_cons, List.map_nil, preserved] using hr
    obtain ⟨p, hp, eqr⟩ := List.mem_map.mp member
    rw [← eqr]
    exact restored p hp
  · rw [popped_sp, spT]
    exact BitVec.sub_add_cancel _ _
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact lt
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact value
  · intro i hi separate
    dsimp only
    rw [show ml (State.addr base + BitVec.ofNat 64 i) = t.mem (State.addr base + BitVec.ofNat 64 i)
      from lost_byte hfl (R := ⟨State.addr base, 8 * len⟩) h.stackWorkspace.symm hi, memT, keeps i hi separate]
    exact framePush.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
      (by change 8 * len ≤ 2 ^ 64; omega_using [nowrap]) hi

end VG.Proof.Bignum.Arm

end

end

/-! # The shared RSA Montgomery contract under AAPCS -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Operand)

abbrev callStackB (s : State) : BitVec 32 := s.mem.readW (State.addr s.sp) 32


theorem montCall_contract_pre (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    CallInput (s.gpr .r0) (s.gpr .r1).toNat (wOf s.mem (State.addr (s.gpr .r0)))
      (s.gpr .r2).toNat (s.gpr .r3).toNat (callStackB s).toNat s ∧
      Operand (s.gpr .r2).toNat ∧ Operand (s.gpr .r3).toNat ∧ Operand (callStackB s).toNat := by
  sig_pre [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argValue : stackArg s 0 = callStackB s := by simp [stackArg, argAddr]
  rw [argAddr, argValue] at h
  obtain ⟨stackFit, _, rd, wr, _, stackWs, stackArgSep, nowrap, layout, ho, ha, hb, inverse, operand⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, layout, rfl, rfl, ?_, ?_, ?_, inverse, operand, stackFit, ?_, ?_, ?_⟩, ho, ha, hb⟩
  · simpa only [Nat.mul_comm] using nowrap
  · rw [wr]; simp only [List.mem_singleton, State.addr, Nat.mul_comm]
  · simp
  · simp
  · simp
  · refine ⟨⟨State.addr s.sp, 4⟩, List.mem_append_left _ ?_, ?_⟩
    · rw [rd]; simp
    · simp [Region.Contains]
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    simpa only [State.addr, Nat.mul_comm] using stackWs
  · unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
    exact stackArgSep


theorem montCall_contract_correct (s : State) (h : (Proof.Rsa.Mont.mulContract abi 40).pre s) :
    ∃ tr t, Exec isa MontCall.code s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.Mont.mulContract abi 40).post s t := by
  obtain ⟨input, ho, ha, hb⟩ := montCall_contract_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := montCallFn_ok s input ho ha hb
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  have argValue : stackArg s 0 = callStackB s := by simp [stackArg, stackArgAddr, callStackB]
  rw [argValue]
  exact post

theorem montCall_contract_ct : ConstantTime isa (Proof.Rsa.Mont.mulContract abi 40).pre
    (Proof.Rsa.Mont.mulContract abi 40).pub MontCall.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨is, ho, ha, hb⟩ := montCall_contract_pre s hs
  obtain ⟨it, _, _, _⟩ := montCall_contract_pre t ht
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, width, p0, p1, p2, p3, pb⟩ := hp
  change [wOf s.mem (State.addr (s.gpr .r0))] = [wOf t.mem (State.addr (t.gpr .r0))] at width
  have wb := List.singleton_inj.mp width
  have bb : callStackB s = callStackB t := by simpa only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero, callStackB] using pb
  rw [← wb, ← p0, ← p1, ← p2, ← p3, ← bb] at it
  exact (montCallFn_ct ho ha hb s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

theorem montCall_contract_sat : ∃ s, (Proof.Rsa.Mont.mulContract abi 40).pre s := by
  sig_implies_sat [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [montSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using montSatState

theorem montCall_verified : Verified target MontCall.code (Proof.Rsa.Mont.mulContract abi 40) :=
  ⟨montCall_contract_correct, montCall_contract_ct, montCall_contract_sat⟩

end VG.Proof.Bignum.Arm
