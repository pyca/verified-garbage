module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Stores
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Stores
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint5
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.Rsa.Arm.RdBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.RecoverDet
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_rsa_recover_primes_det` on ARMv7 is verified against `recoverPrimesDetContract`

The push, entry and restore (`Recover.codeWith`, `Impl/Rsa/Arm/KeyFrame.lean`) around
the body (`bodyD_vp`): a call's result (`rd_ok`), constant time with the
pointers, the lengths, `n` and `e` public (`rd_ct`), and the contract.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm

/-- The public parameters of a call: the frame, the pointers, the lengths,
`n` and `e`. -/
def mkP (s : State) : RP where
  sp := s.sp - BitVec.ofNat 32 56
  pP := s.gpr .r0
  qP := s.gpr .r2
  nP := stackArg s 0
  eP := stackArg s 2
  dP := stackArg s 4
  B := stackArg s 6
  K := (stackArg s 1).toNat
  el := (stackArg s 3).toNat
  dl := (stackArg s 5).toNat
  SL := (stackArg s 7).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat

/-- The regions the body runs with: the frame, `p`, `q`, the working space
and Montgomery multiplication's. -/
def xRegs (s : State) : List Region := [(mkP s).rFr, (mkP s).rP, (mkP s).rQ, (mkP s).rS, (mkP s).rM]

/-- The arguments' regions. -/
abbrev cP (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev cQ (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev cN (s : State) : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
abbrev cE (s : State) : Region := ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
abbrev cD (s : State) : Region := ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩
abbrev cS (s : State) : Region := ⟨State.addr (stackArg s 6), (stackArg s 7).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 32⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 56#64, 56⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 56 ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 ≤ 2 ^ 32
  rd : s.rd = [cN s, cE s, cD s, cA s]
  wr : s.wr = [cP s, cQ s, cS s]
  pq : (cP s).Disjoint (cQ s)
  pn : (cP s).Disjoint (cN s)
  pe : (cP s).Disjoint (cE s)
  pd : (cP s).Disjoint (cD s)
  pS : (cP s).Disjoint (cS s)
  pA : (cP s).Disjoint (cA s)
  qn : (cQ s).Disjoint (cN s)
  qe : (cQ s).Disjoint (cE s)
  qd : (cQ s).Disjoint (cD s)
  qS : (cQ s).Disjoint (cS s)
  qA : (cQ s).Disjoint (cA s)
  nS : (cN s).Disjoint (cS s)
  eS : (cE s).Disjoint (cS s)
  dS : (cD s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fp : (cF s).Disjoint (cP s)
  Fq : (cF s).Disjoint (cQ s)
  Fn : (cF s).Disjoint (cN s)
  Fe : (cF s).Disjoint (cE s)
  Fd : (cF s).Disjoint (cD s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fp : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fq : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fn : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  fe : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  fd : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  fS : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (stackArg s 1).toNat
  pl : (s.gpr .r1).toNat = (stackArg s 1).toNat
  ql : (s.gpr .r3).toNat = (stackArg s 1).toNat
  el1 : 1 ≤ (stackArg s 3).toNat
  el2 : (stackArg s 3).toNat ≤ (stackArg s 1).toNat
  dl1 : 1 ≤ (stackArg s 5).toNat
  dl2 : (stackArg s 5).toNat ≤ (stackArg s 1).toNat
  scr : Spec.Rsa.scratchWords (stackArg s 1).toNat ≤ (stackArg s 7).toNat

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Recover VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Upd Mupd Rest wp_str)

/-- A region apart from both parts of `[a, a + 88)`. -/
theorem disj88 {r : Region} {a : Addr} (h1 : r.Disjoint ⟨a, 56⟩) (h2 : r.Disjoint ⟨a + BitVec.ofNat 64 56, 32⟩) :
    r.Disjoint ⟨a, 88⟩ := by
  intro x hx hc
  simp only [Region.Contains] at hc
  by_cases hlt : (x - a).toNat < 56
  · exact h1 x hx (by simp only [Region.Contains]; omega)
  · refine h2 x hx ?_
    simp only [Region.Contains]
    have := (Offset.lt_iff x a (d := 56) (n := 32) (by decide)).mpr ⟨by omega, by omega⟩
    omega

section
variable {s : State}

theorem CIn.sp' (h : CIn s) : State.addr (s.sp - BitVec.ofNat 32 56) = State.addr s.sp - 56#64 :=
  FrameStack.addr_sub' h.spLo

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 8) :
    off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  simp only [stackArgAddr, off]
  rw [h.sp', addr_add (by omega), ← Offset.add_add, BitVec.sub_add_cancel]

/-- The memory after the push and the entry. -/
abbrev entryMem (s : State) : Mem :=
  (pcPushed s).mem.writeW (off (State.addr (s.sp - BitVec.ofNat 32 56)) 4) (s.gpr .r0)

theorem CIn.frameE (h : CIn s) : Frame [cF s] s.mem (entryMem s) := by
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) h.spLo
  have e : FrameStack.belowA s.sp (4 * 14) = cF s := by
    show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [h.sp']
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  refine f.writeW (r := cF s) (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, off]
  rw [h.sp', Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide

/-- The entry before the check of `n`. -/
def entryHead : List Instr := [.addSp .r12 0, .str .r0 .r12 oP, .ldrSp .r4 aoN, .ldrSp .r6 aoK]

theorem entry_eq : entry = entryHead ++ VG.Impl.Bignum.Arm.modulusCheck := rfl

/-- The entry's head: `p` saved, `n` and `n_len` loaded. -/
theorem head_run (h : CIn s) :
    WP isa (.block entryHead) (pcPushed s) fun u => u.sp = s.sp - BitVec.ofNat 32 56 ∧ u.rd = s.rd ∧
      u.wr = (pcPushed s).wr ∧ u.mem = entryMem s ∧ u.gpr .r4 = stackArg s 0 ∧ u.gpr .r6 = stackArg s 1 := by
  have spLo := h.spLo; have spHi := h.spHi
  have sp' : (pcPushed s).sp = s.sp - BitVec.ofNat 32 56 := rfl
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold entryHead
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
  have stackW : (⟨State.addr (pcPushed s).sp, 56⟩ : Region) ∈ (pcPushed s).wr := List.mem_cons_self
  refine wp_str (a := off (State.addr (s.sp - BitVec.ofNat 32 56)) 4) (by decide)
    (by rw [h1.gpr, BitVec.add_zero, sp']; exact addr_add (by simp only [oP]; omega))
    ⟨_, by rw [h1.wr]; exact stackW, Offset.contains_base _ (by decide) (by decide)⟩ fun u2 m2 => ?_
  have mem2 : u2.mem = entryMem s := by rw [m2.mem, h1.mem, h1.other _ (by decide)]; rfl
  have eA : cA s = ⟨State.addr s.sp, 32⟩ := by simp [cA, stackArgAddr]
  have ei : ∀ i < 8, stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := fun i hi => by
    simp only [stackArgAddr]; exact addr_add (by omega)
  have fr := h.frameE
  have argRead : ∀ i < 8, InRegions (u2.rd ++ u2.wr) (stackArgAddr s i) 4 := fun i hi => by
    refine ⟨cA s, List.mem_append_left _ (by rw [m2.rd, h1.rd]; show cA s ∈ s.rd; rw [h.rd]; simp), ?_⟩
    rw [eA, ei i hi]; exact Offset.contains_base _ (by omega) (by omega)
  have argVal : ∀ i < 8, u2.mem.readW (stackArgAddr s i) 32 = stackArg s i := fun i hi => by
    rw [mem2]
    refine fr.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    refine h.FA.symm.sub_left ?_
    rw [eA, ei i hi]; exact Offset.sub_base _ (by omega)
  have spA : ∀ i < 8, State.addr (u2.sp + BitVec.ofNat 32 (56 + 4 * i)) = stackArgAddr s i := fun i hi => by
    rw [m2.sp, h1.sp, sp', ← h.argAddr hi]
    simp only [off]; exact addr_add (by rw [FrameStack.sub_toNat' spLo]; omega)
  refine wp_loadStack (d := aoN) (a := stackArgAddr s 0) (by decide) (spA 0 (by decide)) (argRead 0 (by decide))
    fun u3 h3 => ?_
  refine wp_loadStack (d := aoK) (a := stackArgAddr s 1) (by decide) (by rw [h3.sp]; exact spA 1 (by decide))
    (by rw [h3.rd, h3.wr]; exact argRead 1 (by decide)) fun u4 h4 => WP.block_nil ?_
  exact ⟨by rw [h4.sp, h3.sp, m2.sp, h1.sp]; rfl, by rw [h4.rd, h3.rd, m2.rd, h1.rd]; rfl,
    by rw [h4.wr, h3.wr, m2.wr, h1.wr], by rw [h4.mem, h3.mem, mem2],
    by rw [h4.other _ (by decide), h3.gpr, argVal 0 (by decide)], by rw [h4.gpr, h3.mem, argVal 1 (by decide)]⟩

/-- The entry: `p` saved, and Z iff `n` is valid. -/
theorem entry_run (h : CIn s) :
    WP isa (.block entry) (pcPushed s) fun u => u.sp = s.sp - BitVec.ofNat 32 56 ∧ u.rd = s.rd ∧
      u.wr = (pcPushed s).wr ∧ u.mem = entryMem s ∧
      u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0))
        (stackArg s 1).toNat)) (stackArg s 1).toNat := by
  rw [entry_eq, WP.block_append_iff]
  refine WP.mono (head_run h) fun u4 ⟨sp4, rd4, wr4, mem4, r4, r6⟩ => ?_
  have hk := h.valid
  simp only [Spec.Rsa.lenValid] at hk
  have readN : InRegions (u4.rd ++ u4.wr) (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    ⟨cN s, List.mem_append_left _ (by rw [rd4]; show cN s ∈ s.rd; rw [h.rd]; simp), Region.contains_self _ _⟩
  refine WP.mono (modulusCheck_ok u4 (src := stackArg s 0) (k := (stackArg s 1).toNat) hk.1 hk.2 h.fn readN
    r4 (by rw [r6]; simp)) fun t ⟨z, m, r⟩ => ?_
  refine ⟨by rw [r.sp, sp4], by rw [r.rd, rd4], by rw [r.wr, wr4], by rw [m, mem4], ?_⟩
  rw [z, mem4]
  congr 2
  exact VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frameE (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.Fn.symm) (by omega)

end

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Recover VG.Proof.Bignum.Arm

section
variable {s : State}

theorem cA_eq (s : State) : cA s = ⟨State.addr s.sp, 32⟩ := by simp [cA, stackArgAddr]

theorem CIn.ei (h : CIn s) {i : Nat} (hi : i < 8) : stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := by
  have := h.spHi
  simp only [stackArgAddr]; exact addr_add (by omega)

/-- The stack arguments after the entry. -/
theorem CIn.argVal (h : CIn s) {i : Nat} (hi : i < 8) : (entryMem s).readW (stackArgAddr s i) 32 = stackArg s i := by
  refine h.frameE.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  refine h.FA.symm.sub_left ?_
  rw [cA_eq, h.ei hi]; exact Offset.sub_base _ (by omega)

theorem CIn.bytes (h : CIn s) {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (entryMem s) R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frameE (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

theorem CIn.rP (h : CIn s) : (mkP s).rP = cP s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (s.gpr .r1).toNat⟩; rw [h.pl]; rfl

theorem CIn.rQ (h : CIn s) : (mkP s).rQ = cQ s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (s.gpr .r3).toNat⟩; rw [h.ql]; rfl

theorem CIn.rFr (h : CIn s) : (mkP s).rFr = cF s := by
  show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _; rw [h.sp']

theorem CIn.disjF (h : CIn s) {r : Region} (h1 : r.Disjoint (cF s)) (h2 : r.Disjoint (cA s)) :
    r.Disjoint (mkP s).rF := by
  show r.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 56), 88⟩
  refine disj88 (by rw [h.sp']; exact h1) ?_
  have e : State.addr (s.sp - BitVec.ofNat 32 56) + BitVec.ofNat 64 56 = State.addr s.sp := by
    rw [h.sp', BitVec.sub_add_cancel]
  rw [e, ← cA_eq]; exact h2

theorem in_x (h : CIn s) {u : State} (hsp : u.sp = s.sp - BitVec.ofNat 32 56) (hrd : u.rd = s.rd)
    (hmem : u.mem = entryMem s) :
    In (mkP s) (u.withRegions u.rd (xRegs s)) := by
  have spLo := h.spLo; have spHi := h.spHi
  have hk := h.valid; simp only [Spec.Rsa.lenValid] at hk
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  have rdm : ∀ r ∈ [cN s, cE s, cD s, cA s], r ∈ (u.withRegions u.rd (xRegs s)).rd ++
      (u.withRegions u.rd (xRegs s)).wr := fun r hr => List.mem_append_left _ (by
    simp only [State.withRegions_rd, hrd, h.rd]; exact hr)
  have fwArg : ∀ i < 8, fw (u.withRegions u.rd (xRegs s)).mem (mkP s) (56 + 4 * i) = stackArg s i := fun i hi => by
    simp only [fw, State.withRegions_mem, hmem]
    show (entryMem s).readW (off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i)) 32 = _
    rw [h.argAddr hi]; exact h.argVal hi
  have nB : Spec.Rsa.bytesAt (entryMem s) (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat := h.bytes (R := cN s) h.Fn (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  have eB : Spec.Rsa.bytesAt (entryMem s) (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat := h.bytes (R := cE s) h.Fe (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  refine ⟨by simp only [State.withRegions_sp, hsp]; rfl, by show (s.sp - BitVec.ofNat 32 56).toNat + 88 ≤ 2 ^ 32; rw [spN]; omega, rfl,
    ⟨cN s, rdm _ (by simp), Region.contains_self _ _⟩, ⟨cE s, rdm _ (by simp), Region.contains_self _ _⟩,
    ⟨cD s, rdm _ (by simp), Region.contains_self _ _⟩, ⟨cA s, rdm _ (by simp), ?_⟩, hk.1, hk.2, h.el1, h.el2, h.dl1,
    h.dl2, h.scr, by show _ + (stackArg s 1).toNat ≤ _; rw [← h.pl]; exact h.fp,
    by show _ + (stackArg s 1).toNat ≤ _; rw [← h.ql]; exact h.fq, h.fn, h.fe, h.fd, h.fS,
    by rw [h.rP]; exact h.pS.symm, by rw [h.rQ]; exact h.qS.symm, h.nS.symm, h.eS.symm, h.dS.symm,
    h.disjF h.FS.symm h.SA, by rw [h.rP, h.rQ]; exact h.pq, by rw [h.rP]; exact h.pn, by rw [h.rP]; exact h.pe,
    by rw [h.rP]; exact h.pd, by rw [h.rP]; exact h.disjF h.Fp.symm h.pA, by rw [h.rQ]; exact h.qn,
    by rw [h.rQ]; exact h.qe, by rw [h.rQ]; exact h.qd, by rw [h.rQ]; exact h.disjF h.Fq.symm h.qA,
    by rw [h.rFr]; exact h.Fn.symm, by rw [h.rFr]; exact h.Fe.symm, by rw [h.rFr]; exact h.Fd.symm,
    ?_, ?_, fwArg 0 (by decide), ?_, fwArg 2 (by decide), ?_, fwArg 4 (by decide), ?_, fwArg 6 (by decide),
    by simp only [State.withRegions_mem, hmem]; exact nB, by simp only [State.withRegions_mem, hmem]; exact eB⟩
  · show (cA s).Contains (off (State.addr (s.sp - BitVec.ofNat 32 56)) 56) 32
    rw [show off (State.addr (s.sp - BitVec.ofNat 32 56)) 56 = stackArgAddr s 0 from h.argAddr (i := 0) (by decide)]
    exact Region.contains_self _ _
  · simp only [fw, State.withRegions_mem, hmem]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [fw, State.withRegions_mem, hmem]
    show ((pcPushed s).mem.writeW (off (State.addr (s.sp - 56)) 4) (s.gpr .r0)).readW
      (off (State.addr (s.sp - 56)) 8) 32 = s.gpr .r2
    rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inr (by decide)) (by decide) (by decide)) (by decide)]
    have := pc_push_saved s spLo (.r2, 8) (by simp [pcAllSaved])
    exact this
  · show fw _ _ (56 + 4 * 1) = _; rw [fwArg 1 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 1).toNat; simp
  · show fw _ _ (56 + 4 * 3) = _; rw [fwArg 3 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 3).toNat; simp
  · show fw _ _ (56 + 4 * 5) = _; rw [fwArg 5 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 5).toNat; simp

end

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm

section
variable {s : State}

/-- The body's regions are within the frame and the caller's writable ones. -/
theorem CIn.xCovers (h : CIn s) (sz : Sizes (mkP s)) : Covers (xRegs s) (pcPushed s).wr := by
  have hf : (mkP s).B.toNat + (mkP s).Z ≤ 2 ^ 32 := h.fS
  have pl := h.pl; have ql := h.ql
  have mS : cS s ∈ (pcPushed s).wr := by rw [pushed_wr, h.wr]; simp
  refine Covers.of_sub fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq rfl⟩
  · exact ⟨cP s, by rw [pushed_wr, h.wr]; simp, 0, by rw [BitVec.add_zero]; rfl,
      by show 0 + (stackArg s 1).toNat ≤ (s.gpr .r1).toNat; omega⟩
  · exact ⟨cQ s, by rw [pushed_wr, h.wr]; simp, 0, by rw [BitVec.add_zero]; rfl,
      by show 0 + (stackArg s 1).toNat ≤ (s.gpr .r3).toNat; omega⟩
  · exact ⟨cS s, mS, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq (Nat.zero_add _)⟩
  · refine ⟨cS s, mS, (mkP s).oM, by show State.addr (mkP s).M0 = State.addr (stackArg s 6) + _; rw [M0_addr sz hf]; rfl, ?_⟩
    show (mkP s).oM + 8 * (mkP s).lenM ≤ (mkP s).Z
    rw [sz.endM]; exact Nat.le_trans (arr_mono (show mBase + 8 ≤ nArr by decide)) sz.fits

/-- The callee-saved registers' slots after the entry. -/
theorem CIn.savedE (h : CIn s) : Spill.Saved (entryMem s) (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
  (pc_push_callee_saved s h.spLo).frame (lo := 16) (hi := 56) (by decide)
    ((Frame.refl [⟨off (State.addr (s.sp - 56)) 4, 4⟩] _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))

end

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm

theorem entry_ct {s₀ t₀ : State} (hs : CIn s₀) (ht : CIn t₀) (sp : s₀.sp = t₀.sp)
    (a0 : stackArg s₀ 0 = stackArg t₀ 0) (a1 : stackArg s₀ 1 = stackArg t₀ 1) :
    RelCT isa (fun a b => a = pcPushed s₀ ∧ b = pcPushed t₀) (.block entry) (fun _ _ => True) := by
  rw [entry_eq]
  have head := ((VG.Proof.Rsa.Arm.setupChecked_ct [.str .r0 .r12 oP, .ldrSp .r4 aoN, .ldrSp .r6 aoK]
    (by decide) (by decide)).mono (P' := fun a b => a = pcPushed s₀ ∧ b = pcPushed t₀)
    (fun a b ⟨ha, hb⟩ => by subst ha; subst hb; simp only [pushed_sp, sp]) fun _ _ h => h).wp
    (F₁ := fun (u : State) => u.gpr .r4 = stackArg s₀ 0 ∧ u.gpr .r6 = stackArg s₀ 1)
    (F₂ := fun (u : State) => u.gpr .r4 = stackArg t₀ 0 ∧ u.gpr .r6 = stackArg t₀ 1) (fun a b ⟨ha, hb⟩ => by
      subst ha; subst hb
      exact ⟨WP.mono (head_run hs) fun u h => ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩,
        WP.mono (head_run ht) fun u h => ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩)
  obtain ⟨_, hc⟩ := check_taint
  refine RelCT.block_append (head.seq (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r4, .r6]) ?_ hc))
  intro a b ⟨_, ⟨a4, a6⟩, b4, b6⟩
  apply Taint.agree_ofRegs
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · rw [a4, b4, a0]
  · rw [a6, b6, a1]

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Recover

/-- A 64-byte modulus, one-byte exponents, the outputs at `0x1000` and
`0x1100`, the working space at `0x4000`, and the stack arguments at
`0x8000`. -/
def rvSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8004 then 0x40 else if a = 0x8009 then 0x30
    else if a = 0x800C then 1 else if a = 0x8011 then 0x31 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x40 else if a = 0x801C then 0x20 else if a = 0x801D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x8000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x4000, 8448⟩]

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.RecoverDet (bodyD_vp ResD)

/-- The body after the entry. -/
abbrev bodyD : Prog isa := .ite .eq VG.Impl.Rsa.Arm.RecoverDet.valid fail

/-- The public parameters. -/
abbrev mkPD (s : State) : RP := mkP s

section
variable {s : State}

/-- A call's result. -/
theorem rd_ok [InvLaw] (h : CIn s) (he : (stackArg s 3).toNat ≤ 8) :
    WP isa VG.Impl.Rsa.Arm.RecoverDet.code s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenAll t.mem [(State.addr (s.gpr .r0), (stackArg s 1).toNat),
        (State.addr (s.gpr .r2), (stackArg s 1).toNat)] (t.gpr .r0)
        ((Spec.Rsa.primesKeyDet (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).map
          fun v => [v.1, v.2]) := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold VG.Impl.Rsa.Arm.RecoverDet.code codeWith
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (entry_run h) fun u ⟨usp, urd, uwr, umem, uz⟩ => ?_
  rw [WP.seq_iff]
  have pre := in_x h usp urd umem
  have sz := pre.sizes
  obtain ⟨tr, v, run, bo, res⟩ := (bodyD_vp (P := mkP s) he).wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers sz
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  refine WP.mono (Q := fun x => x = v.withRegions u.rd u.wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := bo.sp.trans usp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
    h.savedE.frame (lo := 16) (hi := 56) (by decide) (by rw [← umem]; exact bo.frame) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pre.sF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact pre.pF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact pre.qF.symm.sub_left (Offset.sub_base _ (by decide)))
  have fit : (v.withRegions u.rd u.wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; omega
  have read : InRegions ((v.withRegions u.rd u.wr).rd ++ (v.withRegions u.rd u.wr).wr)
      (State.addr (v.withRegions u.rd u.wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (v.withRegions u.rd u.wr).wr := by
      rw [State.withRegions_wr, uwr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, State.withRegions_sp, vsp]
    exact BitVec.sub_add_cancel _ _
  · have dEq : dB (mkP s) (u.withRegions u.rd (xRegs s)) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat := by
      show Spec.Rsa.bytesAt u.mem _ _ = _
      rw [umem]; exact h.bytes (R := cD s) h.Fd (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret, State.withRegions_mem]
    rw [dEq] at res
    exact res

end

/-- The body's run, widened to the caller's regions. -/
theorem body_wideD [InvLaw] {s u : State} (h : CIn s) (he : (stackArg s 3).toNat ≤ 8) (usp : u.sp = s.sp - BitVec.ofNat 32 56) (urd : u.rd = s.rd)
    (uwr : u.wr = (pcPushed s).wr) (umem : u.mem = entryMem s)
    (uz : u.z = Spec.Rsa.modulusValid (mkP s).n (mkP s).K) :
    ∃ tr v, Exec isa bodyD (u.withRegions u.rd (xRegs s)) tr v ∧
      Exec isa bodyD u tr (v.withRegions u.rd u.wr) ∧ v.sp = s.sp - BitVec.ofNat 32 56 := by
  have pre := in_x h usp urd umem
  obtain ⟨tr, v, run, bo, _⟩ := (bodyD_vp (P := mkP s) he).wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers pre.sizes
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  exact ⟨tr, v, run, run', bo.sp.trans usp⟩

/-- Two calls with the same public parameters. -/
theorem rd_ct [InvLaw] : RelCT isa (fun s t => (CIn s ∧ (stackArg s 3).toNat ≤ 8) ∧ CIn t ∧ s.sp = t.sp ∧
    mkPD s = mkPD t ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1) VG.Impl.Rsa.Arm.RecoverDet.code
    (fun _ _ => True) := by
  unfold VG.Impl.Rsa.Arm.RecoverDet.code codeWith
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨⟨hs, he⟩, ht, sp, hP, a0, a1⟩, ps, pt⟩ := hp
  have he' : (stackArg t0 3).toNat ≤ 8 := by
    have e : (mkPD s0).el = (mkPD t0).el := by rw [hP]
    change (stackArg s0 3).toNat = (stackArg t0 3).toNat at e
    omega
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.spLo
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.spLo
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      have trE := ((entry_ct hs ht sp a0 a1) _ _ _ _ _ _ ⟨rfl, rfl⟩ entry1 entry2).1
      obtain ⟨_, u1, run1, usp1, urd1, uwr1, umem1, uz1⟩ := entry_run hs
      obtain ⟨_, v1, run2, usp2, urd2, uwr2, umem2, uz2⟩ := entry_run ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      cases tail1 with
      | seq body1 rest1 =>
        cases tail2 with
        | seq body2 rest2 =>
          obtain ⟨trB1, w1, runB1, wide1, wsp1⟩ := body_wideD hs he usp1 urd1 uwr1 umem1 uz1
          obtain ⟨trB2, w2, runB2, wide2, wsp2⟩ := body_wideD ht he' usp2 urd2 uwr2 umem2 uz2
          obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
          obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
          have pre1 := in_x hs usp1 urd1 umem1
          have pre2 := in_x ht usp2 urd2 umem2
          change In (mkPD t0) _ at pre2
          rw [← hP] at pre2
          have uz2' := uz2
          change _ = Spec.Rsa.modulusValid (mkPD t0).n (mkPD t0).K at uz2'
          rw [← hP] at uz2'
          have trB := ((bodyD_vp (P := mkPD s0) he).ct _ _ _ _ _ _
            ⟨_, _, ⟨⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩, uz1⟩, ⟨⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩, uz2'⟩⟩
            runB1 runB2).1
          have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
            (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
            (by show w1.sp = w2.sp; rw [wsp1, wsp2, sp]) rest1 rest2).1
          exact ⟨by rw [trE, trB, trR], trivial⟩

theorem cinD_of_pre (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 56).pre s) :
    CIn s ∧ (stackArg s 3).toNat ≤ 8 := by
  sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, el8, dl1, dl2, scr⟩ := h
  have hk := valid
  simp only [Spec.Rsa.lenValid] at hk
  exact ⟨⟨spLo, spHi, rd, wr, pq, pn, pe, pd, pS, pA, qn, qe, qd, qS, qA, nS, eS, dS, SA, Fp, Fq, Fn, Fe, Fd, FS, FA,
    fp, fq, fn, fe, fd, fS, valid, pl, ql, el1, by omega, dl1, dl2, scr⟩, el8⟩

theorem rd_contract_correct [InvLaw] (s : State) (h : (Spec.Rsa.recoverPrimesDetContract abi 56).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.Arm.RecoverDet.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesDetContract abi 56).post s t := by
  obtain ⟨hc, he⟩ := cinD_of_pre s h
  obtain ⟨tr, t, run, preserved, post⟩ := rd_ok hc he
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

/-- Calls with the same public arguments, `n` and `e` have the same public parameters. -/
theorem mkPD_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a3 : stackArg s 3 = stackArg t 3) (a4 : stackArg s 4 = stackArg t 4) (a5 : stackArg s 5 = stackArg t 5)
    (a6 : stackArg s 6 = stackArg t 6) (a7 : stackArg s 7 = stackArg t 7)
    (hn : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 3).toNat) :
    mkPD s = mkPD t := by
  unfold mkPD mkP
  rw [hn, he, sp, p0, p2, a0, a1, a2, a3, a4, a5, a6, a7]

theorem rd_contract_ct [InvLaw] : ConstantTime isa (Spec.Rsa.recoverPrimesDetContract abi 56).pre
    (Spec.Rsa.recoverPrimesDetContract abi 56).pub VG.Impl.Rsa.Arm.RecoverDet.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cinD_of_pre s hs
  have it := (cinD_of_pre t ht).1
  sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, a0, a1, a2, a3, a4, a5, a6, a7⟩ := hp
  have b3 := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  obtain ⟨hn, he⟩ := List.append_inj b3 (by
    simp only [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a1])
  exact (rd_ct s t tr1 tr2 u v ⟨is, it, sp, mkPD_eq sp p0 p2 a0 a1 a2 a3 a4 a5 a6 a7 hn he, a0, a1⟩ e1 e2).1

theorem rd_contract_sat : ∃ s, (Spec.Rsa.recoverPrimesDetContract abi 56).pre s := by
  sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [rvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using rvSatState

/-- `vg_rsa_recover_primes_det`. -/
theorem recover_primes_det_verified [InvLaw] :
    Verified target VG.Impl.Rsa.Arm.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi 56) :=
  ⟨rd_contract_correct, rd_contract_ct, rd_contract_sat⟩

end VG.Proof.Rsa.Arm.Recover
