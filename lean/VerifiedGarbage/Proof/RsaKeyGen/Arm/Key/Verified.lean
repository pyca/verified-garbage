module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top1
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint3
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Body
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front3

/-! ### `RsaKeyGen.Arm.Key.Top3`, which only this module used -/

section

/-! ### `RsaKeyGen.Arm.Key.Top2`, which this module and modules that import it used -/

section

/-! # An RSA key on ARMv7: the body's start (`in_k`)

After the push, with the regions `xRegs`: the start `In` of the body.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- A region apart from both halves of `[a, a + 112)`. -/
theorem disj112 {r : Region} {a : Addr} (h1 : r.Disjoint ⟨a, 56⟩) (h2 : r.Disjoint ⟨a + BitVec.ofNat 64 56, 56⟩) :
    r.Disjoint ⟨a, 112⟩ := by
  intro x hx hc
  simp only [Region.Contains] at hc
  by_cases hlt : (x - a).toNat < 56
  · exact h1 x hx (by simp only [Region.Contains]; omega_using [hlt])
  · refine h2 x hx ?_
    simp only [Region.Contains]
    have := (Offset.lt_iff x a (d := 56) (n := 56) (by decide)).mpr ⟨by omega_using [hlt], by omega_using [hc]⟩
    omega_using [this]

section
variable {s : State}

theorem CIn.sp' (h : CIn s) : State.addr (s.sp - BitVec.ofNat 32 56) = State.addr s.sp - 56#64 :=
  FrameStack.addr_sub' h.spLo

theorem cA_eq (s : State) : cA s = ⟨State.addr s.sp, 56⟩ := by simp [cA, stackArgAddr]

theorem CIn.ei (h : CIn s) {i : Nat} (hi : i < 14) :
    stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := by
  have := h.spHi
  simp only [stackArgAddr]; exact addr_add (by omega_using [hi, this])

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 14) :
    off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  simp only [stackArgAddr, off]
  rw [h.sp', addr_add (by omega_using [hi, this]), ← Offset.add_add, BitVec.sub_add_cancel]

theorem CIn.frameP (h : CIn s) : Frame [cF s] s.mem (pcPushed s).mem := by
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) h.spLo
  have e : FrameStack.belowA s.sp (4 * 14) = cF s := by
    show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [h.sp']
  rwa [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f

/-- The stack arguments after the push. -/
theorem CIn.argVal (h : CIn s) {i : Nat} (hi : i < 14) :
    (pcPushed s).mem.readW (stackArgAddr s i) 32 = stackArg s i := by
  refine h.frameP.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  refine h.FA.symm.sub_left ?_
  rw [cA_eq, h.ei hi]; exact Offset.sub_base _ (by omega_using [hi])

theorem CIn.bytes (h : CIn s) {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (pcPushed s).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frameP (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

theorem CIn.rN (h : CIn s) : (mkP s).rN = cN s := by
  show (⟨_, 2 * (stackArg s 1).toNat⟩ : Region) = ⟨_, (s.gpr .r1).toNat⟩; rw [h.nl]; rfl
theorem CIn.rD (h : CIn s) : (mkP s).rD = cD s := by
  show (⟨_, 2 * (stackArg s 1).toNat⟩ : Region) = ⟨_, (s.gpr .r3).toNat⟩; rw [h.dl, h.nl]; rfl
theorem CIn.rQ (h : CIn s) : (mkP s).rQ = cQ s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (stackArg s 3).toNat⟩; rw [h.ql]; rfl
theorem CIn.rDp (h : CIn s) : (mkP s).rDp = cDp s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (stackArg s 5).toNat⟩; rw [h.dpl]; rfl
theorem CIn.rDq (h : CIn s) : (mkP s).rDq = cDq s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (stackArg s 7).toNat⟩; rw [h.dql]; rfl
theorem CIn.rQi (h : CIn s) : (mkP s).rQi = cQi s := by
  show (⟨_, (stackArg s 1).toNat⟩ : Region) = ⟨_, (stackArg s 9).toNat⟩; rw [h.qil]; rfl
theorem CIn.rFr (h : CIn s) : (mkP s).rFr = cF s := by
  show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _; rw [h.sp']

theorem CIn.disjF (h : CIn s) {r : Region} (h1 : r.Disjoint (cF s)) (h2 : r.Disjoint (cA s)) :
    r.Disjoint (mkP s).rF := by
  show r.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 56), 112⟩
  refine disj112 (by rw [h.sp']; exact h1) ?_
  have e : State.addr (s.sp - BitVec.ofNat 32 56) + BitVec.ofNat 64 56 = State.addr s.sp := by
    rw [h.sp', BitVec.sub_add_cancel]
  rw [e, ← cA_eq]; exact h2

/-- The state the body starts from. -/
abbrev sx (s : State) : State := (pcPushed s).withRegions s.rd (xRegs s)

theorem in_k (h : CIn s) : In (mkP s) (sx s) := by
  have spLo := h.spLo; have spHi := h.spHi
  have hk := h.valid; simp only [Spec.RsaKeyGen.primeLenValid] at hk
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  have rdm : ∀ r ∈ [cE s, cA s], r ∈ (sx s).rd ++ (sx s).wr := fun r hr => List.mem_append_left _ (by
    simp only [State.withRegions_rd, h.rd]; exact hr)
  have fwArg : ∀ i < 14, fw (sx s).mem (mkP s) (56 + 4 * i) = stackArg s i := fun i hi => by
    simp only [fw, State.withRegions_mem]
    show (pcPushed s).mem.readW (off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i)) 32 = _
    rw [h.argAddr hi]; exact h.argVal hi
  have fwSaved : ∀ p ∈ [(Reg.r0, 0), (Reg.r1, 4), (Reg.r2, 8)], fw (sx s).mem (mkP s) p.2 = s.gpr p.1 :=
    fun p hp => pc_push_saved s spLo p (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [pcAllSaved])
  have eS : (mkP s).rS = cS s := rfl
  have eE : (mkP s).rE = cE s := rfl
  have eP : (mkP s).rP = cP s := rfl
  have bP : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    h.bytes (R := cP s) h.Fp (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  have bQ : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat :=
    h.bytes (R := (mkP s).rQ) (by rw [h.rQ]; exact h.Fq) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  have bE : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 10)) (stackArg s 11).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat :=
    h.bytes (R := cE s) h.Fe (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  refine ⟨by simp only [State.withRegions_sp]; rfl, by show (s.sp - BitVec.ofNat 32 56).toNat + 112 ≤ 2 ^ 32; omega_using [spHi, spN],
    rfl, ⟨cE s, rdm _ (by simp), Region.contains_self _ _⟩, ⟨cA s, rdm _ (by simp), ?_⟩, hk.1, hk.2.1, hk.2.2,
    h.el1, h.el2, by show Spec.Rsa.scratchWords (2 * (stackArg s 1).toNat) ≤ (stackArg s 13).toNat; rw [← h.nl]; exact h.scr,
    by show _ + 2 * (stackArg s 1).toNat ≤ _; rw [← h.nl]; exact h.fn,
    by show _ + 2 * (stackArg s 1).toNat ≤ _; rw [← h.nl, ← h.dl]; exact h.fd, h.fp,
    by show _ + (stackArg s 1).toNat ≤ _; rw [← h.ql]; exact h.fq,
    by show _ + (stackArg s 1).toNat ≤ _; rw [← h.dpl]; exact h.fdp,
    by show _ + (stackArg s 1).toNat ≤ _; rw [← h.dql]; exact h.fdq,
    by show _ + (stackArg s 1).toNat ≤ _; rw [← h.qil]; exact h.fqi, h.fe, h.fS,
    by rw [eS, h.rN]; exact h.nS.symm, by rw [eS, h.rD]; exact h.dS.symm, by rw [eS, eP]; exact h.pS.symm,
    by rw [eS, h.rQ]; exact h.qS.symm, by rw [eS, h.rDp]; exact h.dpS.symm, by rw [eS, h.rDq]; exact h.dqS.symm,
    by rw [eS, h.rQi]; exact h.qiS.symm, by rw [eS, eE]; exact h.eS.symm, h.disjF h.FS.symm h.SA,
    by rw [h.rN, h.rD]; exact h.nD, by rw [h.rN, eP]; exact h.nP, by rw [h.rN, h.rQ]; exact h.nQ,
    by rw [h.rN, h.rDp]; exact h.nDp, by rw [h.rN, h.rDq]; exact h.nDq, by rw [h.rN, h.rQi]; exact h.nQi,
    by rw [h.rD, eP]; exact h.dP, by rw [h.rD, h.rQ]; exact h.dQ, by rw [h.rD, h.rDp]; exact h.dDp,
    by rw [h.rD, h.rDq]; exact h.dDq, by rw [h.rD, h.rQi]; exact h.dQi,
    by rw [eP, h.rQ]; exact h.pQ, by rw [eP, h.rDp]; exact h.pDp, by rw [eP, h.rDq]; exact h.pDq,
    by rw [eP, h.rQi]; exact h.pQi,
    by rw [h.rQ, h.rDp]; exact h.qDp, by rw [h.rQ, h.rDq]; exact h.qDq, by rw [h.rQ, h.rQi]; exact h.qQi,
    by rw [h.rDp, h.rDq]; exact h.dpDq, by rw [h.rDp, h.rQi]; exact h.dpQi, by rw [h.rDq, h.rQi]; exact h.dqQi,
    by rw [h.rN]; exact h.disjF h.Fn.symm h.nA, by rw [h.rD]; exact h.disjF h.Fd.symm h.dA,
    by rw [eP]; exact h.disjF h.Fp.symm h.pA, by rw [h.rQ]; exact h.disjF h.Fq.symm h.qA,
    by rw [h.rDp]; exact h.disjF h.Fdp.symm h.dpA, by rw [h.rDq]; exact h.disjF h.Fdq.symm h.dqA,
    by rw [h.rQi]; exact h.disjF h.Fqi.symm h.qiA, by rw [eE, h.rFr]; exact h.Fe.symm,
    fwSaved (.r0, 0) (by simp), ?_, fwSaved (.r2, 8) (by simp), fwArg 0 (by decide), ?_, fwArg 2 (by decide), ?_,
    fwArg 4 (by decide), fwArg 6 (by decide), fwArg 8 (by decide), fwArg 10 (by decide), ?_,
    fwArg 12 (by decide), by simp only [State.withRegions_mem]; exact bE, ?_⟩
  · show (cA s).Contains (off (State.addr (s.sp - BitVec.ofNat 32 56)) 56) 56
    rw [show off (State.addr (s.sp - BitVec.ofNat 32 56)) 56 = stackArgAddr s 0 from h.argAddr (i := 0) (by decide)]
    exact Region.contains_self _ _
  · rw [show fw (sx s).mem (mkP s) VG.Impl.RsaKeyGen.Arm.Key.aoNl = s.gpr .r1 from fwSaved (.r1, 4) (by simp)]
    show _ = BitVec.ofNat 32 (2 * (stackArg s 1).toNat); rw [← h.nl]; simp
  · show fw _ _ (56 + 4 * 1) = _; rw [fwArg 1 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 1).toNat; simp
  · show fw _ _ (56 + 4 * 3) = _; rw [fwArg 3 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 1).toNat
    rw [← h.ql]; simp
  · show fw _ _ (56 + 4 * 11) = _; rw [fwArg 11 (by decide)]; show _ = BitVec.ofNat 32 (stackArg s 11).toNat; simp
  · show Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp (stackArg s 1).toNat (mkP s).eB
      (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat)) = _
    rw [bP, bQ]; rfl

end

end VG.Proof.RsaKeyGen.Arm.Key

end

end

/-! # An RSA key on ARMv7: a call's result (`key_ok`)

The push, the body (run with the regions `xRegs` and widened to the
caller's) and the restore.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code body)

/-- A call's result, as the body gives it. -/
def KPost (s t : State) : Prop :=
  (t.gpr .r0).toNat = Proof.RsaKeyGen.keyStatus (resv (mkP s) (sx s)) ∧
    ∀ i < 7, Spec.Rsa.bytesAt t.mem (State.addr (oPtr (mkP s) i)) (oLen (mkP s) i) = outE (mkP s) (sx s) i

section
variable {s : State}

/-- The body's regions are the frame and the caller's writable ones. -/
theorem CIn.xCovers (h : CIn s) : Covers (xRegs s) (pcPushed s).wr := by
  refine Covers.of_mem fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [pushed_wr, h.wr]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · rw [h.rN]; simp
  · rw [h.rD]; simp
  · show cP s ∈ _; simp
  · rw [h.rQ]; simp
  · rw [h.rDp]; simp
  · rw [h.rDq]; simp
  · rw [h.rQi]; simp
  · show cS s ∈ _; simp

/-- The body's run, widened to the caller's regions. -/
theorem body_wide [VG.Proof.Rsa.Arm.Keys.InvLaw] (h : CIn s) :
    ∃ tr v, Exec isa body (sx s) tr v ∧ Exec isa body (pcPushed s) tr (v.withRegions s.rd (pcPushed s).wr) ∧
      Res (mkP s) (sx s) v := by
  have pre := in_k h
  obtain ⟨tr, v, run, res⟩ := body_vp.wp _ _ ⟨pre, pre, rfl, rfl, rfl, Frame.refl _ _⟩
  have cov := h.xCovers
  have run' := Exec.widen (rd := s.rd) (wr := (pcPushed s).wr) run
    (Covers.append (Covers.refl _) cov) cov
  simp only [State.withRegions_withRegions] at run'
  exact ⟨tr, v, run, run', res⟩

/-- A call's result. -/
theorem key_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] (h : CIn s) : WP isa code s fun t => abiPreserved s t ∧ KPost s t := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold Impl.RsaKeyGen.Arm.Key.code
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  have pre := in_k h
  obtain ⟨tr, v, -, run', ⟨bo, r0, outs⟩⟩ := body_wide h
  refine WP.mono (Q := fun x => x = v.withRegions s.rd (pcPushed s).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := bo.sp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
    (pc_push_callee_saved s spLo).frame (lo := 16) (hi := 56) (by decide) bo.frame (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact pre.sF.symm.sub_left (Offset.sub_base _ (by decide))
      · have : ∃ i, i < 7 ∧ r = oR (mkP s) i := by
          simp only [KP.outs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
            ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩]
        obtain ⟨i, hi, rfl⟩ := this
        exact (pre.oF i hi).symm.sub_left (Offset.sub_base _ (by decide)))
  have fit : (v.withRegions s.rd (pcPushed s).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; omega_using []
  have read : InRegions ((v.withRegions s.rd (pcPushed s).wr).rd ++ (v.withRegions s.rd (pcPushed s).wr).wr)
      (State.addr (v.withRegions s.rd (pcPushed s).wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (v.withRegions s.rd (pcPushed s).wr).wr := by
      rw [State.withRegions_wr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
  rintro t ⟨restored, memT, restT⟩ ml ul hfl
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_, fun i hi => ?_⟩
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
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret]; exact r0
  · have fitO : oLen (mkP s) i < 2 ^ 64 := by
      have := (stackArg s 1).isLt
      unfold oLen; split <;> (change _ < _; simp only [mkP]; omega_using [this])
    dsimp only
    rw [VG.Proof.Rsa.rsa_bytes_frame hfl fitO (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r; exact (pre.oF i hi).sub_right (Region.sub_prefix (by decide))),
      memT, State.withRegions_mem]
    exact outs i hi

end

end VG.Proof.RsaKeyGen.Arm.Key

end

end

/-! ### `RsaKeyGen.Arm.Key.Top4`, which only this module used -/

section

/-! # An RSA key on ARMv7: constant time (`key_ct`)

Two calls with the same public parameters `mkP` leak the same: the body's
addresses are the stage's (`body_vp`), and the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code body)

/-- Two calls with the same public parameters. -/
theorem key_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] : RelCT isa (fun s t => CIn s ∧ CIn t ∧ s.sp = t.sp ∧ mkP s = mkP t) code (fun _ _ => True) := by
  unfold Impl.RsaKeyGen.Arm.Key.code
  apply RelCT.frame (fun _ _ h => h.2.2.1)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp, hP⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.spLo
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.spLo
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨trB1, w1, runB1, wide1, res1⟩ := body_wide hs
      obtain ⟨trB2, w2, runB2, wide2, res2⟩ := body_wide ht
      obtain ⟨rfl, rfl⟩ := Exec.det body1 wide1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 wide2
      have pre1 := in_k hs
      have pre2 := in_k ht
      rw [← hP] at pre2
      have trB := ((body_vp (P := mkP s0)).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, pre1, rfl, rfl, rfl, Frame.refl _ _⟩, ⟨pre2, pre2, rfl, rfl, rfl, Frame.refl _ _⟩⟩
        runB1 runB2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [res1.1.sp, res2.1.sp]; show s0.sp - _ = t0.sp - _; rw [sp]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

end VG.Proof.RsaKeyGen.Arm.Key

end

end


/-! # `vg_rsa_keygen_key` on ARMv7 is verified against the shared contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code)
open VG.Proof.Bignum.Arm (pcPushed)

section
variable {s : State}

/-- The result of the call, from the caller's memory. -/
theorem res_mk (h : CIn s) : res (mkP s) (sx s) = Proof.RsaKeyGen.keyOp (stackArg s 1).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat) := by
  have bP : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    h.bytes (R := cP s) h.Fp (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  have bQ : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat :=
    h.bytes (R := (mkP s).rQ) (by rw [h.rQ]; exact h.Fq) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  show Proof.RsaKeyGen.keyOp (stackArg s 1).toNat (mkP s).eB
    (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat) = _
  rw [bP, bQ]; rfl

theorem resv_ok {P : KP} {σ : State} {ys : List (List Byte)} (h : resv P σ = .inl (.ok ys)) : ys = outv P σ := by
  unfold resv at h
  split at h
  · cases h
  · split at h
    · injection h with h; injection h with h; exact h.symm
    · cases h

end

theorem key_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] (s : State) (h : (Proof.RsaKeyGen.keyContract abi 56).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (Proof.RsaKeyGen.keyContract abi 56).post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, outs⟩ := key_ok hc
  refine ⟨tr, t, run, preserved, ?_⟩
  have e := (res_mk hc).symm.trans (res_spec (in_k hc))
  simp only [State.addr] at e
  sig_post [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, e, hc.nl]
  refine ⟨r0, ?_⟩
  unfold outE at outs
  rcases hres : resv (mkP s) (sx s) with (f | ys) | u
  · simp only [hres] at outs
    exact ⟨outs 0 (by decide), outs 1 (by decide), outs 2 (by decide), outs 3 (by decide), outs 4 (by decide),
      outs 5 (by decide), outs 6 (by decide)⟩
  · have hy := resv_ok hres
    simp only [hres] at outs
    subst hy
    show (List.range 7).map (fun i => Spec.Rsa.bytesAt t.mem (State.addr (oPtr (mkP s) i)) (oLen (mkP s) i)) = _
    rw [List.map_congr_left (fun i hi => outs i (List.mem_range.mp hi))]
    rfl
  · simp only [hres] at outs
    exact ⟨outs 0 (by decide), outs 1 (by decide), outs 2 (by decide), outs 3 (by decide), outs 4 (by decide),
      outs 5 (by decide), outs 6 (by decide)⟩

/-- Calls with the same public arguments, `e` and status have the same
public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a4 : stackArg s 4 = stackArg t 4) (a6 : stackArg s 6 = stackArg t 6) (a8 : stackArg s 8 = stackArg t 8)
    (a10 : stackArg s 10 = stackArg t 10) (a11 : stackArg s 11 = stackArg t 11)
    (a12 : stackArg s 12 = stackArg t 12) (a13 : stackArg s 13 = stackArg t 13)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 10)) (stackArg t 11).toNat)
    (hst : Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp (stackArg s 1).toNat
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat)) =
      Proof.RsaKeyGen.keyStatus (Proof.RsaKeyGen.keyOp (stackArg t 1).toNat
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 10)) (stackArg t 11).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 1).toNat))) :
    mkP s = mkP t := by
  unfold mkP
  rw [hst, he, sp, p0, p2, a0, a1, a2, a4, a6, a8, a10, a11, a12, a13]

theorem key_contract_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] : ConstantTime isa (Proof.RsaKeyGen.keyContract abi 56).pre
    (Proof.RsaKeyGen.keyContract abi 56).pub code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, a0, a1, a2, _, a4, _, a6, _, a8, _, a10, a11, a12, a13⟩ := hp
  obtain ⟨b1, b2⟩ := List.append_inj bytes (by
    simp only [List.length_map, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a11])
  have he := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 b1
  exact (key_ct s t tr1 tr2 u v ⟨is, it, sp,
    mkP_eq sp p0 p2 a0 a1 a2 a4 a6 a8 a10 a11 a12 a13 he (List.singleton_inj.1 b2)⟩ e1 e2).1

/-- 32-byte primes, a one-byte exponent, the outputs at `0x1000`–`0x1600`,
`e` at `0x1700`, the working space at `0x4000`, and the stack arguments at
`0x8000`. -/
def keySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x12 else if a = 0x8004 then 0x20 else if a = 0x8009 then 0x13
    else if a = 0x800C then 0x20 else if a = 0x8011 then 0x14 else if a = 0x8014 then 0x20
    else if a = 0x8019 then 0x15 else if a = 0x801C then 0x20 else if a = 0x8021 then 0x16
    else if a = 0x8024 then 0x20 else if a = 0x8029 then 0x17 else if a = 0x802C then 1
    else if a = 0x8031 then 0x40 else if a = 0x8034 then 0x20 else if a = 0x8035 then 0x04 else 0
  rd := [⟨0x1700, 1⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x1200, 32⟩, ⟨0x1300, 32⟩, ⟨0x1400, 32⟩, ⟨0x1500, 32⟩, ⟨0x1600, 32⟩,
    ⟨0x4000, 8448⟩]

theorem key_contract_sat : ∃ s, (Proof.RsaKeyGen.keyContract abi 56).pre s := by
  sig_implies_sat [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.RsaKeyGen.primeLenValid, Spec.Rsa.scratchWords]
    using keySatState

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] : Verified target code (Proof.RsaKeyGen.keyContract abi 56) :=
  ⟨key_contract_correct, key_contract_ct, key_contract_sat⟩

end VG.Proof.RsaKeyGen.Arm.Key
