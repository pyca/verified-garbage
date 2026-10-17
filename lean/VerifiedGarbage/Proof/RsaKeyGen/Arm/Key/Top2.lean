module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top1
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
  · exact h1 x hx (by simp only [Region.Contains]; omega)
  · refine h2 x hx ?_
    simp only [Region.Contains]
    have := (Offset.lt_iff x a (d := 56) (n := 56) (by decide)).mpr ⟨by omega, by omega⟩
    omega

section
variable {s : State}

theorem CIn.sp' (h : CIn s) : State.addr (s.sp - BitVec.ofNat 32 56) = State.addr s.sp - 56#64 :=
  FrameStack.addr_sub' h.spLo

theorem cA_eq (s : State) : cA s = ⟨State.addr s.sp, 56⟩ := by simp [cA, stackArgAddr]

theorem CIn.ei (h : CIn s) {i : Nat} (hi : i < 14) :
    stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := by
  have := h.spHi
  simp only [stackArgAddr]; exact addr_add (by omega)

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 14) :
    off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  simp only [stackArgAddr, off]
  rw [h.sp', addr_add (by omega), ← Offset.add_add, BitVec.sub_add_cancel]

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
  rw [cA_eq, h.ei hi]; exact Offset.sub_base _ (by omega)

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
    h.bytes (R := cP s) h.Fp (Nat.le_of_lt ((BitVec.isLt _).trans_le (by decide)))
  have bQ : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat :=
    h.bytes (R := (mkP s).rQ) (by rw [h.rQ]; exact h.Fq) (Nat.le_of_lt ((BitVec.isLt _).trans_le (by decide)))
  have bE : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 10)) (stackArg s 11).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat :=
    h.bytes (R := cE s) h.Fe (Nat.le_of_lt ((BitVec.isLt _).trans_le (by decide)))
  refine ⟨by simp only [State.withRegions_sp]; rfl, by show (s.sp - BitVec.ofNat 32 56).toNat + 112 ≤ 2 ^ 32; omega,
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
  · show Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp (stackArg s 1).toNat (mkP s).eB
      (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat)) = _
    rw [bP, bQ]; rfl

end

end VG.Proof.RsaKeyGen.Arm.Key
