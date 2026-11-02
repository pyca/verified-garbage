module

public import VerifiedGarbage.Proof.Rsa.Arm.RvTop2
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_recover_primes` on ARMv7: the body's start (`in_x`)

After the push and the entry, with the regions `xRegs`: the start `In` of
the body.
-/

@[expose] public section

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
    In (mkP s) (u.withRegions u.rd (xRegs s)) ∧ Tries (mkP s) (u.withRegions u.rd (xRegs s)) := by
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
  have dB' : Spec.Rsa.bytesAt (entryMem s) (State.addr (stackArg s 4)) (stackArg s 5).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat := h.bytes (R := cD s) h.Fd (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  refine ⟨⟨by simp only [State.withRegions_sp, hsp]; rfl, by show (s.sp - BitVec.ofNat 32 56).toNat + 88 ≤ 2 ^ 32; rw [spN]; omega, rfl,
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
    by simp only [State.withRegions_mem, hmem]; exact nB, by simp only [State.withRegions_mem, hmem]; exact eB⟩, ?_⟩
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
  · show (Spec.Rsa.primesKey (mkP s).nB (mkP s).eB (Spec.Rsa.bytesAt (u.withRegions u.rd (xRegs s)).mem
      (State.addr (stackArg s 4)) (stackArg s 5).toNat)).2 = _
    simp only [State.withRegions_mem, hmem, dB']
    rfl

end

end VG.Proof.Rsa.Arm.Recover
