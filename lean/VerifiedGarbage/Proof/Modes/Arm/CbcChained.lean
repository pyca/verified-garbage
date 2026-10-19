module

public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Modes.Arm.SeqBody
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb

/-!
# CBC on ARMv7 that updates the chaining value

`Impl.Modes.Arm.cbcEncChained` and `cbcDecChained` run CBC (SP 800-38A §6.2,
`Spec/Cbc.lean`) as `cbcEnc` and `cbcDec` do, and leave in the chaining
block the value to continue from (`Spec.Cbc.next`), which they return in the
IV: so their IV is read and written, and their contracts follow from
`seqArm`'s as OFB's and CFB's do (`seqArm_pre_rw`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem cbcEncChained_ok (c : Core) : ModeOk c cbcEncChained :=
  ⟨by rfl, by rfl, by decide, by show encodable (BitVec.ofNat 32 40) = true; decide⟩
theorem cbcDecChained_ok (c : Core) : ModeOk c cbcDecChained :=
  ⟨by rfl, by rfl, by decide, by show encodable (BitVec.ofNat 32 0) = true; decide⟩

theorem runSeq_cbcEncChained (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq cbcEncChained ciph b xs).1 = Spec.Cbc.encrypt ciph b.o xs ∧
        (runSeq cbcEncChained ciph b xs).2.o = Spec.Cbc.next b.o (Spec.Cbc.encrypt ciph b.o xs)
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_cbcEncChained ciph (stepOf cbcEncChained ciph (b.set .d x)) xs
    have hd : (stepOf cbcEncChained ciph (b.set .d x)).d = ciph (Spec.Cbc.xor x b.o) := by
      simp [stepOf, runOps, runOp, cbcEncChained, cbcEnc, Blks.set, Blks.get, xor_comm x]
    have ho : (stepOf cbcEncChained ciph (b.set .d x)).o = ciph (Spec.Cbc.xor x b.o) := by
      simp [stepOf, runOps, runOp, cbcEncChained, cbcEnc, Blks.set, Blks.get, xor_comm x]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, hd, Spec.Cbc.encrypt]
    · simp only [runSeq, ih.2, Spec.Cbc.encrypt, Spec.Cbc.next, List.getLastD_cons]

theorem runSeq_cbcDecChained (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq cbcDecChained ciph b xs).1 = Spec.Cbc.decrypt ciph b.o xs ∧
        (runSeq cbcDecChained ciph b xs).2.o = Spec.Cbc.next b.o xs
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_cbcDecChained ciph (stepOf cbcDecChained ciph (b.set .d x)) xs
    have hd : (stepOf cbcDecChained ciph (b.set .d x)).d = Spec.Cbc.xor (ciph x) b.o := by
      simp [stepOf, runOps, runOp, cbcDecChained, cbcDec, Blks.set, Blks.get]
    have ho : (stepOf cbcDecChained ciph (b.set .d x)).o = x := by
      simp [stepOf, runOps, runOp, cbcDecChained, cbcDec, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, hd, Spec.Cbc.decrypt]
    · simp only [runSeq, ih.2, Spec.Cbc.next, List.getLastD_cons]

theorem cbcEncChained_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcEncChained).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)
    let iv := Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat = Spec.Cbc.encrypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (ivArg c s)) c.bs = Spec.Cbc.next iv (Spec.Cbc.encrypt ciph iv xs) := by
  have e := runSeq_cbcEncChained (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (scArg c s) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat)
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

theorem cbcDecChained_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcDecChained).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)
    let iv := Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat = Spec.Cbc.decrypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (ivArg c s)) c.bs = Spec.Cbc.next iv xs := by
  have e := runSeq_cbcDecChained (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (scArg c s) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat)
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

end VG.Proof.Modes.Arm
