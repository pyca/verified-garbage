module

public import VerifiedGarbage.Impl.Modes.Arm.Ctr
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Modes.Arm.SeqBody
import VerifiedGarbage.Proof.AesCtr.Spec

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem ctr_ok (c : Core) (hbs : c.bs = 16) : ModeOk c ctr := by
  refine ⟨by rfl, ?_, by decide, ?_⟩
  · simp [ctr, opOk, hbs]
  · simpa [ctr, Core.base, hbs, oOff] using (show encodable (BitVec.ofNat 32 56) = true by decide)

theorem runSeq_ctr (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq ctr ciph b xs).1 = Spec.Ctr.crypt ciph b.o xs ∧
        (runSeq ctr ciph b xs).2.o = Spec.Ctr.next b.o xs.length
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_ctr ciph (stepOf ctr ciph (b.set .d x)) xs
    have ho : (stepOf ctr ciph (b.set .d x)).o = Spec.Ctr.inc b.o := by
      simp [stepOf, runOps, runOp, ctr, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, Spec.Ctr.crypt, List.length_cons, Spec.Ctr.counters,
        List.map_cons, List.zipWith_cons_cons]
      simp [stepOf, runOps, runOp, ctr, Blks.set, Blks.get]
    · simp only [runSeq, ih.2, List.length_cons, AesCtr.next_succ']

theorem ctr_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S ctr).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)
    let iv := Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat = Spec.Ctr.crypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (ivArg c s)) c.bs = Spec.Ctr.next iv (nArg c s).toNat := by
  have e := runSeq_ctr (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (ivArg c s)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (scArg c s) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat)
  rw [length_blocksOf] at e
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

end VG.Proof.Modes.Arm
