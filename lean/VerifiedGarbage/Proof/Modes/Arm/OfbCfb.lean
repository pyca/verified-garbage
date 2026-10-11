import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Spec.Ofb
import VerifiedGarbage.Spec.Cfb

/-!
# OFB and CFB as modes one block at a time on ARMv7

`Impl.Modes.Arm.ofb`, `cfbEnc` and `cfbDec` run OFB (SP 800-38A §6.4,
`Spec/Ofb.lean`) and CFB with `s = b` (§6.3, `Spec/Cfb.lean`): from the IV
in the chaining block, whatever the spare block holds, `runSeq` gives
`Spec.Ofb.crypt`, `Spec.Cfb.encrypt` and `Spec.Cfb.decrypt`, and leaves in
the chaining block the value to continue from (`Spec.Ofb.next`,
`Spec.Cbc.next`), which they return in the IV. Each mode whose IV is read
and written has, with a scratch buffer, the precondition `RwPre`, which
implies `seqArm`'s.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem ofb_ok (c : Core) : ModeOk c ofb :=
  ⟨by decide, by decide, by decide, by show encodable (BitVec.ofNat 32 40) = true; decide⟩
theorem cfbEnc_ok (c : Core) : ModeOk c cfbEnc :=
  ⟨by decide, by decide, by decide, by show encodable (BitVec.ofNat 32 40) = true; decide⟩
theorem cfbDec_ok (c : Core) : ModeOk c cfbDec :=
  ⟨by decide, by decide, by decide, by show encodable (BitVec.ofNat 32 40) = true; decide⟩

theorem runSeq_ofb (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq ofb ciph b xs).1 = Spec.Ofb.crypt ciph b.o xs ∧
        (runSeq ofb ciph b xs).2.o = Spec.Ofb.next ciph b.o xs.length
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_ofb ciph (stepOf ofb ciph (b.set .d x)) xs
    have ho : (stepOf ofb ciph (b.set .d x)).o = ciph b.o := by
      simp [stepOf, runOps, runOp, ofb, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, Spec.Ofb.crypt, List.length_cons, Spec.Ofb.outputs, List.zipWith_cons_cons]
      simp [stepOf, runOps, runOp, ofb, Blks.set, Blks.get]
    · simp only [runSeq, ih.2, Spec.Ofb.next, List.length_cons, Spec.Ofb.outputs, List.getLastD_cons]

theorem runSeq_cfbEnc (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq cfbEnc ciph b xs).1 = Spec.Cfb.encrypt ciph b.o xs ∧
        (runSeq cfbEnc ciph b xs).2.o = Spec.Cbc.next b.o (Spec.Cfb.encrypt ciph b.o xs)
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_cfbEnc ciph (stepOf cfbEnc ciph (b.set .d x)) xs
    have hd : (stepOf cfbEnc ciph (b.set .d x)).d = Spec.Cbc.xor x (ciph b.o) := by
      simp [stepOf, runOps, runOp, cfbEnc, Blks.set, Blks.get]
    have ho : (stepOf cfbEnc ciph (b.set .d x)).o = Spec.Cbc.xor x (ciph b.o) := by
      simp [stepOf, runOps, runOp, cfbEnc, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, hd, Spec.Cfb.encrypt]
    · simp only [runSeq, ih.2, Spec.Cfb.encrypt, Spec.Cbc.next, List.getLastD_cons]

theorem runSeq_cfbDec (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)),
      (runSeq cfbDec ciph b xs).1 = Spec.Cfb.decrypt ciph b.o xs ∧
        (runSeq cfbDec ciph b xs).2.o = Spec.Cbc.next b.o xs
  | _, [] => ⟨rfl, rfl⟩
  | b, x :: xs => by
    have ih := runSeq_cfbDec ciph (stepOf cfbDec ciph (b.set .d x)) xs
    have hd : (stepOf cfbDec ciph (b.set .d x)).d = Spec.Cbc.xor x (ciph b.o) := by
      simp [stepOf, runOps, runOp, cfbDec, Blks.set, Blks.get]
    have ho : (stepOf cfbDec ciph (b.set .d x)).o = x := by
      simp [stepOf, runOps, runOp, cfbDec, Blks.set, Blks.get]
    rw [ho] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, ih.1, hd, Spec.Cfb.decrypt]
    · simp only [runSeq, ih.2, Spec.Cbc.next, List.getLastD_cons]

/-! ## The contracts of the ciphers' modes, with the IV read and written -/

section
variable (c : Core) (S : CoreSpec c) (len : Nat → Nat) (s : State)

/-- The precondition of `(schedule, iv, data, n, scratch = [sp])`, with the
schedule only read and the IV read and written, as `Sig.contract` states
it, for data of `len n` bytes. -/
def RwPre : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), S.keyLen⟩
  let iv : Region := ⟨State.addr (s.gpr .r1), c.bs⟩
  let data : Region := ⟨State.addr (s.gpr .r2), len (s.gpr .r3).toNat⟩
  let scr : Region := ⟨State.addr (stackArg s 0), c.scratchBytes⟩
  let arg : Region := ⟨stackArgAddr s 0, 4⟩
  let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩
  S.stack ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧ s.rd = [key, arg] ∧ s.wr = [iv, data, scr] ∧
    key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
    iv.Disjoint arg ∧ data.Disjoint scr ∧ data.Disjoint arg ∧ scr.Disjoint arg ∧
    below.Disjoint key ∧ below.Disjoint iv ∧ below.Disjoint data ∧ below.Disjoint scr ∧ below.Disjoint arg ∧
    (s.gpr .r0).toNat + S.keyLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + c.bs ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + len (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + c.scratchBytes ≤ 2 ^ 32

end

theorem seqArm_pre_rw {c : Core} {S : CoreSpec c} {M : Mode} {len : Nat → Nat}
    (hl : ∀ n, len n = n * c.ds M) {s : State} (h : RwPre c S len s) : (seqArm c S M).pre s := by
  simp only [RwPre, hl] at h
  obtain ⟨a1, a2, rd, wr, -, kd, ks, vd, vs, va, ds, da, sa, bk, -, bd, bs, -, fk, fv, fd, fs⟩ := h
  refine ⟨a1, a2, by simp [rd], by simp [wr], by simp [rd], by simp [wr], by simp [wr], kd, ks, vd, vs, ds,
    bk, bd, bs, fk, fv, fd, fs, fun _ => by simp [wr], ?_⟩
  intro r hr
  rw [wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact va.symm
  · exact da.symm
  · exact sa.symm

theorem ofb_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S ofb).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0))
    let iv := Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = Spec.Ofb.crypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = Spec.Ofb.next ciph iv (s.gpr .r3).toNat := by
  have e := runSeq_ofb (S.ciphAt s.mem (State.addr (s.gpr .r0))) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (s.gpr .r1)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  rw [length_blocksOf] at e
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

theorem cfbEnc_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cfbEnc).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0))
    let iv := Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        Spec.Cfb.encrypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv xs) := by
  have e := runSeq_cfbEnc (S.ciphAt s.mem (State.addr (s.gpr .r0))) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (s.gpr .r1)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

theorem cfbDec_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cfbDec).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0))
    let iv := Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) c.bs
    let xs := VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        Spec.Cfb.decrypt ciph iv xs ∧
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = Spec.Cbc.next iv xs := by
  have e := runSeq_cfbDec (S.ciphAt s.mem (State.addr (s.gpr .r0))) ⟨[], Spec.Aes.bytesAt s.mem
    (State.addr (s.gpr .r1)) c.bs, Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  exact ⟨h.1.trans e.1, (h.2 rfl).trans e.2⟩

end VG.Proof.Modes.Arm
