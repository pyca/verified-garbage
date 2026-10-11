import VerifiedGarbage.Proof.Modes.Arm.SeqCT

/-!
# CBC as a mode one block at a time on ARMv7

`Impl.Modes.Arm.cbcEnc` and `cbcDec` run CBC (SP 800-38A §6.2,
`Spec/Cbc.lean`): from the IV in the chaining block, whatever the spare
block holds, `runSeq` gives `Spec.Cbc.encrypt` and `Spec.Cbc.decrypt`.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem cbcEnc_ok : ModeOk cbcEnc := ⟨by decide, by decide, by decide⟩
theorem cbcDec_ok : ModeOk cbcDec := ⟨by decide, by decide, by decide⟩

theorem xor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cbc.xor y x := by
  simp only [Spec.Cbc.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

theorem runSeq_cbcEnc (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)), (runSeq cbcEnc ciph b xs).1 = Spec.Cbc.encrypt ciph b.o xs
  | _, [] => rfl
  | b, x :: xs => by
    simp only [runSeq, Spec.Cbc.encrypt, runSeq_cbcEnc ciph _ xs]
    simp [stepOf, runOps, runOp, cbcEnc, Blks.set, Blks.get, xor_comm x]

theorem runSeq_cbcDec (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)), (runSeq cbcDec ciph b xs).1 = Spec.Cbc.decrypt ciph b.o xs
  | _, [] => rfl
  | b, x :: xs => by
    simp only [runSeq, Spec.Cbc.decrypt, runSeq_cbcDec ciph _ xs]
    simp [stepOf, runOps, runOp, cbcDec, Blks.set, Blks.get]

/-! ## The contracts of the ciphers' modes

A mode whose IV is only read has, with a scratch buffer, the precondition
`RoPre` (as `Sig.contract` states it for `(schedule, iv, data, n, scratch)`),
which implies `seqArm`'s. -/

section
variable (c : Core) (S : CoreSpec c) (s : State)

/-- The precondition of `(schedule, iv, data, n, scratch = [sp])`, with the
schedule and the IV only read, as `Sig.contract` states it. -/
def RoPre : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), S.keyLen⟩
  let iv : Region := ⟨State.addr (s.gpr .r1), c.bs⟩
  let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * c.bs⟩
  let scr : Region := ⟨State.addr (stackArg s 0), c.scratchBytes⟩
  let arg : Region := ⟨stackArgAddr s 0, 4⟩
  let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩
  S.stack ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧ s.rd = [key, iv, arg] ∧ s.wr = [data, scr] ∧
    key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ data.Disjoint scr ∧
    data.Disjoint arg ∧ scr.Disjoint arg ∧ below.Disjoint key ∧ below.Disjoint iv ∧ below.Disjoint data ∧
    below.Disjoint scr ∧ below.Disjoint arg ∧
    (s.gpr .r0).toNat + S.keyLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + c.bs ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat * c.bs ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + c.scratchBytes ≤ 2 ^ 32

end

theorem seqArm_pre_ro {c : Core} {S : CoreSpec c} {M : Mode} (hM : M.finish = false) {s : State}
    (h : RoPre c S s) : (seqArm c S M).pre s := by
  obtain ⟨a1, a2, rd, wr, kd, ks, vd, vs, ds, da, sa, bk, -, bd, bs, -, fk, fv, fd, fs⟩ := h
  refine ⟨a1, a2, by simp [rd], by simp [rd], by simp [rd], by simp [wr], by simp [wr], kd, ks, vd, vs, ds,
    bk, bd, bs, fk, fv, fd, fs, fun h => absurd h (by simp [hM]), ?_⟩
  intro r hr
  rw [wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact sa.symm

theorem seqArm_pub {c : Core} {S : CoreSpec c} {M : Mode} {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0) : (seqArm c S M).pub s₁ s₂ := h

theorem cbcEnc_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcEnc).post s s') :
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cbc.encrypt (S.ciphAt s.mem (State.addr (s.gpr .r0)))
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) c.bs)
        (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) := by
  rw [h.1, runSeq_cbcEnc]

theorem cbcDec_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcDec).post s s') :
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cbc.decrypt (S.ciphAt s.mem (State.addr (s.gpr .r0)))
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) c.bs)
        (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) := by
  rw [h.1, runSeq_cbcDec]

/-- A core and a mode whose code between the calls passes the taint checks
give a function that is correct and constant time under `seqArm`, and so
under any contract `seqArm` implies. -/
theorem seq_verified {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk M) (hT : SeqTaint c M)
    {k : Contract isa} (hk : (seqArm c S M).Implies k) : Verified Arm.target (c.seq M) k :=
  Verified.of_correct (fun _ hs => seq_wp S hM hs) (seq_ct S hM hT) hk

end VG.Proof.Modes.Arm
