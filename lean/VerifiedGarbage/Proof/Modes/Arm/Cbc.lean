module

public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop

/-!
# CBC as a mode one block at a time on ARMv7

`Impl.Modes.Arm.cbcEnc` and `cbcDec` run CBC (SP 800-38A §6.2,
`Spec/Cbc.lean`): from the IV in the chaining block, whatever the spare
block holds, `runSeq` gives `Spec.Cbc.encrypt` and `Spec.Cbc.decrypt`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem cbcEnc_ok (c : Core) : ModeOk c cbcEnc :=
  ⟨by rfl, by rfl, by decide, by show encodable (BitVec.ofNat 32 40) = true; decide⟩
theorem cbcDec_ok (c : Core) : ModeOk c cbcDec :=
  ⟨by rfl, by rfl, by decide, by show encodable (BitVec.ofNat 32 0) = true; decide⟩

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

/-- The arguments of a core without rounds: `(schedule = r0, iv = r1,
data = r2, n = r3, scratch = [sp])`. -/
theorem args_plain {c : Core} (hr : c.rounds = false) (s : State) :
    ivArg c s = s.gpr .r1 ∧ dArg c s = s.gpr .r2 ∧ nArg c s = s.gpr .r3 ∧ scArg c s = stackArg s 0 ∧
      argBytes c = 4 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

theorem seqArm_pre_ro {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = false) (hM : M.finish = false)
    (hb : M.byte = false) {s : State} (h : RoPre c S s)
    (ht : TabsOk S.consts S.stack s := by exact tabsOk_nil _ _) : (seqArm c S M).pre s := by
  have e : c.ds M = c.bs := ds_of c hb
  obtain ⟨e1, e2, e3, e4, e5⟩ := args_plain hr s
  show (seqArm c S M).pre s
  unfold seqArm; simp only [e, e1, e2, e3, e4, e5]
  obtain ⟨a1, a2, rd, wr, kd, ks, vd, vs, ds, da, sa, bk, -, bd, bs, -, fk, fv, fd, fs⟩ := h
  refine ⟨a1, a2, by simp [rd], by simp [rd], by simp [rd], by simp [wr], by simp [wr], kd, ks, vd, vs, ds,
    bk, bd, bs, fk, fv, fd, fs, fun h => absurd h (by simp [hM]), ?_, fun h => absurd h (by simp [hr]), ht⟩
  intro r hr
  rw [wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact sa.symm

theorem seqArm_pub {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = false) {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, fun h' => absurd h' (by simp [hr]), hk⟩

/-- The arguments of a core with rounds: `(schedule = r0, rounds = r1,
iv = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
theorem args_rounds {c : Core} (hr : c.rounds = true) (s : State) :
    ivArg c s = s.gpr .r2 ∧ dArg c s = s.gpr .r3 ∧ nArg c s = stackArg s 0 ∧ scArg c s = stackArg s 1 ∧
      argBytes c = 8 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

section
variable (c : Core) (S : CoreSpec c) (s : State)

/-- The precondition of `(schedule, rounds, iv, data, n = [sp], scratch = [sp + 4])`,
with the schedule and the IV only read, as `Sig.contract` states it, and
the number of rounds satisfying `S.rok`. -/
def RoPreR : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), S.keyLen⟩
  let iv : Region := ⟨State.addr (s.gpr .r2), c.bs⟩
  let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat * c.bs⟩
  let scr : Region := ⟨State.addr (stackArg s 1), c.scratchBytes⟩
  let arg : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩
  S.stack ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧ s.rd = [key, iv, arg] ∧ s.wr = [data, scr] ∧
    key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ data.Disjoint scr ∧
    data.Disjoint arg ∧ scr.Disjoint arg ∧ below.Disjoint key ∧ below.Disjoint iv ∧ below.Disjoint data ∧
    below.Disjoint scr ∧ below.Disjoint arg ∧
    (s.gpr .r0).toNat + S.keyLen ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + c.bs ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + (stackArg s 0).toNat * c.bs ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + c.scratchBytes ≤ 2 ^ 32 ∧
    S.rok (s.gpr .r1)

end

theorem seqArm_pre_roR {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = true) (hM : M.finish = false)
    (hb : M.byte = false) {s : State} (h : RoPreR c S s)
    (ht : TabsOk S.consts S.stack s := by exact tabsOk_nil _ _) : (seqArm c S M).pre s := by
  have e : c.ds M = c.bs := ds_of c hb
  obtain ⟨e1, e2, e3, e4, e5⟩ := args_rounds hr s
  show (seqArm c S M).pre s
  unfold seqArm; simp only [e, e1, e2, e3, e4, e5]
  obtain ⟨a1, a2, rd, wr, kd, ks, vd, vs, ds, da, sa, bk, -, bd, bs, -, fk, fv, fd, fs, rk⟩ := h
  refine ⟨a1, a2, by simp [rd], by simp [rd], by simp [rd], by simp [wr], by simp [wr], kd, ks, vd, vs, ds,
    bk, bd, bs, fk, fv, fd, fs, fun h => absurd h (by simp [hM]), ?_, fun _ => rk, ht⟩
  intro r hr
  rw [wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact sa.symm

theorem stackArg_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArg (s.withRegions rd wr) i = stackArg s i := rfl

theorem stackArgAddr_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (s.withRegions rd wr) i = stackArgAddr s i := rfl

/-- `seqArm_pre_roR` for a core that reads tables: the precondition holds of
the state without their regions (`rd'`, among `s`'s), and `s` holds them. -/
theorem seqArm_pre_roR' {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = true) (hM : M.finish = false)
    (hb : M.byte = false) {s : State} {rd' : List Region} (h : RoPreR c S (s.withRegions rd' s.wr))
    (hrd : ∀ r ∈ rd', r ∈ s.rd) (ht : TabsOk S.consts S.stack s) : (seqArm c S M).pre s := by
  have e : c.ds M = c.bs := ds_of c hb
  obtain ⟨e1, e2, e3, e4, e5⟩ := args_rounds hr s
  show (seqArm c S M).pre s
  unfold seqArm; simp only [e, e1, e2, e3, e4, e5]
  simp only [RoPreR, State.withRegions_gpr, State.withRegions_sp, State.withRegions_rd, State.withRegions_wr,
    stackArg_withRegions, stackArgAddr_withRegions] at h
  obtain ⟨a1, a2, rd, wr, kd, ks, vd, vs, ds, da, sa, bk, -, bd, bs, -, fk, fv, fd, fs, rk⟩ := h
  have mr : ∀ r ∈ rd', r ∈ s.rd ++ s.wr := fun r h => List.mem_append_left _ (hrd r h)
  refine ⟨a1, a2, mr _ (by simp [rd]), mr _ (by simp [rd]), mr _ (by simp [rd]), by simp [wr], by simp [wr], kd, ks,
    vd, vs, ds, bk, bd, bs, fk, fv, fd, fs, fun h => absurd h (by simp [hM]), ?_, fun _ => rk, ht⟩
  intro r hr
  rw [wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact sa.symm

theorem seqArm_pubR {c : Core} {S : CoreSpec c} {M : Mode} {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun _ => h.2.2.2.2.2.2, hk⟩

theorem cbcEnc_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcEnc).post s s') :
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat =
      Spec.Cbc.encrypt (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
        (Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs)
        (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat) :=
  h.1.trans (runSeq_cbcEnc _ _ _)

theorem cbcDec_post {c : Core} {S : CoreSpec c} {s s' : State} (h : (seqArm c S cbcDec).post s s') :
    VG.Proof.Modes.blocksOf c.bs s'.mem (State.addr (dArg c s)) (nArg c s).toNat =
      Spec.Cbc.decrypt (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
        (Spec.Aes.bytesAt s.mem (State.addr (ivArg c s)) c.bs)
        (VG.Proof.Modes.blocksOf c.bs s.mem (State.addr (dArg c s)) (nArg c s).toNat) :=
  h.1.trans (runSeq_cbcDec _ _ _)

/-- A core and a mode whose code between the calls passes the taint checks
give a function that is correct and constant time under `seqArm`, and so
under any contract `seqArm` implies. -/
theorem seq_verified {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) (hT : SeqTaint c M)
    {k : Contract isa} (hk : (seqArm c S M).Implies k) : Verified Arm.target (c.seq M) k :=
  Verified.of_correct (fun _ hs => seq_wp S hM hs) (seq_ct S hM hT) hk

end VG.Proof.Modes.Arm
