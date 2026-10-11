import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Spec.Cfb8

/-!
# CFB8 as a mode a byte at a time on ARMv7

`Impl.Modes.Arm.cfb8Enc` and `cfb8Dec` run CFB with `s = 8` (SP 800-38A
§6.3, `Spec/Cfb8.lean`): with the input block in the chaining block (from
the IV), whatever the spare block holds, `runSeq` on the data's bytes (as
one-byte elements) gives `Spec.Cfb8.encrypt` and `Spec.Cfb8.decrypt`, and
leaves in the chaining block the input block to continue from
(`Spec.Cfb8.next`), which they return in the IV.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)

theorem cfb8Enc_ok (c : Core) (h : encodable (BitVec.ofNat 32 (oOff + c.bs)) = true) : ModeOk c cfb8Enc :=
  ⟨by decide, by decide, by decide, h⟩

theorem cfb8Dec_ok (c : Core) (h : encodable (BitVec.ofNat 32 (oOff + c.bs)) = true) : ModeOk c cfb8Dec :=
  ⟨by decide, by decide, by decide, h⟩

theorem next_cons (iv cs : List Byte) (x : Byte) (hiv : iv ≠ []) :
    Spec.Cfb8.next iv (x :: cs) = Spec.Cfb8.next (iv.tail ++ [x]) cs := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hiv
  simp [Spec.Cfb8.next]

theorem runSeq_cfb8Enc (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)), b.o ≠ [] → (∀ x ∈ xs, x.length = 1) →
      (runSeq cfb8Enc ciph b xs).1.flatten = Spec.Cfb8.encrypt ciph b.o xs.flatten ∧
        (runSeq cfb8Enc ciph b xs).2.o = Spec.Cfb8.next b.o (Spec.Cfb8.encrypt ciph b.o xs.flatten)
  | _, [], _, _ => ⟨rfl, by simp [Spec.Cfb8.next, Spec.Cfb8.encrypt, runSeq]⟩
  | b, x :: xs, ho, hx => by
    obtain ⟨p, rfl⟩ : ∃ p, x = [p] := by
      have := hx x List.mem_cons_self
      match x, this with | [p], _ => exact ⟨p, rfl⟩
    have hd : (stepOf cfb8Enc ciph (b.set .d [p])).d = [p ^^^ (ciph b.o).headD 0] := by
      simp [stepOf, runOps, runOp, cfb8Enc, Blks.set, Blks.get, xorHead]
    have hO : (stepOf cfb8Enc ciph (b.set .d [p])).o = b.o.tail ++ [p ^^^ (ciph b.o).headD 0] := by
      simp [stepOf, runOps, runOp, cfb8Enc, Blks.set, Blks.get, xorHead]
    have ih := runSeq_cfb8Enc ciph (stepOf cfb8Enc ciph (b.set .d [p])) xs (by rw [hO]; simp)
      (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    rw [hO] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, List.flatten_cons, hd, ih.1, List.singleton_append, Spec.Cfb8.encrypt]
    · simp only [runSeq, List.flatten_cons, ih.2, List.singleton_append, Spec.Cfb8.encrypt, next_cons _ _ _ ho]

theorem runSeq_cfb8Dec (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)), b.o ≠ [] → (∀ x ∈ xs, x.length = 1) →
      (runSeq cfb8Dec ciph b xs).1.flatten = Spec.Cfb8.decrypt ciph b.o xs.flatten ∧
        (runSeq cfb8Dec ciph b xs).2.o = Spec.Cfb8.next b.o xs.flatten
  | _, [], _, _ => ⟨rfl, by simp [Spec.Cfb8.next, runSeq]⟩
  | b, x :: xs, ho, hx => by
    obtain ⟨p, rfl⟩ : ∃ p, x = [p] := by
      have := hx x List.mem_cons_self
      match x, this with | [p], _ => exact ⟨p, rfl⟩
    have hd : (stepOf cfb8Dec ciph (b.set .d [p])).d = [p ^^^ (ciph b.o).headD 0] := by
      simp [stepOf, runOps, runOp, cfb8Dec, Blks.set, Blks.get, xorHead]
    have hO : (stepOf cfb8Dec ciph (b.set .d [p])).o = b.o.tail ++ [p] := by
      simp [stepOf, runOps, runOp, cfb8Dec, Blks.set, Blks.get, xorHead]
    have ih := runSeq_cfb8Dec ciph (stepOf cfb8Dec ciph (b.set .d [p])) xs (by rw [hO]; simp)
      (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    rw [hO] at ih
    refine ⟨?_, ?_⟩
    · simp only [runSeq, List.flatten_cons, hd, ih.1, List.singleton_append, Spec.Cfb8.decrypt]
    · simp only [runSeq, List.flatten_cons, ih.2, List.singleton_append, next_cons _ _ _ ho]

/-- The bytes of the data, as one-byte elements. -/
theorem flatten_blocksOf_one (m : Mem) (p : Addr) (n : Nat) :
    (VG.Proof.Modes.blocksOf 1 m p n).flatten = bytesAt m p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.Modes.blocksOf, List.range_succ, List.map_append, List.flatten_append] at ih ⊢
    rw [ih]
    simp [bytesAt, List.range_succ, Nat.one_mul]

theorem blocksOf_one_len (m : Mem) (p : Addr) (n : Nat) : ∀ x ∈ VG.Proof.Modes.blocksOf 1 m p n, x.length = 1 := by
  intro x hx
  simp only [VG.Proof.Modes.blocksOf, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  simp [bytesAt]

theorem cfb8Enc_post {c : Core} {S : CoreSpec c} (hbs : 0 < c.bs) {s s' : State}
    (h : (seqArm c S cfb8Enc).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0))
    let iv := bytesAt s.mem (State.addr (s.gpr .r1)) c.bs
    let xs := bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
    bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = Spec.Cfb8.encrypt ciph iv xs ∧
      bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = Spec.Cfb8.next iv (Spec.Cfb8.encrypt ciph iv xs) := by
  have e := runSeq_cfb8Enc (S.ciphAt s.mem (State.addr (s.gpr .r0))) ⟨[], bytesAt s.mem
    (State.addr (s.gpr .r1)) c.bs, bytesAt s.mem (State.addr (stackArg s 0) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf 1 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (by show bytesAt _ _ c.bs ≠ []; simp [bytesAt]; omega) (blocksOf_one_len _ _ _)
  rw [flatten_blocksOf_one] at e
  have h1 := congrArg List.flatten h.1
  rw [show c.ds cfb8Enc = 1 from rfl, flatten_blocksOf_one] at h1
  exact ⟨h1.trans e.1, (h.2 rfl).trans e.2⟩

theorem cfb8Dec_post {c : Core} {S : CoreSpec c} (hbs : 0 < c.bs) {s s' : State}
    (h : (seqArm c S cfb8Dec).post s s') :
    let ciph := S.ciphAt s.mem (State.addr (s.gpr .r0))
    let iv := bytesAt s.mem (State.addr (s.gpr .r1)) c.bs
    let xs := bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
    bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = Spec.Cfb8.decrypt ciph iv xs ∧
      bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = Spec.Cfb8.next iv xs := by
  have e := runSeq_cfb8Dec (S.ciphAt s.mem (State.addr (s.gpr .r0))) ⟨[], bytesAt s.mem
    (State.addr (s.gpr .r1)) c.bs, bytesAt s.mem (State.addr (stackArg s 0) +
      BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
    (VG.Proof.Modes.blocksOf 1 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (by show bytesAt _ _ c.bs ≠ []; simp [bytesAt]; omega) (blocksOf_one_len _ _ _)
  rw [flatten_blocksOf_one] at e
  have h1 := congrArg List.flatten h.1
  rw [show c.ds cfb8Dec = 1 from rfl, flatten_blocksOf_one] at h1
  exact ⟨h1.trans e.1, (h.2 rfl).trans e.2⟩

end VG.Proof.Modes.Arm
