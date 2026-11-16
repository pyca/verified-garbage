module

public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Modes.Arm.Seq`, which only this module used -/

section

/-!
# The modes one block at a time on ARMv7: the contract, the invariant, the prologue

`seqArm c S M`: the contract `Core.seq c M` meets, for any core `c` (with
`S : CoreSpec c`) and mode `M`, on
`(schedule = r0, iv = r1, data = r2, n = r3, scratch = [sp])`, or
`(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`
if the core takes a number of rounds (which must then satisfy `S.rok`): the `n`
blocks at `data` become `runSeq`'s, the mode's steps (`stepOf`) from the IV
in the chaining block and the spare block as the scratch buffer has it; with
`M.finish`, the IV becomes the last chaining block. Each mode's own
(target-independent) lemmas say what `runSeq` is: CBC's encryption, and so
on. The callee's `S.stack` bytes below the stack pointer may not overlap a
buffer.

The registers are saved in the scratch buffer (`savedMem`), and the
invariant after `k` blocks (`LInv`): the registers hold the arguments (`r6`
the next block, `r7` the blocks left), only the data, the chaining and spare
blocks and the stack below the stack pointer have changed since the
registers were saved, the first `k` blocks are `runSeq`'s of the first `k`
blocks on entry and the rest are unchanged, and the chaining and spare
blocks are what `runSeq` leaves after them.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over over_frame)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_cmp wp_ldrSp op2_imm op2_reg cmp0)

/-- The mode on blocks: each block, as the data block, through `stepOf`,
from the blocks `b`; the outputs, and the blocks left at the end. -/
def runSeq (M : Mode) (ciph : Spec.Cbc.Cipher) : Blks → List (List Byte) → List (List Byte) × Blks
  | b, [] => ([], b)
  | b, x :: xs =>
    let b' := stepOf M ciph (b.set .d x)
    let r := runSeq M ciph b' xs
    (b'.d :: r.1, r.2)

theorem runSeq_snoc (M : Mode) (ciph : Spec.Cbc.Cipher) (x : List Byte) :
    ∀ (b : Blks) (xs : List (List Byte)), runSeq M ciph b (xs ++ [x]) =
      ((runSeq M ciph b xs).1 ++ [(stepOf M ciph ((runSeq M ciph b xs).2.set .d x)).d],
        stepOf M ciph ((runSeq M ciph b xs).2.set .d x))
  | b, [] => rfl
  | b, y :: ys => by
    simp only [List.cons_append, runSeq, runSeq_snoc M ciph x _ ys]

theorem runSeq_length (M : Mode) (ciph : Spec.Cbc.Cipher) :
    ∀ (b : Blks) (xs : List (List Byte)), (runSeq M ciph b xs).1.length = xs.length
  | _, [] => rfl
  | b, _ :: xs => by simp [runSeq, runSeq_length M ciph _ xs]

section
variable (c : Core) (s : State)

/-- The IV's address, among the arguments of `Core.seq c M`. -/
def ivArg : BitVec 32 := if c.rounds then s.gpr .r2 else s.gpr .r1
/-- The data's address. -/
def dArg : BitVec 32 := if c.rounds then s.gpr .r3 else s.gpr .r2
/-- The number of elements. -/
def nArg : BitVec 32 := if c.rounds then stackArg s 0 else s.gpr .r3
/-- The scratch buffer's address. -/
def scArg : BitVec 32 := stackArg s (if c.rounds then 1 else 0)
/-- The size of the stack arguments. -/
def argBytes : Nat := if c.rounds then 8 else 4

end

/-- What a mode needs of the tables `K` its core reads: held, readable,
within the address space, apart from the writable regions and the `st`
bytes of stack below the stack pointer, and at multiples of 64. -/
def TabsOk (K : List (String × List (BitVec 64))) (st : Nat) (s : State) : Prop :=
  Abi.constsHeld s.mem (fun n => State.addr (s.syms n)) K ∧
    (∀ t ∈ tabRegs K s, t ∈ s.rd ∧ t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
      t.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 st, st⟩) ∧
    ∀ t ∈ tabRegs K s, t.base.toNat % 64 = 0

-- Used only in default arguments (`OfbCfb.lean`), which no index records.
theorem tabsOk_nil (st : Nat) (s : State) : TabsOk [] st s :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

section
variable (c : Core) (S : CoreSpec c)

/-- `Core.seq c M`
`(schedule = r0, iv = r1, data = r2, n = r3, scratch = [sp])`, or
`(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def seqArm (M : Mode) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), S.keyLen⟩
    let iv : Region := ⟨State.addr (ivArg c s), c.bs⟩
    let data : Region := ⟨State.addr (dArg c s), (nArg c s).toNat * c.ds M⟩
    let scr : Region := ⟨State.addr (scArg c s), c.scratchBytes⟩
    let arg : Region := ⟨stackArgAddr s 0, argBytes c⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩
    S.stack ≤ s.sp.toNat ∧ s.sp.toNat + argBytes c ≤ 2 ^ 32 ∧
      key ∈ s.rd ++ s.wr ∧ iv ∈ s.rd ++ s.wr ∧ arg ∈ s.rd ++ s.wr ∧ data ∈ s.wr ∧ scr ∈ s.wr ∧
      key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ data.Disjoint scr ∧
      below.Disjoint key ∧ below.Disjoint data ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + S.keyLen ≤ 2 ^ 32 ∧ (ivArg c s).toNat + c.bs ≤ 2 ^ 32 ∧
      (dArg c s).toNat + (nArg c s).toNat * c.ds M ≤ 2 ^ 32 ∧ (scArg c s).toNat + c.scratchBytes ≤ 2 ^ 32 ∧
      (M.finish = true → iv ∈ s.wr) ∧ (∀ r ∈ s.wr, arg.Disjoint r) ∧ (c.rounds = true → S.rok (s.gpr .r1)) ∧
      TabsOk S.consts S.stack s
  post s s' :=
    let r := runSeq M (S.ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
      ⟨[], bytesAt s.mem (State.addr (ivArg c s)) c.bs,
        bytesAt s.mem (State.addr (scArg c s) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
      (blocksOf (c.ds M) s.mem (State.addr (dArg c s)) (nArg c s).toNat)
    blocksOf (c.ds M) s'.mem (State.addr (dArg c s)) (nArg c s).toNat = r.1 ∧
      (M.finish = true → bytesAt s'.mem (State.addr (ivArg c s)) c.bs = r.2.o)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ (c.rounds = true → stackArg s₁ 1 = stackArg s₂ 1) ∧
      ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1

end

section
variable (c : Core) {c' : Core} (S : CoreSpec c') (s₀ : State)

abbrev Kp : BitVec 32 := s₀.gpr .r0
abbrev Rp : BitVec 32 := s₀.gpr .r1
abbrev Ivp : BitVec 32 := ivArg c s₀
abbrev Dp : BitVec 32 := dArg c s₀
abbrev N : Nat := (nArg c s₀).toNat
abbrev Sc : BitVec 32 := scArg c s₀

abbrev keyR : Region := ⟨State.addr (Kp s₀), S.keyLen⟩
abbrev ivR : Region := ⟨State.addr (Ivp c s₀), c.bs⟩
abbrev dataR (M : Mode) : Region := ⟨State.addr (Dp c s₀), N c s₀ * c.ds M⟩
abbrev scrR : Region := ⟨State.addr (Sc c s₀), c.scratchBytes⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, argBytes c⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 S.stack, S.stack⟩
/-- The chaining and spare blocks, and the callee's working space. -/
abbrev blkR : Region := ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, 2 * c.bs + c.stackScratch⟩
abbrev oA : Addr := State.addr (Sc c s₀) + BitVec.ofNat 64 oOff
abbrev tA : Addr := State.addr (Sc c s₀) + BitVec.ofNat 64 (oOff + c.bs)

/-- The cipher, as on entry. -/
abbrev ciph : Spec.Cbc.Cipher := S.ciphAt s₀.mem (State.addr (Kp s₀)) (Rp s₀)
/-- The blocks on entry. -/
abbrev xs (M : Mode) : List (List Byte) := blocksOf (c.ds M) s₀.mem (State.addr (Dp c s₀)) (N c s₀)
/-- The blocks the mode starts from. -/
abbrev b0 : Blks := ⟨[], bytesAt s₀.mem (State.addr (Ivp c s₀)) c.bs, bytesAt s₀.mem (tA c s₀) c.bs⟩
/-- The mode after the first `k` blocks. -/
abbrev rK (M : Mode) (k : Nat) : List (List Byte) × Blks := runSeq M (ciph S s₀) (b0 c' s₀) ((xs c' s₀ M).take k)

/-- The memory once the registers are saved. -/
def savedMem : Mem := Spill.saveMem s₀.mem (State.addr (Sc c s₀)) s₀.gpr saved

end

theorem N_lt (c : Core) (s₀ : State) : N c s₀ < 2 ^ 32 := (nArg c s₀).isLt

/-- The precondition, by name. -/
structure UPre (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) : Prop where
  stk : S.stack ≤ s₀.sp.toNat
  spF : s₀.sp.toNat + argBytes c ≤ 2 ^ 32
  key_in : keyR S s₀ ∈ s₀.rd ++ s₀.wr
  iv_in : ivR c s₀ ∈ s₀.rd ++ s₀.wr
  arg_in : argR c s₀ ∈ s₀.rd ++ s₀.wr
  data_in : dataR c s₀ M ∈ s₀.wr
  scr_in : scrR c s₀ ∈ s₀.wr
  key_data : (keyR S s₀).Disjoint (dataR c s₀ M)
  key_scr : (keyR S s₀).Disjoint (scrR c s₀)
  iv_data : (ivR c s₀).Disjoint (dataR c s₀ M)
  iv_scr : (ivR c s₀).Disjoint (scrR c s₀)
  data_scr : (dataR c s₀ M).Disjoint (scrR c s₀)
  b_key : (belowR S s₀).Disjoint (keyR S s₀)
  b_data : (belowR S s₀).Disjoint (dataR c s₀ M)
  b_scr : (belowR S s₀).Disjoint (scrR c s₀)
  fK : (Kp s₀).toNat + S.keyLen ≤ 2 ^ 32
  fIv : (Ivp c s₀).toNat + c.bs ≤ 2 ^ 32
  fD : (Dp c s₀).toNat + N c s₀ * c.ds M ≤ 2 ^ 32
  fS : (Sc c s₀).toNat + c.scratchBytes ≤ 2 ^ 32
  fin : M.finish = true → ivR c s₀ ∈ s₀.wr
  arg_wr : ∀ r ∈ s₀.wr, (argR c s₀).Disjoint r
  rok : c.rounds = true → S.rok (Rp s₀)
  tabs : TabsOk S.consts S.stack s₀

theorem UPre.of {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (h : (seqArm c S M).pre s₀) :
    UPre c S M s₀ :=
  let ⟨a, b, d, e, f, g, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩ := h
  ⟨a, b, d, e, f, g, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Kp s₀
  r5 : s.gpr .r5 = Ivp c s₀
  r6 : s.gpr .r6 = Dp c s₀ + BitVec.ofNat 32 (c.ds M * k)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k)
  r8 : s.gpr .r8 = Sc c s₀
  r11 : c.rounds = true → s.gpr .r11 = Rp s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) s.mem
  data : blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀) = (rK S s₀ M k).1 ++ (xs c s₀ M).drop k
  o : bytesAt s.mem (oA c s₀) c.bs = (rK S s₀ M k).2.o
  t : bytesAt s.mem (tA c s₀) c.bs = (rK S s₀ M k).2.t

/-! ## Facts of the layout -/

theorem CoreSpec.bs_pos {c : Core} (S : CoreSpec c) : 0 < c.bs := by have := S.bw_pos; unfold Core.bs; omega_arith

theorem CoreSpec.ds_pos {c : Core} (S : CoreSpec c) (M : Mode) : 0 < c.ds M := by
  have := S.bs_pos; unfold Core.ds; split <;> omega_arith

theorem CoreSpec.ds_le {c : Core} (S : CoreSpec c) (M : Mode) : c.ds M ≤ c.bs := by
  have := S.bs_pos; unfold Core.ds; split <;> omega_arith

theorem CoreSpec.ds_enc {c : Core} (S : CoreSpec c) (M : Mode) : encodable (BitVec.ofNat 32 (c.ds M)) = true := by
  unfold Core.ds; split
  · decide
  · exact S.bs_enc

theorem saved_slots : Spill.Slots 0 36 saved := by decide
/-- The registers restored before `r8`, the base, which is restored last. -/
def savedA : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]
theorem saved_eq : saved = savedA ++ [(.r8, 16)] := rfl
theorem savedA_slots : Spill.Slots 0 36 savedA := by decide
theorem savedA_restorable : Spill.Restorable .r8 savedA := by decide
theorem saved_bound : ∀ p ∈ saved, p.2 + 4 ≤ 36 := by decide

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp


omit hp in
theorem UPre.blk_sub : Region.Sub (blkR c s₀) (scrR c s₀) := VG.Offset.sub_base _ (by unfold Core.scratchBytes Core.csOff; omega_arith)

omit hp in
/-- The chaining and spare blocks, within the scratch buffer. -/
theorem UPre.blk2_sub : Region.Sub ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, 2 * c.bs⟩ (scrR c s₀) :=
  VG.Offset.sub_base _ (by unfold Core.scratchBytes Core.csOff; omega_arith)

theorem UPre.slots_disj_blk : Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 0, 36⟩ (blkR c s₀) :=
  VG.Offset.disjoint _ (.inl (by unfold oOff; omega_arith)) (by omega_arith) (by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith)

omit hp in
theorem UPre.slots_sub : Region.Sub ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 0, 36⟩ (scrR c s₀) :=
  VG.Offset.sub_base _ (by unfold Core.scratchBytes Core.csOff oOff; omega_arith)

omit hp in
/-- Saving the registers changes only the slots. -/
theorem UPre.savedMem_frame : Frame [⟨State.addr (Sc c s₀) + BitVec.ofNat 64 0, 36⟩] s₀.mem (savedMem c s₀) :=
  Spill.saveMem_frame_slots saved_slots _ _ _

/-- What a frame within the scratch buffer, the data and the stack leaves of
the schedule. -/
theorem UPre.ciph_eq {m : Mem}
    (hf : Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem m) :
    S.ciphAt m (State.addr (Kp s₀)) (Rp s₀) = ciph S s₀ := by
  refine (S.ciphAt_congr fun i hi => ?_).symm
  refine (hf.bytes (R := keyR S s₀) (fun r hr => ?_) (by show S.keyLen ≤ 2 ^ 64; have := hp.fK; omega_arith) hi).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.key_data
  · exact hp.key_scr
  · exact hp.b_key.symm

end

/-! ## The prologue -/


/-- What the saves and the copy of the IV leave in memory. -/
theorem prologue_mem {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀) :
    let m := over (savedMem c s₀) (oA c s₀) (4 * c.bw) fun i =>
      savedMem c s₀ (State.addr (Ivp c s₀) + BitVec.ofNat 64 0 + BitVec.ofNat 64 i)
    Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) m ∧
      blocksOf (c.ds M) m (State.addr (Dp c s₀)) (N c s₀) = xs c s₀ M ∧
      bytesAt m (oA c s₀) c.bs = bytesAt s₀.mem (State.addr (Ivp c s₀)) c.bs ∧
      bytesAt m (tA c s₀) c.bs = bytesAt s₀.mem (tA c s₀) c.bs := by
  intro m
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  obtain fs := UPre.savedMem_frame (c := c) (s₀ := s₀)
  -- The slots are apart from all but the scratch buffer's own bytes.
  obtain slotsDisj : ∀ {R : Region}, R.Disjoint (scrR c s₀) →
      ∀ r ∈ [(⟨State.addr (Sc c s₀) + BitVec.ofNat 64 0, 36⟩ : Region)], R.Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (UPre.slots_sub (c := c) (s₀ := s₀))
  obtain oSub : Region.Sub ⟨oA c s₀, 4 * c.bw⟩ (blkR c s₀) := Region.sub_prefix (by omega_arith)
  refine ⟨(over_frame _ _ _ _).sub fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨blkR c s₀, by simp, oSub⟩
  · -- The data: apart from the slots and the chaining block.
    refine List.map_congr_left fun j hj => ?_
    obtain hj := List.mem_range.mp hj
    obtain hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
      VG.Offset.sub_base _ (by have := VG.Proof.Modes.idx_lt (L := c.ds M) hj; rw [Nat.mul_comm (N c s₀)]; omega_arith)
    rw [bytesAt_over_other _ _ ((hp.data_scr.sub_left hsub).sub_right (fun a h => UPre.blk_sub a (oSub a h))).symm
      (by have := S.ds_le M; omega_arith)]
    exact VG.Proof.Modes.bytesAt_frame fs (slotsDisj (hp.data_scr.sub_left hsub)) (by have := S.ds_le M; omega_arith)
  · have e := VG.Proof.Modes.bytesAt_frame fs (slotsDisj hp.iv_scr) (by show c.bs ≤ 2 ^ 64; omega_arith)
    rw [hbs] at e ⊢
    rw [bytesAt_over_self _ _ _ (by omega_arith), ← e]
    simp only [bytesAt, add0]
  · rw [bytesAt_over_other _ _ (VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (by omega_arith)]
    exact VG.Proof.Modes.bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint _ (.inr (by unfold oOff; omega_arith)) (by omega_arith) (by omega_arith))) (by omega_arith)

end VG.Proof.Modes.Arm

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf over over_frame)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_cmp wp_ldrSp op2_imm op2_reg cmp0)

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
/-- A region at an offset within one of the regions `rs`. -/
theorem cov_off {rs : List Region} {R : Region} (hR : R ∈ rs) {d n : Nat} (h : d + n ≤ R.len) :
    Covers [⟨R.base + BitVec.ofNat 64 d, n⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨R, hR, d, rfl, h⟩

theorem UPre.npreIv {s : State} (h8 : s.gpr .r8 = Sc c s₀) (h5 : s.gpr .r5 = Ivp c s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    NPre c.bw s .r8 .r5 oOff 0 (oA c s₀) (State.addr (Ivp c s₀) + BitVec.ofNat 64 0) := by
  have hS := hp.fS
  have hI := hp.fIv
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have hb := S.bw_le
  have ho : oOff = 40 := rfl
  refine ⟨by rw [h8], by rw [h5], by rw [h8]; omega_arith, by rw [h5]; omega_arith, by omega_arith, by omega_arith, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [hwr]; exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 4 * c.bw ≤ c.scratchBytes; omega_arith)
  · rw [hrd, hwr]; exact cov_off (R := ivR c s₀) hp.iv_in (by show 0 + 4 * c.bw ≤ c.bs; omega_arith)
  · refine (hp.iv_scr.symm.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right ?_
    rw [add0]; exact Region.sub_prefix (by omega_arith)

omit hp in
/-- A stack argument, within the arguments' region. -/
theorem argR_contains (hF : s₀.sp.toNat + argBytes c ≤ 2 ^ 32) {i : Nat} (hi : 4 * i + 4 ≤ argBytes c) :
    (argR c s₀).Contains (stackArgAddr s₀ i) 4 := by
  obtain e : stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]; exact addr_add (by omega_arith)
  rw [e]; exact VG.Offset.contains_base _ hi (by omega_arith)

/-- The rest of the prologue: the IV to the chaining block, and Z. -/
theorem prologue_tail {s₇ : State} (r4 : s₇.gpr .r4 = Kp s₀) (r5 : s₇.gpr .r5 = Ivp c s₀)
    (r6 : s₇.gpr .r6 = Dp c s₀) (r7 : s₇.gpr .r7 = nArg c s₀) (r8 : s₇.gpr .r8 = Sc c s₀)
    (r11 : c.rounds = true → s₇.gpr .r11 = Rp s₀) (rd₇ : s₇.rd = s₀.rd) (wr₇ : s₇.wr = s₀.wr)
    (sp₇ : s₇.sp = s₀.sp) (m₇ : s₇.mem = savedMem c s₀) :
    WP isa (.block ((List.range c.bw).flatMap (copyWord .r8 .r5 oOff 0) ++
      ([.cmp .r7 (.imm 0)] : List Instr))) s₇ fun s => LInv c S M s₀ 0 s ∧ s.z = decide (N c s₀ = 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (copyN_wp (hp.npreIv r8 r5 rd₇ wr₇)) fun s₈ hi => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ =>
    WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r9 → r ≠ .r10 → s₉.gpr r = s₇.gpr r := fun r a b => by rw [f₉.gpr, hi.regs r a b]
  obtain ⟨fr, dt, oo, tt⟩ := prologue_mem hp
  obtain m₉ : s₉.mem = over (savedMem c s₀) (oA c s₀) (4 * c.bw) fun i =>
      savedMem c s₀ (State.addr (Ivp c s₀) + BitVec.ofNat 64 0 + BitVec.ofNat 64 i) := by
    rw [f₉.mem, hi.mem, m₇]
  obtain a0 : nArg c s₀ = BitVec.ofNat 32 (N c s₀) := by simp [N]
  refine ⟨⟨by rw [g _ (by decide) (by decide), r4], by rw [g _ (by decide) (by decide), r5],
    by rw [g _ (by decide) (by decide), r6, Nat.mul_zero, BitVec.add_zero],
    by rw [g _ (by decide) (by decide), r7, a0, Nat.sub_zero], by rw [g _ (by decide) (by decide), r8],
    fun hr => by rw [g _ (by decide) (by decide), r11 hr],
    by rw [f₉.sp, hi.sp, sp₇], by rw [f₉.rd, hi.rd, rd₇], by rw [f₉.wr, hi.wr, wr₇], by rw [m₉]; exact fr,
    by rw [m₉, dt]; simp [rK, runSeq], by rw [m₉, oo]; simp [rK, runSeq], by rw [m₉, tt]; simp [rK, runSeq]⟩, ?_⟩
  rw [z₉, show s₈.gpr .r7 = s₇.gpr .r7 from hi.regs _ (by decide) (by decide), r7, a0]
  exact cmp0 (N_lt c s₀)

theorem prologue_wp :
    WP isa (.block (c.save ++ c.setup)) s₀ fun s => LInv c S M s₀ 0 s ∧ s.z = decide (N c s₀ = 0) := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have ho : oOff = 40 := rfl
  have hF := hp.spF
  rw [show c.save ++ c.setup = .ldrSp .r12 c.scOff :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ c.setup)
    from rfl]
  obtain hoff : c.scOff < 4096 := by unfold Core.scOff; split <;> decide
  obtain haddr : State.addr (s₀.sp + BitVec.ofNat 32 c.scOff) = stackArgAddr s₀ (if c.rounds then 1 else 0) := by
    unfold Core.scOff stackArgAddr; split <;> rfl
  obtain hin : (argR c s₀).Contains (stackArgAddr s₀ (if c.rounds then 1 else 0)) 4 :=
    argR_contains hF (by unfold argBytes; split <;> simp)
  refine wp_ldrSp hoff haddr ⟨argR c s₀, hp.arg_in, hin⟩ fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = Sc c s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega_arith, by omega_arith, ⟨scrR c s₀, hp.scr_in, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩⟩
  obtain hm₂ : s₂.mem = savedMem c s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (by revert p; decide)
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  obtain sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  obtain g₂' : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂, u₁.other _ h]
  obtain h12' : s₂.gpr .r12 = Sc c s₀ := by rw [g₂, h12]
  unfold Core.setup
  cases hr : c.rounds
  · simp only [Bool.false_eq_true, ↓reduceIte, mov, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
      wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
    refine prologue_tail hp ?_ ?_ ?_ ?_ ?_ (fun h => absurd h (by simp [hr]))
      (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂'])
      (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂']) (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂])
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂']
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂', Ivp, ivArg, hr]; rfl
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂', Dp, dArg, hr]; rfl
    · simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂', nArg, hr]; rfl
    · simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, h12']
  · simp only [↓reduceIte, mov, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
      wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
    obtain m₆ : s₆.mem = savedMem c s₀ := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
    obtain sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂']
    obtain in0 : (argR c s₀).Contains (stackArgAddr s₀ 0) 4 := argR_contains hF (by simp [argBytes, hr])
    refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [sp₆]; rfl)
      (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂', u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']; exact ⟨_, hp.arg_in, in0⟩)
      fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ => ?_
    obtain n7 : s₇.gpr .r7 = nArg c s₀ := by
      rw [u₇.gpr, m₆]
      obtain fs := UPre.savedMem_frame (c := c) (s₀ := s₀)
      refine (fs.readW in0 (fun r hr' => ?_) (by decide)).trans ?_
      · simp only [List.mem_singleton] at hr'; subst hr'
        exact (hp.arg_wr _ hp.scr_in).sub_right UPre.slots_sub
      · simp [nArg, hr, stackArg]
    refine prologue_tail hp ?_ ?_ ?_ ?_ ?_ ?_
      (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'])
      (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂'])
      (by rw [u₈.sp, u₇.sp, sp₆]) (by rw [u₈.mem, u₇.mem, m₆])
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂']
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂', Ivp, ivArg, hr]
      rfl
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂', Dp, dArg, hr]
      rfl
    · rw [u₈.other _ (by decide), n7]
    · simp (disch := decide) only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, h12']
    · intro _
      simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂']

end

end VG.Proof.Modes.Arm

end

end


/-!
# The modes one block at a time on ARMv7: one block

`body_ok`: one run of `Core.body c M`, on block `k`, takes the invariant
from `k` blocks to `k + 1`, and sets Z when no blocks are left. The data
block `k`, the chaining block and the spare block are `Blks` in memory
(`BlkMem`) throughout: the operations before the call (`opsCode_wp`), the
call of the core on the mode's block (`call_wp`), the operations after it,
and the step to the next block. Block `k` is then `stepOf`'s data block,
and the others are unchanged.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_subs op2_imm op2_reg ofNat_beq_zero)

/-- A mode whose operations are each on two different blocks (and, a byte
at a time, do not treat the data byte as a block), and which calls the
cipher on a whole block at an encodable offset. -/
structure ModeOk (c : Core) (M : Mode) : Prop where
  pre : M.pre.all (opOk c.bs M.byte) = true
  post : M.post.all (opOk c.bs M.byte) = true
  tgt : M.byte = true → M.tgt ≠ .d
  tgt_enc : encodable (BitVec.ofNat 32 (c.base M.tgt).2) = true

theorem ds_of (c : Core) {M : Mode} (h : M.byte = false) : c.ds M = c.bs := by simp [Core.ds, h]

/-- The call's block is a whole block. -/
theorem ModeOk.tgt_sz {c : Core} {M : Mode} (hM : ModeOk c M) : sz c (c.ds M) M.tgt = c.bs := by
  cases ht : M.tgt
  · cases hb : M.byte
    · simp [sz, ds_of c hb]
    · exact absurd ht (hM.tgt hb)
  · rfl
  · rfl

/-! ## Blocks in memory -/

theorem length_blocksOf (L : Nat) (m : Mem) (p : Addr) (n : Nat) : (blocksOf L m p n).length = n := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

theorem getElem_blocksOf (L : Nat) (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (blocksOf L m p n)[k]'(by rw [length_blocksOf]; exact hk) = bytesAt m (p + BitVec.ofNat 64 (L * k)) L := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

/-- The blocks after one of them changed. -/
theorem blocksOf_set {L : Nat} {m m' : Mem} {p : Addr} {n k : Nat}
    (h : ∀ j < n, j ≠ k →
      bytesAt m' (p + BitVec.ofNat 64 (L * j)) L = bytesAt m (p + BitVec.ofNat 64 (L * j)) L) :
    blocksOf L m' p n = (blocksOf L m p n).set k (bytesAt m' (p + BitVec.ofNat 64 (L * k)) L) := by
  apply List.ext_getElem (by simp [length_blocksOf])
  intro j h₁ h₂
  rw [length_blocksOf] at h₁
  rw [List.getElem_set, getElem_blocksOf _ _ _ h₁]
  by_cases hj : k = j
  · subst hj; simp
  · simp only [hj, ↓reduceIte]; rw [getElem_blocksOf _ _ _ h₁, h j h₁ (Ne.symm hj)]

/-- The first `k` blocks transformed and the rest not, with block `k`
replaced. -/
theorem set_prefix {α : Type} (ys xs : List α) (x : α) {k : Nat} (hy : ys.length = k) (hk : k < xs.length) :
    (ys ++ xs.drop k).set k x = (ys ++ [x]) ++ xs.drop (k + 1) := by
  subst hy
  rw [List.set_append_right _ _ (by omega_arith), Nat.sub_self, List.append_assoc]
  congr 1
  rw [List.drop_eq_getElem_cons hk, List.set_cons_zero]
  rfl

/-! ## Block `k` -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem idx_lt' {L k n : Nat} (hk : k < n) : L * k + L ≤ n * L := by
  rw [Nat.mul_comm n]; exact VG.Proof.Modes.idx_lt hk

/-- The address of block `k`, in 32 bits. -/
abbrev Dk (s₀ : State) (c : Core) (M : Mode) (k : Nat) : BitVec 32 := Dp c s₀ + BitVec.ofNat 32 (c.ds M * k)

theorem UPre.dk_toNat {k : Nat} (hk : k < N c s₀) : (Dk s₀ c M k).toNat = (Dp c s₀).toNat + c.ds M * k := by
  have := hp.fD
  have := idx_lt' (L := c.ds M) hk
  have := S.ds_pos M
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.ds M * k) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem UPre.dk_addr {k : Nat} (hk : k < N c s₀) :
    State.addr (Dk s₀ c M k) = State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * k) := by
  have := hp.fD
  have := idx_lt' (L := c.ds M) hk
  exact addr_add (by have := S.ds_pos M; omega_arith)

theorem UPre.blk_sub_data {k : Nat} (hk : k < N c s₀) :
    Region.Sub ⟨State.addr (Dk s₀ c M k), c.ds M⟩ (dataR c s₀ M) := by
  rw [hp.dk_addr hk]
  exact VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hk; omega_arith)

theorem UPre.lay {k : Nat} (hk : k < N c s₀) : Lay c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₀.wr := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs + c.stackScratch := rfl
  refine ⟨S.bw_pos, S.bw_le, S.ds_pos M, S.ds_le M, ?_, by omega_arith, ?_, ?_, ?_⟩
  · rw [hp.dk_toNat hk]
    have := hp.fD; have := idx_lt' (L := c.ds M) hk; omega_arith
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨dataR c s₀ M, hp.data_in, c.ds M * k, hp.dk_addr hk, ?_⟩
      have := idx_lt' (L := c.ds M) hk; show _ ≤ N c s₀ * c.ds M; omega_arith
  · exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 2 * c.bs ≤ c.scratchBytes; omega_arith)
  · exact (hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right UPre.blk2_sub

/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N c s₀) :
    bytesAt s.mem (State.addr (Dk s₀ c M k)) (c.ds M) = (xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk) := by
  obtain hl : (rK S s₀ M k).1.length = k := by
    rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (blocksOf (c.ds M) s.mem (State.addr (Dp c s₀)) (N c s₀)).length by
      rw [length_blocksOf]; exact hk),
    List.getElem?_append_right (show (rK S s₀ M k).1.length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (xs c s₀ M).length by rw [length_blocksOf]; exact hk)] at this
  rw [hp.dk_addr hk, ← getElem_blocksOf _ _ _ hk]
  exact Option.some.inj this

/-- The blocks of the step, in memory. -/
theorem LInv.blkMem {k : Nat} {s : State} (h : LInv c S M s₀ k s) (hk : k < N c s₀) :
    BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s.mem
      ((rK S s₀ M k).2.set .d ((xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk))) := by
  intro x
  cases x
  · exact h.block hp hk
  · exact h.o
  · exact h.t

end

/-! ## The callee's working space -/

/-- The address of the callee's working space, at the end of the scratch
buffer. -/
abbrev Cs (c : Core) (s₀ : State) : BitVec 32 := Sc c s₀ + BitVec.ofNat 32 c.csOff

/-- The callee's working space. -/
abbrev csR (c : Core) (s₀ : State) : Region := ⟨State.addr (Cs c s₀), c.stackScratch⟩

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

theorem UPre.cs_toNat (hs : c.stackScratch ≠ 0) : (Cs c s₀).toNat = (Sc c s₀).toNat + c.csOff := by
  have := hp.fS; unfold Core.scratchBytes at this
  have := S.bw_le
  have e : c.csOff = oOff + 2 * c.bs := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.csOff) (by rw [e]; unfold oOff at *; omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem UPre.cs_addr (hs : c.stackScratch ≠ 0) :
    State.addr (Cs c s₀) = State.addr (Sc c s₀) + BitVec.ofNat 64 c.csOff := by
  have := hp.fS; unfold Core.scratchBytes at this
  exact addr_add (by omega_arith)

theorem UPre.cs_fit (hs : c.stackScratch ≠ 0) : (Cs c s₀).toNat + c.stackScratch ≤ 2 ^ 32 := by
  have := hp.fS; unfold Core.scratchBytes at this; rw [hp.cs_toNat hs]; omega_arith

omit hp in
theorem csR_empty (hs : c.stackScratch = 0) (a : Addr) : ¬ (csR c s₀).Contains a 1 := by
  simp only [Region.Contains, hs]; omega_arith

theorem UPre.cs_sub_scr : Region.Sub (csR c s₀) (scrR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a h => absurd h (csR_empty hs a)
  show Region.Sub ⟨State.addr (Cs c s₀), _⟩ _
  rw [hp.cs_addr hs]; exact VG.Offset.sub_base _ (by unfold Core.scratchBytes; omega_arith)

theorem UPre.cs_sub_blk : Region.Sub (csR c s₀) (blkR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a h => absurd h (csR_empty hs a)
  show Region.Sub ⟨State.addr (Cs c s₀), _⟩ _
  rw [hp.cs_addr hs]; exact VG.Offset.sub _ (by unfold Core.csOff; omega_arith) (by unfold Core.csOff; omega_arith)

/-- The blocks of a step are apart from the callee's working space. -/
theorem UPre.blk_cs {k : Nat} (hk : k < N c s₀) (x : Blk) :
    Region.Disjoint ⟨addrOf c (Dk s₀ c M k) (Sc c s₀) x, sz c (c.ds M) x⟩ (csR c s₀) := by
  by_cases hs : c.stackScratch = 0
  · exact fun a _ h => csR_empty hs a h
  obtain hS := hp.fS; unfold Core.scratchBytes at hS
  have hcs : c.csOff = oOff + 2 * c.bs := rfl
  cases x
  · exact (hp.data_scr.sub_left (hp.blk_sub_data hk)).sub_right hp.cs_sub_scr
  · show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 oOff, c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
    rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨State.addr (Sc c s₀) + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ ⟨State.addr (Cs c s₀), _⟩
    rw [hp.cs_addr hs]; exact VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

end

theorem scrArg_wp {c : Core} (S : CoreSpec c) {s : State} {Sb : BitVec 32} {Q : State → Prop}
    (h8 : s.gpr .r8 = Sb)
    (hQ : ∀ s', (∀ x, x ≠ .r12 → s'.gpr x = s.gpr x) →
      (c.stackScratch ≠ 0 → s'.gpr .r12 = Sb + BitVec.ofNat 32 c.csOff) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.mem = s.mem → Q s') :
    WP isa (.block c.scrArg) s Q := by
  unfold Core.scrArg
  split
  · exact WP.block_nil (hQ s (fun _ _ => rfl) (fun h => absurd ‹_› h) rfl rfl rfl rfl)
  · exact wp_add (op2_imm (S.cs_enc ‹_›)) fun s' u => WP.block_nil
      (hQ s' u.other (fun _ => by rw [u.gpr, h8]) u.rd u.wr u.sp u.mem)

/-- The constant argument to `r3`, if the core takes one. -/
theorem arg3_wp {c : Core} (S : CoreSpec c) {s : State} {Q : State → Prop}
    (hQ : ∀ s', (∀ x, x ≠ .r3 → s'.gpr x = s.gpr x) → (c.arg3 = none → s'.gpr .r3 = s.gpr .r3) →
      (∀ k, c.arg3 = some k → s'.gpr .r3 = BitVec.ofNat 32 k) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.mem = s.mem → Q s') :
    WP isa (.block c.arg3Code) s Q := by
  unfold Core.arg3Code
  split
  · rename_i k hk
    exact wp_mov (op2_imm (S.arg3_enc k hk)) fun s' u => WP.block_nil
      (hQ s' u.other (fun h => by rw [hk] at h; cases h)
        (fun k' h => by rw [hk] at h; cases h; exact u.gpr) u.rd u.wr u.sp u.mem)
  · rename_i hk
    exact WP.block_nil (hQ s (fun _ _ => rfl) (fun _ => rfl) (fun k h => by rw [hk] at h; cases h) rfl rfl rfl rfl)

/-! ## The call's block -/

/-- The address of block `x` in 32 bits, with the data block at `D` and the
scratch buffer at `Sb`. -/
def bt (c : Core) (D Sb : BitVec 32) : Blk → BitVec 32
  | .d => D + BitVec.ofNat 32 (c.base .d).2
  | .o => Sb + BitVec.ofNat 32 (c.base .o).2
  | .t => Sb + BitVec.ofNat 32 (c.base .t).2

theorem bt_eq {c : Core} {D Sb : BitVec 32} {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = Sb) (x : Blk) :
    s.gpr (c.base x).1 + BitVec.ofNat 32 (c.base x).2 = bt c D Sb x := by
  cases x <;> simp [Core.base, bt, h6, h8]

theorem Lay.bt_addr {c : Core} {ds : Nat} {D Sb : BitVec 32} {wr : List Region} (h : Lay c ds D Sb wr) (x : Blk) :
    State.addr (bt c D Sb x) = addrOf c D Sb x := by
  have := h.fD; have := h.fS; have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp [bt, Core.base, addrOf]
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega_arith)
  · simp only [bt, Core.base, addrOf]; exact addr_add (by omega_arith)

theorem Lay.bt_fit {c : Core} {ds : Nat} {D Sb : BitVec 32} {wr : List Region} (h : Lay c ds D Sb wr) (x : Blk) :
    (bt c D Sb x).toNat + sz c ds x ≤ 2 ^ 32 := by
  have := h.fD; have := h.fS
  obtain e : ∀ (a : BitVec 32) (d : Nat), a.toNat + d < 2 ^ 32 → (a + BitVec.ofNat 32 d).toNat = a.toNat + d :=
    fun a d hd => by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
      Nat.mod_eq_of_lt hd]
  have := h.bw
  have hb : c.bs = 4 * c.bw := rfl
  cases x
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith
  · simp only [bt, Core.base]; rw [e _ _ (by omega_arith)]; simp only [sz]; omega_arith

/-! ## One block -/

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

/-- The memory since entry, for the cipher's schedule. -/
theorem UPre.frame_entry {m₁ m₂ : Mem} {k : Nat} (hk : k < N c s₀)
    (h₁ : Frame [dataR c s₀ M, blkR c s₀, belowR S s₀] (savedMem c s₀) m₁)
    (h₂ : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀)) m₁ m₂) :
    Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem m₂ := by
  obtain f₀ : Frame [dataR c s₀ M, scrR c s₀, belowR S s₀] s₀.mem (savedMem c s₀) :=
    (UPre.savedMem_frame (c := c) (s₀ := s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR c s₀, .tail _ (.head _), UPre.slots_sub⟩
  refine f₀.trans ((h₁.sub fun r hr => ?_).trans (h₂.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, fun _ h => h⟩
    · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk_sub⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩
  · simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, .head _, hp.blk_sub_data hk⟩
    · exact ⟨scrR c s₀, .tail _ (.head _), UPre.blk2_sub⟩

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (b : Blks) (s s₂ : State) : Prop where
  regs : ∀ x, x ≠ .r0 → x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r9 → x ≠ .r10 → x ≠ .r12 → s₂.gpr x = s.gpr x
  r0 : s₂.gpr .r0 = Kp s₀
  r1 : c.rounds = true → s₂.gpr .r1 = Rp s₀
  rD : s₂.gpr c.dReg = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt
  rN : s₂.gpr c.nReg = 1
  a3 : ∀ k, c.arg3 = some k → s₂.gpr .r3 = BitVec.ofNat 32 k
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  frame : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀)) s.mem s₂.mem
  blks : BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₂.mem b
  r12 : c.stackScratch ≠ 0 → s₂.gpr .r12 = Cs c s₀

theorem pre_wp (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {s : State} (h : LInv c S M s₀ k s) :
    WP isa (.block (c.opsCode M.pre ++ c.callArgs M.tgt)) s
      (PreA (c := c) (M := M) s₀ k (runOps M.pre ((rK S s₀ M k).2.set .d
        ((xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk)))) s) := by
  obtain hb := h.blkMem hp hk
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (ds_of c) (h.wr ▸ hp.lay hk) h.r6 h.r8 hb hM.pre) fun s₁ h₁ => ?_
  obtain h4 : s₁.gpr .r4 = Kp s₀ := by rw [h₁.regs _ (by decide) (by decide), h.r4]
  obtain hbt : s₁.gpr (c.base M.tgt).1 + BitVec.ofNat 32 (c.base M.tgt).2 = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt :=
    bt_eq (by rw [h₁.regs _ (by decide) (by decide), h.r6]) (by rw [h₁.regs _ (by decide) (by decide), h.r8]) _
  have enc := hM.tgt_enc
  obtain hne : (c.base M.tgt).1 ≠ .r0 ∧ (c.base M.tgt).1 ≠ .r1 := by cases M.tgt <;> simp [Core.base]
  simp only [Core.callArgs, mov]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  obtain h11 : c.rounds = true → s₂.gpr .r11 = Rp s₀ := fun hr => by
    rw [u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), h.r11 hr]
  obtain bt₂ : s₂.gpr (c.base M.tgt).1 + BitVec.ofNat 32 (c.base M.tgt).2 = bt c (Dk s₀ c M k) (Sc c s₀) M.tgt := by
    rw [u₂.other _ hne.1, hbt]
  cases hr : c.rounds
  · have hD : c.dReg = .r1 := by unfold Core.dReg; rw [hr]; rfl
    obtain hN : c.nReg = .r2 := by unfold Core.nReg; rw [hr]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, hD, hN]
    refine wp_add (op2_imm enc) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
      WP.block_append_iff.2 (arg3_wp S fun s₄' g₄ _ a₄ rd₄ wr₄ sp₄ m₄ => scrArg_wp S
      (by rw [g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        h₁.regs _ (by decide) (by decide), h.r8]) fun s₅ g₅ c₅ rd₅ wr₅ sp₅ m₅ =>
      ⟨fun x a b d e f g i => ?_, ?_, fun h => absurd h (by simp [hr]), ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_,
        ?_, c₅⟩)
    · rw [g₅ _ i, g₄ _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a, h₁.regs _ f g]
    · rw [g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h4]
    · rw [hD, g₅ _ (by decide), g₄ _ (by decide), u₄.other _ (by decide), u₃.gpr, bt₂]
    · rw [hN, g₅ _ (by decide), g₄ _ (by decide), u₄.gpr]
    · rw [g₅ _ (by decide), a₄ k hk]
    · rw [rd₅, rd₄, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
    · rw [wr₅, wr₄, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
    · rw [sp₅, sp₄, u₄.sp, u₃.sp, u₂.sp, h₁.sp]
    · rw [m₅, m₄, u₄.mem, u₃.mem, u₂.mem]; exact h₁.frame
    · rw [m₅, m₄, u₄.mem, u₃.mem, u₂.mem]; exact h₁.blks
  · have hD : c.dReg = .r2 := by unfold Core.dReg; rw [hr]; rfl
    obtain hN : c.nReg = .r3 := by unfold Core.nReg; rw [hr]; rfl
    obtain hn3 : c.arg3 = none := by
      cases h3 : c.arg3
      · rfl
      · have := S.arg3_rounds (by rw [h3]; rfl); rw [hr] at this; cases this
    simp only [↓reduceIte, List.cons_append, List.nil_append, hD, hN]
    refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_add (op2_imm enc) fun s₄ u₄ => wp_mov (op2_imm (by decide))
      fun s₅ u₅ => WP.block_append_iff.2 (arg3_wp S fun s₅' g₅' n₅ _ rd₅' wr₅' sp₅' m₅' => scrArg_wp S
      (by rw [g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), h.r8]) fun s₆ g₆ c₆ rd₆ wr₆ sp₆ m₆ =>
      ⟨fun x a b d e f g i => ?_, ?_, fun _ => ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, c₆⟩)
    · rw [g₆ _ i, g₅' _ e, u₅.other _ e, u₄.other _ d, u₃.other _ b, u₂.other _ a, h₁.regs _ f g]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, h4]
    · rw [g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, h11 hr]
    · rw [hD, g₆ _ (by decide), g₅' _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ hne.2, bt₂]
    · rw [hN, g₆ _ (by decide), n₅ hn3, u₅.gpr]
    · rw [hn3] at hk; cases hk
    · rw [rd₆, rd₅', u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
    · rw [wr₆, wr₅', u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
    · rw [sp₆, sp₅', u₅.sp, u₄.sp, u₃.sp, u₂.sp, h₁.sp]
    · rw [m₆, m₅', u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.frame
    · rw [m₆, m₅', u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.blks


/-- A region apart from the data and the scratch buffer is apart from the
blocks of a step. -/
theorem UPre.disj_blks {k : Nat} (hk : k < N c s₀) {R : Region} (hd : R.Disjoint (dataR c s₀ M))
    (hs : R.Disjoint (scrR c s₀)) (x : Blk) :
    R.Disjoint ⟨addrOf c (Dk s₀ c M k) (Sc c s₀) x, sz c (c.ds M) x⟩ := by
  obtain ⟨r, hr, hsub⟩ := Lay.sub (c := c) (ds := c.ds M) (Dp := Dk s₀ c M k) (S := Sc c s₀) x
  refine Region.Disjoint.sub_right ?_ hsub
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hd.sub_right (hp.blk_sub_data hk)
  · exact hs.sub_right UPre.blk2_sub

/-- The call's arguments make its precondition. -/
theorem PreA.callPre (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {b : Blks} {s s₂ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂) (hsy : s₂.syms = s₀.syms) :
    CallPre c S s₂ (Kp s₀) (Rp s₀) (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt) (Cs c s₀) := by
  obtain hL := hp.lay hk
  obtain sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  have ts := hM.tgt_sz
  obtain et : tabRegs S.consts s₂ = tabRegs S.consts s₀ := by simp only [tabRegs, hsy]
  have tw := hp.tabs.2.1
  refine ⟨a.r0, a.r1, hp.rok, a.rD, a.rN, a.a3, by rw [sp]; exact hp.stk, hp.fK, ts ▸ hL.bt_fit _, ?_, ?_, ?_, ?_, ?_,
    a.r12, hp.cs_fit, hp.key_scr.sub_right hp.cs_sub_scr, ?_, by rw [sp]; exact hp.b_scr.sub_right hp.cs_sub_scr,
    fun hs => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.bt_addr, ← ts]; exact hp.disj_blks hk hp.key_data hp.key_scr _
  · rw [sp]; exact hp.b_key
  · rw [sp, hL.bt_addr, ← ts]; exact hp.disj_blks hk hp.b_data hp.b_scr _
  · rw [a.rd, a.wr, h.rd, h.wr]; exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.key_in
  · rw [a.wr, h.wr, hL.bt_addr, ← ts]; exact hL.writable _
  · rw [hL.bt_addr, ← ts]; exact hp.blk_cs hk _
  · rw [a.wr, h.wr]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := hp.fS; unfold Core.scratchBytes at this
      exact ⟨_, hp.scr_in, c.csOff, hp.cs_addr hs, by show c.csOff + c.stackScratch ≤ c.scratchBytes; rfl⟩
  · rw [et, a.rd, h.rd]; exact fun t ht => (tw t ht).1
  · have e2 : (fun n => State.addr (s₂.syms n)) = fun n => State.addr (s₀.syms n) := by rw [hsy]
    rw [e2]
    refine held_frame (hp.frame_entry hk h.frame a.frame) (fun t ht r hr => ?_) (fun t ht => ?_) hp.tabs.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (tw t ht).2.2.1 _ hp.data_in
      · exact (tw t ht).2.2.1 _ hp.scr_in
      · exact (tw t ht).2.2.2
    · have := (tw t ht).2.1; omega_arith
  · rw [et]; exact fun t ht => (tw t ht).2.1
  · rw [et]; intro t ht
    rw [hL.bt_addr, ← ts]
    exact hp.disj_blks hk ((tw t ht).2.2.1 _ hp.data_in) ((tw t ht).2.2.1 _ hp.scr_in) _
  · rw [et]; exact fun t ht => ((tw t ht).2.2.1 _ hp.scr_in).sub_right hp.cs_sub_scr
  · rw [et, sp]; exact fun t ht => (tw t ht).2.2.2
  · rw [et]; exact hp.tabs.2.2

/-- The blocks after the call. -/
theorem call_blks (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {b : Blks} {s s₂ s₃ : State}
    (h : LInv c S M s₀ k s) (a : PreA (c := c) (M := M) s₀ k b s s₂)
    (cp : CallPost c S s₂ (Kp s₀) (Rp s₀) (bt c (Dk s₀ c M k) (Sc c s₀) M.tgt) (Cs c s₀) s₃) :
    BlkMem c (c.ds M) (Dk s₀ c M k) (Sc c s₀) s₃.mem (b.set M.tgt (ciph S s₀ (b.get M.tgt))) := by
  obtain hL := hp.lay hk
  obtain sp : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  obtain hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  intro x
  by_cases hx : x = M.tgt
  · subst hx
    rw [Blks.get_set_self, hM.tgt_sz, ← hL.bt_addr, cp.out, hL.bt_addr, ← hM.tgt_sz, a.blks M.tgt,
      hp.ciph_eq (hp.frame_entry hk h.frame a.frame)]
  · rw [Blks.get_set_of_ne _ _ hx, ← a.blks x]
    refine VG.Proof.Modes.bytesAt_frame cp.frame (fun r hr => ?_) (by have := hL.sz_le x; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hL.bt_addr, ← hM.tgt_sz]; exact hL.disjoint hx
    · exact hp.blk_cs hk x
    · rw [sp]; exact (hp.disj_blks hk hp.b_data hp.b_scr x).symm

end

section
variable {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀)
include hp

omit hp in
theorem take_succ_xs {k : Nat} (hk : k < N c s₀) :
    (xs c s₀ M).take (k + 1) = (xs c s₀ M).take k ++ [(xs c s₀ M)[k]'(by rw [length_blocksOf]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_blocksOf]; exact hk)]
  rfl

/-- The regions a step may change, within those the invariant allows. -/
theorem UPre.step_sub {k : Nat} (hk : k < N c s₀) :
    ∀ r ∈ blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀), ∃ r' ∈ [dataR c s₀ M, blkR c s₀, belowR S s₀], Region.Sub r r' := by
  intro r hr
  simp only [blkRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, .head _, hp.blk_sub_data hk⟩
  · exact ⟨_, .tail _ (.head _), Region.sub_prefix (by omega_arith)⟩

theorem body_ok (hM : ModeOk c M) {k : Nat} (hk : k < N c s₀) {s : State} (h : LInv c S M s₀ k s)
    (hsy : s.syms = s₀.syms) :
    WP isa (c.body M) s fun s' => LInv c S M s₀ (k + 1) s' ∧ s'.z = decide (N c s₀ - (k + 1) = 0) := by
  obtain hL := hp.lay hk
  obtain hfit : c.bs ≤ 2 ^ 64 := by have := hp.fS; unfold Core.scratchBytes Core.csOff at this; omega_arith
  refine WP.seq (VG.Arm.WP.mono_syms (pre_wp hp hM hk h) fun s₂ a sy₂ => ?_)
  refine WP.seq (WP.mono (call_wp S (a.callPre hp hM hk h (sy₂.trans hsy))) fun s₃ cp => ?_)
  obtain hb₂ := call_blks hp hM hk h a cp
  obtain g₃ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr hl h9 h10 => by
    rw [cp.saved r hr hl, a.regs r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
      (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr) h9 h10
      (by rintro rfl; simp [preserved] at hr)]
  obtain r6 : s₃.gpr .r6 = Dk s₀ c M k := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r6]
  obtain r8 : s₃.gpr .r8 = Sc c s₀ := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), h.r8]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [cp.wr, a.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp (ds_of c) (wr₃ ▸ hL) r6 r8 hb₂ hM.post) fun s₄ h₄ => ?_
  -- The memory the step changed: block `k`, the chaining and spare blocks, the stack.
  obtain sp₂ : s₂.sp = s₀.sp := by rw [a.sp, h.sp]
  obtain fstep : Frame (blkRegions c (c.ds M) (Dk s₀ c M k) (Sc c s₀) ++ [csR c s₀, belowR S s₀]) s.mem s₄.mem := by
    refine ((a.frame.mono fun r hr => List.mem_append_left _ hr).trans (cp.frame.sub fun r hr => ?_)).trans
      (h₄.frame.mono fun r hr => List.mem_append_left _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hL.bt_addr]
      obtain ⟨r', hr', hs'⟩ := Lay.sub (c := c) (ds := c.ds M) (Dp := Dk s₀ c M k) (S := Sc c s₀) M.tgt
      exact ⟨r', List.mem_append_left _ hr', hM.tgt_sz ▸ hs'⟩
    · exact ⟨csR c s₀, by simp, fun _ h => h⟩
    · exact ⟨belowR S s₀, by simp, by rw [sp₂]; exact fun _ h => h⟩
  obtain r6' : s₄.gpr .r6 = Dk s₀ c M k := by rw [h₄.regs _ (by decide) (by decide), r6]
  obtain r7 : s₄.gpr .r7 = BitVec.ofNat 32 (N c s₀ - k) := by
    rw [h₄.regs _ (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), h.r7]
  simp only [Core.advance]
  refine wp_add (op2_imm (S.ds_enc M)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, fun hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.gpr, r6', Dk, VG.Offset.add_add, Nat.mul_succ]
  · rw [u₆.gpr, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide), r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), h₄.regs _ (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide), h.r11 hr]
  · rw [u₆.sp, u₅.sp, h₄.sp, cp.sp, a.sp, h.sp]
  · rw [u₆.rd, u₅.rd, h₄.rd, cp.rd, a.rd, h.rd]
  · rw [u₆.wr, u₅.wr, h₄.wr, wr₃]
  · rw [u₆.mem, u₅.mem]
    exact h.frame.trans (fstep.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hp.step_sub hk r hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, hp.cs_sub_blk⟩
        · exact ⟨_, by simp, fun _ h => h⟩)
  · rw [u₆.mem, u₅.mem]
    obtain hl : (rK S s₀ M k).1.length = k := by rw [runSeq_length, List.length_take, length_blocksOf]; omega_arith
    rw [blocksOf_set (k := k) fun j hj hjk => ?_, h.data, set_prefix _ _ _ hl (by rw [length_blocksOf]; exact hk)]
    simp only [rK]
    rw [take_succ_xs hk, runSeq_snoc]
    · congr 2
      rw [← hp.dk_addr hk]
      exact congrArg (fun z => [z]) (h₄.blks .d)
    · refine VG.Proof.Modes.bytesAt_frame fstep (fun r hr => ?_) (by have := S.ds_le M; omega_arith)
      obtain hsub : Region.Sub ⟨State.addr (Dp c s₀) + BitVec.ofNat 64 (c.ds M * j), c.ds M⟩ (dataR c s₀ M) :=
        VG.Offset.sub_base _ (by have := idx_lt' (L := c.ds M) hj; omega_arith)
      simp only [blkRegions, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hp.dk_addr hk]
        have := hp.fD; have := idx_lt' (L := c.ds M) hj; have := idx_lt' (L := c.ds M) hk
        rcases Nat.lt_or_gt_of_ne hjk with hlt | hlt
        · exact VG.Offset.disjoint _ (.inl (by have := VG.Proof.Modes.idx_lt (L := c.ds M) hlt; omega_arith))
            (by omega_arith) (by omega_arith)
        · exact VG.Offset.disjoint _ (.inr (by have := VG.Proof.Modes.idx_lt (L := c.ds M) hlt; omega_arith))
            (by omega_arith) (by omega_arith)
      · exact (hp.data_scr.sub_left hsub).sub_right UPre.blk2_sub
      · exact (hp.data_scr.sub_left hsub).sub_right hp.cs_sub_scr
      · exact hp.b_data.symm.sub_left hsub
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .o
  · simp only [rK]; rw [u₆.mem, u₅.mem, take_succ_xs hk, runSeq_snoc]; exact h₄.blks .t
  · rw [z₆, u₅.other _ (by decide), r7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_arith)]
    exact ofNat_beq_zero (by have := N_lt c s₀; omega_arith)

end

end VG.Proof.Modes.Arm
