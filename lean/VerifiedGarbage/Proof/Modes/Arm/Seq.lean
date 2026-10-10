import VerifiedGarbage.Proof.Modes.Arm.Core

/-!
# The modes one block at a time on ARMv7: the contract, the invariant, the prologue

`seqArm c S M`: the contract `Core.seq c M` meets, for any core `c` (with
`S : CoreSpec c`) and mode `M`, on
`(schedule = r0, iv = r1, data = r2, n = r3, scratch = [sp])`: the `n`
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

/-- The blocks after a step stay blocks. -/
theorem stepOf_length {M : Mode} {ciph : Spec.Cbc.Cipher} {L : Nat} (hc : ∀ b, b.length = L → (ciph b).length = L)
    {b : Blks} (hl : ∀ x, (b.get x).length = L) : ∀ x, ((stepOf M ciph b).get x).length = L := by
  have h₁ := runOps_length (ops := M.pre) hl
  refine runOps_length fun x => ?_
  by_cases hx : x = M.tgt
  · subst hx; rw [Blks.get_set_self]; exact hc _ (h₁ _)
  · rw [Blks.get_set_of_ne _ _ hx]; exact h₁ x

theorem runSeq_blks_length {M : Mode} {ciph : Spec.Cbc.Cipher} {L : Nat}
    (hc : ∀ b, b.length = L → (ciph b).length = L) :
    ∀ {b : Blks} {xs : List (List Byte)}, (∀ x, (b.get x).length = L) → (∀ x ∈ xs, x.length = L) →
      ∀ y, ((runSeq M ciph b xs).2.get y).length = L
  | _, [], hb, _ => hb
  | b, x :: xs, hb, hx => by
    refine runSeq_blks_length (b := stepOf M ciph (b.set .d x)) (xs := xs) hc (stepOf_length hc fun y => ?_)
      (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    by_cases hy : y = .d
    · subst hy; rw [Blks.get_set_self]; exact hx x List.mem_cons_self
    · rw [Blks.get_set_of_ne _ _ hy]; exact hb y

section
variable (c : Core) (S : CoreSpec c)

/-- `Core.seq c M`
`(schedule = r0, iv = r1, data = r2, n = r3, scratch = [sp])`. -/
def seqArm (M : Mode) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), S.keyLen⟩
    let iv : Region := ⟨State.addr (s.gpr .r1), c.bs⟩
    let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * c.bs⟩
    let scr : Region := ⟨State.addr (stackArg s 0), c.scratchBytes⟩
    let arg : Region := ⟨stackArgAddr s 0, 4⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩
    S.stack ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      key ∈ s.rd ++ s.wr ∧ iv ∈ s.rd ++ s.wr ∧ arg ∈ s.rd ++ s.wr ∧ data ∈ s.wr ∧ scr ∈ s.wr ∧
      key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ data.Disjoint scr ∧
      below.Disjoint key ∧ below.Disjoint data ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + S.keyLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + c.bs ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + (s.gpr .r3).toNat * c.bs ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + c.scratchBytes ≤ 2 ^ 32 ∧
      (M.finish = true → iv ∈ s.wr) ∧ (∀ r ∈ s.wr, arg.Disjoint r)
  post s s' :=
    let r := runSeq M (S.ciphAt s.mem (State.addr (s.gpr .r0)))
      ⟨[], bytesAt s.mem (State.addr (s.gpr .r1)) c.bs,
        bytesAt s.mem (State.addr (stackArg s 0) + BitVec.ofNat 64 (oOff + c.bs)) c.bs⟩
      (blocksOf c.bs s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    blocksOf c.bs s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = r.1 ∧
      (M.finish = true → bytesAt s'.mem (State.addr (s.gpr .r1)) c.bs = r.2.o)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end

section
variable (c : Core) {c' : Core} (S : CoreSpec c') (s₀ : State)

abbrev Kp : BitVec 32 := s₀.gpr .r0
abbrev Ivp : BitVec 32 := s₀.gpr .r1
abbrev Dp : BitVec 32 := s₀.gpr .r2
abbrev N : Nat := (s₀.gpr .r3).toNat
abbrev Sc : BitVec 32 := stackArg s₀ 0

abbrev keyR : Region := ⟨State.addr (Kp s₀), S.keyLen⟩
abbrev ivR : Region := ⟨State.addr (Ivp s₀), c.bs⟩
abbrev dataR : Region := ⟨State.addr (Dp s₀), N s₀ * c.bs⟩
abbrev scrR : Region := ⟨State.addr (Sc s₀), c.scratchBytes⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 S.stack, S.stack⟩
/-- The chaining and spare blocks. -/
abbrev blkR : Region := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 oOff, 2 * c.bs⟩
abbrev oA : Addr := State.addr (Sc s₀) + BitVec.ofNat 64 oOff
abbrev tA : Addr := State.addr (Sc s₀) + BitVec.ofNat 64 (oOff + c.bs)

/-- The cipher, as on entry. -/
abbrev ciph : Spec.Cbc.Cipher := S.ciphAt s₀.mem (State.addr (Kp s₀))
/-- The blocks on entry. -/
abbrev xs : List (List Byte) := blocksOf c.bs s₀.mem (State.addr (Dp s₀)) (N s₀)
/-- The blocks the mode starts from. -/
abbrev b0 : Blks := ⟨[], bytesAt s₀.mem (State.addr (Ivp s₀)) c.bs, bytesAt s₀.mem (tA c s₀) c.bs⟩
/-- The mode after the first `k` blocks. -/
abbrev rK (M : Mode) (k : Nat) : List (List Byte) × Blks := runSeq M (ciph S s₀) (b0 c' s₀) ((xs c' s₀).take k)

/-- The memory once the registers are saved. -/
def savedMem : Mem := Spill.saveMem s₀.mem (State.addr (Sc s₀)) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) : Prop where
  stk : S.stack ≤ s₀.sp.toNat
  spF : s₀.sp.toNat + 4 ≤ 2 ^ 32
  key_in : keyR S s₀ ∈ s₀.rd ++ s₀.wr
  iv_in : ivR c s₀ ∈ s₀.rd ++ s₀.wr
  arg_in : argR s₀ ∈ s₀.rd ++ s₀.wr
  data_in : dataR c s₀ ∈ s₀.wr
  scr_in : scrR c s₀ ∈ s₀.wr
  key_data : (keyR S s₀).Disjoint (dataR c s₀)
  key_scr : (keyR S s₀).Disjoint (scrR c s₀)
  iv_data : (ivR c s₀).Disjoint (dataR c s₀)
  iv_scr : (ivR c s₀).Disjoint (scrR c s₀)
  data_scr : (dataR c s₀).Disjoint (scrR c s₀)
  b_key : (belowR S s₀).Disjoint (keyR S s₀)
  b_data : (belowR S s₀).Disjoint (dataR c s₀)
  b_scr : (belowR S s₀).Disjoint (scrR c s₀)
  fK : (Kp s₀).toNat + S.keyLen ≤ 2 ^ 32
  fIv : (Ivp s₀).toNat + c.bs ≤ 2 ^ 32
  fD : (Dp s₀).toNat + N s₀ * c.bs ≤ 2 ^ 32
  fS : (Sc s₀).toNat + c.scratchBytes ≤ 2 ^ 32
  fin : M.finish = true → ivR c s₀ ∈ s₀.wr
  arg_wr : ∀ r ∈ s₀.wr, (argR s₀).Disjoint r

theorem UPre.of {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (h : (seqArm c S M).pre s₀) :
    UPre c S M s₀ :=
  let ⟨a, b, d, e, f, g, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩ := h
  ⟨a, b, d, e, f, g, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (c : Core) (S : CoreSpec c) (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Kp s₀
  r5 : s.gpr .r5 = Ivp s₀
  r6 : s.gpr .r6 = Dp s₀ + BitVec.ofNat 32 (c.bs * k)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (N s₀ - k)
  r8 : s.gpr .r8 = Sc s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR c s₀, blkR c s₀, belowR S s₀] (savedMem s₀) s.mem
  data : blocksOf c.bs s.mem (State.addr (Dp s₀)) (N s₀) = (rK S s₀ M k).1 ++ (xs c s₀).drop k
  o : bytesAt s.mem (oA s₀) c.bs = (rK S s₀ M k).2.o
  t : bytesAt s.mem (tA c s₀) c.bs = (rK S s₀ M k).2.t

/-! ## Facts of the layout -/

theorem CoreSpec.bs_pos {c : Core} (S : CoreSpec c) : 0 < c.bs := by have := S.bw_pos; unfold Core.bs; omega

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
theorem UPre.scrB : c.scratchBytes = oOff + 2 * c.bs := rfl

omit hp in
theorem UPre.blk_sub : Region.Sub (blkR c s₀) (scrR c s₀) := VG.Offset.sub_base _ (by unfold Core.scratchBytes; omega)

theorem UPre.slots_disj_blk : Region.Disjoint ⟨State.addr (Sc s₀) + BitVec.ofNat 64 0, 36⟩ (blkR c s₀) :=
  VG.Offset.disjoint _ (.inl (by unfold oOff; omega)) (by omega) (by have := hp.fS; unfold Core.scratchBytes at this; omega)

omit hp in
theorem UPre.slots_sub : Region.Sub ⟨State.addr (Sc s₀) + BitVec.ofNat 64 0, 36⟩ (scrR c s₀) :=
  VG.Offset.sub_base _ (by unfold Core.scratchBytes oOff; omega)

omit hp in
/-- Saving the registers changes only the slots. -/
theorem UPre.savedMem_frame : Frame [⟨State.addr (Sc s₀) + BitVec.ofNat 64 0, 36⟩] s₀.mem (savedMem s₀) :=
  Spill.saveMem_frame_slots saved_slots _ _ _

/-- What a frame within the scratch buffer, the data and the stack leaves of
the schedule. -/
theorem UPre.ciph_eq {m : Mem}
    (hf : Frame [dataR c s₀, scrR c s₀, belowR S s₀] s₀.mem m) :
    S.ciphAt m (State.addr (Kp s₀)) = ciph S s₀ := by
  refine (S.ciphAt_congr fun i hi => ?_).symm
  refine (hf.bytes (R := keyR S s₀) (fun r hr => ?_) (by show S.keyLen ≤ 2 ^ 64; have := hp.fK; omega) hi).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.key_data
  · exact hp.key_scr
  · exact hp.b_key.symm

end

/-! ## The prologue -/

theorem stackArgAddr0 (s : State) : State.addr (s.sp + BitVec.ofNat 32 0) = stackArgAddr s 0 := rfl

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- What the saves and the copy of the IV leave in memory. -/
theorem prologue_mem {c : Core} {S : CoreSpec c} {M : Mode} {s₀ : State} (hp : UPre c S M s₀) :
    let m := over (savedMem s₀) (oA s₀) (4 * c.bw) fun i =>
      savedMem s₀ (State.addr (Ivp s₀) + BitVec.ofNat 64 0 + BitVec.ofNat 64 i)
    Frame [dataR c s₀, blkR c s₀, belowR S s₀] (savedMem s₀) m ∧
      blocksOf c.bs m (State.addr (Dp s₀)) (N s₀) = xs c s₀ ∧
      bytesAt m (oA s₀) c.bs = bytesAt s₀.mem (State.addr (Ivp s₀)) c.bs ∧
      bytesAt m (tA c s₀) c.bs = bytesAt s₀.mem (tA c s₀) c.bs := by
  intro m
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have fs := UPre.savedMem_frame (s₀ := s₀)
  -- The slots are apart from all but the scratch buffer's own bytes.
  have slotsDisj : ∀ {R : Region}, R.Disjoint (scrR c s₀) →
      ∀ r ∈ [(⟨State.addr (Sc s₀) + BitVec.ofNat 64 0, 36⟩ : Region)], R.Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (UPre.slots_sub (c := c) (s₀ := s₀))
  have oSub : Region.Sub ⟨oA s₀, 4 * c.bw⟩ (blkR c s₀) := Region.sub_prefix (by omega)
  refine ⟨(over_frame _ _ _ _).sub fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨blkR c s₀, by simp, oSub⟩
  · -- The data: apart from the slots and the chaining block.
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hsub : Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (c.bs * j), c.bs⟩ (dataR c s₀) :=
      VG.Offset.sub_base _ (by have := VG.Proof.Modes.idx_lt (L := c.bs) hj; rw [Nat.mul_comm (N s₀)]; omega)
    rw [bytesAt_over_other _ _ ((hp.data_scr.sub_left hsub).sub_right (fun a h => UPre.blk_sub a (oSub a h))).symm
      (by have := hp.fD; omega)]
    exact VG.Proof.Modes.bytesAt_frame fs (slotsDisj (hp.data_scr.sub_left hsub)) (by have := hp.fD; omega)
  · have e := VG.Proof.Modes.bytesAt_frame fs (slotsDisj hp.iv_scr) (by show c.bs ≤ 2 ^ 64; omega)
    rw [hbs] at e ⊢
    rw [bytesAt_over_self _ _ _ (by omega), ← e]
    simp only [bytesAt, add0]
  · rw [bytesAt_over_other _ _ (VG.Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by omega)]
    exact VG.Proof.Modes.bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint _ (.inr (by unfold oOff; omega)) (by omega) (by omega))) (by omega)

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

theorem UPre.npreIv {s : State} (h8 : s.gpr .r8 = Sc s₀) (h5 : s.gpr .r5 = Ivp s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    NPre c.bw s .r8 .r5 oOff 0 (oA s₀) (State.addr (Ivp s₀) + BitVec.ofNat 64 0) := by
  have hS := hp.fS
  have hI := hp.fIv
  have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have hb := S.bw_le
  have ho : oOff = 40 := rfl
  refine ⟨by rw [h8], by rw [h5], by rw [h8]; omega, by rw [h5]; omega, by omega, by omega, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [hwr]; exact cov_off (R := scrR c s₀) hp.scr_in (by show oOff + 4 * c.bw ≤ c.scratchBytes; omega)
  · rw [hrd, hwr]; exact cov_off (R := ivR c s₀) hp.iv_in (by show 0 + 4 * c.bw ≤ c.bs; omega)
  · refine (hp.iv_scr.symm.sub_left (VG.Offset.sub_base _ (by omega))).sub_right ?_
    rw [add0]; exact Region.sub_prefix (by omega)

theorem prologue_wp :
    WP isa (.block (save ++ c.setup)) s₀ fun s => LInv c S M s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hS := hp.fS
  have hsc : c.scratchBytes = oOff + 2 * c.bs := rfl
  have hbs : c.bs = 4 * c.bw := rfl
  have ho : oOff = 40 := rfl
  rw [show save ++ c.setup = .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ c.setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ⟨argR s₀, hp.arg_in, Region.contains_self _ _⟩
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = Sc s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, ⟨scrR c s₀, hp.scr_in, VG.Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (by revert p; decide)
  simp only [Core.setup, mov, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  have r4 : s₇.gpr .r4 = Kp s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  have r5 : s₇.gpr .r5 = Ivp s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  have r6 : s₇.gpr .r6 = Dp s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  have r7 : s₇.gpr .r7 = s₀.gpr .r3 := by
    simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
  have r8 : s₇.gpr .r8 = Sc s₀ := by
    simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have m₇ : s₇.mem = savedMem s₀ := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  rw [WP.block_append_iff]
  refine WP.mono (copyN_wp (hp.npreIv r8 r5 rd₇ wr₇)) fun s₈ hi => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .r9 → r ≠ .r10 → s₉.gpr r = s₇.gpr r := fun r a b => by rw [f₉.gpr, hi.regs r a b]
  obtain ⟨fr, dt, oo, tt⟩ := prologue_mem hp
  have m₉ : s₉.mem = over (savedMem s₀) (oA s₀) (4 * c.bw) fun i =>
      savedMem s₀ (State.addr (Ivp s₀) + BitVec.ofNat 64 0 + BitVec.ofNat 64 i) := by
    rw [f₉.mem, hi.mem, m₇]
  have a0 : s₀.gpr .r3 = BitVec.ofNat 32 (N s₀) := by simp [N]
  refine ⟨⟨by rw [g _ (by decide) (by decide), r4], by rw [g _ (by decide) (by decide), r5],
    by rw [g _ (by decide) (by decide), r6, Nat.mul_zero, BitVec.add_zero],
    by rw [g _ (by decide) (by decide), r7, a0, Nat.sub_zero], by rw [g _ (by decide) (by decide), r8],
    by rw [f₉.sp, hi.sp, sp₇], by rw [f₉.rd, hi.rd, rd₇], by rw [f₉.wr, hi.wr, wr₇], by rw [m₉]; exact fr,
    by rw [m₉, dt]; simp [rK, runSeq], by rw [m₉, oo]; simp [rK, runSeq], by rw [m₉, tt]; simp [rK, runSeq]⟩, ?_⟩
  rw [z₉, show s₈.gpr .r7 = s₇.gpr .r7 from hi.regs _ (by decide) (by decide), r7, a0]
  exact cmp0 (by have := (s₀.gpr .r3).isLt; simpa [N] using this)

end

end VG.Proof.Modes.Arm
