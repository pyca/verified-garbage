module

public import VerifiedGarbage.Proof.Sha3.Arm.Permute
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Sha3.Stream
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Arm.Permute
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sha3.Arm.Stream.Squeeze`, which the modules that import this one used -/

section

/-!
# The SHA-3 sponge on ARMv7: `squeeze`

The same structure as the AArch64 proof
(`VG.Proof.Sha3.AArch64.Stream.Squeeze`), with the prologue and epilogue of
`absorb` (`VG.Proof.Sha3.Arm.Stream.Absorb`). An iteration of the loop
copies one byte (`store_ok`) or the whole words left of the output and of
the block (`words_ok`, `word_step`), after permuting the state if the block
has been used up (`refill_ok`): once, or, with more than a block of output
left, for each of its whole blocks and once more (`sbulk_ok`), on the state
interleaved in the scratch space (`enter_call`), which the rounds permute
(`rounds_call`) and whose lanes are copied to the output (`copy_step`, by
evaluation: `copySeg_ok`), before it is brought back (`leave_call`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Stream.Squeeze

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (saveA_ok restoreA_ok saveMemA_frame SSaved ssaved_ok saveMemA_ssaved
  restore_eq call_ok covers_of preserved_cases ofNat32_succ sub_ofNat32 ofNat32_beq_zero sub_beq_zero32
  beq_zero32 ofNat_toNat32 sub_imm0 arg_in argByte_eq addr_toNat words_ok shl2_ofNat32 writeW32_apply
  regR Stored RCs Masks segs segs_ok segs_rate segs_imm copySeg_ok cfgC ok_offs lane_words Hi storeVars
  storeVars_keep storeVars_frame saveL bulkSave_eq saveL_ok saveMemA_hi savedHi_regs bulkLoad_ok
  bulkStore_ok bulkRestore_ok wp_geq geq_beq ladder_ok enter_call rounds_call leave_call rd64_add rd64_eq)
open VG.Proof.Sha512.Arm (A A_eq contains_A rd64)
open VG.Arm.Straight (Ok)
open VG.Impl.Sha3.Arm (enterCall roundsCall leaveCall copySeg)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_sub wp_subs wp_cmp
  wp_ldr wp_str wp_ldrb wp_strb wp_ldrSp eval_eq eval_ne add_ofNat)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF stateAt_congr writeW8_self writeW8_other div_mod_eq contains_offset sub_offset)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev rt : Nat := (s₀.gpr .r1).toNat
abbrev pos₀ : Nat := (s₀.gpr .r2).toNat
abbrev op : BitVec 32 := s₀.gpr .r3
abbrev outn : Nat := (stackArg s₀ 0).toNat
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev oA : Addr := State.addr (op s₀)
abbrev SR : Region := ⟨stA s₀, 200⟩
abbrev OR : Region := ⟨oA s₀, outn s₀⟩
abbrev CR : Region := ⟨State.addr (scr s₀), 640⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stA s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  a_st : (argR s₀).Disjoint (SR s₀)
  a_o : (argR s₀).Disjoint (OR s₀)
  a_c : (argR s₀).Disjoint (CR s₀)
  st_fit : (s₀.gpr .r0).toNat + 200 ≤ 2 ^ 32
  o_fit : (s₀.gpr .r3).toNat + outn s₀ ≤ 2 ^ 32
  c_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem Pre.rate_pos {s₀ : State} (hp : Pre s₀) :
    0 < rt s₀ ∧ rt s₀ ≤ 200 ∧ 72 ≤ (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 168 := by
  obtain h : 72 ≤ (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  show 0 < (s₀.gpr .r1).toNat ∧ (s₀.gpr .r1).toNat ≤ 200 ∧ _
  omega_arith

theorem Pre.arg {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], arg_in (n := 2) hp.sp_fit hk⟩

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rt s₀ * k + pos
  pos_le : pos ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r4 : s.gpr .r4 = s₀.gpr .r1
  r5 : s.gpr .r5 = BitVec.ofNat 32 pos
  r6 : s.gpr .r6 = op s₀ + BitVec.ofNat 32 i
  r7 : s.gpr .r7 = BitVec.ofNat 32 (outn s₀ - i)
  hi8 : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s.gpr r = s₀.gpr r
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : SSaved (scr s₀) s₀.gpr s.mem
  state : stateAt s.mem (stA s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

theorem Inv.of_flags {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (u : Fupd s s') : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  sp := u.sp.trans h.sp
  r0 := by rw [u.gpr]; exact h.r0
  r1 := by rw [u.gpr]; exact h.r1
  r4 := by rw [u.gpr]; exact h.r4
  r5 := by rw [u.gpr]; exact h.r5
  r6 := by rw [u.gpr]; exact h.r6
  r7 := by rw [u.gpr]; exact h.r7
  hi8 := fun r hr => by rw [u.gpr]; exact h.hi8 r hr
  frame := by rw [u.mem]; exact h.frame
  saved := by rw [u.mem]; exact h.saved
  state := by rw [u.mem]; exact h.state
  out := by rw [u.mem]; exact h.out

/-! ## The prologue -/

theorem setup_eq : setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([.mov .r4 (.reg .r1), .mov .r1 (.reg .r12), .mov .r5 (.reg .r2), .mov .r6 (.reg .r3),
      .ldrSp .r7 0, .cmp .r7 (.imm 0)] : List Instr)) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.z = decide (outn s₀ = 0) := by
  have fC := hp.c_fit
  rw [setup_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg (by omega_arith)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine saveA_ok saved s₁ _ (fun p hp' => ⟨(ssaved_ok p hp').2.2.1, ?_⟩)
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · rw [u₁.wr, h12, hp.wr]
    exact ⟨CR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  obtain hm : s₆.mem = saveMemA s₀.mem (scr s₀) s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, h12]
  obtain hf : Frame [regR (scr s₀) 640] s₀.mem s₆.mem := by
    rw [hm]; exact saveMemA_frame fC _ _ _ fun p hp' => by have := ssaved_ok p hp'; omega
  obtain ha : s₆.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 :=
    hf.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.a_c.sub_left (Region.sub_prefix (by omega_arith))) (by decide)
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ u₈ hz => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r12 → r ≠ .r4 → r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₈.gpr r = s₀.gpr r :=
    fun r h12 h4 h1 h5 h6 h7 => by
      rw [u₈.gpr, u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h1, u₃.other r h4, g₂,
        u₁.other r h12]
  obtain h7 : s₈.gpr .r7 = stackArg s₀ 0 := by rw [u₈.gpr, u₇.gpr, ha]
  obtain hsf : stateAt s₈.mem (stA s₀) = S₀ s₀ := by
    rw [u₈.mem, u₇.mem]
    exact stateAt_congr fun i hi =>
      hf.bytes (R := SR s₀) (by simpa using hp.st_c.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp) hi
  refine ⟨{
    i_le := Nat.zero_le _, hi := (by omega_arith), pos_le := hp.pos_le, rd := ?_, wr := ?_, sp := ?_,
    r0 := g .r0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    r1 := ?_, r4 := ?_, r5 := ?_, r6 := ?_,
    r7 := (by rw [h7, Nat.sub_zero]; exact (ofNat_toNat32 _).symm), hi8 := fun r hr => ?_,
    frame := ?_, saved := ?_, state := hsf, out := fun j hj => absurd hj (Nat.not_lt_zero _) }, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    exact (ofNat_toNat32 _).symm
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    rw [BitVec.add_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [u₈.mem, u₇.mem]; exact hf.mono (by simp)
  · rw [u₈.mem, u₇.mem, hm]
    exact (saveMemA_ssaved _ fC _).of_gpr fun r hr => u₁.other r hr
  · rw [hz, u₇.gpr, ha]; simp only [sub_imm0]; rw [beq_zero32]

/-! ## One iteration -/

theorem hi_ok : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ preserved ∧ r ≠ .lr ∧ r ≠ .r5 := by decide

/-- A permutation, at the end of a block. -/
theorem permute_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s) :
    WP isa (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) s (Inv s₀ i (k + 1) 0) := by
  obtain hn := outn_lt s₀
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  refine call_ok (st := st s₀) (scr := scr s₀) (by rw [u₂.other _ (by decide), hI.r0])
    (by rw [u₂.other _ (by decide), hI.r1]) hp.st_fit (by have := hp.c_fit; omega_arith)
    (hp.st_c.sub_right (Region.sub_prefix (by omega_arith)))
    (by rw [u₂.wr, hI.wr, hp.wr]; exact covers_of (N := 640) (by omega_arith) (by simp) (by simp))
    fun s₃ rd₃ wr₃ sp₃ cs₃ r0₃ r1₃ f₃ e₃ => ?_
  obtain hd : ∀ r ∈ [regR (st s₀) 200, regR (scr s₀) 512], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right (Region.sub_prefix (by omega_arith))
  refine {
    i_le := hI.i_le, hi := (by rw [hI.hi, Nat.mul_succ]; rfl), pos_le := Nat.zero_le _,
    rd := rd₃.trans (u₂.rd.trans hI.rd), wr := wr₃.trans (u₂.wr.trans hI.wr),
    sp := sp₃.trans (u₂.sp.trans hI.sp), r0 := r0₃, r1 := r1₃, r4 := ?_, r5 := ?_, r6 := ?_, r7 := ?_,
    hi8 := fun r hr => ?_, frame := ?_, saved := ?_, state := ?_, out := fun j hj => ?_ }
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r4]
  · rw [cs₃ _ (by decide) (by decide), u₂.gpr]; rfl
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r6]
  · rw [cs₃ _ (by decide) (by decide), u₂.other _ (by decide), hI.r7]
  · rw [cs₃ r (hi_ok r hr).1 (hi_ok r hr).2.1, u₂.other r (hi_ok r hr).2.2]; exact hI.hi8 r hr
  · refine hI.frame.trans ?_
    rw [← u₂.mem]
    refine f₃.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, fun _ h => h⟩
    · exact ⟨CR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
  · exact SSaved.frame hp.c_fit hp.st_c (by rw [u₂.mem]; exact hI.saved) f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact hr
  · rw [e₃, u₂.mem, hI.state, iterF_succ]
  · refine Eq.trans (f₃.bytes (R := OR s₀) hd (by simp; omega_arith)
      (by have := hI.i_le; omega_arith : j < outn s₀)) ?_
    rw [u₂.mem]; exact hI.out j hj

theorem store_regs : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ [Reg.r3, .r2, .r6, .r5, .r7] := by decide

/-- Copying one byte of the state to the output. -/
theorem store_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rt s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  have fS : (st s₀).toNat + 200 ≤ 2 ^ 32 := hp.st_fit
  have fO : (op s₀).toNat + outn s₀ ≤ 2 ^ 32 := hp.o_fit
  have fC := hp.c_fit
  obtain hpos : pos < 200 := by omega_arith
  unfold squeezeByte
  refine wp_add (op2_reg _ _) fun s₁ u₁ => ?_
  obtain ea : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 pos := by
    rw [u₁.gpr, hI.r0, hI.r5, BitVec.add_zero]
    exact addr_add (by omega_arith)
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 pos) (by decide) ea
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₂ u₂ => ?_
  refine wp_strb (a := oA s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other .r6 (by decide), u₁.other .r6 (by decide), hI.r6, BitVec.add_zero]
        exact addr_add (by omega_arith))
    ⟨OR s₀, by simp [u₂.wr, u₁.wr, hI.wr, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₃ g₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_sub (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ∉ [Reg.r3, .r2, .r6, .r5, .r7] → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h2, h6, h5, h7⟩ := hr
    rw [u₆.other r h7, u₅.other r h5, u₄.other r h6, g₃.gpr, u₂.other r h2, u₁.other r h3]
  obtain hb : s.mem (stA s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega_arith)]
  obtain hm : s₆.mem = s.mem.writeW (oA s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega_arith), BitVec.setWidth_eq, hb]
  obtain hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain h7 : s₅.gpr .r7 = BitVec.ofNat 32 (outn s₀ - i) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r7]
  obtain e1 : BitVec.ofNat 32 (outn s₀ - i) - 1 = BitVec.ofNat 32 (outn s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat32 (by omega_arith), Nat.sub_sub]
  refine {
    i_le := (by omega_arith), hi := (by have := hI.hi; omega_arith), pos_le := (by omega_arith), rd := ?_, wr := ?_,
    sp := ?_, r0 := (by rw [g .r0 (by decide), hI.r0]), r1 := (by rw [g .r1 (by decide), hI.r1]),
    r4 := (by rw [g .r4 (by decide), hI.r4]), r5 := ?_, r6 := ?_, r7 := (by rw [u₆.gpr, h7, e1]),
    hi8 := fun r hr => (by rw [g r (store_regs r hr)]; exact hI.hi8 r hr),
    frame := hI.frame.trans (hfw.mono (by simp)), saved := ?_, state := ?_, out := fun j hj => ?_ }
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r5, ofNat32_succ]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r6, BitVec.add_assoc, ofNat32_succ]
  · refine hI.saved.keep fun d hd₁ hd₂ => hfw.readW (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    rw [List.mem_singleton.mp hr]
    refine hp.o_c.symm.sub_left ?_
    rw [A_eq (by omega_arith)]; exact sub_offset (by omega_arith) (by omega_arith)
  · rw [stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) e)]
      exact hI.out j (by omega_arith)

/-! ## Whole words -/

/-- In the words of an iteration that began with `i` bytes of output written,
in block `k` at the position `pos`: after `w` of its `nw` words. The bytes
left and the position are already those after the words. -/
structure WInv (s₀ : State) (i k pos nw w : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r3 : s.gpr .r3 = st s₀ + BitVec.ofNat 32 (pos + 4 * w)
  r4 : s.gpr .r4 = s₀.gpr .r1
  r5 : s.gpr .r5 = BitVec.ofNat 32 (pos + 4 * nw)
  r6 : s.gpr .r6 = op s₀ + BitVec.ofNat 32 (i + 4 * w)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (outn s₀ - (i + 4 * nw))
  lr : s.gpr .lr = BitVec.ofNat 32 (nw - w)
  hi8 : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s.gpr r = s₀.gpr r
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : SSaved (scr s₀) s₀.gpr s.mem
  state : stateAt s.mem (stA s₀) = iterF k (S₀ s₀)
  out : ∀ j < i + 4 * w, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

/-- Before the words. -/
theorem wordsPre_ok {s₀ : State} {i k pos nw : Nat} (h4 : i + 4 * nw ≤ outn s₀) {s : State}
    (hI : Inv s₀ i k pos s) (hlr : s.gpr .lr = BitVec.ofNat 32 nw) :
    WP isa (.block wordsPre) s (WInv s₀ i k pos nw 0) := by
  unfold wordsPre
  refine wp_sub (op2_lsl (by decide)) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_add (op2_lsl (by decide)) fun s₃ u₃ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r7 → r ≠ .r3 → r ≠ .r5 → s₃.gpr r = s.gpr r := fun r a b c => by
    rw [u₃.other r c, u₂.other r b, u₁.other r a]
  obtain gm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp, hI.sp], by rw [g _ (by decide) (by decide) (by decide), hI.r0],
    by rw [g _ (by decide) (by decide) (by decide), hI.r1], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hI.r4], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hI.r6, Nat.mul_zero, Nat.add_zero], ?_,
    by rw [g _ (by decide) (by decide) (by decide), hlr, Nat.sub_zero], fun r hr => ?_,
    by rw [gm]; exact hI.frame, by rw [gm]; exact hI.saved, by rw [gm]; exact hI.state,
    fun j hj => by rw [gm]; exact hI.out j (by omega_arith)⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r0, hI.r5,
      Nat.mul_zero, Nat.add_zero]
  · rw [u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide), hI.r5, hlr, shl2_ofNat32, ← BitVec.ofNat_add]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r7, hlr, shl2_ofNat32,
      sub_ofNat32 (by omega_arith), Nat.sub_sub]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [g _ (by decide) (by decide) (by decide)]; exact hI.hi8 _ (by simp))

theorem word_regs : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ≠ .r2 ∧ r ≠ .r6 ∧ r ≠ .r3 ∧ r ≠ .lr := by
  decide

/-- One word: the four bytes of the state at position `pos + 4 w` copied to
the output. -/
theorem word_step {s₀ : State} (hp : Pre s₀) {i k pos nw w : Nat} (hw : w < nw)
    (h4 : i + 4 * nw ≤ outn s₀) (hp4 : pos + 4 * nw ≤ rt s₀) (hik : pos₀ s₀ + i = rt s₀ * k + pos)
    {s : State} (hW : WInv s₀ i k pos nw w s) :
    WP isa (.block squeezeWord) s fun s' =>
      WInv s₀ i k pos nw (w + 1) s' ∧ s'.z = decide (nw - (w + 1) = 0) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  have fS : (st s₀).toNat + 200 ≤ 2 ^ 32 := hp.st_fit
  have fO : (op s₀).toNat + outn s₀ ≤ 2 ^ 32 := hp.o_fit
  have fC := hp.c_fit
  obtain co : (OR s₀).Contains (oA s₀ + BitVec.ofNat 64 (i + 4 * w)) 4 :=
    contains_offset (by omega_arith) (by omega_arith)
  obtain cs : (SR s₀).Contains (stA s₀ + BitVec.ofNat 64 (pos + 4 * w)) 4 :=
    contains_offset (by omega_arith) (by omega_arith)
  unfold squeezeWord
  refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (pos + 4 * w)) (by decide)
    (by rw [hW.r3, BitVec.add_zero]; exact addr_add (by omega_arith))
    ⟨SR s₀, by simp [hW.rd, hW.wr, hp.rd, hp.wr], cs⟩ fun s₁ u₁ => ?_
  refine wp_str (a := oA s₀ + BitVec.ofNat 64 (i + 4 * w)) (by decide)
    (by rw [u₁.other _ (by decide), hW.r6, BitVec.add_zero]; exact addr_add (by omega_arith))
    ⟨OR s₀, by simp [u₁.wr, hW.wr, hp.wr], co⟩ fun s₂ g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  obtain hm : s₅.mem = s.mem.writeW (oA s₀ + BitVec.ofNat 64 (i + 4 * w))
      (s.mem.readW (stA s₀ + BitVec.ofNat 64 (pos + 4 * w)) 32) := by
    rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem]
  obtain hfw : Frame [OR s₀] s.mem s₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ co
  obtain g : ∀ r, r ≠ .r2 → r ≠ .r6 → r ≠ .r3 → r ≠ .lr → s₅.gpr r = s.gpr r := fun r a b c d => by
    rw [u₅.other r d, u₄.other r c, u₃.other r b, g₂.gpr, u₁.other r a]
  obtain hlr : s₄.gpr .lr = BitVec.ofNat 32 (nw - w) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), hW.lr]
  obtain e1 : BitVec.ofNat 32 (nw - w) - 1 = BitVec.ofNat 32 (nw - (w + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat32 (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, hW.rd], by rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, hW.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, hW.sp],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hW.r0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hW.r1], ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hW.r4],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hW.r5], ?_,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hW.r7], by rw [u₅.gpr, hlr, e1],
    fun r hr => ?_, hW.frame.trans (hfw.mono (by simp)), ?_, ?_, fun j hj => ?_⟩,
    by rw [hz, hlr, e1, ofNat32_beq_zero (by omega_arith)]⟩
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), hW.r3,
      BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show pos + 4 * w + 4 = pos + 4 * (w + 1) by omega_arith]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), hW.r6,
      BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add,
      show i + 4 * w + 4 = i + 4 * (w + 1) by omega_arith]
  · obtain ⟨a, b, c, d⟩ := word_regs r hr
    rw [g r a b c d]; exact hW.hi8 r hr
  · refine hW.saved.keep fun d hd₁ hd₂ => hfw.readW (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    rw [List.mem_singleton.mp hr]
    refine hp.o_c.symm.sub_left ?_
    rw [A_eq (by omega_arith)]; exact sub_offset (by omega_arith) (by omega_arith)
  · rw [stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hW.state
  · rw [hm, writeW32_apply, Offset.sub_toNat' (oA s₀) (by omega_arith) (by omega_arith)]
    by_cases c : i + 4 * w ≤ j
    · have hd : j - (i + 4 * w) < 4 := by omega_arith
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 (show pos + 4 * w + (j - (i + 4 * w)) < rt s₀ by omega_arith)
      rw [ite_eq_left c, ite_eq_left hd, ← Mem.readW_byte _ _ hd, add_ofNat,
        ← byteOf_stateAt s.mem (stA s₀) (j := pos + 4 * w + (j - (i + 4 * w))) (by omega_arith), hW.state,
        show pos₀ s₀ + j = rt s₀ * k + (pos + 4 * w + (j - (i + 4 * w))) by omega_arith, d, m]
    · rw [ite_eq_right c, ite_eq_right (by omega_arith)]
      exact hW.out j (by omega_arith)

/-- After the words. -/
theorem WInv.toInv {s₀ : State} {i k pos nw : Nat} (h4 : i + 4 * nw ≤ outn s₀)
    (hp4 : pos + 4 * nw ≤ rt s₀) (hik : pos₀ s₀ + i = rt s₀ * k + pos) {s : State}
    (hW : WInv s₀ i k pos nw nw s) : Inv s₀ (i + 4 * nw) k (pos + 4 * nw) s :=
  ⟨h4, by omega_arith, hp4, hW.rd, hW.wr, hW.sp, hW.r0, hW.r1, hW.r4, hW.r5, hW.r6, hW.r7, hW.hi8,
    hW.frame, hW.saved, hW.state, hW.out⟩

/-! ## The whole iteration -/

theorem hi_tmp : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ [Reg.r2, .r3, .r12, .lr] := by decide

/-- The invariant does not depend on the temporaries or the flags. -/
theorem Inv.of_gpr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r, r ∉ [Reg.r2, .r3, .r12, .lr] → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := by rw [hg _ (by decide)]; exact h.r0
  r1 := by rw [hg _ (by decide)]; exact h.r1
  r4 := by rw [hg _ (by decide)]; exact h.r4
  r5 := by rw [hg _ (by decide)]; exact h.r5
  r6 := by rw [hg _ (by decide)]; exact h.r6
  r7 := by rw [hg _ (by decide)]; exact h.r7
  hi8 := fun r hr => by rw [hg r (hi_tmp r hr)]; exact h.hi8 r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

/-- The test at the end of the body. -/
theorem cmp_ok {s₀ : State} {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s) :
    WP isa (.block [.cmp .r7 (.imm 0)]) s fun s' =>
      Inv s₀ i k pos s' ∧ s'.z = decide (outn s₀ - i = 0) :=
  wp_cmp (op2_imm (by decide)) fun s' u hz => WP.block_nil ⟨hI.of_flags u, by
    rw [hz, hI.r7]; simp only [sub_imm0]; rw [ofNat32_beq_zero (by have := outn_lt s₀; omega_arith)]⟩

/-! ## Several blocks between one `enter` and one `leave` -/

theorem Pre.scr_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {d : Nat}
    (hd : d + 4 ≤ 640) : InRegions s.wr (A (scr s₀) d) 4 := by
  rw [hwr, hp.wr]; exact ⟨CR s₀, by simp, contains_A hp.c_fit hd⟩

theorem Pre.covers {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) :
    Covers [regR (st s₀) 200, regR (scr s₀) 512] s.wr := by
  rw [hwr, hp.wr]; exact covers_of (N := 640) (by omega_arith) (by simp) (by simp)

/-- The output does not overlap the state or the permutation's scratch space. -/
theorem Pre.o_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [regR (st s₀) 200, regR (scr s₀) 512], (OR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.st_o.symm
  · exact hp.o_c.sub_right (Region.sub_prefix (by omega_arith))

/-- A byte of the output is kept by writes to the state and to the scratch space. -/
theorem Pre.out_keep {s₀ : State} (hp : Pre s₀) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = regR (st s₀) 200 ∨ Region.Sub r (CR s₀)) {j : Nat} (hj : j < outn s₀) :
    m' (oA s₀ + BitVec.ofNat 64 j) = m (oA s₀ + BitVec.ofNat 64 j) :=
  hf.bytes (R := OR s₀) (fun r hr => by
    rcases hrs r hr with rfl | h
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right h) (by have := outn_lt s₀; simp; omega_using [this]) hj

/-- A word of the scratch space is kept by writes to the output. -/
theorem Pre.scr_keep {s₀ : State} (hp : Pre s₀) {m m' : Mem} {off n : Nat}
    (hf : Frame [⟨oA s₀ + BitVec.ofNat 64 off, n⟩] m m') (hon : off + n ≤ outn s₀) {d : Nat}
    (hd : d + 4 ≤ 640) : m'.readW (A (scr s₀) d) 32 = m.readW (A (scr s₀) d) 32 := by
  have fC := hp.c_fit
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  refine (hp.o_c.symm.sub_left ?_).sub_right
    (sub_offset hon (by have := outn_lt s₀; omega_using [this, hon]))
  rw [A_eq (by omega_using [fC, hd])]; exact sub_offset hd (by omega_using [hd])

/-- The bytes of a lane in memory. -/
theorem lane_bytes (m : Mem) (p : Addr) {u : Nat} (hu : u < 8) :
    m (p + BitVec.ofNat 64 u) = (m.readW p 64).extractLsb' (8 * u) 8 := by
  simp only [Mem.readW]
  rw [show (m.read p (64 / 8)).setWidth 64 = m.read p 8 from BitVec.setWidth_eq _,
    Mem.extractLsb'_read m _ hu]

/-- Between `enter` and `leave`, after `i` bytes of output, at the end of
block `k`: the interleaved state is the state after `k` permutations. -/
structure SInv (s₀ : State) (i k : Nat) (s : State) : Prop where
  i_lt : i < outn s₀
  hi : pos₀ s₀ + i = rt s₀ * (k + 1)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  vars : Hi (scr s₀) s₀.gpr (s₀.gpr .r1) (op s₀ + BitVec.ofNat 32 i) (BitVec.ofNat 32 (outn s₀ - i)) s.mem
  rcs : RCs (scr s₀) s.mem
  state : Stored s.mem (scr s₀) (iterF k (S₀ s₀))
  out : ∀ j < i, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

/-- While the lanes of the interleaved state `K` are copied to the block of
output at `i`, from the state `s₁`: after `n` lanes. -/
structure CInv (s₀ : State) (i : Nat) (K : Spec.Sha3.State) (s₁ : State) (n : Nat) (s : State) :
    Prop where
  le : 8 * n ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = st s₀
  r1 : s.gpr .r1 = scr s₀
  r9 : s.gpr .r9 = op s₀ + BitVec.ofNat 32 (i + 8 * n)
  r10 : s.gpr .r10 = s₀.gpr .r1
  r11 : s.gpr .r11 = BitVec.ofNat 32 (outn s₀ - i)
  masks : Masks s
  bytes : ∀ x < 8 * n, s.mem (oA s₀ + BitVec.ofNat 64 (i + x)) = byteOf K x
  frame : Frame [⟨oA s₀ + BitVec.ofNat 64 i, 8 * n⟩] s₁.mem s.mem

theorem CInv.of_flags {s₀ : State} {i : Nat} {K : Spec.Sha3.State} {s₁ : State} {n : Nat} {s s' : State}
    (h : CInv s₀ i K s₁ n s) (u : Fupd s s') : CInv s₀ i K s₁ n s' where
  le := h.le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  sp := u.sp.trans h.sp
  r0 := by rw [u.gpr]; exact h.r0
  r1 := by rw [u.gpr]; exact h.r1
  r9 := by rw [u.gpr]; exact h.r9
  r10 := by rw [u.gpr]; exact h.r10
  r11 := by rw [u.gpr]; exact h.r11
  masks := by have := h.masks; unfold Masks at this ⊢; rw [u.gpr]; exact this
  bytes := by rw [u.mem]; exact h.bytes
  frame := by rw [u.mem]; exact h.frame

/-- A run of lanes of the block, and `r9` after them. -/
theorem copy_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + rt s₀ ≤ outn s₀) {K : Spec.Sha3.State}
    {s₁ : State} (hK : Stored s₁.mem (scr s₀) K) (p : Nat × Nat) (hpm : p ∈ segs)
    (ha : p.1 = 0 ∨ rt s₀ ≠ 8 * p.1) (s : State) (hX : CInv s₀ i K s₁ p.1 s) (rest : List Instr)
    (Q : State → Prop) (k : ∀ s', CInv s₀ i K s₁ p.2 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (copySeg p.1 p.2 ++
      .dp .add .r9 .r9 (.imm (BitVec.ofNat 32 (8 * (p.2 - p.1)))) :: rest)) s Q := by
  have hb : 8 * p.2 ≤ rt s₀ := segs_rate hp.rate _ hpm ha hX.le
  obtain ⟨hab, hb21, hn⟩ := segs_ok _ hpm
  have himm := (segs_imm _ hpm).1
  obtain ⟨a, b⟩ := p
  have h₁ : a ≤ b := hab
  have h₂ : 8 * b ≤ rt s₀ := hb
  have fO : (op s₀).toNat + outn s₀ ≤ 2 ^ 32 := hp.o_fit
  have fC := hp.c_fit
  obtain hl := outn_lt s₀
  have hok : Ok (cfgC .r9 (b - a)) s :=
    ok_offs (lb := outn s₀) (le := 640) (ob := i + 8 * a) (oe := 0) hX.r9
      (show s.gpr .r1 = scr s₀ + BitVec.ofNat 32 0 by rw [hX.r1]; simp)
      (show OR s₀ ∈ s.wr by rw [hX.wr, hp.wr]; simp)
      (show CR s₀ ∈ s.rd ++ s.wr by rw [hX.wr, hp.wr]; simp) fO fC
      (show i + 8 * a + 4 * (2 * (b - a)) ≤ outn s₀ by omega_using [hi, h₁, h₂])
      (show 0 + 4 * 50 ≤ 640 by decide) hp.o_c
  have hKs : Stored s.mem (s.gpr .r1) K := by
    rw [hX.r1]
    exact hK.keep fun d hd => hp.scr_keep hX.frame (by omega_using [hi, hX.le]) (by omega_using [hd])
  obtain ⟨s', hs', hl', rd', wr', sp', g9, g1, go, f⟩ := copySeg_ok hpm hok hKs hX.masks
  rw [hX.r9] at hl' f
  have h₃ : a < b := (by decide : ∀ p ∈ segs, p.1 < p.2) _ hpm
  rw [addr_add (by omega_using [fO, hi, h₂, h₃])] at f
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s', hs', ?_⟩
  refine wp_add (op2_imm himm) fun s₂ u₂ => k s₂ ?_
  obtain ⟨m4, m5, m6, m7, m8⟩ := hX.masks
  refine {
    le := hb, rd := by rw [u₂.rd, rd', hX.rd], wr := by rw [u₂.wr, wr', hX.wr],
    sp := by rw [u₂.sp, sp', hX.sp], r0 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r0],
    r1 := by rw [u₂.other _ (by decide), g1, hX.r1], r9 := ?_,
    r10 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r10],
    r11 := by rw [u₂.other _ (by decide), go _ (by decide), hX.r11],
    masks := ⟨by rw [u₂.other _ (by decide), go _ (by decide), m4],
      by rw [u₂.other _ (by decide), go _ (by decide), m5],
      by rw [u₂.other _ (by decide), go _ (by decide), m6],
      by rw [u₂.other _ (by decide), go _ (by decide), m7],
      by rw [u₂.other _ (by decide), go _ (by decide), m8]⟩,
    bytes := fun x hx => ?_, frame := ?_ }
  · rw [u₂.gpr, g9, hX.r9, Straight.add_ofNat_ofNat,
      show i + 8 * a + 8 * (b - a) = i + 8 * b by omega_using [h₁]]
  · rw [u₂.mem]
    by_cases hxa : x < 8 * a
    · have := f.bytes (R := ⟨oA s₀ + BitVec.ofNat 64 i, 8 * a⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact off_disjoint _ (by omega_using [hl, hi, h₁, h₂]) (by omega_using [hl, hi, h₁, h₂])
          (.inl (Nat.le_refl _))) (by simp; omega_using [h₁, h₂, hl, hi]) hxa
      rw [add_ofNat] at this
      rw [this]; exact hX.bytes x hxa
    · have hlane := hl' (x / 8 - a) (by omega_using [hx, hxa])
      rw [lane_words, rd64_add, rd64_eq _ (by omega_using [fO, hi, h₂, hx, hxa])] at hlane
      rw [show i + x = (i + 8 * a + 8 * (x / 8 - a)) + x % 8 by omega_using [hxa], ← add_ofNat,
        lane_bytes s'.mem _ (Nat.mod_lt _ (by decide)), hlane, byteOf,
        show a + (x / 8 - a) = x / 8 by omega_using [hxa]]
  · rw [u₂.mem]
    refine (hX.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton.mp hr]
      exact Proof.Sha3.off_sub _ (by omega_using [hl, hi, h₂]) (Nat.le_refl _) (by omega_using [h₁])
    · rw [List.mem_singleton.mp hr]
      exact Proof.Sha3.off_sub _ (by omega_using [hl, hi, h₂]) (by omega_using []) (by omega_using [h₁])

/-- A block: the rounds permute the interleaved state, and its lanes are
copied to the output; Z is clear if more than a block of output is left. -/
theorem sblock_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hS : SInv s₀ i k s)
    (hgt : rt s₀ < outn s₀ - i) :
    WP isa (.seq roundsCall (.seq (.block bulkLoad) (.seq (ladder copySeg)
      (.block (bulkStore ++ squeezeBlockTest))))) s fun s' =>
      SInv s₀ (i + rt s₀) (k + 1) s' ∧ s'.z = decide (outn s₀ - (i + rt s₀) ≤ rt s₀) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  obtain hl := outn_lt s₀
  have fC := hp.c_fit
  have hr168' : rt s₀ ≤ 168 := hr168
  obtain ⟨n, hn, hn21⟩ : ∃ n, rt s₀ = 8 * n ∧ n ≤ 21 := by
    have := hp.rate
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at this
    exact ⟨rt s₀ / 8, by omega_using [this], by omega_using [this]⟩
  have hsub : ∀ r ∈ [regR (st s₀) 200, regR (scr s₀) 512], r = regR (st s₀) 200 ∨ Region.Sub r (CR s₀) :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (Region.sub_prefix (by decide))
  refine WP.seq (rounds_call hS.r0 hS.r1 hp.st_fit (by omega_using [fC])
    (hp.st_c.sub_right (Region.sub_prefix (by decide))) (hp.covers hS.wr) hS.state hS.rcs
    fun s₁ rd₁ wr₁ sp₁ r0₁ r1₁ f₁ hK₁ hrc₁ _ => ?_)
  have hH₁ := hS.vars.frame fC hp.st_c f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hr
  refine WP.seq ?_
  rw [← List.append_nil bulkLoad]
  refine bulkLoad_ok r1₁ (fun d hd => hp.scr_in (wr₁.trans hS.wr) hd)
    fun s₂ hm h9 h10 h11 g0 g1 m₂ rd₂ wr₂ sp₂ => WP.block_nil ?_
  rw [hH₁.ptr] at h9
  rw [hH₁.rate] at h10
  rw [hH₁.left] at h11
  have hK₂ : Stored s₂.mem (scr s₀) (iterF (k + 1) (S₀ s₀)) := by rw [m₂]; exact hK₁
  have hX₀ : CInv s₀ i (iterF (k + 1) (S₀ s₀)) s₂ 0 s₂ := {
    le := Nat.zero_le _, rd := by rw [rd₂, rd₁, hS.rd], wr := by rw [wr₂, wr₁, hS.wr],
    sp := by rw [sp₂, sp₁, hS.sp], r0 := g0.trans r0₁, r1 := g1,
    r9 := by rw [h9, Nat.mul_zero, Nat.add_zero], r10 := h10, r11 := h11, masks := hm,
    bytes := fun x hx => absurd hx (Nat.not_lt_zero _), frame := Frame.refl _ _ }
  refine WP.seq (WP.mono (ladder_ok (P := CInv s₀ i (iterF (k + 1) (S₀ s₀)) s₂) (rt := rt s₀)
    (fun a s h => by rw [h.r10]; exact (ofNat_toNat32 _).symm) (fun a s s' h u => h.of_flags u)
    (fun p hpm ha s hX rest Q k => copy_step hp (by omega_using [hgt]) hK₂ p hpm ha s hX rest Q k)
    hp.rate hX₀) fun s₃ hX => ?_)
  rw [show rt s₀ / 8 = n by omega_using [hn]] at hX
  have keep₃ : ∀ d, d + 4 ≤ 640 → s₃.mem.readW (A (scr s₀) d) 32 = s₁.mem.readW (A (scr s₀) d) 32 :=
    fun d hd => by rw [hp.scr_keep hX.frame (by omega_using [hgt, hn]) hd, m₂]
  refine bulkStore_ok hX.r1 (fun d hd => hp.scr_in hX.wr hd)
    fun s₄ e11 o₄ m₄ rd₄ wr₄ sp₄ => ?_
  have e9 : s₃.gpr .r9 = op s₀ + BitVec.ofNat 32 (i + rt s₀) := by rw [hX.r9, hn]
  have el : s₃.gpr .r11 - s₃.gpr .r10 = BitVec.ofNat 32 (outn s₀ - (i + rt s₀)) := by
    rw [hX.r11, hX.r10, ← ofNat_toNat32 (s₀.gpr .r1),
      sub_ofNat32 (show rt s₀ ≤ outn s₀ - i by omega_using [hgt]), Nat.sub_sub]
  rw [el] at e11
  rw [el, hX.r10, e9] at m₄
  unfold squeezeBlockTest
  refine wp_geq (d := .r12) (n := .r10) (x := BitVec.ofNat 32 (rt s₀))
    (y := BitVec.ofNat 32 (outn s₀ - (i + rt s₀))) (by decide) (by decide)
    (by rw [o₄ _ (by decide), hX.r10]; exact (ofNat_toNat32 _).symm)
    (fun s' h => by rw [op2_reg, h .r11 (by decide), e11]) fun s₅ g₅ o₅ m₅ rd₅ wr₅ sp₅ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ⟨?_, ?_⟩
  · have em : s₆.mem = storeVars s₃.mem (scr s₀) (s₀.gpr .r1) (op s₀ + BitVec.ofNat 32 (i + rt s₀))
        (BitVec.ofNat 32 (outn s₀ - (i + rt s₀))) := by rw [u₆.mem, m₅, m₄]
    have eg : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .r11 → s₆.gpr r = s₃.gpr r := fun r a b c => by
      rw [u₆.gpr, o₅ r a b, o₄ r c]
    have klo : ∀ d, d + 4 ≤ 532 → s₆.mem.readW (A (scr s₀) d) 32 = s₁.mem.readW (A (scr s₀) d) 32 :=
      fun d hd => by
        rw [em, storeVars_keep _ fC _ _ _ (by omega_using [hd]) (.inl hd), keep₃ d (by omega_using [hd])]
    refine {
      i_lt := by omega_using [hgt], hi := by rw [← Nat.add_assoc, hS.hi, ← Nat.mul_succ],
      rd := by rw [u₆.rd, rd₅, rd₄, hX.rd], wr := by rw [u₆.wr, wr₅, wr₄, hX.wr],
      sp := by rw [u₆.sp, sp₅, sp₄, hX.sp],
      r0 := by rw [eg _ (by decide) (by decide) (by decide), hX.r0],
      r1 := by rw [eg _ (by decide) (by decide) (by decide), hX.r1],
      frame := ?_, vars := ?_,
      rcs := hrc₁.keep fun d _ h₂ => klo d (by omega_using [h₂]),
      state := hK₁.keep fun d hd => klo d (by omega_using [hd]), out := fun j hj => ?_ }
    · rw [em]
      refine ((hS.frame.trans (f₁.sub fun r hr => ?_)).trans (m₂ ▸ hX.frame.sub fun r hr => ?_)).trans
        ((storeVars_frame _ fC _ _ _).mono fun r hr => by rw [List.mem_singleton.mp hr]; simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨SR s₀, by simp, fun _ h => h⟩
        · exact ⟨CR s₀, by simp, Region.sub_prefix (by decide)⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨OR s₀, by simp, sub_offset (by omega_using [hgt, hn]) (by omega_using [hl, hgt])⟩
    · rw [em]
      exact (hH₁.keep fun d _ h₂ => keep₃ d h₂).store fC _ _ _
    · rw [em, hp.out_keep (storeVars_frame _ fC _ _ _)
        (fun r hr => .inr (by rw [List.mem_singleton.mp hr]; exact fun _ h => h)) (by omega_using [hj, hgt])]
      by_cases hji : j < i
      · have := hX.frame.bytes (R := ⟨oA s₀ + BitVec.ofNat 64 0, i⟩) (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact off_disjoint _ (by omega_using [hl, hgt]) (by omega_using [hl, hgt, hn])
            (.inl (by omega_using []))) (by simp; omega_using [hl, hgt]) hji
        rw [add_ofNat, Nat.zero_add] at this
        rw [this, m₂, hp.out_keep f₁ hsub (by omega_using [hji, hgt])]
        exact hS.out j hji
      · have := hX.bytes (j - i) (by omega_using [hj, hji, hn])
        rw [show i + (j - i) = j by omega_using [hji]] at this
        obtain ⟨d, m⟩ := div_mod_eq (k := k + 1) hr0 (show j - i < rt s₀ by omega_using [hj, hji])
        rw [this, show pos₀ s₀ + j = rt s₀ * (k + 1) + (j - i) by have := hS.hi; omega_using [this, hji], d, m]
  · rw [hz, g₅, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl]),
      Nat.mod_eq_of_lt (by omega_using [hr168']), geq_beq]

/-- At the end of a block, with more than a block of output left: the whole
blocks of the output, and a permutation for what is left after them. -/
theorem sbulk_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s)
    (hgt : rt s₀ < outn s₀ - i) :
    WP isa squeezeBulk s fun s' => ∃ i' k', i < i' ∧ i' < outn s₀ ∧ Inv s₀ i' k' 0 s' := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  have fC := hp.c_fit
  have fC' : (scr s₀).toNat + 512 ≤ 2 ^ 32 := by omega_using [fC]
  have hd' := hp.st_c.sub_right (Region.sub_prefix (show 512 ≤ 640 by decide))
  have hsub : ∀ r ∈ [regR (st s₀) 200, regR (scr s₀) 512], r = regR (st s₀) 200 ∨ Region.Sub r (CR s₀) :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (Region.sub_prefix (by decide))
  unfold squeezeBulk
  refine WP.seq ?_
  rw [bulkSave_eq]
  refine saveA_ok saveL s _ (fun p hp' => ⟨(saveL_ok p hp').1, by
    rw [hI.r1]; exact hp.scr_in hI.wr (by have := saveL_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [hI.r1] at m₁
  have hH₁ : Hi (scr s₀) s₀.gpr (s₀.gpr .r1) (op s₀ + BitVec.ofNat 32 i) (BitVec.ofNat 32 (outn s₀ - i))
      s₁.mem := by
    have h := saveMemA_hi fC hI.saved s.gpr (fun p hp' => hI.hi8 p.1 (savedHi_regs p hp'))
    rw [hI.r4, hI.r6, hI.r7, ← m₁] at h
    exact h
  have f₁ : Frame [regR (scr s₀) 640] s.mem s₁.mem := by
    rw [m₁]; exact saveMemA_frame fC _ _ _ fun p hp' => by have := saveL_ok p hp'; omega
  have hst₁ : stateAt s₁.mem (stA s₀) = stateAt s.mem (stA s₀) :=
    stateAt_congr fun j hj => f₁.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj
  refine WP.seq (enter_call (st := st s₀) (scr := scr s₀) (by rw [g₁]; exact hI.r0)
    (by rw [g₁]; exact hI.r1) hp.st_fit fC' hd' (hp.covers (wr₁.trans hI.wr))
    fun s₂ rd₂ wr₂ sp₂ r0₂ r1₂ f₂ hK₂ hrc₂ => ?_)
  rw [hst₁, hI.state] at hK₂
  have hS₂ : SInv s₀ i k s₂ := {
    i_lt := by omega_using [hgt], hi := by rw [hI.hi, Nat.mul_succ],
    rd := by rw [rd₂, rd₁, hI.rd], wr := by rw [wr₂, wr₁, hI.wr], sp := by rw [sp₂, sp₁, hI.sp],
    r0 := r0₂, r1 := r1₂,
    frame := hI.frame.trans ((f₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp).trans
      (f₂.sub fun r hr => ⟨CR s₀, by simp, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)),
    vars := hH₁.frame fC hp.st_c (rs := [regR (scr s₀) 512])
      (f₂.sub fun r hr => ⟨regR (scr s₀) 512, by simp, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)
      (fun r hr => .inr (List.mem_singleton.mp hr)),
    rcs := hrc₂, state := hK₂,
    out := fun j hj => by
      rw [hp.out_keep f₂ (fun r hr => .inr (by
          rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))) (by omega_using [hj, hgt]),
        hp.out_keep f₁ (fun r hr => .inr (by rw [List.mem_singleton.mp hr]; exact fun _ h => h))
          (by omega_using [hj, hgt])]
      exact hI.out j hj }
  refine WP.seq (WP.mono (Q := fun s' => ∃ i' k', i < i' ∧ SInv s₀ i' k' s' ∧ outn s₀ - i' ≤ rt s₀) ?_
    fun s₃ ⟨i', k', hii, hS₃, hle⟩ => ?_)
  · refine WP.loop (M := isa)
      (fun n s => ∃ i' k', n = outn s₀ - i' ∧ i ≤ i' ∧ rt s₀ < outn s₀ - i' ∧ SInv s₀ i' k' s) ?_
      (outn s₀ - i) s₂ ⟨i, k, rfl, Nat.le_refl _, hgt, hS₂⟩
    rintro n s ⟨i', k', rfl, hii, hgt', hS⟩
    refine WP.mono (sblock_ok hp hS hgt') fun s' ⟨hS', hz'⟩ => ?_
    by_cases he : outn s₀ - (i' + rt s₀) ≤ rt s₀
    · exact .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl,
        i' + rt s₀, k' + 1, by omega_using [hii, hr0], hS', he⟩
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        outn s₀ - (i' + rt s₀), by omega_using [hgt', hr0], i' + rt s₀, k' + 1, rfl,
        by omega_using [hii], by omega_using [he], hS'⟩
  refine WP.seq (rounds_call hS₃.r0 hS₃.r1 hp.st_fit fC' hd' (hp.covers hS₃.wr) hS₃.state hS₃.rcs
    fun s₄ rd₄ wr₄ sp₄ r0₄ r1₄ f₄ hK₄ hrc₄ _ => ?_)
  have hH₄ := hS₃.vars.frame fC hp.st_c f₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hr
  refine WP.seq (leave_call r0₄ r1₄ hp.st_fit fC' hd' (hp.covers (wr₄.trans hS₃.wr)) hK₄
    fun s₅ rd₅ wr₅ sp₅ r0₅ r1₅ f₅ hst₅ => ?_)
  have hH₅ := hH₄.frame fC hp.st_c f₅ (fun r hr => .inl (List.mem_singleton.mp hr))
  refine bulkRestore_ok r1₅ (fun d hd => hp.scr_in (wr₅.trans (wr₄.trans hS₃.wr)) hd) hH₅
    fun s' e4 e5 e6 e7 e8 e0 e1 em erd ewr esp => ⟨i', k' + 1, hii, hS₃.i_lt, ?_⟩
  exact {
    i_le := Nat.le_of_lt hS₃.i_lt, hi := hS₃.hi, pos_le := Nat.zero_le _,
    rd := by rw [erd, rd₅, rd₄, hS₃.rd], wr := by rw [ewr, wr₅, wr₄, hS₃.wr],
    sp := by rw [esp, sp₅, sp₄, hS₃.sp], r0 := e0.trans r0₅, r1 := e1, r4 := e4,
    r5 := by rw [e5]; rfl, r6 := e6, r7 := e7, hi8 := e8,
    frame := by
      rw [em]
      refine (hS₃.frame.trans (f₄.sub fun r hr => ?_)).trans
        (f₅.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨SR s₀, by simp, fun _ h => h⟩
      · exact ⟨CR s₀, by simp, Region.sub_prefix (by decide)⟩,
    saved := by rw [em]; exact hH₅.saved, state := by rw [em, hst₅, iterF_succ],
    out := fun j hj => by
      rw [em, hp.out_keep f₅ (fun r hr => .inl (List.mem_singleton.mp hr)) (by omega_using [hj, hS₃.i_lt]),
        hp.out_keep f₄ hsub (by omega_using [hj, hS₃.i_lt])]
      exact hS₃.out j hj }

/-- At the end of a block: a permutation, or the whole blocks of the output
and one, when more than a block of output is left. -/
theorem refill_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s)
    (hi : i < outn s₀) :
    WP isa (.seq (.block squeezeBulkTest)
      (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) squeezeBulk)) s fun s' =>
      ∃ i' k', i ≤ i' ∧ i' < outn s₀ ∧ Inv s₀ i' k' 0 s' := by
  have ⟨hr0, _, _, hr168⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  unfold squeezeBulkTest
  refine WP.seq (wp_geq (d := .r3) (n := .r4) (x := BitVec.ofNat 32 (rt s₀))
    (y := BitVec.ofNat 32 (outn s₀ - i)) (by decide) (by decide)
    (by rw [hI.r4]; exact (ofNat_toNat32 _).symm) (fun s' h => by rw [op2_reg, h .r7 (by decide), hI.r7])
    fun s₁ g₁ o₁ m₁ rd₁ wr₁ sp₁ => wp_cmp (op2_imm (by decide)) fun s₂ u₂ hz => WP.block_nil ?_)
  have hI₂ : Inv s₀ i k (rt s₀) s₂ :=
    (hI.of_gpr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact o₁ r hr.2.1 hr.1) m₁ rd₁ wr₁ sp₁).of_flags u₂
  have hz' : s₂.z = decide (outn s₀ - i ≤ rt s₀) := by
    rw [hz, g₁, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn]),
      Nat.mod_eq_of_lt (show rt s₀ < 2 ^ 32 by have h : rt s₀ ≤ 168 := hr168; omega_using [h]), geq_beq]
  refine WP.ite (decide (outn s₀ - i ≤ rt s₀)) (by show VG.Arm.eval .eq s₂ = _; rw [eval_eq, hz'])
    (fun _ => ?_) (fun hb => ?_)
  · exact WP.mono (permute_ok hp hI₂) fun s' h => ⟨i, k + 1, Nat.le_refl _, hi, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.mono (sbulk_ok hp hI₂ (by omega_using [hb])) fun s' ⟨i', k', h₁, h₂, h₃⟩ =>
      ⟨i', k', Nat.le_of_lt h₁, h₂, h₃⟩

/-- The bytes that are left of the block, or of the output: `n > 0` more
bytes of output. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {i k' pos' : Nat} {s₂ : State} (hI₂ : Inv s₀ i k' pos' s₂)
    (hlt : pos' < rt s₀) (hi : i < outn s₀) :
    WP isa (.seq (.block words)
      (.seq (.ite .eq (.block squeezeByte) (.seq (.block wordsPre) (.loop (.block squeezeWord) .ne)))
        (.block [.cmp .r7 (.imm 0)]))) s₂ fun s' => ∃ n pos'', 0 < n ∧ i + n ≤ outn s₀ ∧
      Inv s₀ (i + n) k' pos'' s' ∧ s'.z = decide (outn s₀ - (i + n) = 0) := by
  have ⟨hr0, _, _, hr168⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  -- The words left, then a byte or the words.
  refine WP.seq (WP.mono (words_ok (l := outn s₀ - i) (j := pos') (rt := rt s₀) hI₂.r7 hI₂.r5
    (by rw [hI₂.r4]; exact (ofNat_toNat32 _).symm) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨g₃, m₃, rd₃, wr₃, sp₃, hlr, hz₃⟩ => ?_)
  obtain hI₃ := hI₂.of_gpr g₃ m₃ rd₃ wr₃ sp₃
  generalize hnw : min (outn s₀ - i) (rt s₀ - pos') / 4 = nw at hlr hz₃
  obtain h4 : i + 4 * nw ≤ outn s₀ := by omega_arith
  obtain hp4 : pos' + 4 * nw ≤ rt s₀ := by omega_arith
  refine WP.seq (WP.mono (Q := fun s => ∃ n pos'', 0 < n ∧ i + n ≤ outn s₀ ∧ Inv s₀ (i + n) k' pos'' s) ?_
    fun s₄ ⟨n, pos'', hn0, hin, hI₄⟩ => WP.mono (cmp_ok hI₄) fun s' h => ⟨n, pos'', hn0, hin, h⟩)
  refine WP.ite (decide (nw = 0)) (by show VG.Arm.eval .eq s₃ = _; rw [eval_eq, hz₃])
    (fun _ => ?_) (fun hb => ?_)
  · exact WP.mono (store_ok hp hI₃ hlt hi) fun s' h => ⟨1, pos' + 1, by decide, by omega_arith, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (wordsPre_ok h4 hI₃ hlr) fun s₄ hW => ?_)
    refine WP.mono (Q := WInv s₀ i k' pos' nw nw) ?_ fun s₅ hW₅ =>
      ⟨4 * nw, pos' + 4 * nw, by omega_arith, h4, hW₅.toInv h4 hp4 hI₂.hi⟩
    refine WP.loop (M := isa) (fun n s => ∃ w, n = nw - w ∧ w < nw ∧ WInv s₀ i k' pos' nw w s) ?_ nw s₄
      ⟨0, rfl, by omega_arith, hW⟩
    rintro n s ⟨w, rfl, hw, hWs⟩
    refine WP.mono (word_step hp hw h4 hp4 hI₂.hi hWs) fun s' ⟨hW', hz'⟩ => ?_
    by_cases he : nw - (w + 1) = 0
    · refine .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl, ?_⟩
      rwa [show w + 1 = nw by omega_arith] at hW'
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        nw - (w + 1), by omega_arith, w + 1, rfl, by omega_arith, hW'⟩

/-- The whole body: it writes `n > 0` more bytes of output. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ n k' pos', 0 < n ∧ i + n ≤ outn s₀ ∧
      Inv s₀ (i + n) k' pos' s' ∧ s'.z = decide (outn s₀ - (i + n) = 0) := by
  have ⟨hr0, _, _, hr168⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  unfold squeezeBody
  refine WP.seq (wp_cmp (op2_reg _ _) fun s₁ u₁ hz => WP.block_nil ?_)
  obtain hI₁ := hI.of_flags u₁
  obtain hz' : s₁.z = decide (pos = rt s₀) := by
    rw [hz, hI.r5, hI.r4, sub_beq_zero32 (by have := hI.pos_le; omega_arith)]
  refine WP.seq (WP.mono
    (Q := fun s => ∃ i' k' pos', i ≤ i' ∧ i' < outn s₀ ∧ Inv s₀ i' k' pos' s ∧ pos' < rt s₀) ?_
    fun s₂ ⟨i', k', pos', hii, hi', hI₂, hlt⟩ => ?_)
  · refine WP.ite (decide (pos = rt s₀)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz'])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      exact WP.mono (refill_ok hp hI₁ hi) fun s' ⟨i', k', h₁, h₂, h₃⟩ => ⟨i', k', 0, h₁, h₂, h₃, hr0⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact WP.block_nil (M := isa) ⟨i, k, pos, Nat.le_refl _, hi, hI₁, by have := hI.pos_le; omega_arith⟩
  refine WP.mono (tail_ok hp hI₂ hlt hi') fun s' ⟨n, pos'', hn0, hin, hI', hz⟩ => ?_
  have e : i + (i' - i + n) = i' + n := by omega_using [hii]
  exact ⟨i' - i + n, k', pos'', by omega_using [hn0], by omega_using [hii, hin], by rw [e]; exact hI',
    by rw [e]; exact hz⟩

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.squeezeArm.post s₀ s'

theorem hi_not_saved : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∉ saved.map Prod.fst ∧ r ≠ .r0 := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {k pos : Nat} {s : State}
    (hI : Inv s₀ (outn s₀) k pos s) : WP isa (.block epilogue) s (Post s₀) := by
  have ⟨hr0, hr200, _, hr168⟩ := hp.rate_pos
  have fC := hp.c_fit
  have hpl := hI.pos_le
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreA_ok saved s₁ _ (by decide) (fun p hp' => ⟨(ssaved_ok p hp').1, (ssaved_ok p hp').2.2.1,
    ?_⟩) fun s' ho hr hm => WP.block_nil ⟨fun r hr' => ?_, ?_, ?_, fun d => ?_⟩
  · rw [u₁.rd, u₁.wr, u₁.other .r1 (by decide), hI.rd, hI.wr, hI.r1, hp.wr]
    exact ⟨CR s₀, by simp, contains_A fC (by have := ssaved_ok p hp'; omega)⟩
  · rcases preserved_cases r hr' with ⟨p, hp', rfl⟩ | hr''
    · rw [ho p hp', u₁.other .r1 (by decide), hI.r1, u₁.mem]; exact hI.saved p hp'
    · rw [hr r (hi_not_saved r hr'').1, u₁.other r (hi_not_saved r hr'').2]; exact hI.hi8 r hr''
  · show bytesAt s'.mem (oA s₀) (outn s₀) =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [hm, u₁.mem]
    refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
    obtain hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr0 hr200 _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · rw [hr .r0 (by decide), u₁.gpr, hI.r5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    exact hpl
  · show Spec.Sha3.squeezeFrom (rt s₀) (stateAt s'.mem (stA s₀)) (s'.gpr .r0).toNat d =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [hm, u₁.mem, hI.state, hr .r0 (by decide), u₁.gpr, hI.r5, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith), squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa squeeze s₀ (Post s₀) := by
  obtain hl := outn_lt s₀
  unfold squeeze
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (M := isa) ⟨0, pos₀ s₀, hb ▸ hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_ (outn s₀) s₁
      ⟨0, 0, pos₀ s₀, by omega_arith, by omega_arith, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨n, k', pos', hn0, hin, hI', hz'⟩ => ?_
    by_cases he : outn s₀ - (i + n) = 0
    · refine .inl ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_true he]; rfl,
        k', pos', ?_⟩
      rwa [show i + n = outn s₀ by omega_arith] at hI'
    · exact .inr ⟨by show VG.Arm.eval .ne s' = _; rw [eval_ne, hz', decide_eq_false he]; rfl,
        outn s₀ - (i + n), by omega_arith, i + n, k', pos', rfl, by omega_arith, hI'⟩

/-! ## Constant time -/

/-- The initial taint: the register arguments are public, `r0` points at the
state, and the 8 bytes of stack arguments are public, the second one
pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [200, 0, 640], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 2)] }

theorem wf₀ {s : State} (h : Proof.Sha3.squeezeArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of h
  obtain hst := hp.st_fit; have hso := hp.o_fit; have hsc := hp.c_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨hp.st_o, hp.st_c⟩, hp.o_c⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega_arith
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_o
    · exact hp.a_c
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeArm.pre s₁) (h₂ : Proof.Sha3.squeezeArm.pre s₂)
    (hpub : Proof.Sha3.squeezeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [SR, OR, CR, stA, oA, outn, scr, st, op, p0, p3, a0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega_arith
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition (with no output, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 72 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x4000, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0, 640⟩]

theorem squeeze_verified : Verified Arm.target squeeze Proof.Sha3.squeezeArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak VG.Proof.Sha3.Arm.dropRC)
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha3.squeezeArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide, by decide, by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm.Stream.Squeeze

end

end

/-!
# The SHA-3 sponge on ARMv7: `pad`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Pad`),
with the return address saved in the scratch space instead of a frame.
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Stream.Pad

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (call_ok covers_of readW_hi xor_setWidth32' ofNat_toNat32 argByte_eq
  addr_toNat)
open VG.Proof.Sha512.Arm (A contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_sub wp_ldr wp_str wp_ldrb
  wp_strb wp_ldrSp)
open VG.Proof.Sha512.Arm (wp_eor)
open VG.Proof.Sha3 (Rep xorByte stateAt_xorByte stateAt_congr writeW8_apply contains_offset ne_of_lt200
  absorb_pad)
open VG.Spec.Sha3 (stateAt keccakF rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev rt : Nat := (s₀.gpr .r1).toNat
abbrev pos : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev stA : Addr := State.addr (st s₀)
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 640⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (s₀.gpr .r0).toNat + 200 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.padArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## Correctness -/

/-- The postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.padArm.post s₀ s'

theorem x80 : ((0x80 : BitVec 32).setWidth 8) = (0x80 : BitVec 8) := by decide

theorem keep_ne : ∀ r ∈ preserved, r ≠ .r12 ∧ r ≠ .r2 ∧ r ≠ .r1 := by decide

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa pad s₀ (Post s₀) := by
  have ⟨hr₀, hr₁⟩ := Proof.Sha3.rate_bounds hp.rate
  have hr₀' : 72 ≤ (s₀.gpr .r1).toNat := hr₀
  have hr₁' : (s₀.gpr .r1).toNat ≤ 168 := hr₁
  have hpl : (s₀.gpr .r2).toNat < (s₀.gpr .r1).toNat := hp.pos_lt
  have fS := hp.st_fit
  have fC := hp.scr_fit
  obtain hin : ∀ rs : List Region, stR s₀ ∈ rs → ∀ j < 200,
      InRegions rs (stA s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h j hj => ⟨stR s₀, h, contains_offset (by omega_using [hj]) (by omega_using [hj])⟩
  obtain hlr : ∀ rs : List Region, scR s₀ ∈ rs → InRegions rs (A (scr s₀) 512) 4 :=
    fun rs h => ⟨scR s₀, h, contains_A fC (by omega_using [])⟩
  obtain hp1 : pos s₀ < 200 := show (s₀.gpr .r2).toNat < 200 by omega_using [hr₁', hpl]
  obtain hq : rt s₀ - 1 < 200 := show (s₀.gpr .r1).toNat - 1 < 200 by omega_using [hr₁']
  unfold pad
  refine WP.seq ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩ fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine wp_str (a := A (scr s₀) 512) (by decide) (by rw [h12])
    (hlr _ (by simp [u₁.wr, hp.wr])) fun s₂ m₂ => ?_
  obtain hm₂ : s₂.mem = s₀.mem.writeW (A (scr s₀) 512) (s₀.gpr .lr) := by
    rw [m₂.mem, u₁.mem, u₁.other .lr (by decide)]
  obtain hf₂ : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A fC (by omega_using []))
  obtain k₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [m₂.gpr, u₁.other r h]
  -- The suffix.
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  obtain e₁ : State.addr (s₃.gpr .r2 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 (pos s₀) := by
    rw [u₃.gpr, k₂ .r0 (by decide), k₂ .r2 (by decide), BitVec.add_zero]
    have := addr_add (a := s₀.gpr .r0) (k := pos s₀) (by omega_using [fS, hp1])
    rwa [ofNat_toNat32] at this
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by decide) e₁
    (hin _ (by simp [u₃.rd, u₃.wr, m₂.rd, m₂.wr, u₁.rd, u₁.wr, hp.rd, hp.wr]) _ hp1) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_strb (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by decide)
    (by rw [u₅.other .r2 (by decide), u₄.other .r2 (by decide)]; exact e₁)
    (hin _ (by simp [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, hp.wr]) _ hp1) fun s₆ g₆ => ?_
  obtain hb₁ : s₆.mem = s₂.mem.writeW (stA s₀ + BitVec.ofNat 64 (pos s₀))
      (s₂.mem (stA s₀ + BitVec.ofNat 64 (pos s₀)) ^^^ (s₀.gpr .r3).setWidth 8) := by
    rw [g₆.mem, u₅.gpr, u₄.gpr, u₄.other .r3 (by decide), u₃.other .r3 (by decide), k₂ .r3 (by decide),
      xor_setWidth32', u₅.mem, u₄.mem, u₃.mem]
  obtain k₆ : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .lr → s₆.gpr r = s₀.gpr r := fun r h12 h2 hl => by
    rw [g₆.gpr, u₅.other r hl, u₄.other r hl, u₃.other r h2, k₂ r h12]
  -- The final bit.
  refine wp_add (op2_reg _ _) fun s₇ u₇ => wp_sub (op2_imm (by decide)) fun s₈ u₈ => ?_
  obtain e₂ : State.addr (s₈.gpr .r2 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 (rt s₀ - 1) := by
    rw [u₈.gpr, u₇.gpr, k₆ .r0 (by decide) (by decide) (by decide),
      k₆ .r1 (by decide) (by decide) (by decide), BitVec.add_zero,
      show s₀.gpr .r0 + s₀.gpr .r1 - 1 = s₀.gpr .r0 + BitVec.ofNat 32 ((s₀.gpr .r1).toNat - 1) by
        exact Offset.add_sub_one32 _ _ (by omega_using [hr₀'])]
    exact addr_add (by omega_using [hr₁', fS])
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by decide) e₂
    (hin _ (by simp [u₈.rd, u₈.wr, u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd,
      u₃.wr, m₂.rd, m₂.wr, u₁.rd, u₁.wr, hp.rd, hp.wr]) _ hq) fun s₉ u₉ => ?_
  refine wp_eor (op2_imm (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_strb (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by decide)
    (by rw [u₁₀.other .r2 (by decide), u₉.other .r2 (by decide)]; exact e₂)
    (hin _ (by simp [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, hp.wr]) _ hq)
    fun s₁₁ g₁₁ => ?_
  obtain hb₂ : s₁₁.mem = s₆.mem.writeW (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
      (s₆.mem (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) ^^^ 0x80) := by
    rw [g₁₁.mem, u₁₀.gpr, u₉.gpr, xor_setWidth32', x80, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  refine wp_mov (op2_reg _ _) fun s₁₂ u₁₂ => WP.block_nil ?_
  -- The state and the frame.
  obtain hS₂ : stateAt s₂.mem (stA s₀) = stateAt s₀.mem (stA s₀) :=
    stateAt_congr fun i hi => hf₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  obtain hS : stateAt s₁₂.mem (stA s₀) = xorByte (xorByte (stateAt s₀.mem (stA s₀)) (pos s₀)
      ((s₀.gpr .r3).setWidth 8)) (rt s₀ - 1) 0x80 := by
    rw [u₁₂.mem, ← hS₂, ← stateAt_xorByte (m := s₂.mem) (m' := s₆.mem) hp1
      (by rw [hb₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [hb₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi hp1 hne))])]
    exact stateAt_xorByte hq (by rw [hb₂, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [hb₂, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi hq hne))])
  obtain hf₆ : Frame [stR s₀] s₂.mem s₆.mem := by
    rw [hb₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_using [hp1]) (by omega_using [hp1]))
  obtain hf₁₂ : Frame [stR s₀] s₂.mem s₁₂.mem := by
    rw [u₁₂.mem, hb₂]
    exact hf₆.writeW (List.mem_singleton_self _) _ (contains_offset (by omega_using [hr₁]) (by omega_using [hr₁]))
  obtain k₁₂ : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .lr → r ≠ .r1 → s₁₂.gpr r = s₀.gpr r :=
    fun r h12 h2 hl h1 => by
      rw [u₁₂.other r h1, g₁₁.gpr, u₁₀.other r hl, u₉.other r hl, u₈.other r h2, u₇.other r h2,
        k₆ r h12 h2 hl]
  obtain r1₁₂ : s₁₂.gpr .r1 = scr s₀ := by
    rw [u₁₂.gpr, g₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), g₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), m₂.gpr, h12]
  obtain rd₁₂ : s₁₂.rd = s₀.rd := by
    rw [u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd]
  obtain wr₁₂ : s₁₂.wr = s₀.wr := by
    rw [u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]
  -- The call, and the return address.
  refine WP.seq (call_ok (st := st s₀) (scr := scr s₀)
    (k₁₂ .r0 (by decide) (by decide) (by decide) (by decide)) r1₁₂ fS (by omega_using [fC])
    (hp.st_scr.sub_right (Region.sub_prefix (by omega_using [])))
    (by rw [wr₁₂, hp.wr]; exact covers_of (N := 640) (by omega_using []) (by simp) (by simp))
    fun s' rd' wr' _ cs' _ r1' f' e' => ?_)
  refine wp_ldr (a := A (scr s₀) 512) (by decide) (by rw [r1'])
    (hlr _ (by simp [rd', wr', rd₁₂, wr₁₂, hp.rd, hp.wr])) fun s'' u'' => WP.block_nil ?_
  refine ⟨fun r hr => ?_, fun msg hR hm => ?_⟩
  · by_cases hl : r = .lr
    · subst hl
      rw [u''.gpr, readW_hi fC hp.st_scr f' (fun r hr => by simpa using hr) (d := 512) (Nat.le_refl _)
        (by omega_using []), readW_hi fC hp.st_scr hf₁₂ (fun r hr => .inl (List.mem_singleton.mp hr))
        (d := 512) (Nat.le_refl _) (by omega_using []), hm₂, Mem.readW_writeW_self32]
    · have ne := keep_ne r hr
      rw [u''.other r hl, cs' r hr hl, k₁₂ r ne.1 ne.2.1 hl ne.2.2]
  · rw [u''.mem, e', hS, Proof.Sha3.repr_iff.mp hR, absorb_pad (by omega_using [hr₀']) (by omega_using [hr₁']), ← hm]

/-! ## Constant time -/

/-- The initial taint: the register arguments are public, `r0` points at the
state, and the stack argument is public and points at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [200, 640], bases := [(.r0, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.padArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of h
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_,
    fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.padArm.pre s₁) (h₂ : Proof.Sha3.padArm.pre s₂)
    (hpub : Proof.Sha3.padArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stA, scr, st, p0, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using [])),
      show k / 4 = 0 by omega_using [hk]]
    exact congrArg _ a0

/-- A state satisfying the precondition (with the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 72 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x4000, 4⟩]
  wr := [⟨0x1000, 200⟩, ⟨0, 640⟩]

theorem pad_verified : Verified Arm.target pad Proof.Sha3.padArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak VG.Proof.Sha3.Arm.dropRC)
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha3.padArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm.Stream.Pad
