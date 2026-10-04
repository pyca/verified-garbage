import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.CmacAes.Arm.Call

section

section

/-!
# AES-CMAC on ARMv7: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function pushes `vg_aes_ctr32`'s two
stack arguments in the 8 bytes below the stack pointer, which may not overlap
any buffer.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint data ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
      Spec.Cmac.chain (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r3)) 16 (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`. -/
def subkeysArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let subk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2176⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      below.Disjoint sched ∧ below.Disjoint subk ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2176 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 16
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let last : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint key ∧ below.Disjoint last ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) ∧
      (stackArg s 0).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (stackArg s 0).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r7` the next block, `r8` the blocks left), only the state, the first 2064
bytes of the scratch buffer and the 8 bytes below the stack pointer have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldrSp saveMem
  saveList_ok saveMem_frame readW_writeW_save cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev R : Nat := (s₀.gpr .r1).toNat
abbrev St : BitVec 32 := s₀.gpr .r2
abbrev Dp : BitVec 32 := s₀.gpr .r3
abbrev N : Nat := (stackArg s₀ 0).toNat
abbrev S : BitVec 32 := stackArg s₀ 1

abbrev schR : Region := ⟨State.addr (W s₀), 240⟩
abbrev stR : Region := ⟨State.addr (St s₀), 16⟩
abbrev dataR : Region := ⟨State.addr (Dp s₀), 16 * N s₀⟩
abbrev scrR : Region := ⟨State.addr (S s₀), 2176⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev belowR : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (State.addr (W s₀)) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (Dp s₀)) 16 (N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := saveMem s₀.mem (State.addr (S s₀)) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_data : (belowR s₀).Disjoint (dataR s₀)
  b_st : (belowR s₀).Disjoint (stR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = St s₀
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16) ((blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) :
    State.addr (Dp s₀ + BitVec.ofNat 32 (16 * k)) = State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k) :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp in
theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

omit hp in
theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem UPre.arg_sub : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argsR s₀) := Region.sub_prefix (by decide)

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2096 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

export VG.Arm.Spill (saveMem_congr)

theorem saved_slots : Spill.Slots 2064 2096 saved := by decide

theorem savedMem_frame (s₀ : State) : Frame [⟨State.addr (S s₀), 2096⟩] s₀.mem (savedMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr (S s₀)) s₀.gpr s₀.mem saved saved_slots (r, d) h

/-! ## The prologue -/

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  have harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (savedMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.scr_args.symm.sub_left UPre.arg_sub).sub_right (Region.sub_prefix (by decide))) (by decide)
  simp only [setup, mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
        exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have r8 : s₉.gpr .r8 = stackArg s₀ 0 := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg]
  have mm : s₉.mem = savedMem s₀ := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  have a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  have stS : Spec.Aes.bytesAt (savedMem s₀) (State.addr (St s₀)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, u₁.other]
    exact (BitVec.add_zero _).symm
  · rw [r8, a0]; rfl
  · simp (disch := decide) only [f₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, h12]
  · simp (disch := decide) only [f₉.gpr, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂,
      u₁.other]
  · rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [mm]; exact Frame.refl _ _
  · rw [mm, stS]; rfl
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

end VG.Proof.CmacAes.Arm

end

/-!
# AES-CMAC on ARMv7: the loop of `vg_cmac_aes_update`

One block keeps the loop invariant (`body_ok`): the counter block is `C ⊕ Mᵢ`
and the state is zeroed (`Cmac.chainMem4`), and the call of `vg_aes_ctr32`
leaves `CIPH_K(C ⊕ Mᵢ)` in the state.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs eval_ne ofNat_beq_zero sub_ofNat)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀, belowR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- The counter block's address. -/
abbrev Cb (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Cb s₀) (St s₀) (S s₀) (R s₀) .r9 .r10
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.chainMem4 s.mem (State.addr (S s₀) + BitVec.ofNat 64 2048) (State.addr (St s₀))
    (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem chainIn_eq : chainIn ++ updArgs = xorBlk .r0 .r1 .r6 .r7 .r10 0 0 2048 ++
    (.mov .r0 (.imm 0) :: (zeroBlk .r0 .r6 0 ++
      ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 2048)),
       .mov .r3 (.reg .r6), .mov .r9 (.imm 1)] : List Instr))) := rfl

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  have qN := hp.dataN hk
  rw [chainIn_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r6]; omega) (by rw [h.r7, qN]; omega)
    (by rw [h.r10]; omega) ?_ ?_ ?_ fun s₁ g₁ => ?_
  · rw [h.r6, add0, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.r7, add0, hp.dataA hk, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
  · rw [h.r10, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
  have e₁ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r := g₁.gpr
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r6₂ : s₂.gpr .r6 = St s₀ := by rw [u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r6]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r6₂]; omega) ?_ fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  · rw [r6₂, add0, u₂.wr, g₁.wr, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₈.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h9 => by
      rw [u₈.other _ h9, u₇.other _ h3, u₆.other _ h2, u₅.other _ h1, u₄.other _ h0, G₃, u₂.other _ h0,
        e₁ _ h0 h1]
  have sp₈ : s₈.sp = s₀.sp := by
    rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr]
  have mem₈ : s₈.mem = Proof.Cmac.chainMem4 s.mem (State.addr (S s₀) + BitVec.ofNat 64 2048)
      (State.addr (St s₀)) (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, r6₂, u₂.mem, g₁.mem, h.r6, h.r7, h.r10, add0, add0,
      hp.dataA hk]
    rfl
  have hb : below s₈ = belowR s₀ := by rw [below, sp₈]; rfl
  have cA : State.addr (Cb s₀) = State.addr (S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have cSt : (⟨State.addr (Cb s₀), 16⟩ : Region).Disjoint (stR s₀) := by
    rw [cA]; exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, by decide, hp.rounds, by rw [sp₈]; exact hp.sp8, ?_, hp.sch_st, ?_, cSt,
    ?_, ?_, by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_st, ?_, hp.sch_fit, ?_, hp.st_fit, ?_, ?_, ?_,
    ?_⟩, keep, by rw [sp₈, h.sp], mem₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r5]
    simp [R]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r10]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, r6₂]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [cA]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hb, cA]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hp.scrN (by decide)]; omega
  · omega
  · rw [rd₈, wr₈, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hW, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈]; exact Proof.Cmac.chainMem4_state _ _ _ _

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa body s fun s' => LInv s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hdf := hp.data_fit
  have hN := (stackArg s₀ 0).isLt
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (ctr_call a.pre) fun s₂ h₂ => ?_)
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) :
      s₄.gpr r = s.gpr r := by
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ h8, u₃.other _ h7, h₂.saved r hr hlr, a.keep r this.1 this.2.1 this.2.2.1 this.2.2.2 h9]
  have r7₂ : s₂.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .r7 (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r7]
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [u₃.other _ (by decide), h₂.saved .r8 (by simp [preserved]) (by decide),
      a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  have dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have cA : State.addr (Cb s₀) = State.addr (S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have f₁ : Frame [⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩, stR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact Proof.Cmac.chainMem4_frame _ _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint
      ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, cA, a.mem, Proof.Cmac.chainMem4_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g .r4 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [g .r5 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₄.other _ (by decide), u₃.gpr, r7₂, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [u₄.gpr, r8₃, dec]
  · rw [g .r10 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r11]
  · rw [u₄.sp, u₃.sp, h₂.sp, a.sp, h.sp]
  · rw [u₄.rd, u₃.rd, h₂.rd, a.rd, h.rd]
  · rw [u₄.wr, u₃.wr, h₂.wr, a.wr, h.wr]
  · have hb : below s₁ = belowR s₀ := by rw [below, a.sp, h.sp]; rfl
    rw [u₄.mem, u₃.mem]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, by rw [cA]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨belowR s₀, by simp, by rw [hb]; exact fun _ h => h⟩
  · rw [u₄.mem, u₃.mem, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega)

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.loop body .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end VG.Proof.CmacAes.Arm
