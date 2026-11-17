module

import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
public import VerifiedGarbage.Impl.AesCbc.Arm
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop
public import VerifiedGarbage.Proof.Aes.Arm.KeyedCall
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CBC on ARMv7: the contracts, and the loop for any mode on whole blocks

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcArm enc`, for encryption
(`enc = true`) and decryption, `modeArm` for CBC (`cbcMode`). Each call of a
block function pushes its stack argument in the 8 bytes below the stack
pointer, which may not overlap any buffer.

The registers are saved, and the arguments kept, as by AES-CMAC's
`vg_cmac_aes_update` (`Proof/CmacAes/Arm/UpdateLoop.lean`), whose names for
them (`W`, `R`, `Dp`, `N`, `S`) and saved memory (`savedMem`) this reuses.

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r7` the next block, `r8` the blocks left), `r11` and the stack pointer are
unchanged, only the chaining value, the data, the first 2064 bytes of the
scratch buffer and the 8 bytes below the stack pointer have changed since
the registers were saved, the first `k` blocks are the mode's (`Mode.out`)
of the first `k` blocks on entry and the rest are unchanged, and the
chaining value is the mode's after them (`Mode.chain`). CBC is `cbcMode`;
other modes' functions with the same arguments reuse the loop.

`loop_ok`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks and sets Z when none are left (`BodyOk`), the loop over the blocks
takes it to all of them, and the prologue and the epilogue around it meet
the contract (`ends_wp`).

`wholeK_wp`: `wholeK body` meets the contract, for a `body` that enciphers
its block from the round keys in the working space, which a call bitslices
there before the first block (`keysCall_wp`): `body` may count on them, and
leaves them (`BodyOkK`, with `Keys`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore saved mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem savedMem_frame savedMem_slot
  saved_bound saved_ne_r12 saved_eq add0)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_cmp wp_ldrSp cmp0 eval_eq eval_ne)
open VG.Spec.Aes (bytesAt)
open VG.Impl.Aes.Arm (keysCall)
open VG.Proof.Aes (KeysIn)
open VG.Proof.Aes.Arm (KeysArgs KeysPost)

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`
`(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def modeArm (M : Mode) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let iv : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ iv.Disjoint args ∧ data.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint iv ∧ below.Disjoint data ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1))
    let iv := bytesAt s.mem (State.addr (s.gpr .r2)) 16
    let xs := Spec.Cbc.blocksAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
    Spec.Cbc.blocksAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat = M.out (s.gpr .r1).toNat w iv xs ∧
      bytesAt s'.mem (State.addr (s.gpr .r2)) 16 = M.chain (s.gpr .r1).toNat w iv xs
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcArm (enc : Bool) : Contract isa := modeArm (cbcMode enc)

section
variable (s₀ : State)

abbrev Iv : BitVec 32 := s₀.gpr .r2

abbrev ivR : Region := ⟨State.addr (Iv s₀), 16⟩

/-- The blocks on entry. -/
abbrev blks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀)

/-- The chaining value on entry. -/
abbrev iv0 : List Byte := bytesAt s₀.mem (State.addr (Iv s₀)) 16

/-- The address of block `k`. -/
abbrev blk (k : Nat) : Addr := State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, argsR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_args : (ivR s₀).Disjoint (argsR s₀)
  data_args : (dataR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_sch : (belowR s₀).Disjoint (schR s₀)
  b_iv : (belowR s₀).Disjoint (ivR s₀)
  b_data : (belowR s₀).Disjoint (dataR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (Iv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {M : Mode} {s₀ : State} (h : (modeArm M).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩

/-- The key schedule as the mode uses it. -/
abbrev wK (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1))

/-- The first `k` blocks after the mode. -/
abbrev outK (M : Mode) (s₀ : State) (k : Nat) : List (List Byte) :=
  M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The chaining value after the first `k` blocks. -/
abbrev chainK (M : Mode) (s₀ : State) (k : Nat) : List Byte :=
  M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The loop invariant, after `k` blocks. -/
structure LInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 = chainK M s₀ k

/-! ## Addresses and regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega_arith)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : State.addr (Dp s₀ + BitVec.ofNat 32 (16 * k)) = blk s₀ k :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega_arith)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) :
    (Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
    Nat.mod_eq_of_lt (by omega_using [hk, this])]

theorem UPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [this]), addr_add (by omega_using [])]
  simp

theorem UPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

theorem UPre.blk_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.arg_sub {s₀ : State} : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argsR s₀) :=
  Region.sub_prefix (by decide)

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, belowR s₀]

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (State.addr (W s₀)) (16 * (R s₀ + 1)) = bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

/-- The blocks after a step that changed only block `k`, the chaining
value, the first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m') :
    Spec.Cbc.blocksAt m' (State.addr (Dp s₀)) (N s₀) =
      (Spec.Cbc.blocksAt m (State.addr (Dp s₀)) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hj)

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ k by omega_using [hl]), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at this
  show bytesAt s.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj this

end

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hk)]
  rfl

/-! ## The prologue -/

theorem prologue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv M s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega_using [hb], by omega_using [hsc, hb], ⟨scrR s₀, by simp, Offset.contains_base _ (by omega_using [hb]) (by omega_using [hb])⟩⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
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
  have f₀ := savedMem_frame s₀
  have ivS : bytesAt (savedMem s₀) (State.addr (Iv s₀)) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) (State.addr (Dp s₀)) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_scr.sub_left (UPre.data_sub (List.mem_range.mp hj))).sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
  · rw [mm, dataS]
    rw [outK, List.take_zero, M.out_nil, List.drop_zero, List.nil_append]
  · rw [mm, ivS]
    rw [chainK, List.take_zero, M.chain_nil]
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`, and sets
Z if no blocks are left. -/
def BodyOk (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s fun s' => LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)

/-- The loop over `n` blocks, for any invariant `J` that one run of `body`
takes from `k` blocks to `k + 1`, setting Z if none are left. -/
theorem loop_of {J : Nat → State → Prop} {body : Prog isa} {n : Nat}
    (hb : ∀ (k : Nat) (s : State), k < n → J k s →
      WP isa body s fun s' => J (k + 1) s' ∧ s'.z = decide (n - (k + 1) = 0))
    {k : Nat} (hk : k < n) {s : State} (h : J k s) : WP isa (.loop body .ne) s (J n) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := J n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ J j t) ?_ (n - k) s
    ⟨k, rfl, hk, h⟩
  rintro m s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb k s hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (n - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : n - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show n = k + 1 by omega_using [hk, hz']]
  · right
    refine ⟨by rw [ev]; simp [hz'], n - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz'], h'⟩

theorem loop_ok {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) : WP isa (.loop body .ne) s (LInv M s₀ (N s₀)) :=
  loop_of (J := LInv M s₀) (fun _ _ hk h => hb hp hk h) hk h

/-- The blocks, if there are any, by any code `L` that takes the invariant
from no blocks to all of them. -/
theorem mid_of {M : Mode} {L : Prog isa} {s₀ : State} {s₁ : State}
    (hl : 0 < N s₀ → WP isa L s₁ (LInv M s₀ (N s₀)))
    (h : LInv M s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) L) s₁ (LInv M s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hl (by omega_using [hn])

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))
    · exact Offset.disjoint_base _ h₁ (by have := hp.scr_fit; omega_using [h₂])
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega_using [h₂]))) (by decide)

theorem epilogue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega_using [hb], by rw [h.r10]; omega_using [hsc, hb], by rw [h.r10]; exact inS _ (by omega_using [hb])⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show Spec.Cbc.blocksAt s₂.mem (State.addr (Dp s₀)) (N s₀) = _
    rw [m₁, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem (State.addr (Iv s₀)) 16 = _
    rw [m₁, h.iv]; simp only [chainK, hall]

/-- The prologue, the blocks by any code `L` that takes the invariant from
no blocks to all of them, and the epilogue, meet the contract. -/
theorem ends_wp {M : Mode} {L : Prog isa} {s₀ : State} (h0 : (modeArm M).pre s₀)
    (hl : UPre s₀ → 0 < N s₀ → ∀ {s : State}, LInv M s₀ 0 s → WP isa L s (LInv M s₀ (N s₀))) :
    WP isa (.seq (.block (save ++ setup)) (.seq (.ite .eq (.block []) L) (.block restore))) s₀
      fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_of (fun hn => hl hp hn h₁) h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

/-! ## The round keys bitsliced once -/

/-- The round keys of the key schedule on entry are in the working space. -/
abbrev Keys (s₀ : State) (m : Mem) : Prop := KeysIn m (S s₀) (R s₀) (wK s₀)

theorem UPre.rounds_le {s₀ : State} (hp : UPre s₀) : R s₀ ≤ 14 := by
  rcases hp.rounds with h | h | h <;> omega_using [h]

theorem UPre.work_fit {s₀ : State} (hp : UPre s₀) : (S s₀).toNat + 2048 ≤ 2 ^ 32 := by
  have := hp.scr_fit; omega_using [this]

/-- The round keys stay where the memory changes only apart from the working
space. -/
theorem Keys.frame {s₀ : State} (hp : UPre s₀) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr (S s₀), 2048⟩ : Region).Disjoint r) (h : Keys s₀ m) : Keys s₀ m' :=
  Proof.Aes.Arm.Ecb.keysIn_frame hp.work_fit hp.rounds_le hf hd h

/-- The working space is apart from the chaining value, and from a block of
the data. -/
theorem UPre.work_iv {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀], (⟨State.addr (S s₀), 2048⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.iv_scr.sub_right (Region.sub_prefix (by decide))).symm

theorem UPre.work_blk {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) :
    ∀ r ∈ [(⟨blk s₀ k, 16⟩ : Region)], (⟨State.addr (S s₀), 2048⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ((hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))).symm

/-- The round keys at a call: those of the key schedule as the memory then
holds it, which is as on entry. -/
theorem Keys.call {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame (Big s₀) s₀.mem m) (h : Keys s₀ m) :
    KeysIn m (S s₀) (R s₀) (Proof.Aes.Arm.schedAt m (W s₀) (R s₀)) := by
  rw [show Proof.Aes.Arm.schedAt m (W s₀) (R s₀) = wK s₀ from hp.sched_bytes hf]; exact h

/-- The round keys a call leaves are those of the key schedule on entry. -/
theorem Keys.of_call {s₀ : State} (hp : UPre s₀) {m m' : Mem} (hf : Frame (Big s₀) s₀.mem m)
    (h : KeysIn m' (S s₀) (R s₀) (Proof.Aes.Arm.schedAt m (W s₀) (R s₀))) : Keys s₀ m' := by
  rw [show Proof.Aes.Arm.schedAt m (W s₀) (R s₀) = wK s₀ from hp.sched_bytes hf] at h; exact h

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`, and
sets Z if no blocks are left, with the round keys in the working space
before and after. -/
def BodyOkK (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s → Keys s₀ s.mem →
    WP isa body s fun s' => (LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)) ∧ Keys s₀ s'.mem

theorem loopK_ok {M : Mode} {body : Prog isa} (hb : BodyOkK M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) (hkeys : Keys s₀ s.mem) :
    WP isa (.loop body .ne) s (LInv M s₀ (N s₀)) :=
  WP.mono (loop_of (J := fun k s => LInv M s₀ k s ∧ Keys s₀ s.mem)
    (fun _ _ hk h => WP.mono (hb hp hk h.1 h.2) fun _ h' => ⟨⟨h'.1.1, h'.2⟩, h'.1.2⟩) hk ⟨h, hkeys⟩)
    fun _ h => h.1

/-- The blocks of the data are as they were where the memory changes only
apart from them. -/
theorem UPre.blocksAt_frame {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dataR s₀).Disjoint r) :
    Spec.Cbc.blocksAt m' (State.addr (Dp s₀)) (N s₀) = Spec.Cbc.blocksAt m (State.addr (Dp s₀)) (N s₀) := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  exact (hd r hr).sub_left (UPre.data_sub (List.mem_range.mp hj))

/-- The arguments of the call that bitslices the round keys, from the
invariant. -/
theorem LInv.keysArgs {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    KeysArgs s (W s₀) (S s₀) (R s₀) := by
  refine ⟨h.r4, by rw [h.r5]; simp [R], h.r10, hp.rounds, hp.sch_fit, hp.work_fit,
    hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The call that bitslices the round keys keeps the invariant, and leaves
them in the working space. -/
theorem keysCall_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa keysCall s fun s' => LInv M s₀ k s' ∧ Keys s₀ s'.mem := by
  refine WP.mono (Proof.Aes.Arm.keysCall_wp (h.keysArgs hp)) fun s₂ c => ?_
  obtain g : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := c.saved
  obtain work : ∀ {x : Region}, x.Disjoint ⟨State.addr (S s₀), 2048⟩ →
      ∀ r ∈ [(⟨State.addr (S s₀), 2048⟩ : Region)], x.Disjoint r := fun hx r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hx
  refine ⟨⟨by rw [g _ (by simp [preserved]) (by decide), h.r4], by rw [g _ (by simp [preserved]) (by decide), h.r5],
    by rw [g _ (by simp [preserved]) (by decide), h.r6], by rw [g _ (by simp [preserved]) (by decide), h.r7],
    by rw [g _ (by simp [preserved]) (by decide), h.r8], by rw [g _ (by simp [preserved]) (by decide), h.r10],
    by rw [g _ (by simp [preserved]) (by decide), h.r11],
    by rw [c.sp, h.sp], by rw [c.rd, h.rd], by rw [c.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · exact h.frame.trans (c.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩)
  · rw [UPre.blocksAt_frame c.frame (work (hp.data_scr.sub_right (Region.sub_prefix (by decide)))), h.data]
  · rw [Proof.Cmac.bytesAt_frame c.frame (work (hp.iv_scr.sub_right (Region.sub_prefix (by decide))))
      (by decide), h.iv]
  · exact Keys.of_call hp (UPre.big_of h.frame) c.keys

theorem wholeK_wp {M : Mode} {body : Prog isa} (hb : BodyOkK M body) {s₀ : State} (h0 : (modeArm M).pre s₀) :
    WP isa (wholeK body) s₀ fun s' => abiPreserved s₀ s' ∧ (modeArm M).post s₀ s' :=
  ends_wp h0 fun hp hn _ h =>
    WP.seq (WP.mono (keysCall_wp hp h) fun _ h' => loopK_ok hb hp hn h'.1 h'.2)

end VG.Proof.AesCbc.Arm
