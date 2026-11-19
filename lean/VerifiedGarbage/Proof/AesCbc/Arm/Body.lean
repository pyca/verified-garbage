module

public import VerifiedGarbage.Proof.AesOcb.Arm.Callee
public import VerifiedGarbage.Proof.AesCbc.Mem32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
public import VerifiedGarbage.Impl.AesCbc.Arm
public import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `AesCbc.Arm.Loop`, which this module and modules that import it used -/

section

/-!
# AES-CBC on ARMv7: the contracts, and the loop for any mode on whole blocks

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcArm enc`, for encryption
(`enc = true`) and decryption, `modeArm` for CBC (`cbcMode`). Each call of a
block function pushes its stack argument in the 8 bytes below the stack
pointer, which may not overlap any buffer.

The registers are saved, and the arguments kept, as by AES-CMAC's
`vg_cmac_aes_update` (`Proof/CmacAes/Arm/UpdateCorrect.lean`), whose names for
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

end

end

/-!
# AES-CBC on ARMv7: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOkK`, with the round keys in
the working space, and `BodyOk`). The block functions are called as AES-OCB
calls them (`Proof.AesOcb.Arm.blk_call`), in a frame that pushes the working
space; encryption's, from the round keys there (`Proof.Aes.Arm.kblk_call`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem xorBlk zeroBlk xorBlk_ok zeroBlk_ok
  add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call encF decF)
open VG.Proof.Aes (KeysIn)
open VG.Proof.Aes.Arm (schedAt kblk_call)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_add wp_subs ofNat_beq_zero sub_ofNat)
open VG.Spec.Aes (bytesAt)

theorem encFrame_eq : encFrame = blkFrame encF := rfl
theorem decFrame_eq : decFrame = blkFrame decF := rfl

/-- The block `r7` points at, as a 32-bit address. -/
abbrev D32 (s₀ : State) (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 (16 * k)

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := State.addr (S s₀) + BitVec.ofNat 64 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨State.addr (S s₀), 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega_using [])

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.blkCall {k : Nat} (hk : k < N s₀) {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = D32 s₀ k) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 := by
  obtain hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  obtain hd := hp.dataA hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by rw [qN]; omega_using [hk, hdf], by omega_using [hsc], ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hd]; exact hp.sch_data.sub_right (UPre.data_sub hk)
  · rw [hd]; exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  · rw [hb, hd]; exact hp.b_data.sub_right (UPre.data_sub hk)
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hk]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

section
variable {s₀ : State}

theorem covBlk {k : Nat} (hk : k < N s₀) {rs : List Region} (h : dataR s₀ ∈ rs) :
    Covers [⟨blk s₀ k, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dataR s₀, h, 16 * k, rfl, by simp; omega_using [hk]⟩

theorem covIv {rs : List Region} (h : ivR s₀ ∈ rs) : Covers [⟨State.addr (Iv s₀), 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ivR s₀, h, 0, by simp, by simp⟩

theorem covSv {rs : List Region} (h : scrR s₀ ∈ rs) : Covers [⟨Sv s₀, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, h, 2048, rfl, by simp⟩

/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩

/-- A region within those a step may change. -/
theorem stepIn {k : Nat} {r : Region}
    (h : r = ⟨blk s₀ k, 16⟩ ∨ r = ivR s₀ ∨ Region.Sub r ⟨State.addr (S s₀), 2064⟩ ∨ r = belowR s₀) :
    ∃ r' ∈ [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀], Region.Sub r r' := by
  rcases h with rfl | rfl | h | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem bigOf (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hs : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem) {m : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem m) :
    Frame (Big s₀) s₀.mem m :=
  have _ := hp
  UPre.big_of (hs.trans (stepFrame hk hf))

end

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-! ## The arguments of the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s : State) (m : Mem) (s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The registers the invariant pins that the code before the call reads. -/
structure Regs (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r10 : s.gpr .r10 = S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem LInv.regs {M : Mode} {s₀ : State} {k : Nat} {s : State} (h : LInv M s₀ k s) : Regs s₀ k s :=
  ⟨h.r4, h.r5, h.r6, h.r7, h.r10, h.sp, h.rd, h.wr⟩

/-- `Regs` after a step that keeps those registers. -/
theorem Regs.of {s₀ : State} {k : Nat} {s s' : State} (h : Regs s₀ k s)
    (g : ∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) (sp : s'.sp = s.sp) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) : Regs s₀ k s' :=
  ⟨by rw [g _ (by decide) (by decide), h.r4], by rw [g _ (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide), h.r6], by rw [g _ (by decide) (by decide), h.r7],
    by rw [g _ (by decide) (by decide), h.r10], by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr]⟩

theorem callArgs_eq : callArgs = [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r7),
    .mov .r3 (.imm 1), .mov .r12 (.reg .r10)] := rfl

theorem callArgs_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Regs s₀ k s) :
    WP isa (.block callArgs) s (PreA s₀ k s s.mem) := by
  rw [callArgs_eq]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 _ => by
      rw [u₅.other _ h12, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  obtain sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨hp.blkCall hk ?_ ?_ ?_ ?_ ?_ (by rw [sp₅, h.sp]) (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]), keep, sp₅,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      h.r4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      h.r5]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r7]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r10]

/-- What a call leaves, about the registers. -/
theorem post_regs {s₀ : State} {k : Nat} {s s₁ s₂ : State} {m : Mem} (F : BlkFn) (h : Regs s₀ k s)
    (a : PreA s₀ k s m s₁) (c : BlkPost F s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 s₂) : Regs s₀ k s₂ := by
  obtain g : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := fun r hr hlr => by
    rw [c.saved r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hlr
      | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨by rw [g .r4 (by simp [preserved]) (by decide), h.r4], by rw [g .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [g .r6 (by simp [preserved]) (by decide), h.r6], by rw [g .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [g .r10 (by simp [preserved]) (by decide), h.r10], by rw [c.sp, a.sp, h.sp], by rw [c.rd, a.rd, h.rd],
    by rw [c.wr, a.wr, h.wr]⟩

/-- What `advance` leaves after block `k`, and that it keeps the memory. -/
theorem advance_mem {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Regs s₀ k s) (h8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k))
    (h11 : s.gpr .r11 = s₀.gpr .r11)
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem)
    (hd : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK M s₀ (k + 1) ++ (blks s₀).drop (k + 1))
    (hi : bytesAt s.mem (State.addr (Iv s₀)) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s fun s' =>
      (LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)) ∧ s'.mem = s.mem := by
  have hdf := hp.data_fit
  obtain hN := (stackArg s₀ 0).isLt
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  obtain r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by rw [u₃.other _ (by decide), h8]
  obtain dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_using [hk])]; rfl
  obtain g : ∀ r, r ≠ .r7 → r ≠ .r8 → s₄.gpr r = s.gpr r := fun r h7 h8' => by
    rw [u₄.other _ h8', u₃.other _ h7]
  refine ⟨⟨⟨by rw [g _ (by decide) (by decide), h.r4], by rw [g _ (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide), h.r6], ?_, by rw [u₄.gpr, r8₃, dec],
    by rw [g _ (by decide) (by decide), h.r10], by rw [g _ (by decide) (by decide), h11],
    by rw [u₄.sp, u₃.sp, h.sp], by rw [u₄.rd, u₃.rd, h.rd], by rw [u₄.wr, u₃.wr, h.wr],
    by rw [u₄.mem, u₃.mem]; exact hf, by rw [u₄.mem, u₃.mem]; exact hd, by rw [u₄.mem, u₃.mem]; exact hi⟩, ?_⟩,
    by rw [u₄.mem, u₃.mem]⟩
  · rw [u₄.other _ (by decide), u₃.gpr, h.r7, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_using [])]
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega_using [hdf])

/-- What `advance` leaves after block `k`. -/
theorem advance_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Regs s₀ k s) (h8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k))
    (h11 : s.gpr .r11 = s₀.gpr .r11)
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem)
    (hd : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK M s₀ (k + 1) ++ (blks s₀).drop (k + 1))
    (hi : bytesAt s.mem (State.addr (Iv s₀)) 16 = chainK M s₀ (k + 1)) :
    WP isa (.block advance) s fun s' => LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) :=
  WP.mono (advance_mem hp hk h h8 h11 hf hd hi) fun _ h' => h'.1

/-- What `advance` leaves after block `k`, with the round keys. -/
theorem advance_wpK {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Regs s₀ k s) (h8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k))
    (h11 : s.gpr .r11 = s₀.gpr .r11)
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem)
    (hd : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK M s₀ (k + 1) ++ (blks s₀).drop (k + 1))
    (hi : bytesAt s.mem (State.addr (Iv s₀)) 16 = chainK M s₀ (k + 1)) (hkeys : Keys s₀ s.mem) :
    WP isa (.block advance) s fun s' =>
      (LInv M s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)) ∧ Keys s₀ s'.mem :=
  WP.mono (advance_mem hp hk h h8 h11 hf hd hi) fun _ h' => ⟨h'.1, by rw [h'.2]; exact hkeys⟩

/-! ## Moving blocks -/

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) (is : List Instr) :
    xor4 pb qb cb pd qd cd ++ is = xorBlk .r12 .lr pb qb cb pd qd cd ++ is := rfl

theorem zero4_eq (b : Reg) (d : Nat) (is : List Instr) :
    zero4 b d ++ is = .mov .r12 (.imm 0) :: (zeroBlk .r12 b d ++ is) := rfl

/-- What moving a block leaves. -/
structure Moved (s : State) (m : Mem) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- The block at `qb + qd` XORed into the block at `cb + cd`. -/
theorem xorIn_wp {cb qb : Reg} {cd qd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hq : qb ≠ .r12 ∧ qb ≠ .lr) (hc : cb ≠ .r12 ∧ cb ≠ .lr) (hcd : cd + 12 < 4096) (hqd : qd + 12 < 4096)
    (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32) (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Moved s (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr cb) + BitVec.ofNat 64 cd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s' →
      WP isa (.block is) s' Q) :
    WP isa (.block (xor4 cb qb cb cd qd cd ++ is)) s Q := by
  rw [xor4_eq]
  exact xorBlk_ok (by decide) hc.1 hc.2 hq.1 hq.2 hc.1 hc.2 hcd hqd hcd fc fq fc
    (Covers.right wC)
    rQ wC fun s' g => k s' ⟨g.gpr, g.mem, g.rd, g.wr, g.sp⟩

/-- The block at `qb + qd` copied to `cb + cd`, as a zeroed block XORed with it. -/
theorem copy_wp {cb qb : Reg} {cd qd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hq : qb ≠ .r12 ∧ qb ≠ .lr) (hc : cb ≠ .r12 ∧ cb ≠ .lr) (hcd : cd + 12 < 4096) (hqd : qd + 12 < 4096)
    (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32) (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Moved s (copy4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s' → WP isa (.block is) s' Q) :
    WP isa (.block (zero4 cb cd ++ (xor4 cb qb cb cd qd cd ++ is))) s Q := by
  rw [zero4_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have e₁ : ∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r := u₁.other
  refine zeroBlk_ok u₁.gpr hcd (by rw [e₁ _ hc.1]; exact fc)
    (by rw [e₁ _ hc.1, u₁.wr]; exact wC) fun s₂ G₂ m₂ rd₂ wr₂ sp₂ => ?_
  obtain e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h => by rw [G₂, e₁ r h]
  refine xorIn_wp hq hc hcd hqd (by rw [e₂ _ hq.1]; exact fq) (by rw [e₂ _ hc.1]; exact fc)
    (by rw [e₂ _ hq.1, rd₂, wr₂, u₁.rd, u₁.wr]; exact rQ) (by rw [e₂ _ hc.1, wr₂, u₁.wr]; exact wC)
    fun s₃ g₃ => k s₃ ⟨fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁], ?_, by rw [g₃.rd, rd₂, u₁.rd],
      by rw [g₃.wr, wr₂, u₁.wr], by rw [g₃.sp, sp₂, u₁.sp]⟩
  rw [g₃.mem, m₂, e₂ _ hc.1, e₂ _ hq.1, e₁ _ hc.1, u₁.mem]; rfl

/-! ## Encryption -/

theorem encPost_eq : encPost = zero4 .r6 0 ++ (xor4 .r6 .r7 .r6 0 0 0 ++ advance) := rfl

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode true) s₀ k s) :
    WP isa (.block encPre) s
      (PreA s₀ k s (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)))) := by
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  obtain qN := hp.dataN hk
  obtain hd := hp.dataA hk
  obtain rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega_using [hiv])
    (by rw [h.r7, qN]; omega_using [hk, hdf]) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r7, add0, hd, w₀]; exact covBlk hk (by simp)) fun s₁ g₁ => ?_
  obtain m₁ : s₁.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₁.mem, h.r7, h.r6, add0, add0, hd]
  refine WP.mono (callArgs_wp hp hk (h.regs.of g₁.gpr g₁.sp g₁.rd g₁.wr)) fun s₂ a => ?_
  exact ⟨a.pre, fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12 hlr, g₁.gpr r h12 hlr],
    by rw [a.sp, g₁.sp], by rw [a.mem, m₁], by rw [a.rd, g₁.rd], by rw [a.wr, g₁.wr]⟩

/-- A register the code before and after the call keeps. -/
theorem kept {s₀ : State} {k : Nat} {s s₁ s₂ : State} {m : Mem} {F : BlkFn} (a : PreA s₀ k s m s₁)
    (c : BlkPost F s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 s₂) {r : Reg} (hr : r = .r8 ∨ r = .r11) :
    s₂.gpr r = s.gpr r := by
  rcases hr with rfl | rfl
  · rw [c.saved _ (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [c.saved _ (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]

/-- The round keys at the call, after `Pⱼ ⊕ Cⱼ₋₁` in place. -/
theorem encA_keys {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    (h : LInv (cbcMode true) s₀ k s)
    (a : PreA s₀ k s (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀))) s₁)
    (hkeys : Keys s₀ s.mem) : KeysIn s₁.mem (S s₀) (R s₀) (schedAt s₁.mem (W s₀) (R s₀)) := by
  obtain f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  exact Keys.call hp (bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)))
    (Keys.frame hp f₁ (hp.work_blk hk) hkeys)

theorem encBody_ok : BodyOkK (cbcMode true) encBody := by
  intro s₀ hp k hk s h hkeys
  obtain hd := hp.dataA hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (kblk_call a.pre (encA_keys hp hk h a hkeys)) fun s₂ ⟨c, k₂⟩ => ?_)
  obtain rg₂ := post_regs encF h.regs a c
  obtain hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  -- Memory so far.
  obtain f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    obtain fr := c.frame; rw [hb, hd] at fr; exact fr
  obtain fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  obtain rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [encPost_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r7, qN]; omega_using [hk, hdf])
    (by rw [rg₂.r6]; omega_using [hiv]) (by rw [rg₂.r7, add0, hd, rw₂]; exact covBlk hk (by simp))
    (by rw [rg₂.r6, add0, w₂]; exact covIv (by simp)) fun s₃ g₃ => ?_
  obtain m₃ : s₃.mem = copy4Mem s₂.mem (State.addr (Iv s₀)) (blk s₀ k) := by
    rw [g₃.mem, rg₂.r6, rg₂.r7, add0, add0, hd]
  obtain f₃ : Frame [ivR s₀] s₂.mem s₃.mem := by rw [m₃]; exact copy4Mem_frame _ _ _
  obtain fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₃.mem :=
    fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  -- The new block, and the chaining value.
  obtain hblk := h.block hk
  obtain newBlk : bytesAt s₃.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK (cbcMode true) s₀ k))) := by
    rw [Proof.Cmac.bytesAt_frame f₃ (one (hp.blk_iv hk)) (by decide), ← hd, bytesAt_of_statesAt c.out, hd,
      show encF.f = Spec.Aes.cipher from rfl, ← UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      xorIn4_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  obtain newIv : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = bytesAt s₃.mem (blk s₀ k) 16 := by
    rw [m₃, copy4Mem_bytes _ (hp.blk_iv hk).symm,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame s₂.mem (State.addr (Iv s₀)) (blk s₀ k)) (one (hp.blk_iv hk))
        (by decide)]
  obtain hl : (outK (cbcMode true) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain outSucc :
      outK (cbcMode true) s₀ (k + 1) = outK (cbcMode true) s₀ k ++ [bytesAt s₃.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  refine advance_wpK hp hk (rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr)
    (by rw [g₃.gpr _ (by decide) (by decide), kept a c (.inl rfl), h.r8])
    (by rw [g₃.gpr _ (by decide) (by decide), kept a c (.inr rfl), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_ (Keys.frame hp f₃ hp.work_iv (Keys.of_call hp big₁ k₂))
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, ite_true, outSucc, next_snoc]

/-! ## Decryption -/

theorem decPre_eq : decPre = zero4 .r10 2048 ++ (xor4 .r10 .r7 .r10 2048 0 2048 ++ callArgs) := rfl

theorem decPost_eq : decPost =
    xor4 .r7 .r6 .r7 0 0 0 ++ (zero4 .r6 0 ++ (xor4 .r6 .r10 .r6 0 2048 0 ++ advance)) := rfl

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block decPre) s (PreA s₀ k s (copy4Mem s.mem (Sv s₀) (blk s₀ k))) := by
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  obtain qN := hp.dataN hk
  obtain hd := hp.dataA hk
  obtain rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [decPre_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r7, qN]; omega_using [hk, hdf])
    (by rw [h.r10]; omega_using [hsc]) (by rw [h.r7, add0, hd, rw₀]; exact covBlk hk (by simp))
    (by rw [h.r10, w₀]; exact covSv (by simp)) fun s₁ g₁ => ?_
  obtain m₁ : s₁.mem = copy4Mem s.mem (Sv s₀) (blk s₀ k) := by rw [g₁.mem, h.r10, h.r7, add0, hd]
  refine WP.mono (callArgs_wp hp hk (h.regs.of g₁.gpr g₁.sp g₁.rd g₁.wr)) fun s₂ a => ?_
  exact ⟨a.pre, fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12 hlr, g₁.gpr r h12 hlr],
    by rw [a.sp, g₁.sp], by rw [a.mem, m₁], by rw [a.rd, g₁.rd], by rw [a.wr, g₁.wr]⟩

theorem decBody_ok : BodyOk (cbcMode false) decBody := by
  intro s₀ hp k hk s h
  obtain hd := hp.dataA hk
  obtain qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  rw [decFrame_eq]
  refine WP.seq (WP.mono (blk_call decF a.pre) fun s₂ c => ?_)
  obtain rg₂ := post_regs decF h.regs a c
  obtain hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  obtain svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨State.addr (S s₀), 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  obtain f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  obtain f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    obtain fr := c.frame; rw [hb, hd] at fr; exact fr
  obtain fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  obtain rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [decPost_eq]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r6]; omega_using [hiv])
    (by rw [rg₂.r7, qN]; omega_using [hk, hdf]) (by rw [rg₂.r6, add0, rw₂]; exact covIv (by simp))
    (by rw [rg₂.r7, add0, hd, w₂]; exact covBlk hk (by simp)) fun s₃ g₃ => ?_
  obtain m₃ : s₃.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₃.mem, rg₂.r7, rg₂.r6, add0, add0, hd]
  obtain f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain rg₃ := rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr
  obtain w₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₃.wr, hp.wr]
  obtain rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₃.rd, rg₃.wr, hp.rd, hp.wr]; rfl
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₃.r10]; omega_using [hsc])
    (by rw [rg₃.r6]; omega_using [hiv]) (by rw [rg₃.r10, rw₃]; exact covSv (by simp))
    (by rw [rg₃.r6, add0, w₃]; exact covIv (by simp)) fun s₄ g₄ => ?_
  obtain m₄ : s₄.mem = copy4Mem s₃.mem (State.addr (Iv s₀)) (Sv s₀) := by
    rw [g₄.mem, rg₃.r6, rg₃.r10, add0]
  obtain f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  obtain fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₄.mem :=
    (fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  obtain callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  obtain callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
      (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
    · exact (hp.b_scr.sub_right (UPre.scr_sub (by decide))).symm
  obtain hblk := h.block hk
  obtain ivIn : bytesAt s₂.mem (State.addr (Iv s₀)) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
    rfl
  obtain blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), hblk]
  obtain newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide), m₃, xorIn4_bytes _ (hp.blk_iv hk),
      ivIn, ← hd, bytesAt_of_statesAt c.out, hd, show decF.f = Spec.Aes.invCipher from rfl,
      ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  obtain newIv : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [m₄, copy4Mem_bytes _ hp.iv_sv, m₃,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_sv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callSv (by decide), a.mem, copy4Mem_bytes _ (hp.blk_sv hk).symm, hblk]
  obtain hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain outSucc :
      outK (cbcMode false) s₀ (k + 1) = outK (cbcMode false) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  refine advance_wp hp hk (rg₃.of g₄.gpr g₄.sp g₄.rd g₄.wr)
    (by rw [g₄.gpr _ (by decide) (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inl rfl), h.r8])
    (by rw [g₄.gpr _ (by decide) (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inr rfl), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.Arm
