import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesCbc.Arm.Loop
import VerifiedGarbage.Impl.AesCfb8.Arm

/-!
# AES-CFB8 on ARMv7: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8Arm enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/Arm/Loop.lean`), whose stride-free definitions this reuses.

The invariant after `k` bytes (`LInv`): the registers hold the arguments
(`r7` the next byte, `r8` the bytes left), `r11` and the stack pointer are
unchanged, only the input block, the data, the first 2064 bytes of the
scratch buffer and the 8 bytes below the stack pointer have changed since
the registers were saved, the first `k` bytes are CFB8's of the first `k`
bytes on entry and the rest are unchanged, and the input block is the one
after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets Z when none are left (`BodyOk`), `whole body` meets the
contract.
-/

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore saved mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR scrR argsR belowR savedMem savedMem_frame savedMem_slot
  saved_bound saved_ne_r12 saved_eq add0)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_cmp wp_ldrSp cmp0 eval_eq eval_ne)
open VG.Proof.AesCbc.Arm (Iv ivR iv0 wK)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`
`(schedule = r0, rounds = r1, iv = r2, data = r3, len = [sp], scratch = [sp + 4])`. -/
def cfb8Arm (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let iv : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ iv.Disjoint args ∧ data.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint iv ∧ below.Disjoint data ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .r1).toNat
      (bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
    let iv := bytesAt s.mem (State.addr (s.gpr .r2)) 16
    let xs := bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
    bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (State.addr (s.gpr .r2)) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

section
variable (s₀ : State)

abbrev dataR : Region := ⟨State.addr (Dp s₀), N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := State.addr (Dp s₀) + BitVec.ofNat 64 k

/-- The byte `r7` points at, as a 32-bit address. -/
abbrev D32 (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 k

/-- The first `k` bytes after CFB8. -/
abbrev outK (enc : Bool) (k : Nat) : List Byte := cfb8 enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- The input block after the first `k` bytes. -/
abbrev inKk (enc : Bool) (k : Nat) : List Byte := inK enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

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
  data_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8Arm enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  data : bytesAt s.mem (State.addr (Dp s₀)) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 = inKk s₀ enc k

/-! ## Addresses and regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    State.addr (S s₀ + BitVec.ofNat 32 d) = State.addr (S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; have := (S s₀).isLt; omega)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : State.addr (D32 s₀ k) = byt s₀ k :=
  addr_add (by have := hp.data_fit; have := (Dp s₀).isLt; omega)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) : (D32 s₀ k).toNat = (Dp s₀).toNat + k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

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

theorem UPre.byt_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

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
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

/-- The bytes after a step that changed only byte `k`, the input block, the
first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m') :
    bytesAt m' (State.addr (Dp s₀)) (N s₀) = (bytesAt m (State.addr (Dp s₀)) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := Proof.Cmac.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hj)

end

theorem length_bs (s₀ : State) : (bs s₀).length = N s₀ := by simp [bytesAt]

/-- Byte `k` before the step, from the invariant. -/
theorem LInv.byte {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    s.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem (by simp [bytesAt]; exact hk),
    List.getElem?_eq_getElem (by rw [length_bs]; exact hk)] at this
  simpa [bytesAt] using Option.some.inj this

theorem take_succ_bs (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (bs s₀).take (k + 1) = (bs s₀).take k ++ [(bs s₀)[k]'(by rw [length_bs]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk)]
  rfl

/-! ## The prologue -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s => LInv enc s₀ 0 s ∧ s.z = decide (N s₀ = 0) := by
  have hsc := hp.scr_fit
  rw [show save ++ setup = .ldrSp .r12 4 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++ setup) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
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
  have dataS : bytesAt (savedMem s₀) (State.addr (Dp s₀)) (N s₀) = bs s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.data_scr.sub_right (Region.sub_prefix (by decide))) (by have := hp.data_fit; omega)
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
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  · rw [mm, ivS]
    simp only [inKk, List.take_zero, inK_nil]
  · rw [z₉, show s₈.gpr .r8 = s₉.gpr .r8 from (congrFun f₉.gpr _).symm, r8, a0]
    exact cmp0 (stackArg s₀ 0).isLt

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
Z if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0)

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega) h

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by have := hp.scr_fit; omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv enc s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (cfb8Arm enc).post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega, by rw [h.r10]; omega, by rw [h.r10]; exact inS _ (by omega)⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show bytesAt s₂.mem (State.addr (Dp s₀)) (N s₀) = _
    rw [m₁, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem (State.addr (Iv s₀)) 16 = _
    rw [m₁, h.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8Arm enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => abiPreserved s₀ s' ∧ (cfb8Arm enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.Arm
