module

public import VerifiedGarbage.Impl.AesCfb8.X86
public import VerifiedGarbage.Proof.AesCbc.X86.Groups
public import VerifiedGarbage.Proof.AesCfb8.Rounds
public import VerifiedGarbage.Proof.AesCfb8.Spec
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Impl.AesCfb8.X86
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

-- separate module: built beside encryption's proof, with which it shares nothing

/-!
# CFB8 decryption around a block function, on x86 (32-bit)

`Impl.AesCfb8.X86.decrypt`, 64 bytes a call, for any implementation of the
block function, meets `Spec.Cfb8.aesDecryptContract` (`decrypt_verified`).

As for CBC and CFB128 (`Proof/AesCbc/X86/Groups.lean`), from whose proof the
names of the arguments, the rules of the instructions and the group's size
are. The data is stated a byte at a time (`DataIs`), as a function of the
byte's index: byte `j` is deciphered with input block `j`, `inp j`, the one
before it shifted left by a byte, with the ciphertext byte shifted in
(`inp_succ`). Between groups the first `k` bytes are the plaintext, the rest
are unchanged and the block at `iv` is input block `k` (`GInv`). In a group of
`m` bytes from byte `k`: `buf` is filled with its input blocks (`FInv`), the
block function is called on it (`Mid`), and the first byte of each block is
XORed into the data (`XInv`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.X86.Groups

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCfb8.X86.Groups
open VG.Impl.AesCbc.X86.Groups (saved setup restore size fillPre bufFrame)
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.CmacAes.X86 (wp_arg arg_ofNat ea_at' ofNat_and_self_beq wp_xor)
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_addi wp_cmpi wp_test wp_sub wp_subi wp_movzx8 wp_store8 eval_e
  eval_ne eval_b)
open VG.Proof.AesXts.X86 (bx bytesAt_bx bytesAt_writeW_bx)
open VG.Proof.AesOcb.X86 (BCall BPost)
open VG.Proof.AesGcm.X86 (w64)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Cfb8 (next)
open VG.Proof.AesCbc.X86.Groups (gE gW gR gIv gD gN gS gB schR ivR scrR bufR blkR argsR retR stkR bA b32 gK svMem
  svMem_frame svMem_buf stk_eq addr0 bA_disj buf_sub1 blk_buf inBuf saved_fits saved_bound saved_ne_eax wp_movX wp_argX
  wp_addiX wp_subiX setup_eq restore_eq gm gm_le gm_fit gm_pos n_lt ofNat_toNat_lt wp_load wp_storeX add_b32 left1
  out_block Pt arg_cur taint_rel setup_taint restore_taint)

/-! ## The mode -/

/-- A plaintext byte, from the input block for it. -/
theorem getElem?_decrypt (ciph : Spec.Cbc.Cipher) {iv : List Byte} (hv : iv ≠ []) (xs : List Byte) (k : Nat)
    (h : k < xs.length) :
    (Spec.Cfb8.decrypt ciph iv xs)[k]? = some (xs[k] ^^^ (ciph (next iv (xs.take k))).headD 0) := by
  induction xs generalizing iv k with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases k with
    | zero => simp [Spec.Cfb8.decrypt, next_nil]
    | succ k =>
      have hk : k < xs.length := by simpa using h
      simp only [Spec.Cfb8.decrypt, List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons,
        next_cons hv]
      exact ih (by simp) k hk

/-- The register the next input block is in, shifted left by a byte (its
first byte is the least significant), with `c` shifted in. -/
theorem bx_shift (x : BitVec 128) (c : Byte) :
    bx (x >>> 8 ||| ((0 : BitVec 96) ++ c.setWidth 32) <<< 120) = (bx x).tail ++ [c] := by
  apply List.ext_getElem (by simp [bx])
  intro i h₁ _
  have hi : i < 16 := by simpa [bx] using h₁
  simp only [bx, List.getElem_map, List.getElem_range, List.getElem_append, List.length_tail, List.length_map,
    List.length_range, List.getElem_tail, List.getElem_singleton]
  split
  · ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    have : 8 * i + j < 120 := by omega
    simp only [this, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
    congr 1; omega
  · have hi' : i = 15 := by omega
    subst hi'
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    rw [BitVec.getLsbD_of_ge x _ (by omega)]
    simp only [show 8 * 15 + j < 128 by omega, show ¬ 8 * 15 + j < 120 by omega, decide_true, decide_false,
      Bool.not_false, Bool.true_and, Bool.false_or, show 8 * 15 + j - 120 = j by omega, BitVec.getLsbD_append,
      show j < 32 by omega, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_eq_getElem hj]

/-! ## The contract -/

/-- `groups` `(schedule, rounds, iv, data, len, scratch, buf)`. -/
def groupsX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let buf : Region := ⟨(arg s 6).setWidth 64, 1040⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr, buf] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint buf ∧ iv.Disjoint args ∧
      data.Disjoint scr ∧ data.Disjoint buf ∧ data.Disjoint args ∧
      scr.Disjoint buf ∧ scr.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint buf ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      stack.Disjoint buf ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 1040 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (arg s 1).toNat
      (bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    let iv := bytesAt s.mem ((arg s 2).setWidth 64) 16
    let xs := bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = Spec.Cfb8.decrypt ciph iv xs ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = next iv xs
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-! ## The data, by name -/

section
variable (s₀ : State)

abbrev dataR : Region := ⟨(gD s₀).setWidth 64, gN s₀⟩

/-- The address of byte `k` of the data. -/
abbrev dA (k : Nat) : Addr := (gD s₀).setWidth 64 + BitVec.ofNat 64 k
abbrev d32 (k : Nat) : BitVec 32 := gD s₀ + BitVec.ofNat 32 k

/-- Ciphertext byte `k`, the input block on entry, and the ciphertext. -/
abbrev ct (k : Nat) : Byte := s₀.mem (dA s₀ k)
abbrev iv0 : List Byte := bytesAt s₀.mem ((gIv s₀).setWidth 64) 16
abbrev bs : List Byte := bytesAt s₀.mem ((gD s₀).setWidth 64) (gN s₀)

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (gR s₀) (gK s₀)

/-- Input block `k`, and plaintext byte `k`. -/
def inp (k : Nat) : List Byte := next (iv0 s₀) ((bs s₀).take k)
def pt (k : Nat) : Byte := ct s₀ k ^^^ (ciph s₀ (inp s₀ k)).headD 0

/-- The regions the function writes, with the stack below it. -/
abbrev Big : List Region := [ivR s₀, dataR s₀, scrR s₀, bufR s₀, stkR s₀]

/-- What the groups change. -/
abbrev Mut : List Region := [ivR s₀, dataR s₀, scrR s₀, blkR s₀, stkR s₀]

end

theorem iv0_ne (s₀ : State) : iv0 s₀ ≠ [] := by
  intro h; have := congrArg List.length h; simp [bytesAt] at this

theorem length_bs (s₀ : State) : (bs s₀).length = gN s₀ := by simp [bytesAt]

theorem getElem_bs (s₀ : State) {k : Nat} (hk : k < gN s₀) : (bs s₀)[k]'(by rw [length_bs]; exact hk) = ct s₀ k := by
  simp [bytesAt]

theorem inp_zero (s₀ : State) : inp s₀ 0 = iv0 s₀ := by rw [inp, List.take_zero, next_nil]

theorem inp_succ (s₀ : State) {k : Nat} (hk : k < gN s₀) : inp s₀ (k + 1) = (inp s₀ k).tail ++ [ct s₀ k] := by
  rw [inp, inp, List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk), getElem_bs s₀ hk,
    Option.toList_some, next_snoc (iv0_ne s₀)]

/-- The data, byte by byte. -/
def DataIs (s₀ : State) (m : Mem) (g : Nat → Byte) : Prop := ∀ j < gN s₀, m (dA s₀ j) = g j

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := Proof.Cmac.bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

/-- The precondition, by name. -/
structure GPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, argsR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀, bufR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  sch_buf : (schR s₀).Disjoint (bufR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  iv_buf : (ivR s₀).Disjoint (bufR s₀)
  iv_args : (ivR s₀).Disjoint (argsR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  data_buf : (dataR s₀).Disjoint (bufR s₀)
  data_args : (dataR s₀).Disjoint (argsR s₀)
  scr_buf : (scrR s₀).Disjoint (bufR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  buf_args : (bufR s₀).Disjoint (argsR s₀)
  ret_iv : (retR s₀).Disjoint (ivR s₀)
  ret_data : (retR s₀).Disjoint (dataR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  ret_buf : (retR s₀).Disjoint (bufR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_iv : (stkR s₀).Disjoint (ivR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  stk_buf : (stkR s₀).Disjoint (bufR s₀)
  sch_fit : (gW s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (gIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (gD s₀).toNat + gN s₀ ≤ 2 ^ 32
  scr_fit : (gS s₀).toNat + 2176 ≤ 2 ^ 32
  buf_fit : (gB s₀).toNat + 1040 ≤ 2 ^ 32
  esp24 : 24 ≤ (gE s₀).toNat
  esp_fit : (gE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : gR s₀ = 10 ∨ gR s₀ = 12 ∨ gR s₀ = 14

theorem GPre.of {s₀ : State} (h : groupsX86.pre s₀) : GPre s₀ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33⟩ := h
  obtain e := stk_eq a31
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    e ▸ a21, e ▸ a22, e ▸ a23, e ▸ a24, e ▸ a25, a26, a27, a28, a29, a30, a31, a32, a33⟩

/-! ## Addresses and regions -/

section
variable {s₀ : State} (hp : GPre s₀)
include hp

theorem GPre.argA {i : Nat} (hi : i < 7) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_using [hi, this]), addr_eq (by omega_using [this]), Offset.add_add]

theorem GPre.arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_using [hi])

theorem GPre.arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem GPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  obtain e : argAddr s₀ 0 = (gE s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [this])
  rw [stk_eq hp.esp24]
  show Region.Disjoint ⟨argAddr s₀ 0, 28⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

theorem GPre.ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  rw [stk_eq hp.esp24]
  have := Offset.disjoint_below_above ((gE s₀).setWidth 64) (m := 24) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  exact this.symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem GPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.scr_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.buf_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

/-- The return address is unchanged where only `Big` changes. -/
theorem GPre.ret_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    m.readW ((gE s₀).setWidth 64) 32 = s₀.mem.readW ((gE s₀).setWidth 64) 32 :=
  hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_buf
    · exact hp.ret_stk) (by decide)

theorem GPre.sched_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m ((gW s₀).setWidth 64) (16 * (gR s₀ + 1)) = gK s₀ := by
  have hR : 16 * (gR s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.sch_buf.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

theorem GPre.d32_addr {k : Nat} (hk : k < gN s₀) : (d32 s₀ k).setWidth 64 = dA s₀ k := by
  have := hp.data_fit
  exact addr_eq (x := gD s₀) (k := k) (by omega_using [hk, this])

theorem GPre.b32_addr {j : Nat} (hj : j < 64) : (b32 s₀ j).setWidth 64 = bA s₀ j := by
  have := hp.buf_fit
  exact addr_eq (x := gB s₀) (k := 16 * j) (by omega_using [hj, this])

theorem GPre.dA_disj {i j : Nat} (hi : i < gN s₀) (hj : j < gN s₀) (hij : i ≠ j) :
    (⟨dA s₀ i, 1⟩ : Region).Disjoint ⟨dA s₀ j, 1⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hij]) (by omega_using [hi, this]) (by omega_using [hj, this])

omit hp in
theorem data_sub1 {k : Nat} (h : k < gN s₀) : Region.Sub ⟨dA s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [h])

omit hp in
theorem inData {k : Nat} (h : k < gN s₀) {rs : List Region} (hr : dataR s₀ ∈ rs) : InRegions rs (dA s₀ k) 1 :=
  ⟨dataR s₀, hr, Offset.contains_base _ (by omega_using [h])
    (by have hN : gN s₀ < 2 ^ 32 := (arg s₀ 4).isLt; omega_using [h, hN])⟩

end

theorem big_of {s₀ : State} {m : Mem} (hf : Frame (Mut s₀) (svMem s₀) m) : Frame (Big s₀) s₀.mem m :=
  ((svMem_buf s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨bufR s₀, by simp, blk_buf⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-! ## The invariant between groups -/

/-- After `k` blocks: `P` is the mode's plaintext, block by block. -/
structure GInv (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ gN s₀
  esi : s.gpr .esi = d32 s₀ k
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k then pt s₀ j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = inp s₀ k

theorem setup_wp {s₀ : State} (hp : GPre s₀) :
    WP isa (.block setup) s₀ fun s => GInv s₀ 0 s ∧ s.zf = some (decide (gN s₀ = 0)) := by
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = gB s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; exact hp.buf_fit) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨bufR s₀, by simp, Offset.contains_base _ hb.2 (by omega_using [hb])⟩
  obtain hm₂ : s₂.mem = svMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, svMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  obtain big := big_of (Frame.refl (Mut s₀) (svMem s₀))
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep big (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep big (by decide)) fun s₄ u₄ => ?_
  obtain one : ∀ {a : Addr}, (⟨a, 16⟩ : Region).Disjoint (bufR s₀) →
      bytesAt (svMem s₀) a 16 = bytesAt s₀.mem a 16 := fun hd =>
    Proof.Cmac.bytesAt_frame16 (svMem_buf s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr]; exact (BitVec.add_zero _).symm
  · rw [f₅.gpr, u₄.gpr, Nat.sub_zero]; exact arg_ofNat s₀ 4
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · intro j hj
    rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
    show _ = if j < 0 then pt s₀ j else ct s₀ j
    rw [ite_eq_right (Nat.not_lt_zero _)]
    exact byte_frame (svMem_buf s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.data_buf.sub_left (data_sub1 hj)
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, inp_zero]; exact one hp.iv_buf
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

/-- The registers restored. -/
theorem restore_wp {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State}
    (h : GInv s₀ k s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  obtain big := big_of h.frame
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hs : Spill.Saved s.mem ((gB s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved :=
    (Spill.saveMem_saved_ofNat s₀.mem _ s₀.gpr saved_fits (by decide)).of_frame
      (R := ⟨(gB s₀).setWidth 64 + BitVec.ofNat 64 1024, 16⟩) h.frame
      (fun p hp' => by
        have := saved_bound p hp'
        exact Offset.contains _ this.1 (by omega_using [this]) (by decide))
      fun r hr => by
        have sub : Region.Sub ⟨(gB s₀).setWidth 64 + BitVec.ofNat 64 1024, 16⟩ (bufR s₀) :=
          Offset.sub_base _ (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hp.iv_buf.symm.sub_left sub
        · exact hp.data_buf.symm.sub_left sub
        · exact hp.scr_buf.symm.sub_left sub
        · exact Offset.disjoint_base _ (Nat.le_refl _) (by decide)
        · exact hp.stk_buf.symm.sub_left sub
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; exact hp.buf_fit) saved_ne_eax
    (fun p hp' => ?_) (by rw [u₁.gpr, u₁.mem]; exact hs) fun s₂ r₂ => WP.block_nil ?_
  · have := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, hrw, hp.rd, hp.wr]
    exact ⟨bufR s₀, by simp, Offset.contains_base _ this.2 (by omega_using [this])⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  rw [r₂.mem, u₁.mem]; exact hp.ret_keep big

/-! ## A group: its size, and `buf` filled -/

theorem GInv.of_eq {s₀ : State} {k : Nat} {s s' : State} (h : GInv s₀ k s)
    (esi : s'.gpr .esi = s.gpr .esi) (edi : s'.gpr .edi = s.gpr .edi) (esp : s'.gpr .esp = s.gpr .esp)
    (mem : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : GInv s₀ k s' :=
  ⟨h.le, by rw [esi, h.esi], by rw [edi, h.edi], by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [mem]; exact h.frame, by rw [mem]; exact h.data, by rw [mem]; exact h.iv⟩

theorem size_wp {s₀ : State} {k : Nat} {s : State}
    (h : GInv s₀ k s) :
    WP isa size s fun s' => GInv s₀ k s' ∧ s'.gpr .ebx = BitVec.ofNat 32 (gm s₀ k) := by
  have hN := n_lt s₀
  refine WP.seq (wp_movi fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_)
  obtain e : s₂.gpr .edi = BitVec.ofNat 32 (gN s₀ - k) := by rw [f₂.gpr, u₁.other _ (by decide), h.edi]
  obtain h₂ : GInv s₀ k s₂ := h.of_eq (by rw [f₂.gpr, u₁.other _ (by decide)])
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem])
    (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr])
  obtain ev : isa.eval .b s₂ = some (decide (gN s₀ - k < 64)) := by
    show s₂.cf = _
    rw [c₂, u₁.other _ (by decide), h.edi, ofNat_toNat_lt (by omega_using [hN])]
    rfl
  by_cases hm : gN s₀ - k < 64
  · refine WP.ite true (by rw [ev]; simp [hm]) (fun _ => ?_) (fun h => by cases h)
    refine wp_mov fun s₃ u₃ => WP.block_nil ⟨h₂.of_eq (u₃.other _ (by decide)) (u₃.other _ (by decide))
      (u₃.other _ (by decide)) u₃.mem u₃.rd u₃.wr, ?_⟩
    rw [u₃.gpr, e, gm, Nat.min_eq_right (by omega_using [hm])]
  · refine WP.ite false (by rw [ev]; simp [hm]) (fun h => by cases h) (fun _ => WP.block_nil ⟨h₂, ?_⟩)
    rw [f₂.gpr, u₁.gpr, gm, Nat.min_eq_left (by omega_using [hm])]; rfl

/-- The group's first `i` blocks of `buf` are filled. -/
structure FInv (s₀ : State) (k i : Nat) (s : State) : Prop where
  g : GInv s₀ k s
  ebx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)
  eax : s.gpr .eax = d32 s₀ (k + i)
  edx : s.gpr .edx = b32 s₀ i
  ecx : s.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i)
  x0 : bx (s.xmm .xmm0) = inp s₀ (k + i)
  buf : ∀ j < i, bytesAt s.mem (bA s₀ j) 16 = inp s₀ (k + j)

theorem fillPre_wp {s₀ : State} (hp : GPre s₀) {k : Nat}
    {s : State} (h : GInv s₀ k s) (hbx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)) :
    WP isa (.block fillPre) s (FInv s₀ k 0) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := big_of h.frame
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  refine wp_load (A := (gIv s₀).setWidth 64) (by rw [u₁.gpr]) (by
    rw [u₁.rd, u₁.wr, hrw, hp.rd, hp.wr]
    exact ⟨ivR s₀, by simp, Region.contains_self _ _⟩) ?_
  generalize hs₂ : s₁.setXmm .xmm0 (s₁.mem.readW ((gIv s₀).setWidth 64) 128) = s₂
  obtain g₂ : s₂.gpr = s₁.gpr := by rw [← hs₂, gpr_setXmm]
  obtain m₂ : s₂.mem = s.mem := by rw [← hs₂, mem_setXmm, u₁.mem]
  obtain rd₂ : s₂.rd = s.rd := by rw [← hs₂, rd_setXmm, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [← hs₂, wr_setXmm, u₁.wr]
  obtain x₂ : bx (s₂.xmm .xmm0) = inp s₀ k := by
    rw [← hs₂, xmm_setXmm_self, u₁.mem, ← bytesAt_bx, h.iv]
  refine wp_movX fun s₃ u₃ x₃ => ?_
  refine wp_argX (s₀ := s₀) (by rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.esp])
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, hrw]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, m₂]; exact hp.arg_keep big (by decide)) fun s₄ u₄ x₄ => wp_movX fun s₅ u₅ x₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r ha hc hd hb => by
    rw [u₅.other _ hc, u₄.other _ hd, u₃.other _ ha, g₂, u₁.other _ hb]
  refine ⟨h.of_eq (keep _ (by decide) (by decide) (by decide) (by decide))
    (keep _ (by decide) (by decide) (by decide) (by decide)) (keep _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, m₂]) (by rw [u₅.rd, u₄.rd, u₃.rd, rd₂]) (by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]),
    ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), hbx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), h.esi]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr]; exact (BitVec.add_zero _).symm
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hbx]; rfl
  · rw [x₅, x₄, x₃, x₂]; rfl

/-- A change of `buf`'s blocks alone. -/
theorem GInv.buf {s₀ : State} (hp : GPre s₀) {k : Nat} {s s' : State}
    (h : GInv s₀ k s) (esi : s'.gpr .esi = s.gpr .esi) (edi : s'.gpr .edi = s.gpr .edi)
    (esp : s'.gpr .esp = s.gpr .esp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (hf : Frame [blkR s₀] s.mem s'.mem) :
    GInv s₀ k s' := by
  refine ⟨h.le, by rw [esi, h.esi], by rw [edi, h.edi], by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr],
    h.frame.trans (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]), fun j hj => ?_, ?_⟩
  · rw [byte_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_buf.sub_left (data_sub1 hj)).sub_right blk_buf]
    exact h.data j hj
  · rw [Proof.Cmac.bytesAt_frame16 hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_buf.sub_right blk_buf]
    exact h.iv

/-! ## Bytes, one instruction at a time, keeping the SSE registers -/

theorem wp_byteX {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {A : Addr}
    (ha : (s.gpr b).setWidth 64 = A) (hin : InRegions (s.rd ++ s.wr) A 1)
    (k : ∀ s', Upd s s' d ((s.mem A).setWidth 32) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b 0) :: is)) s Q :=
  MdStream.X86.WP.cons (s' := s.setReg d ((s.mem A).setWidth 32))
    (by simp only [exec, State.load8, ea_at', addr0, ha, hin, ↓reduceIte, Option.map_some])
    (k _ (MdStream.X86.Upd.setReg _ _ _) (xmm_setReg _ _ _))

theorem wp_byteStore {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {A : Addr}
    (ha : (s.gpr b).setWidth 64 = A) (hout : InRegions s.wr A 1)
    (k : WP isa (.block is) { s with mem := s.mem.writeW A ((s.gpr .eax).setWidth 8) } Q) :
    WP isa (.block (.store8 (at_ b 0) .al :: is)) s Q :=
  MdStream.X86.WP.cons (by simp only [exec, State.store8, ea_at', addr0, ha, hout, ↓reduceIte, Reg8.reg]) k

/-! ## `buf` filled -/

/-- The shift of the input block, and the ciphertext byte in. -/
def step : List Instr :=
  [.xop (.movd .xmm1 .ebp), .xop (.shift .psrldq .xmm0 1), .xop (.shift .pslldq .xmm1 15),
   .xop (.bin .por .xmm0 .xmm1)]

theorem step_ok (s : State) : ∃ s', runBlock isa step s = some s' ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧
    s'.xmm .xmm0 = (s.xmm .xmm0 >>> 8 ||| ((0 : BitVec 96) ++ s.gpr .ebp) <<< 120) := by
  refine ⟨_, by
    simp only [step, runBlock_cons, runStep_some, runBlock_nil, exec]
    rfl, ?_⟩
  refine ⟨by rfl, by rfl, by rfl, by rfl, ?_⟩
  simp only [XOp.exec, XBinOp.eval, XShiftOp.eval, xmm_setXmm_self, xmm_setXmm_of_ne, reduceCtorEq,
    not_false_eq_true]
  rfl

theorem fillBody_eq : fillBody = .movdquStore (at_ .edx 0) .xmm0 :: .movzx8 .ebp (at_ .eax 0) :: (step ++
    ([.alu .add .eax (.imm 1), .alu .add .edx (.imm 16), .alu .sub .ecx (.imm 1)] : List Instr)) := rfl

theorem add_d32 (s₀ : State) (k : Nat) : d32 s₀ k + 1 = d32 s₀ (k + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, d32, d32, Offset.add_add_eq _ (c := k + 1) (by omega_using [])]

theorem fillBody_wp {s₀ : State} (hp : GPre s₀) {k i : Nat} (hk : k < gN s₀) (hi : i < gm s₀ k) {s : State}
    (h : FInv s₀ k i s) :
    WP isa (.block fillBody) s fun s' => FInv s₀ k (i + 1) s' ∧ s'.zf = some (decide (i + 1 = gm s₀ k)) := by
  have hm := gm_le s₀ k
  have hf := gm_fit hk
  have hi64 : i < 64 := by omega_using [hi, hm]
  have hki : k + i < gN s₀ := by omega_using [hi, hf]
  rw [fillBody_eq]
  refine wp_storeX (A := bA s₀ i) (by rw [h.edx]; exact hp.b32_addr hi64)
    (by rw [h.g.wr, hp.wr]; exact inBuf hi64 (by simp)) ?_
  generalize hs₁ : ({ s with mem := s.mem.writeW (bA s₀ i) (s.xmm .xmm0) } : State) = s₁
  obtain g₁ : s₁.gpr = s.gpr := by rw [← hs₁]
  obtain m₁ : s₁.mem = s.mem.writeW (bA s₀ i) (s.xmm .xmm0) := by rw [← hs₁]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁]
  obtain x₁ : s₁.xmm .xmm0 = s.xmm .xmm0 := by rw [← hs₁]
  obtain f₁ : Frame [⟨bA s₀ i, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain G₁ : GInv s₀ k s₁ := h.g.buf hp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨blkR s₀, by simp, buf_sub1 hi64⟩)
  refine wp_byteX (A := dA s₀ (k + i)) (by rw [g₁, h.eax]; exact hp.d32_addr hki)
    (by rw [G₁.rd, G₁.wr, hp.rd, hp.wr]; exact inData hki (by simp)) fun s₂ u₂ x₂ => ?_
  obtain b₂ : s₂.gpr .ebp = (ct s₀ (k + i)).setWidth 32 := by
    rw [u₂.gpr, G₁.data _ hki]
    show BitVec.setWidth 32 (if k + i < k then _ else _) = _
    rw [ite_eq_right (by omega_using [])]
  obtain ⟨s₃, run₃, g₃, m₃, rd₃, wr₃, x₃⟩ := step_ok s₂
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain X₃ : bx (s₃.xmm .xmm0) = inp s₀ (k + (i + 1)) := by
    rw [x₃, b₂, bx_shift, x₂, x₁, h.x0, ← Nat.add_assoc, inp_succ s₀ hki]
  refine wp_addiX fun s₄ u₄ x₄ => wp_addiX fun s₅ u₅ x₅ => wp_subiX fun s₆ u₆ x₆ z₆ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₆.gpr r = s.gpr r := fun r ha hc hd hb => by
    rw [u₆.other _ hc, u₅.other _ hd, u₄.other _ ha, g₃, u₂.other _ hb, g₁]
  obtain m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem]
  obtain c₅ : s₅.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide), g₁, h.ecx]
  obtain ⟨l₁, l₂⟩ := left1 hm hi
  refine ⟨⟨G₁.of_eq (by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₁])
      (by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₁])
      (by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₁]) m₆
      (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr]), ?_, ?_, ?_, ?_, ?_,
      fun j hj => ?_⟩, ?_⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃, u₂.other _ (by decide), g₁, h.eax, add_d32]; rfl
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide), g₁, h.edx, add_b32]
  · rw [u₆.gpr, c₅, l₁]
  · rw [x₆, x₅, x₄, X₃]
  · rw [m₆]
    by_cases hji : j = i
    · subst hji
      rw [m₁, bytesAt_writeW_bx, h.x0]
    · rw [Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact bA_disj (by omega_using [hj, hi64]) hi64 hji]
      exact h.buf j (by omega_using [hj, hji])
  · rw [z₆, c₅, l₂]

theorem fillLoop_wp {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀)
    {s : State} (h : FInv s₀ k 0 s) : WP isa (.loop (.block fillBody) .ne) s (FInv s₀ k (gm s₀ k)) := by
  refine WP.loop (M := isa) (body := .block fillBody) (c := .ne) (Q := FInv s₀ k (gm s₀ k))
    (fun (n : Nat) (t : State) => ∃ i, n = gm s₀ k - i ∧ i < gm s₀ k ∧ FInv s₀ k i t) ?_ (gm s₀ k - 0) s
    ⟨0, rfl, gm_pos hk, h⟩
  rintro n t ⟨i, rfl, hi, h⟩
  refine WP.mono (fillBody_wp hp hk hi h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (i + 1 = gm s₀ k) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases he : i + 1 = gm s₀ k
  · left
    refine ⟨by rw [ev]; simp [he], ?_⟩
    rwa [← he]
  · right
    refine ⟨by rw [ev]; simp [he], gm s₀ k - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], h'⟩

/-! ## The call -/

/-- Before the call: `buf` is filled, and the block at `iv` the next group's
input block. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  bc : BCall s (gW s₀) (gB s₀) (gS s₀) (gR s₀) (gm s₀ k)
  esi : s.gpr .esi = d32 s₀ k
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k then pt s₀ j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = inp s₀ (k + gm s₀ k)
  buf : ∀ j < gm s₀ k, bytesAt s.mem (bA s₀ j) 16 = inp s₀ (k + j)

theorem callArgs_wp {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State} (h : FInv s₀ k (gm s₀ k) s) :
    WP isa (.block callArgs) s (Mid s₀ k) := by
  have hm := gm_le s₀ k
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.g.rd, h.g.wr]
  refine wp_argX (s₀ := s₀) h.g.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (big_of h.g.frame) (by decide)) fun sa ua xa => ?_
  refine wp_storeX (A := (gIv s₀).setWidth 64) (by rw [ua.gpr])
    (by rw [ua.wr, h.g.wr, hp.wr]; exact ⟨ivR s₀, by simp, Region.contains_self _ _⟩) ?_
  generalize hs₁ : ({ sa with mem := sa.mem.writeW ((gIv s₀).setWidth 64) (sa.xmm .xmm0) } : State) = s₁
  obtain g₁ : s₁.gpr = sa.gpr := by rw [← hs₁]
  obtain m₁ : s₁.mem = s.mem.writeW ((gIv s₀).setWidth 64) (s.xmm .xmm0) := by rw [← hs₁, ← ua.mem, ← xa]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁, ← ua.rd]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁, ← ua.wr]
  obtain e₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [g₁, ua.other _ (by decide), h.g.esp]
  obtain f₁ : Frame [ivR s₀] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain F₁ : Frame (Mut s₀) (svMem s₀) s₁.mem :=
    h.g.frame.trans (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  obtain big := big_of F₁
  obtain hrw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [rd₁, wr₁, hrw]
  refine wp_arg (s₀ := s₀) e₁ (by rw [hrw₁]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide)) (by rw [u₂.mem]; exact hp.arg_keep big (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, u₂.mem]; exact hp.arg_keep big (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem]; exact hp.arg_keep big (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r ha hc hd hb => by
    rw [u₅.other _ hb, u₄.other _ hd, u₃.other _ hc, u₂.other _ ha, g₁, ua.other _ hb]
  obtain m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.g.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.g.wr]
  obtain esp₅ : s₅.gpr .esp = gE s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.esp]
  obtain scS : Region.Sub ⟨(gS s₀).setWidth 64, 2048⟩ (scrR s₀) := Region.sub_prefix (by decide)
  obtain buS : Region.Sub ⟨(gB s₀).setWidth 64, 16 * gm s₀ k⟩ (bufR s₀) := Region.sub_prefix (by omega_using [hm])
  have hsc := hp.scr_fit
  have hb := hp.buf_fit
  refine ⟨⟨?_, ?_, ?_, ?_, u₅.gpr, hp.rounds, by rw [esp₅]; exact hp.esp24, hp.sch_buf.sub_right buS,
    hp.sch_scr.sub_right scS, (hp.scr_buf.sub_left scS).symm.sub_left buS, by rw [esp₅]; exact hp.stk_sch,
    by rw [esp₅]; exact hp.stk_buf.sub_right buS, by rw [esp₅]; exact hp.stk_scr.sub_right scS, hp.sch_fit,
    by omega_using [hb, hm], by omega_using [hsc], ?_, ?_⟩,
    ?_, ?_, esp₅, rd₅, wr₅, by rw [m₅]; exact F₁, fun j hj => ?_, ?_, fun j hj => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact arg_ofNat s₀ 1
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [rd₅, wr₅, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₅, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨bufR s₀, by simp, 0, (BitVec.add_zero _).symm, by show 0 + 16 * gm s₀ k ≤ 1040; omega_using [hm]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.esi]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.edi]
  · rw [m₅, byte_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.iv_data.sub_right (data_sub1 hj)).symm]
    exact h.g.data j hj
  · rw [m₅, m₁, bytesAt_writeW_bx, h.x0]
  · rw [m₅, Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.iv_buf.sub_right blk_buf).sub_right (buf_sub1 (Nat.lt_of_lt_of_le hj (gm_le _ _)))).symm]
    exact h.buf j hj

theorem fill_wp {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State} (h : GInv s₀ k s) :
    WP isa fill s (Mid s₀ k) :=
  WP.seq (WP.mono (size_wp h) fun _ ⟨h₁, b₁⟩ =>
    WP.seq (WP.mono (fillPre_wp hp h₁ b₁) fun _ h₂ =>
      WP.seq (WP.mono (fillLoop_wp hp hk h₂) fun _ h₃ => callArgs_wp hp h₃)))

/-- After the call, with `i` of the group's bytes XORed. -/
structure XInv (s₀ : State) (k i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = d32 s₀ (k + i)
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  ebx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k + i then pt s₀ j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = inp s₀ (k + gm s₀ k)
  buf : ∀ j < gm s₀ k, s.mem (bA s₀ j) = (ciph s₀ (inp s₀ (k + j))).headD 0

theorem call_wp (v : BlocksImpl) {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State} (h : Mid s₀ k s) :
    WP isa (Impl.AesOcb.X86.blocksFrame ⟨v.enc.name, v.enc.code⟩) s (XInv s₀ k 0) := by
  refine WP.mono (AesOcb.X86.blk_call (fn := ⟨v.enc.name, v.enc.code⟩) v.encOk v.encNosp v.encStack h.bc)
    fun s' c => ?_
  have hm := gm_le s₀ k
  obtain fr : Frame [⟨(gB s₀).setWidth 64, 16 * gm s₀ k⟩, ⟨(gS s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s'.mem := by
    have := c.frame
    rw [h.esp] at this
    exact this
  obtain scS : Region.Sub ⟨(gS s₀).setWidth 64, 2048⟩ (scrR s₀) := Region.sub_prefix (by decide)
  obtain buS : Region.Sub ⟨(gB s₀).setWidth 64, 16 * gm s₀ k⟩ (bufR s₀) := Region.sub_prefix (by omega_using [hm])
  obtain sched : bytesAt s.mem (w64 (gW s₀)) (16 * (gR s₀ + 1)) = gK s₀ := hp.sched_keep (big_of h.frame)
  obtain out := c.out
  rw [sched] at out
  refine ⟨by rw [c.saved .esi (by simp [calleeSaved]), h.esi]; rfl, by rw [c.saved .edi (by simp [calleeSaved]), h.edi],
    by rw [c.saved .ebx (by simp [calleeSaved]), h.bc.ebx], by rw [c.saved .esp (by simp [calleeSaved]), h.esp],
    by rw [c.rd, h.rd], by rw [c.wr, h.wr], h.frame.trans (fr.sub fun r hr => ?_), fun j hj => ?_, ?_,
    fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨blkR s₀, by simp, Region.sub_prefix (by omega_using [hm])⟩
    · exact ⟨scrR s₀, by simp, scS⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [byte_frame fr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.data_buf.sub_left (data_sub1 hj)).sub_right buS
      · exact (hp.data_scr.sub_left (data_sub1 hj)).sub_right scS
      · exact hp.stk_data.symm.sub_left (data_sub1 hj)]
    exact h.data j hj
  · rw [Proof.Cmac.bytesAt_frame16 fr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_buf.sub_right buS
      · exact hp.iv_scr.sub_right scS
      · exact hp.stk_iv.symm, h.iv]
  · have o := out_block (fun m p => (AesCbc.aesWith_state (gR s₀) (gK s₀) m p).symm) out hj
    rw [show w64 (gB s₀) + BitVec.ofNat 64 (16 * j) = bA s₀ j from rfl, h.buf j hj] at o
    rw [← headD_bytesAt s'.mem (bA s₀ j), o]

/-! ## `buf` XORed into the data -/

/-- `XInv` in the loop. -/
structure LInv (s₀ : State) (k i : Nat) (s : State) : Prop where
  x : XInv s₀ k i s
  edx : s.gpr .edx = b32 s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (gm s₀ k - i)

theorem xorPre_wp {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State} (h : XInv s₀ k 0 s) :
    WP isa (.block xorPre) s (LInv s₀ k 0) := by
  refine wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.arg_keep (big_of h.frame) (by decide)) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .edx → r ≠ .ebp → s₂.gpr r = s.gpr r := fun r hd hb => by rw [u₂.other _ hb, u₁.other _ hd]
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨by rw [keep _ (by decide) (by decide), h.esi], by rw [keep _ (by decide) (by decide), h.edi],
    by rw [keep _ (by decide) (by decide), h.ebx], by rw [keep _ (by decide) (by decide), h.esp],
    by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], by rw [m₂]; exact h.frame, by rw [m₂]; exact h.data,
    by rw [m₂]; exact h.iv, by rw [m₂]; exact h.buf⟩, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr]; exact (BitVec.add_zero _).symm
  · rw [u₂.gpr, u₁.other _ (by decide), h.ebx]; rfl

theorem low_xor (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem xorBody_wp {s₀ : State} (hp : GPre s₀) {k i : Nat} (hk : k < gN s₀) (hi : i < gm s₀ k) {s : State}
    (h : LInv s₀ k i s) :
    WP isa (.block xorBody) s fun s' => LInv s₀ k (i + 1) s' ∧ s'.zf = some (decide (i + 1 = gm s₀ k)) := by
  have hm := gm_le s₀ k
  have hf := gm_fit hk
  have hi64 : i < 64 := by omega_using [hi, hm]
  have hki : k + i < gN s₀ := by omega_using [hi, hf]
  obtain ad : (s.gpr .esi).setWidth 64 = dA s₀ (k + i) := by rw [h.x.esi]; exact hp.d32_addr hki
  obtain ab : (s.gpr .edx).setWidth 64 = bA s₀ i := by rw [h.edx]; exact hp.b32_addr hi64
  obtain rin : InRegions (s.rd ++ s.wr) (dA s₀ (k + i)) 1 := by
    rw [h.x.rd, h.x.wr, hp.rd, hp.wr]; exact inData hki (by simp)
  obtain bin : InRegions (s.rd ++ s.wr) (bA s₀ i) 1 := by
    rw [h.x.rd, h.x.wr, hp.rd, hp.wr]
    exact ⟨bufR s₀, by simp, Offset.contains_base _ (by omega_using [hi64]) (by omega_using [hi64])⟩
  obtain win : InRegions s.wr (dA s₀ (k + i)) 1 := by rw [h.x.wr, hp.wr]; exact inData hki (by simp)
  obtain dold : s.mem (dA s₀ (k + i)) = ct s₀ (k + i) := by
    rw [h.x.data _ hki]
    show (if k + i < k + i then _ else _) = _
    rw [ite_eq_right (Nat.lt_irrefl _)]
  obtain bold : s.mem (bA s₀ i) = (ciph s₀ (inp s₀ (k + i))).headD 0 := h.x.buf i hi
  refine wp_byteX ad rin fun s₁ u₁ _ => ?_
  refine wp_byteX (A := bA s₀ i) (by rw [u₁.other _ (by decide), ab]) (by rw [u₁.rd, u₁.wr]; exact bin) fun s₂ u₂ _ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  obtain v₃ : (s₃.gpr .eax).setWidth 8 = pt s₀ (k + i) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, low_xor, dold, bold]; rfl
  refine wp_byteStore (A := dA s₀ (k + i))
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ad])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact win) ?_
  rw [v₃]
  generalize hs₄ : ({ s₃ with mem := s₃.mem.writeW (dA s₀ (k + i)) (pt s₀ (k + i)) } : State) = s₄
  obtain g₄ : s₄.gpr = s₃.gpr := by rw [← hs₄]
  obtain m₄ : s₄.mem = s.mem.writeW (dA s₀ (k + i)) (pt s₀ (k + i)) := by rw [← hs₄, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₄ : s₄.rd = s.rd := by rw [← hs₄, ← u₁.rd, ← u₂.rd, ← u₃.rd]
  obtain wr₄ : s₄.wr = s.wr := by rw [← hs₄, ← u₁.wr, ← u₂.wr, ← u₃.wr]
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ z₇ => WP.block_nil ?_
  obtain f₄ : Frame [⟨dA s₀ (k + i), 1⟩] s.mem s₄.mem := by
    rw [m₄]
    exact (Frame.refl _ _).writeW (r := ⟨_, 1⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain m₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s₇.gpr r = s.gpr r :=
    fun r ha hc hd hs hb => by
      rw [u₇.other _ hb, u₆.other _ hd, u₅.other _ hs, g₄, u₃.other _ ha, u₂.other _ hc, u₁.other _ ha]
  obtain c₆ : s₆.gpr .ebp = BitVec.ofNat 32 (gm s₀ k - i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.ebp]
  obtain ⟨l₁, l₂⟩ := left1 hm hi
  refine ⟨⟨⟨?_, by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x.edi],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x.ebx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x.esp],
      by rw [u₇.rd, u₆.rd, u₅.rd, rd₄, h.x.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, wr₄, h.x.wr], ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩, ?_, by rw [u₇.gpr, c₆, l₁]⟩,
    by rw [z₇, c₆, l₂]⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.x.esi, add_d32]; rfl
  · rw [m₇]
    exact h.x.frame.trans (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, data_sub1 hki⟩)
  · rw [m₇]
    show _ = if j < k + (i + 1) then _ else _
    by_cases hji : j = k + i
    · subst hji
      rw [ite_eq_left (by omega_using []), m₄, writeW8_apply, BitVec.sub_self]
      simp
    · rw [byte_frame f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dA_disj hj hki hji, h.x.data j hj]
      show (if j < k + i then _ else _) = _
      by_cases h₁ : j < k + i
      · rw [ite_eq_left h₁, ite_eq_left (by omega_using [h₁])]
      · rw [ite_eq_right h₁, ite_eq_right (show ¬ j < k + (i + 1) by omega_using [h₁, hji])]
  · rw [m₇, Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.sub_right (data_sub1 hki), h.x.iv]
  · rw [m₇, byte_frame f₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (((hp.data_buf.sub_left (data_sub1 hki)).sub_right blk_buf).sub_right
        fun a ha => buf_sub1 (Nat.lt_of_lt_of_le hj hm) a (Region.sub_prefix (by decide) a ha)).symm, h.x.buf j hj]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx, add_b32]

theorem xorLoop_wp {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State} (h : LInv s₀ k 0 s) :
    WP isa (.loop (.block xorBody) .ne) s (LInv s₀ k (gm s₀ k)) := by
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne) (Q := LInv s₀ k (gm s₀ k))
    (fun (n : Nat) (t : State) => ∃ i, n = gm s₀ k - i ∧ i < gm s₀ k ∧ LInv s₀ k i t) ?_ (gm s₀ k - 0) s
    ⟨0, rfl, gm_pos hk, h⟩
  rintro n t ⟨i, rfl, hi, h⟩
  refine WP.mono (xorBody_wp hp hk hi h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (i + 1 = gm s₀ k) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases he : i + 1 = gm s₀ k
  · left
    refine ⟨by rw [ev]; simp [he], ?_⟩
    rwa [← he]
  · right
    refine ⟨by rw [ev]; simp [he], gm s₀ k - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], h'⟩

/-- After the group: ZF set if no blocks are left. -/
abbrev Next (s₀ : State) (k : Nat) (s : State) : Prop :=
  GInv s₀ (k + gm s₀ k) s ∧ s.zf = some (decide (k + gm s₀ k = gN s₀))

theorem finish_wp {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State}
    (h : XInv s₀ k 0 s) : WP isa finish s (Next s₀ k) := by
  have hN := n_lt s₀
  have hfit := gm_fit hk
  have hm := gm_le s₀ k
  refine WP.seq (WP.mono (xorPre_wp hp h) fun s₁ h₁ => WP.seq (WP.mono (xorLoop_wp hp hk h₁) fun s₂ h₂ => ?_))
  refine wp_sub fun s₃ u₃ z₃ => WP.block_nil ?_
  obtain e : BitVec.ofNat 32 (gN s₀ - k) - BitVec.ofNat 32 (gm s₀ k) = BitVec.ofNat 32 (gN s₀ - (k + gm s₀ k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_toNat_lt (show gm s₀ k < 2 ^ 32 by omega_using [hm]),
      ofNat_toNat_lt (show gN s₀ - k < 2 ^ 32 by omega_using [hN]),
      ofNat_toNat_lt (show gN s₀ - (k + gm s₀ k) < 2 ^ 32 by omega_using [hN])]
    omega_using [hN, hfit, hm]
  refine ⟨⟨hfit, by rw [u₃.other _ (by decide), h₂.x.esi], by rw [u₃.gpr, h₂.x.edi, h₂.x.ebx, e],
    by rw [u₃.other _ (by decide), h₂.x.esp], by rw [u₃.rd, h₂.x.rd], by rw [u₃.wr, h₂.x.wr],
    by rw [u₃.mem]; exact h₂.x.frame, fun j hj => by rw [u₃.mem, h₂.x.data j hj], by rw [u₃.mem, h₂.x.iv]⟩, ?_⟩
  rw [z₃, h₂.x.edi, h₂.x.ebx, e, MdStream.X86.ofNat_beq_zero (show gN s₀ - (k + gm s₀ k) < 2 ^ 32 by omega_using [hN])]
  exact congrArg some (decide_eq_decide.mpr (by omega_using [hfit]))

/-! ## The whole function -/

theorem body_wp (v : BlocksImpl) {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State}
    (h : GInv s₀ k s) : WP isa (body v.enc) s (Next s₀ k) :=
  WP.seq (WP.mono (fill_wp hp hk h) fun _ h₁ =>
    WP.seq (WP.mono (call_wp v hp h₁) fun _ h₂ => finish_wp hp hk h₂))

theorem loop_wp (v : BlocksImpl) {s₀ : State} (hp : GPre s₀) (hn : 0 < gN s₀) {s : State} (h : GInv s₀ 0 s) :
    WP isa (.loop (body v.enc) .ne) s (GInv s₀ (gN s₀)) := by
  refine WP.loop (M := isa) (body := body v.enc) (c := .ne) (Q := GInv s₀ (gN s₀))
    (fun (n : Nat) (t : State) => ∃ k, n = gN s₀ - k ∧ k < gN s₀ ∧ GInv s₀ k t) ?_ (gN s₀ - 0) s
    ⟨0, rfl, hn, h⟩
  rintro n t ⟨k, rfl, hk, h⟩
  refine WP.mono (body_wp v hp hk h) fun s' ⟨h', hz⟩ => ?_
  have hm := gm_pos hk
  have hf := gm_fit hk
  obtain ev : isa.eval .ne s' = some !decide (k + gm s₀ k = gN s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases he : k + gm s₀ k = gN s₀
  · left
    refine ⟨by rw [ev]; simp [he], ?_⟩
    rwa [he] at h'
  · right
    refine ⟨by rw [ev]; simp [he], gN s₀ - (k + gm s₀ k), by omega_using [hk, hm], k + gm s₀ k, rfl,
      by omega_using [hf, he], h'⟩

theorem mid_wp (v : BlocksImpl) {s₀ : State} (hp : GPre s₀) {s : State} (h : GInv s₀ 0 s)
    (hz : s.zf = some (decide (gN s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body v.enc) .ne)) s (GInv s₀ (gN s₀)) := by
  obtain ev : isa.eval .e s = some (decide (gN s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, hz]
  by_cases hn : gN s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · exact WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ =>
      loop_wp v hp (Nat.pos_of_ne_zero hn) h

/-- The contract's postcondition, from the invariant after all the bytes. -/
theorem post_of {s₀ s s' : State} (h : GInv s₀ (gN s₀) s) (hm : s'.mem = s.mem) : groupsX86.post s₀ s' := by
  refine ⟨?_, ?_⟩
  · show bytesAt s'.mem ((gD s₀).setWidth 64) (gN s₀) = Spec.Cfb8.decrypt (ciph s₀) (iv0 s₀) (bs s₀)
    refine List.ext_getElem? fun j => ?_
    by_cases hj : j < gN s₀
    · rw [getElem?_decrypt _ (iv0_ne s₀) _ _ (by rw [length_bs]; exact hj), getElem_bs s₀ hj,
        List.getElem?_eq_getElem (by simp only [bytesAt, List.length_map, List.length_range]; exact hj)]
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [hm]
      refine congrArg some ((h.data j hj).trans ?_)
      show (if j < gN s₀ then pt s₀ j else _) = _
      rw [ite_eq_left hj]
      rfl
    · rw [List.getElem?_eq_none (by simp only [bytesAt, List.length_map, List.length_range]; exact Nat.le_of_not_lt hj),
        List.getElem?_eq_none (by rw [length_decrypt, length_bs]; exact Nat.le_of_not_lt hj)]
  · show bytesAt s'.mem ((gIv s₀).setWidth 64) 16 = next (iv0 s₀) (bs s₀)
    rw [hm, h.iv, inp, List.take_of_length_le (by rw [length_bs])]

theorem groups_correct (v : BlocksImpl) (s : State) (hs : groupsX86.pre s) :
    ∃ t s', Exec isa (groups v.enc) s t s' ∧ abiPreserved s s' ∧ groupsX86.post s s' := by
  obtain hp := GPre.of hs
  show WP isa (groups v.enc) s fun s' => abiPreserved s s' ∧ groupsX86.post s s'
  exact WP.seq (WP.mono (setup_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp v hp h₁ z₁) fun s₂ h₂ =>
      WP.mono (restore_wp hp h₂) fun s₃ ⟨a, m⟩ => ⟨a, post_of h₂ m⟩))

/-! ## Constant time -/

theorem GPre.argsOut {s₀ : State} (hp : GPre s₀) {s : State} (h : Pt s₀ s) : ArgsOut 7 s := by
  have hs := hp.esp_fit
  refine ⟨by rw [h.esp]; omega_using [hs], ?_⟩
  rw [h.wr, hp.wr, h.esp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 28) (by omega_using [hs]) hp.ret_iv hp.iv_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega_using [hs]) hp.ret_data hp.data_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega_using [hs]) hp.ret_scr hp.scr_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega_using [hs]) hp.ret_buf hp.buf_args.symm

theorem fill_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 7)) fill h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem finish_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi, .ebx] (4 + 4 * 7)) finish h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem GInv.pt {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State} (h : GInv s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

theorem XInv.pt {s₀ : State} (hp : GPre s₀) {k i : Nat} {s : State} (h : XInv s₀ k i s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

section
variable {s₀ s₀' : State} (hq : groupsX86.pub s₀ s₀')
include hq

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem agree (hp : GPre s₀) (hp' : GPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, gE, gE, hq.1]) (hp.argsOut h₁) (hp'.argsOut h₂)
    fun i hi => by rw [arg_cur h₁.esp (h₁.args i hi), arg_cur h₂.esp (h₂.args i hi), hq.2 i hi]

theorem pub_E : gE s₀ = gE s₀' := hq.1
theorem pub_W : gW s₀ = gW s₀' := hq.2 0 (by decide)
theorem pub_R : gR s₀ = gR s₀' := by rw [gR, gR, hq.2 1 (by decide)]
theorem pub_D : gD s₀ = gD s₀' := hq.2 3 (by decide)
theorem pub_N : gN s₀ = gN s₀' := by rw [gN, gN, hq.2 4 (by decide)]
theorem pub_S : gS s₀ = gS s₀' := hq.2 5 (by decide)
theorem pub_B : gB s₀ = gB s₀' := hq.2 6 (by decide)
theorem pub_d32 (k : Nat) : d32 s₀ k = d32 s₀' k := by rw [d32, d32, pub_D hq]
theorem pub_gm (k : Nat) : gm s₀ k = gm s₀' k := by rw [gm, gm, pub_N hq]

variable (v : BlocksImpl) (hp : GPre s₀) (hp' : GPre s₀')
include hp hp'

/-- One group, in two runs. -/
theorem body_rel {k : Nat} (hk : k < gN s₀) :
    RelCT isa (fun a b => GInv s₀ k a ∧ GInv s₀' k b) (body v.enc) fun a b => Next s₀ k a ∧ Next s₀' k b := by
  have hk' : k < gN s₀' := by rw [← pub_N hq]; exact hk
  have a := taint_rel [.esi, .edi] fill_taint (P := fun a b => GInv s₀ k a ∧ GInv s₀' k b)
    (fun _ _ h => agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.esi, h.2.esi, pub_d32 hq]
      · rw [h.1.edi, h.2.edi, pub_N hq])
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h => ⟨fill_wp hp hk h.1, fill_wp hp' hk' h.2⟩
  have c := (RelCT.mono (AesOcb.X86.blk_ct (fn := ⟨v.enc.name, v.enc.code⟩) v.encOk v.encCt
      (I := fun s => BCall s (gW s₀) (gB s₀) (gS s₀) (gR s₀) (gm s₀ k) ∧ s.gpr .esp = gE s₀)
      fun _ h => h)
      (P' := fun a b => Mid s₀ k a ∧ Mid s₀' k b)
      (fun _ _ h => ⟨⟨h.1.bc, h.1.esp⟩, by
        rw [pub_W hq, pub_B hq, pub_S hq, pub_R hq, pub_gm hq, pub_E hq]; exact ⟨h.2.bc, h.2.esp⟩⟩)
      fun _ _ _ => trivial).wp
    (F₁ := XInv s₀ k 0) (F₂ := XInv s₀' k 0) fun _ _ h => ⟨call_wp v hp h.1, call_wp v hp' h.2⟩
  have d := taint_rel [.esi, .edi, .ebx] finish_taint (P := fun a b => XInv s₀ k 0 a ∧ XInv s₀' k 0 b)
    (fun _ _ h => agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.esi, h.2.esi, pub_d32 hq]
      · rw [h.1.edi, h.2.edi, pub_N hq]
      · rw [h.1.ebx, h.2.ebx, pub_gm hq])
    (F₁ := Next s₀ k) (F₂ := Next s₀' k) fun _ _ h => ⟨finish_wp hp hk h.1, finish_wp hp' hk' h.2⟩
  exact a.seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq d)

/-- The groups, in two runs. -/
theorem loop_rel (hn : 0 < gN s₀) :
    RelCT isa (fun a b => GInv s₀ 0 a ∧ GInv s₀' 0 b) (.loop (body v.enc) .ne)
      fun a b => GInv s₀ (gN s₀) a ∧ GInv s₀' (gN s₀') b := by
  have hN := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop := ∃ k, n = gN s₀ - k ∧ k < gN s₀ ∧ GInv s₀ k s₁ ∧ GInv s₀' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (gN s₀ - 0)).mono
    (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hc : n = gN s₀ - k ∧ k < gN s₀
  swap
  · exact RelCT.of_false fun _ _ h => hc ⟨h.1, h.2.1⟩
  obtain ⟨rfl, hk⟩ := hc
  refine (body_rel hq v hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
    fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  have hm := gm_pos hk
  have hf := gm_fit hk
  obtain e₁ : isa.eval .ne s₁ = some !decide (k + gm s₀ k = gN s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  obtain e₂ : isa.eval .ne s₂ = some !decide (k + gm s₀ k = gN s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN, ← pub_gm hq]; rfl
  refine ⟨by rw [e₁, e₂], fun hf' => ?_, fun ht => ?_⟩
  · rw [e₁] at hf'
    obtain h0 : k + gm s₀ k = gN s₀ := by simpa using hf'
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0, pub_gm hq]; exact l₂⟩
  · rw [e₁] at ht
    obtain h0 : k + gm s₀ k ≠ gN s₀ := by simpa using ht
    exact ⟨gN s₀ - (k + gm s₀ k), by omega_using [hk, hm], k + gm s₀ k, rfl, by omega_using [hf, h0], l₁,
      by rw [pub_gm hq]; exact l₂⟩

theorem groups_rel : RelCT isa (fun x y => x = s₀ ∧ y = s₀') (groups v.enc) fun _ _ => True := by
  have hN := pub_N hq
  obtain pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := taint_rel [] setup_taint (P := fun x y => x = s₀ ∧ y = s₀')
    (fun x y h => by
      obtain ⟨rfl, rfl⟩ := h
      exact agree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (F₁ := fun (s : State) => GInv s₀ 0 s ∧ s.zf = some (decide (gN s₀ = 0)))
    (F₂ := fun (s : State) => GInv s₀' 0 s ∧ s.zf = some (decide (gN s₀' = 0)))
    fun x y h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨setup_wp hp, setup_wp hp'⟩
  have c : RelCT isa (fun x y => (GInv s₀ 0 x ∧ x.zf = some (decide (gN s₀ = 0))) ∧
      GInv s₀' 0 y ∧ y.zf = some (decide (gN s₀' = 0)))
      (.ite .e (.block []) (.loop (body v.enc) .ne))
      fun x y => GInv s₀ (gN s₀) x ∧ GInv s₀' (gN s₀') y := by
    refine RelCT.ite (fun x y h => ?_) ?_ ?_
    · show x.zf = y.zf; rw [h.1.2, h.2.2, hN]
    · refine RelCT.block_nil fun x y h => ?_
      obtain h0 : gN s₀ = 0 := by
        have := h.2; change x.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨h0 ▸ h.1.1.1, by rw [← hN, h0]; exact h.1.2.1⟩
    · refine (RelCT.exists_ fun (hn : 0 < gN s₀) => loop_rel hq v hp hp' hn).mono
        (fun x y h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; change x.zf = _ at this; rw [h.1.1.2] at this
      have : gN s₀ ≠ 0 := by simpa using this
      omega_using [this]
  obtain ⟨_, t₃⟩ := restore_taint
  have d := RelCT.taint (A := sseTaint)
    (P := fun x y => GInv s₀ (gN s₀) x ∧ GInv s₀' (gN s₀') y) _
    (fun _ _ h => agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₃
  exact a.seq (c.seq d)

end

theorem groups_ct (v : BlocksImpl) : ConstantTime isa groupsX86.pre groupsX86.pub (groups v.enc) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (groups_rel hq v (GPre.of h₁) (GPre.of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified`, and with `buf` on the stack -/

open VG.Proof.AesEcb (agree_of bytesAt_congr n_le)

/-- The contracts' precondition. -/
def pre (pb : Nat) : Curry (Spec.Cfb8.aesSig.words pb) (Mem → Prop) := fun _schedule rounds _iv _data _len _scratch _ =>
  rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- Decryption's postcondition, for the key schedule it is given and 10, 12 or
14 rounds (so that it reads only the schedule's 240 bytes). -/
def post (pb : Nat) : Spec.Cfb8.aesSig.Post pb := fun schedule rounds iv data len _scratch m m' _ =>
  (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    bytesAt m' data len.toNat = Spec.Cfb8.decrypt
        (Spec.Cbc.aesWith rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1))))
        (bytesAt m iv 16) (bytesAt m data len.toNat) ∧
      bytesAt m' iv 16 = next (bytesAt m iv 16) (bytesAt m data len.toNat)

/-- The contract the frame needs: `buf`, 1040 bytes, as a seventh argument,
and 24 bytes of stack (the block function's arguments and return address). -/
abbrev groupsContract : Contract isa :=
  Sig.scratchContract X86.abi Spec.Cfb8.aesSig "buf" .u64 130 (pre X86.abi.ptrBits) (post X86.abi.ptrBits) false 24

open VG.Proof.AesCbc.X86.Groups (sat)

theorem groups_implies : groupsX86.Implies groupsContract := by
  obtain a0 : arg sat 0 = 0x1000 := by decide
  obtain a1 : arg sat 1 = 10 := by decide
  obtain a2 : arg sat 2 = 0x2000 := by decide
  obtain a3 : arg sat 3 = 0x3000 := by decide
  obtain a4 : arg sat 4 = 0 := by decide
  obtain a5 : arg sat 5 = 0x4000 := by decide
  obtain a6 : arg sat 6 = 0x5000 := by decide
  obtain e : argAddr sat 0 = 0x8004 := by decide
  have esp : sat.gpr .esp = 0x8000 := rfl
  exact {
    pre := by
      sig_implies_pre [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cfb8.aesSig, pre, post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
    post := by
      intro s s' _ h
      sig_post [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cfb8.aesSig, pre, post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
      exact fun _ => h
    pub := by
      sig_implies_pub [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cfb8.aesSig, pre, post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
    sat := by
      sig_implies_sat [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cfb8.aesSig, pre, post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
        [a0, a1, a2, a3, a4, a5, a6, e, esp] using sat }

/-- The arguments, six words. -/
theorem vs_eq {pb : Nat} {vs : List (BitVec 64)} (h : vs.length = (Spec.Cfb8.aesSig.words pb).length) :
    ∃ a b c d e f, vs = [a, b, c, d, e, f] := AesCbc.Wipe.vs_eq (pb := pb) h

theorem bufs_eq {a b c d e f : BitVec 64} :
    Sig.bufs Spec.Cfb8.aesSig.params [a, b, c, d, e, f] =
      [(⟨a, 240⟩, false), (⟨c, 16⟩, true), (⟨d, e.toNat * 1⟩, true), (⟨f, 2176⟩, true)] :=
  rfl

theorem pre_local (pb : Nat) : ∀ vs (m₁ m₂ : Mem), vs.length = (Spec.Cfb8.aesSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Cfb8.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Cfb8.aesSig.words pb) (pre pb) vs m₁ →
      Curry.apply (Spec.Cfb8.aesSig.words pb) (pre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, _, rfl⟩ := vs_eq hlen
  exact h

/-- `post` reads the memory on entry only within the buffers. -/
theorem post_local (pb : Nat) :
    ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cfb8.aesSig.words pb).length →
      (∀ b ∈ Sig.bufs Spec.Cfb8.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cfb8.aesSig.words pb) (post pb) vs m₁ m' x →
        Curry.apply (Spec.Cfb8.aesSig.words pb) (post pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2.2.1
  intro hr
  have es : bytesAt m₂ a (16 * ((b.setWidth pb).toNat + 1)) = bytesAt m₁ a (16 * ((b.setWidth pb).toNat + 1)) :=
    bytesAt_congr fun i hi => hs i (by
      have hr' : (b.setWidth pb).toNat = 10 ∨ (b.setWidth pb).toNat = 12 ∨ (b.setWidth pb).toNat = 14 := hr
      rcases hr' with h | h | h <;> omega_using [h, hi])
  have ed : bytesAt m₂ d (e.setWidth pb).toNat = bytesAt m₁ d (e.setWidth pb).toNat :=
    bytesAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  have ec : bytesAt m₂ c 16 = bytesAt m₁ c 16 := bytesAt_congr (agree_of hb.2.1)
  have h1 := h hr
  show bytesAt m' d (e.setWidth pb).toNat = Spec.Cfb8.decrypt
      (Spec.Cbc.aesWith (b.setWidth pb).toNat (bytesAt m₂ a (16 * ((b.setWidth pb).toNat + 1))))
      (bytesAt m₂ c 16) (bytesAt m₂ d (e.setWidth pb).toNat) ∧
    bytesAt m' c 16 = next (bytesAt m₂ c 16) (bytesAt m₂ d (e.setWidth pb).toNat)
  rw [es, ec, ed]
  exact h1

/-- `post` reads the memory on return only within the buffers. -/
theorem post_localOut (pb : Nat) :
    ∀ vs m m₁ m₂ x, vs.length = (Spec.Cfb8.aesSig.words pb).length →
      (∀ b ∈ Sig.bufs Spec.Cfb8.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cfb8.aesSig.words pb) (post pb) vs m m₁ x →
        Curry.apply (Spec.Cfb8.aesSig.words pb) (post pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have hd := agree_of hb.2.2.1
  intro hr
  have ed : bytesAt m₂ d (e.setWidth pb).toNat = bytesAt m₁ d (e.setWidth pb).toNat :=
    bytesAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  have ec : bytesAt m₂ c 16 = bytesAt m₁ c 16 := bytesAt_congr (agree_of hb.2.1)
  have h1 := h hr
  show bytesAt m₂ d (e.setWidth pb).toNat = Spec.Cfb8.decrypt
      (Spec.Cbc.aesWith (b.setWidth pb).toNat (bytesAt m a (16 * ((b.setWidth pb).toNat + 1))))
      (bytesAt m c 16) (bytesAt m d (e.setWidth pb).toNat) ∧
    bytesAt m₂ c 16 = next (bytesAt m c 16) (bytesAt m d (e.setWidth pb).toNat)
  rw [ec, ed]
  exact h1

/-! ## The code's properties -/

theorem groups_noSp (b : Impl.Aes.X86.Blocks) (h : NoSp b.code) : NoSp (groups b) := by
  refine NoSp.of_all ?_
  have hb : b.code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    simp [h i hi]
  simp only [groups, body, Impl.AesOcb.X86.blocksFrame, Code.allInstrs, hb]
  decide +kernel

theorem groups_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) : stackUse (groups b) ≤ 24 := by
  simp only [groups, body, Impl.AesOcb.X86.blocksFrame, stackUse, h]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCfb8.X86.decrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.AesCfb8.X86.decrypt, Impl.StackScratch.X86.withStackScratch, groups, body,
    Impl.AesOcb.X86.blocksFrame, Code.all, v.encSpSafe]
  decide +kernel

theorem frameSat_pre (post : Spec.Cfb8.aesSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cfb8.aesSig.contract X86.abi (pre := pre X86.abi.ptrBits) (post := post) (stack := 1108)).pre s := by
  obtain a0 : arg AesCbc.X86.sat 0 = 0x1000 := by decide
  obtain a1 : arg AesCbc.X86.sat 1 = 10 := by decide
  obtain a2 : arg AesCbc.X86.sat 2 = 0x2000 := by decide
  obtain a3 : arg AesCbc.X86.sat 3 = 0x3000 := by decide
  obtain a4 : arg AesCbc.X86.sat 4 = 0 := by decide
  obtain a5 : arg AesCbc.X86.sat 5 = 0x4000 := by decide
  obtain e : argAddr AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Cfb8.aesSig, pre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using AesCbc.X86.sat

/-- With `buf` on the stack: 1084 bytes of frame, and 24 for the block
function's arguments and return address. -/
theorem framed_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCfb8.X86.decrypt v.enc)
      (Spec.Cfb8.aesSig.contract X86.abi (pre X86.abi.ptrBits) (post X86.abi.ptrBits) false 1108 none) :=
  X86.Verified.stackScratch (sig := Spec.Cfb8.aesSig) (nm := "buf") (e := .u64) (n := 130)
    (pre := pre X86.abi.ptrBits) (post := post X86.abi.ptrBits) (wa := false) (stack := 24)
    (bytes := bufFrame)
    (Verified.of_correct (groups_correct v) (groups_ct v) groups_implies) (by decide)
    (by
      rw [Code.allInstrs_eq, List.all_eq_true]
      intro i hi
      simp [groups_noSp v.enc v.encNosp i hi])
    (groups_stack v.enc v.encStack) (pre_local _) (post_local _)
    (fun vs m m₁ m₂ x hl _ => post_localOut _ vs m m₁ m₂ x hl) (frameSat_pre _)

/-- `Spec.Cfb8.aesDecryptContract` from `post`. -/
theorem keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (Spec.Cfb8.aesSig.contract A (pre A.ptrBits) (post A.ptrBits) false stack none)) :
    Verified T c (Spec.Cfb8.aesDecryptContract A stack) :=
  Verified.post_mono (post := post A.ptrBits) h fun _ _ _ _ _ _ _ _ _ hp key ⟨hk, hr, hw⟩ => by
    dsimp only [post] at hp
    have h' := hp (by rw [hr]; rcases hk with h | h | h <;> rw [h] <;> decide)
    rw [hw, hr] at h'
    exact h'

/-- `vg_aes_cfb8_decrypt` meets its contract. -/
theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCfb8.X86.decrypt v.enc) (Spec.Cfb8.aesDecryptContract X86.abi 1108) :=
  keyed (framed_verified v)

end VG.Proof.AesCfb8.X86.Groups
