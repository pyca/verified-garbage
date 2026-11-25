module

public import VerifiedGarbage.Impl.AesCbc.X86.Groups
public import VerifiedGarbage.Proof.AesCbc.X86.Call
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesXts.X86.Steps
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesXts.Batch
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
public import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Impl.AesCbc.X86.Groups
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

-- separate module: CFB128's decryption shares it

/-!
# CBC and CFB128 decryption around a block function, on x86 (32-bit)

`Impl.AesCbc.X86.Groups.groups`, 64 blocks a call, for any implementation of
the block functions, meets `groupsX86` (`groups_correct`, `groups_ct`): the
mode's plaintext and chaining value, and nothing written in `scratch` beyond
what the block function writes. `framed_verified`: with `buf` on the stack, it
meets `Spec.Cbc.aesSig`'s contract with `modePost` (`tailPost`).

The mode is one whose plaintext block is `plain` of its ciphertext block and
the one before it (`Par`): CBC's `CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, around the inverse
cipher, or CFB128's `Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, around the cipher. The data is stated
a block at a time (`DataIs`), as a function of the block's index. Between
groups the first `k` blocks are the plaintext, the rest are unchanged and the
block at `iv` is the ciphertext block before block `k` (`GInv`). In a group of
`m` blocks from block `k`: `buf` is filled with the ciphertext blocks before
its blocks (`FInv`), the block function is called (`Mid`), and `buf` is XORed
into the data (`XInv`).

Constant time, as for AES-CBC (`Proof/AesCbc/X86/CT.lean`): the taint analysis
covers the code around the call, from `esp`, the stack arguments and `esi`,
`edi` and `ebx`, which the correctness proof pins to the public arguments, and
the call is constant time by the block function's own proof.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Groups

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCbc.X86.Groups
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.CmacAes.X86 (wp_arg arg_ofNat ea_at' ofNat_and_self_beq)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi wp_cmpi wp_test wp_sub wp_subi eval_e eval_ne eval_b)
open VG.Proof.AesXts.X86 (bx bytesAt_bx bytesAt_writeW_bx bx_xor)
open VG.Proof.AesOcb.X86 (BCall BPost exec_bin)
open VG.Proof.AesGcm.X86 (w64 runBlock_app_of)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-! ## The mode -/

/-- The plaintext block, from the cipher `f`, the ciphertext block `x` and the
one before it, `c`: in CBC (`cbc`) or CFB128. -/
def plain (cbc : Bool) (f : List Byte → List Byte) (c x : List Byte) : List Byte :=
  if cbc then Spec.Cbc.xor (f x) c else Spec.Cbc.xor x (f c)

/-- `M` is decryption by `plain`, with the cipher `F`. -/
structure Par (M : Mode) (cbc : Bool) (F : Nat → List Byte → List Byte → List Byte) : Prop where
  out : ∀ R w iv xs k (h : k < xs.length),
    (M.out R w iv xs)[k]? = some (plain cbc (F R w) (if k = 0 then iv else xs.getD (k - 1) []) xs[k])
  chain : ∀ R w iv xs, M.chain R w iv xs = Spec.Cbc.next iv xs

theorem par_cbc : Par (cbcMode false) true (ciphOf false) where
  out R w iv xs k h := by
    simp only [cbcMode_out, cbc, Bool.false_eq_true, ite_false, plain, ite_true]
    induction xs generalizing iv k with
    | nil => exact absurd h (Nat.not_lt_zero _)
    | cons x xs ih =>
      cases k with
      | zero => simp [Spec.Cbc.decrypt]
      | succ k =>
        have hk : k < xs.length := by simpa using h
        simp only [Spec.Cbc.decrypt, List.getElem?_cons_succ, List.getElem_cons_succ, ih x k hk]
        cases k <;> simp
  chain R w iv xs := rfl

theorem par_cfb : Par (AesCfb.cfbMode false) false Spec.Cbc.aesWith where
  out R w iv xs k h := by
    simp only [AesCfb.cfbMode_out, AesCfb.cfb, Bool.false_eq_true, ite_false, plain]
    induction xs generalizing iv k with
    | nil => exact absurd h (Nat.not_lt_zero _)
    | cons x xs ih =>
      cases k with
      | zero => simp [Spec.Cfb.decrypt]
      | succ k =>
        have hk : k < xs.length := by simpa using h
        simp only [Spec.Cfb.decrypt, List.getElem?_cons_succ, List.getElem_cons_succ, ih x k hk]
        cases k <;> simp
  chain R w iv xs := rfl

/-! ## The contract -/

/-- `groups` `(schedule, rounds, iv, data, n, scratch, buf)`, with a block
function that writes no byte of `scratch` at offset `w` or beyond. -/
def groupsX86 (M : Mode) (w : Nat) : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
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
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 1040 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let k := bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1))
    let iv := bytesAt s.mem ((arg s 2).setWidth 64) 16
    let xs := Spec.Cbc.blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
    (Spec.Cbc.blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = M.out (arg s 1).toNat k iv xs ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = M.chain (arg s 1).toNat k iv xs) ∧
    ∀ i, w ≤ i → i < 2176 →
      s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev gE : BitVec 32 := s₀.gpr .esp
abbrev gW : BitVec 32 := arg s₀ 0
abbrev gR : Nat := (arg s₀ 1).toNat
abbrev gIv : BitVec 32 := arg s₀ 2
abbrev gD : BitVec 32 := arg s₀ 3
abbrev gN : Nat := (arg s₀ 4).toNat
abbrev gS : BitVec 32 := arg s₀ 5
abbrev gB : BitVec 32 := arg s₀ 6

abbrev schR : Region := ⟨(gW s₀).setWidth 64, 240⟩
abbrev ivR : Region := ⟨(gIv s₀).setWidth 64, 16⟩
abbrev dataR : Region := ⟨(gD s₀).setWidth 64, 16 * gN s₀⟩
abbrev scrR : Region := ⟨(gS s₀).setWidth 64, 2176⟩
abbrev bufR : Region := ⟨(gB s₀).setWidth 64, 1040⟩
/-- The blocks of `buf`. -/
abbrev blkR : Region := ⟨(gB s₀).setWidth 64, 1024⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(gE s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (gE s₀) 24

/-- The address of block `k` of the data, and of block `j` of `buf`. -/
abbrev dA (k : Nat) : Addr := (gD s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev bA (j : Nat) : Addr := (gB s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)
abbrev d32 (k : Nat) : BitVec 32 := gD s₀ + BitVec.ofNat 32 (16 * k)
abbrev b32 (j : Nat) : BitVec 32 := gB s₀ + BitVec.ofNat 32 (16 * j)

/-- The key schedule, ciphertext block `k`, and the block before block `k`. -/
abbrev gK : List Byte := bytesAt s₀.mem ((gW s₀).setWidth 64) (16 * (gR s₀ + 1))
abbrev ct (k : Nat) : List Byte := bytesAt s₀.mem (dA s₀ k) 16
def prev (k : Nat) : List Byte :=
  if k = 0 then bytesAt s₀.mem ((gIv s₀).setWidth 64) 16 else ct s₀ (k - 1)

/-- The memory once the registers are saved. -/
def svMem : Mem := Spill.saveMem s₀.mem ((gB s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

/-- The regions the function writes, with the stack below it. -/
abbrev Big : List Region := [ivR s₀, dataR s₀, scrR s₀, bufR s₀, stkR s₀]

/-- What the groups change, for a block function that writes the first `w`
bytes of its working space. -/
abbrev Mut (w : Nat) : List Region := [ivR s₀, dataR s₀, ⟨(gS s₀).setWidth 64, w⟩, blkR s₀, stkR s₀]

end

theorem prev_zero (s₀ : State) : prev s₀ 0 = bytesAt s₀.mem ((gIv s₀).setWidth 64) 16 := rfl

theorem prev_succ (s₀ : State) (k : Nat) : prev s₀ (k + 1) = ct s₀ k := rfl

/-- The data, block by block. -/
def DataIs (s₀ : State) (m : Mem) (g : Nat → List Byte) : Prop := ∀ j < gN s₀, bytesAt m (dA s₀ j) 16 = g j

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
  data_fit : (gD s₀).toNat + 16 * gN s₀ ≤ 2 ^ 32
  scr_fit : (gS s₀).toNat + 2176 ≤ 2 ^ 32
  buf_fit : (gB s₀).toNat + 1040 ≤ 2 ^ 32
  esp24 : 24 ≤ (gE s₀).toNat
  esp_fit : (gE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : gR s₀ = 10 ∨ gR s₀ = 12 ∨ gR s₀ = 14

theorem stk_eq {s₀ : State} (h : 24 ≤ (gE s₀).toNat) :
    stkR s₀ = ⟨(gE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ := by
  show (⟨(gE s₀ - BitVec.ofNat 32 24).setWidth 64, 24⟩ : Region) = _
  rw [Taint.sub_setWidth h]

theorem GPre.of {M : Mode} {w : Nat} {s₀ : State} (h : (groupsX86 M w).pre s₀) : GPre s₀ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33⟩ := h
  obtain e := stk_eq a31
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    e ▸ a21, e ▸ a22, e ▸ a23, e ▸ a24, e ▸ a25, a26, a27, a28, a29, a30, a31, a32, a33⟩

/-! ## Addresses and regions -/

theorem addr0 (b : BitVec 32) : addr b 0 = b.setWidth 64 := by
  rw [addr]; exact congrArg _ (BitVec.add_zero b)

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
  exact addr_eq (x := gD s₀) (k := 16 * k) (by omega_using [hk, this])

theorem GPre.d32_nat {k : Nat} (hk : k < gN s₀) : (d32 s₀ k).toNat = (gD s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
    Nat.mod_eq_of_lt (by omega_using [hk, this])]

theorem GPre.b32_addr {j : Nat} (hj : j < 64) : (b32 s₀ j).setWidth 64 = bA s₀ j := by
  have := hp.buf_fit
  exact addr_eq (x := gB s₀) (k := 16 * j) (by omega_using [hj, this])

theorem GPre.dA_disj {i j : Nat} (hi : i < gN s₀) (hj : j < gN s₀) (hij : i ≠ j) :
    (⟨dA s₀ i, 16⟩ : Region).Disjoint ⟨dA s₀ j, 16⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega_using [hij]) (by omega_using [hi, this]) (by omega_using [hj, this])

omit hp in
theorem bA_disj {i j : Nat} (hi : i < 64) (hj : j < 64) (hij : i ≠ j) :
    (⟨bA s₀ i, 16⟩ : Region).Disjoint ⟨bA s₀ j, 16⟩ :=
  Offset.disjoint _ (by omega_using [hij]) (by omega_using [hi]) (by omega_using [hj])

omit hp in
theorem data_sub {k m : Nat} (h : k + m ≤ gN s₀) : Region.Sub ⟨dA s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [h])

omit hp in
theorem data_sub1 {k : Nat} (h : k < gN s₀) : Region.Sub ⟨dA s₀ k, 16⟩ (dataR s₀) := data_sub (m := 1) h

omit hp in
theorem buf_sub1 {j : Nat} (h : j < 64) : Region.Sub ⟨bA s₀ j, 16⟩ (blkR s₀) :=
  Offset.sub_base _ (by omega_using [h])

omit hp in
theorem blk_buf : Region.Sub (blkR s₀) (bufR s₀) := Region.sub_prefix (by decide)

omit hp in
theorem inData {k : Nat} (h : k < gN s₀) {rs : List Region} (hr : dataR s₀ ∈ rs) : InRegions rs (dA s₀ k) 16 :=
  ⟨dataR s₀, hr, Offset.contains_base _ (by omega_using [h])
    (by have hN : gN s₀ < 2 ^ 32 := (arg s₀ 4).isLt; omega_using [h, hN])⟩

omit hp in
theorem inBuf {j : Nat} (h : j < 64) {rs : List Region} (hr : bufR s₀ ∈ rs) : InRegions rs (bA s₀ j) 16 :=
  ⟨bufR s₀, hr, Offset.contains_base _ (by omega_using [h]) (by omega_using [h])⟩

omit hp in
theorem mut_big {w : Nat} (hw : w ≤ 2176) {m m' : Mem} (hf : Frame (Mut s₀ w) m m') : Frame (Big s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix hw⟩
    · exact ⟨bufR s₀, by simp, blk_buf⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

end

/-! ## Saving and restoring the registers -/

theorem saved_fits : Spill.Fits 1040 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 1024 ≤ p.2 ∧ p.2 + 4 ≤ 1040 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem svMem_frame (s₀ : State) : Frame [⟨(gB s₀).setWidth 64 + BitVec.ofNat 64 1024, 16⟩] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    have := saved_bound p hp
    exact Offset.contains _ this.1 (by omega_using [this]) (by decide)

theorem svMem_buf (s₀ : State) : Frame [bufR s₀] s₀.mem (svMem s₀) :=
  (svMem_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bufR s₀, by simp, Offset.sub_base _ (by decide)⟩

theorem big_of {s₀ : State} {w : Nat} (hw : w ≤ 2176) {m : Mem} (hf : Frame (Mut s₀ w) (svMem s₀) m) :
    Frame (Big s₀) s₀.mem m :=
  ((svMem_buf s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans (mut_big hw hf)

/-! ## One instruction at a time, keeping the SSE registers -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movX {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  MdStream.X86.WP.cons rfl (k _ (MdStream.X86.Upd.setReg _ _ _) (xmm_setReg _ _ _))

theorem wp_argX {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q := by
  refine MdStream.X86.WP.cons (s' := s.setReg d (arg s₀ i)) ?_
    (k _ (MdStream.X86.Upd.setReg _ _ _) (xmm_setReg _ _ _))
  have ea : s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by rw [ea_at', hesp]; rfl
  show (readSrc s (.mem (at_ .esp (4 + 4 * i)))).map _ = _
  simp only [readSrc, State.load32, ea, hin, ↓reduceIte, hv, Option.map_some]

theorem wp_addiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  MdStream.X86.WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl)

theorem wp_subiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → s'.zf = some (s.gpr d - v == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  MdStream.X86.WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl rfl)

end

/-! ## The invariant between groups -/

/-- After `k` blocks: `P` is the mode's plaintext, block by block. -/
structure GInv (P : Nat → List Byte) (w : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ gN s₀
  esi : s.gpr .esi = d32 s₀ k
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀ w) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k then P j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = prev s₀ k

theorem setup_eq : setup = .mov .eax (argOp 6) :: (Spill.saveCode .eax saved ++
    ([.mov .esi (argOp 3), .mov .edi (argOp 4), .alu .test .edi (.reg .edi)] : List Instr)) := rfl

theorem setup_wp {P : Nat → List Byte} {w : Nat} {s₀ : State} (hp : GPre s₀) :
    WP isa (.block setup) s₀ fun s => GInv P w s₀ 0 s ∧ s.zf = some (decide (gN s₀ = 0)) := by
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
  obtain big := big_of (w := 0) (by decide) (Frame.refl (Mut s₀ 0) (svMem s₀))
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
    show _ = if j < 0 then P j else ct s₀ j
    rw [ite_eq_right (Nat.not_lt_zero _)]
    exact one (hp.data_buf.sub_left (data_sub1 hj))
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, prev_zero]; exact one hp.iv_buf
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

theorem restore_eq : restore = .mov .eax (argOp 6) :: (Spill.restoreCode .eax saved ++ []) := rfl

/-- The registers restored. -/
theorem restore_wp {P : Nat → List Byte} {w : Nat} (hw : w ≤ 2176) {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State}
    (h : GInv P w s₀ k s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  obtain big := big_of hw h.frame
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
        · exact (hp.scr_buf.symm.sub_left sub).sub_right (Region.sub_prefix hw)
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

/-- The number of blocks of the group from block `k`. -/
def gm (s₀ : State) (k : Nat) : Nat := min 64 (gN s₀ - k)

theorem gm_le (s₀ : State) (k : Nat) : gm s₀ k ≤ 64 := Nat.min_le_left _ _

theorem gm_fit {s₀ : State} {k : Nat} (hk : k < gN s₀) : k + gm s₀ k ≤ gN s₀ := by
  unfold gm; omega_arith

theorem gm_pos {s₀ : State} {k : Nat} (hk : k < gN s₀) : 0 < gm s₀ k := by unfold gm; omega_arith

theorem n_lt (s₀ : State) : gN s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem GInv.of_eq {P : Nat → List Byte} {w : Nat} {s₀ : State} {k : Nat} {s s' : State} (h : GInv P w s₀ k s)
    (esi : s'.gpr .esi = s.gpr .esi) (edi : s'.gpr .edi = s.gpr .edi) (esp : s'.gpr .esp = s.gpr .esp)
    (mem : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : GInv P w s₀ k s' :=
  ⟨h.le, by rw [esi, h.esi], by rw [edi, h.edi], by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [mem]; exact h.frame, by rw [mem]; exact h.data, by rw [mem]; exact h.iv⟩

theorem size_wp {P : Nat → List Byte} {w : Nat} {s₀ : State} {k : Nat} {s : State}
    (h : GInv P w s₀ k s) :
    WP isa size s fun s' => GInv P w s₀ k s' ∧ s'.gpr .ebx = BitVec.ofNat 32 (gm s₀ k) := by
  have hN := n_lt s₀
  refine WP.seq (wp_movi fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_)
  obtain e : s₂.gpr .edi = BitVec.ofNat 32 (gN s₀ - k) := by rw [f₂.gpr, u₁.other _ (by decide), h.edi]
  obtain h₂ : GInv P w s₀ k s₂ := h.of_eq (by rw [f₂.gpr, u₁.other _ (by decide)])
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
structure FInv (P : Nat → List Byte) (w : Nat) (s₀ : State) (k i : Nat) (s : State) : Prop where
  g : GInv P w s₀ k s
  ebx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)
  ebp : s.gpr .ebp = gIv s₀
  eax : s.gpr .eax = d32 s₀ (k + i)
  edx : s.gpr .edx = b32 s₀ i
  ecx : s.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i)
  x0 : bx (s.xmm .xmm0) = prev s₀ (k + i)
  buf : ∀ j < i, bytesAt s.mem (bA s₀ j) 16 = prev s₀ (k + j)

theorem wp_load {is : List Instr} {s : State} {Q : State → Prop} {x : XReg} {b : Reg} {A : Addr}
    (ha : (s.gpr b).setWidth 64 = A) (hin : InRegions (s.rd ++ s.wr) A 16)
    (k : WP isa (.block is) (s.setXmm x (s.mem.readW A 128)) Q) :
    WP isa (.block (.movdquLoad x (at_ b 0) :: is)) s Q :=
  MdStream.X86.WP.cons (by
    simp only [exec, State.load128, ea_at', addr0, ha, hin, ↓reduceIte, Option.map_some]) k

theorem wp_storeX {is : List Instr} {s : State} {Q : State → Prop} {x : XReg} {b : Reg} {A : Addr}
    (ha : (s.gpr b).setWidth 64 = A) (hout : InRegions s.wr A 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW A (s.xmm x) } Q) :
    WP isa (.block (.movdquStore (at_ b 0) x :: is)) s Q :=
  MdStream.X86.WP.cons (by simp only [exec, State.store128, ea_at', addr0, ha, hout, ↓reduceIte]) k

theorem add_d32 (s₀ : State) (k : Nat) : d32 s₀ k + 16 = d32 s₀ (k + 1) := by
  rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, d32, d32,
    Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_using [])]

theorem add_b32 (s₀ : State) (j : Nat) : b32 s₀ j + 16 = b32 s₀ (j + 1) := by
  rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, b32, b32,
    Offset.add_add_eq _ (c := 16 * (j + 1)) (by omega_using [])]

theorem fillPre_wp {P : Nat → List Byte} {w : Nat} (hw : w ≤ 2176) {s₀ : State} (hp : GPre s₀) {k : Nat}
    {s : State} (h : GInv P w s₀ k s) (hbx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)) :
    WP isa (.block fillPre) s (FInv P w s₀ k 0) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := big_of hw h.frame
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
  obtain x₂ : bx (s₂.xmm .xmm0) = prev s₀ k := by
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
    ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), hbx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), h.esi]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr]; exact (BitVec.add_zero _).symm
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), hbx]; rfl
  · rw [x₅, x₄, x₃, x₂]; rfl

/-- A change of `buf`'s blocks alone. -/
theorem GInv.buf {P : Nat → List Byte} {w : Nat} {s₀ : State} (hp : GPre s₀) {k : Nat} {s s' : State}
    (h : GInv P w s₀ k s) (esi : s'.gpr .esi = s.gpr .esi) (edi : s'.gpr .edi = s.gpr .edi)
    (esp : s'.gpr .esp = s.gpr .esp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (hf : Frame [blkR s₀] s.mem s'.mem) :
    GInv P w s₀ k s' := by
  refine ⟨h.le, by rw [esi, h.esi], by rw [edi, h.edi], by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr],
    h.frame.trans (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]), fun j hj => ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_frame16 hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_buf.sub_left (data_sub1 hj)).sub_right blk_buf]
    exact h.data j hj
  · rw [Proof.Cmac.bytesAt_frame16 hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_buf.sub_right blk_buf]
    exact h.iv

theorem left1 {n i : Nat} (hn : n ≤ 64) (hi : i < n) :
    BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) ∧
      (BitVec.ofNat 32 (n - i) - 1 == 0) = decide (i + 1 = n) := by
  have e : BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega_using [hn]), ofNat_toNat_lt (by omega_using [hn])]
    show (2 ^ 32 - 1 + (n - i)) % 2 ^ 32 = _
    omega_using [hn, hi]
  refine ⟨e, ?_⟩
  rw [e, MdStream.X86.ofNat_beq_zero (by omega_using [hn])]
  exact decide_eq_decide.mpr (by omega_using [hi])

theorem fillBody_wp {P : Nat → List Byte} {w : Nat} {s₀ : State} (hp : GPre s₀) {k i : Nat} (hk : k < gN s₀)
    (hi : i < gm s₀ k) {s : State} (h : FInv P w s₀ k i s) :
    WP isa (.block fillBody) s fun s' => FInv P w s₀ k (i + 1) s' ∧ s'.zf = some (decide (i + 1 = gm s₀ k)) := by
  have hm := gm_le s₀ k
  have hf := gm_fit hk
  have hi64 : i < 64 := by omega_using [hi, hm]
  have hki : k + i < gN s₀ := by omega_using [hi, hf]
  refine wp_storeX (A := bA s₀ i) (by rw [h.edx]; exact hp.b32_addr hi64)
    (by rw [h.g.wr, hp.wr]; exact inBuf hi64 (by simp)) ?_
  generalize hs₁ : ({ s with mem := s.mem.writeW (bA s₀ i) (s.xmm .xmm0) } : State) = s₁
  obtain g₁ : s₁.gpr = s.gpr := by rw [← hs₁]
  obtain m₁ : s₁.mem = s.mem.writeW (bA s₀ i) (s.xmm .xmm0) := by rw [← hs₁]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁]
  obtain f₁ : Frame [⟨bA s₀ i, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain G₁ : GInv P w s₀ k s₁ := h.g.buf hp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨blkR s₀, by simp, buf_sub1 hi64⟩)
  refine wp_load (A := dA s₀ (k + i)) (by rw [g₁, h.eax]; exact hp.d32_addr hki)
    (by rw [G₁.rd, G₁.wr, hp.rd, hp.wr]; exact inData hki (by simp)) ?_
  generalize hs₂ : s₁.setXmm .xmm0 (s₁.mem.readW (dA s₀ (k + i)) 128) = s₂
  obtain g₂ : s₂.gpr = s.gpr := by rw [← hs₂, gpr_setXmm, g₁]
  obtain m₂ : s₂.mem = s₁.mem := by rw [← hs₂, mem_setXmm]
  obtain rd₂ : s₂.rd = s₁.rd := by rw [← hs₂, rd_setXmm]
  obtain wr₂ : s₂.wr = s₁.wr := by rw [← hs₂, wr_setXmm]
  obtain x₂ : bx (s₂.xmm .xmm0) = prev s₀ (k + (i + 1)) := by
    rw [← hs₂, xmm_setXmm_self, ← bytesAt_bx, G₁.data _ hki]
    show (if k + i < k then P (k + i) else ct s₀ (k + i)) = _
    rw [ite_eq_right (by omega_using []), ← Nat.add_assoc, prev_succ]
  refine wp_addiX fun s₃ u₃ x₃ => wp_addiX fun s₄ u₄ x₄ => wp_subiX fun s₅ u₅ x₅ z₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₅.gpr r = s.gpr r := fun r ha hc hd => by
    rw [u₅.other _ hc, u₄.other _ hd, u₃.other _ ha, g₂]
  obtain m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, m₂]
  obtain c₄ : s₄.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ecx]
  obtain ⟨l₁, l₂⟩ := left1 hm hi
  refine ⟨⟨G₁.of_eq (by rw [keep _ (by decide) (by decide) (by decide), g₁])
      (by rw [keep _ (by decide) (by decide) (by decide), g₁])
      (by rw [keep _ (by decide) (by decide) (by decide), g₁]) m₅ (by rw [u₅.rd, u₄.rd, u₃.rd, rd₂])
      (by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]), ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [keep _ (by decide) (by decide) (by decide), h.ebx]
  · rw [keep _ (by decide) (by decide) (by decide), h.ebp]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h.eax, add_d32]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, h.edx, add_b32]
  · rw [u₅.gpr, c₄, l₁]
  · rw [x₅, x₄, x₃, x₂]
  · rw [m₅]
    by_cases hji : j = i
    · subst hji
      rw [m₁, bytesAt_writeW_bx, h.x0]
    · rw [Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact bA_disj (by omega_using [hj, hi64]) hi64 hji]
      exact h.buf j (by omega_using [hj, hji])
  · rw [z₅, c₄, l₂]

theorem fillLoop_wp {P : Nat → List Byte} {w : Nat} {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀)
    {s : State} (h : FInv P w s₀ k 0 s) : WP isa (.loop (.block fillBody) .ne) s (FInv P w s₀ k (gm s₀ k)) := by
  refine WP.loop (M := isa) (body := .block fillBody) (c := .ne) (Q := FInv P w s₀ k (gm s₀ k))
    (fun (n : Nat) (t : State) => ∃ i, n = gm s₀ k - i ∧ i < gm s₀ k ∧ FInv P w s₀ k i t) ?_ (gm s₀ k - 0) s
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

/-- The blocks the block function is given. -/
def dst (cbc : Bool) (s₀ : State) (k : Nat) : BitVec 32 := if cbc then d32 s₀ k else gB s₀

/-- Before the call: `buf` is filled, and the block at `iv` the group's last
ciphertext block. -/
structure Mid (P : Nat → List Byte) (w : Nat) (cbc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  bc : BCall s (gW s₀) (dst cbc s₀ k) (gS s₀) (gR s₀) (gm s₀ k)
  esi : s.gpr .esi = d32 s₀ k
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀ w) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k then P j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = prev s₀ (k + gm s₀ k)
  buf : ∀ j < gm s₀ k, bytesAt s.mem (bA s₀ j) 16 = prev s₀ (k + j)

/-- The blocks the call is given, as a region of what the function writes. -/
structure Dst (s₀ : State) (D : BitVec 32) (n : Nat) : Prop where
  fit : D.toNat + 16 * n ≤ 2 ^ 32
  sch : (schR s₀).Disjoint ⟨D.setWidth 64, 16 * n⟩
  scr : (⟨D.setWidth 64, 16 * n⟩ : Region).Disjoint (scrR s₀)
  stk : (stkR s₀).Disjoint ⟨D.setWidth 64, 16 * n⟩
  wr : ∃ r ∈ s₀.wr, Region.Sub ⟨D.setWidth 64, 16 * n⟩ r
  cov : Covers [⟨D.setWidth 64, 16 * n⟩] s₀.wr

theorem dst_ok {s₀ : State} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) (cbc : Bool) :
    Dst s₀ (dst cbc s₀ k) (gm s₀ k) := by
  have hm := gm_le s₀ k
  have hf := gm_fit hk
  cases cbc
  · have sub : Region.Sub ⟨(gB s₀).setWidth 64, 16 * gm s₀ k⟩ (bufR s₀) :=
      Region.sub_prefix (by omega_using [hm])
    have hb := hp.buf_fit
    exact ⟨by show (gB s₀).toNat + _ ≤ _; omega_using [hb, hm], hp.sch_buf.sub_right sub,
      (hp.scr_buf.sub_right sub).symm, hp.stk_buf.sub_right sub, ⟨bufR s₀, by rw [hp.wr]; simp, sub⟩, by
        rw [hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨bufR s₀, by simp, 0, (BitVec.add_zero _).symm, by show 0 + 16 * gm s₀ k ≤ 1040; omega_using [hm]⟩⟩
  · have e : (d32 s₀ k).setWidth 64 = dA s₀ k := hp.d32_addr hk
    have sub : Region.Sub ⟨(d32 s₀ k).setWidth 64, 16 * gm s₀ k⟩ (dataR s₀) := by rw [e]; exact data_sub hf
    have hd := hp.data_fit
    exact ⟨by show (d32 s₀ k).toNat + _ ≤ _; rw [hp.d32_nat hk]; omega_using [hd, hf], hp.sch_data.sub_right sub,
      hp.data_scr.sub_left sub, hp.stk_data.sub_right sub, ⟨dataR s₀, by rw [hp.wr]; simp, sub⟩, by
        show Covers [⟨(d32 s₀ k).setWidth 64, 16 * gm s₀ k⟩] s₀.wr
        rw [hp.wr, e]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨dataR s₀, by simp, 16 * k, rfl, by show 16 * k + 16 * gm s₀ k ≤ 16 * gN s₀; omega_using [hf]⟩⟩

theorem callArgs_wp {P : Nat → List Byte} {w : Nat} (hw : w ≤ 2176) (cbc : Bool) {s₀ : State} (hp : GPre s₀)
    {k : Nat} (hk : k < gN s₀) {s : State} (h : FInv P w s₀ k (gm s₀ k) s) :
    WP isa (.block (callArgs cbc)) s (Mid P w cbc s₀ k) := by
  have hf := gm_fit hk
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.g.rd, h.g.wr]
  refine wp_storeX (A := (gIv s₀).setWidth 64) (by rw [h.ebp])
    (by rw [h.g.wr, hp.wr]; exact ⟨ivR s₀, by simp, Region.contains_self _ _⟩) ?_
  generalize hs₁ : ({ s with mem := s.mem.writeW ((gIv s₀).setWidth 64) (s.xmm .xmm0) } : State) = s₁
  obtain g₁ : s₁.gpr = s.gpr := by rw [← hs₁]
  obtain m₁ : s₁.mem = s.mem.writeW ((gIv s₀).setWidth 64) (s.xmm .xmm0) := by rw [← hs₁]
  obtain rd₁ : s₁.rd = s.rd := by rw [← hs₁]
  obtain wr₁ : s₁.wr = s.wr := by rw [← hs₁]
  obtain f₁ : Frame [ivR s₀] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain F₁ : Frame (Mut s₀ w) (svMem s₀) s₁.mem :=
    h.g.frame.trans (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  obtain big := big_of hw F₁
  obtain hrw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [rd₁, wr₁, hrw]
  refine wp_arg (s₀ := s₀) (by rw [g₁, h.g.esp]) (by rw [hrw₁]; exact hp.arg_in (by decide))
    (hp.arg_keep big (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), g₁, h.g.esp])
    (by rw [u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide)) (by rw [u₂.mem]; exact hp.arg_keep big (by decide))
    fun s₃ u₃ => ?_
  -- The blocks: `esi`, or `buf`.
  obtain k₃ : ∀ {Q : State → Prop}, (∀ s₄, Upd s₃ s₄ .edx (dst cbc s₀ k) →
      WP isa (.block [.mov .ebp (argOp 5)]) s₄ Q) →
      WP isa (.block [.mov .edx (if cbc then .reg .esi else argOp 6), .mov .ebp (argOp 5)]) s₃ Q := fun q => by
    cases cbc
    · exact wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.g.esp])
        (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide))
        (by rw [u₃.mem, u₂.mem]; exact hp.arg_keep big (by decide)) q
    · refine wp_mov fun s₄ u₄ => q s₄ ?_
      have e : s₃.gpr .esi = d32 s₀ k := by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.g.esi]
      rw [e] at u₄
      exact u₄
  refine k₃ fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.g.esp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, hrw₁]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem]; exact hp.arg_keep big (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r ha hc hd hb => by
    rw [u₅.other _ hb, u₄.other _ hd, u₃.other _ hc, u₂.other _ ha, g₁]
  obtain m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.g.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.g.wr]
  obtain esp₅ : s₅.gpr .esp = gE s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.esp]
  obtain d := dst_ok hp hk cbc
  obtain scS : Region.Sub ⟨(gS s₀).setWidth 64, 2048⟩ (scrR s₀) := Region.sub_prefix (by decide)
  have hsc := hp.scr_fit
  refine ⟨⟨?_, ?_, ?_, ?_, u₅.gpr, hp.rounds, by rw [esp₅]; exact hp.esp24, d.sch, hp.sch_scr.sub_right scS,
    d.scr.sub_right scS, by rw [esp₅]; exact hp.stk_sch, by rw [esp₅]; exact d.stk,
    by rw [esp₅]; exact hp.stk_scr.sub_right scS, hp.sch_fit, d.fit, by omega_using [hsc], ?_, ?_⟩,
    ?_, ?_, esp₅, rd₅, wr₅, by rw [m₅]; exact F₁, fun j hj => ?_, ?_, fun j hj => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; exact arg_ofNat s₀ 1
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [rd₅, wr₅, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₅]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact d.cov a n ⟨_, List.mem_singleton_self _, hc⟩
    · refine Covers.of_sub (rs := [⟨(gS s₀).setWidth 64, 2048⟩]) (fun r hr => ?_) a n
        ⟨_, List.mem_singleton_self _, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by rw [hp.wr]; simp, 0, by simp, by simp⟩
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.esi]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), h.g.edi]
  · rw [m₅, Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.iv_data.sub_right (data_sub1 hj)).symm]
    exact h.g.data j hj
  · rw [m₅, m₁, bytesAt_writeW_bx, h.x0]
  · rw [m₅, Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.iv_buf.sub_right blk_buf).sub_right (buf_sub1 (Nat.lt_of_lt_of_le hj (gm_le _ _)))).symm]
    exact h.buf j hj

theorem fill_wp {P : Nat → List Byte} {w : Nat} (hw : w ≤ 2176) (cbc : Bool) {s₀ : State} (hp : GPre s₀)
    {k : Nat} (hk : k < gN s₀) {s : State} (h : GInv P w s₀ k s) : WP isa (fill cbc) s (Mid P w cbc s₀ k) :=
  WP.seq (WP.mono (size_wp h) fun _ ⟨h₁, b₁⟩ =>
    WP.seq (WP.mono (fillPre_wp hw hp h₁ b₁) fun _ h₂ =>
      WP.seq (WP.mono (fillLoop_wp hp hk h₂) fun _ h₃ => callArgs_wp hw cbc hp hk h₃)))

/-- A call of a block function that writes only the first `w` bytes of the
working space: only the blocks, those bytes and the stack change. -/
theorem blks_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks} {w : Nat}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (wok : ∀ s, (Proof.Aes.blocksX86 f).pre s → ∀ t s', Exec isa b.code s t s' → ∀ i, w ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i))
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    {s : State} {K D S : BitVec 32} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) s fun s' => BPost f s K D S R n s' ∧
      Frame [⟨D.setWidth 64, 16 * n⟩, ⟨S.setWidth 64, w⟩, below (s.gpr .esp) 24] s.mem s'.mem := by
  have ok' : ∀ s, (blocksTailX86 f w).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (blocksTailX86 f w).post s s' := fun s hs =>
    let ⟨t, s', he, ha, hq⟩ := ok s hs
    ⟨t, s', he, ha, hq, wok s hs t s' he⟩
  have hB : WP isa (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) s fun s' =>
      Frame [⟨D.setWidth 64, 16 * n⟩, ⟨S.setWidth 64, w⟩, below (s.gpr .esp) 24] s.mem s'.mem := by
    unfold Impl.AesOcb.X86.blocksFrame
    refine WP.callWith (rs := AesOcb.X86.blkRegs) (k := blocksTailX86 f w) ok' nosp (by simp) AesOcb.X86.blkRegs_esp
      (by rw [stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this])
      (let hc := h.callPre f; ⟨hc.pre, hc.cov, hc.covw⟩) fun s' _ _ _ f' ⟨s₂, m₂, _, tail⟩ => ?_
    obtain ⟨-, -, -, -, a4⟩ := h.args
    rw [stack] at f'
    have fE := callEntry_frame h.fit AesOcb.X86.blkRegs_esp
    rw [show 4 * AesOcb.X86.blkRegs.length + 4 = 24 from rfl] at fE
    simp only [arg_withRegions, State.withRegions_mem, a4] at tail
    intro x hx
    by_cases hc : (⟨S.setWidth 64, 2048⟩ : Region).Contains x 1
    · have hi : (x - S.setWidth 64).toNat < 2048 := by simp only [Region.Contains] at hc; omega_using [hc]
      have ex : S.setWidth 64 + BitVec.ofNat 64 (x - S.setWidth 64).toNat = x := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hw : w ≤ (x - S.setWidth 64).toNat := by
        have := hx ⟨S.setWidth 64, w⟩ (by simp)
        simp only [Region.Contains] at this
        omega_using [this]
      have t := tail _ hw hi
      rw [ex] at t
      rw [m₂ x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact fun hb => h.bs x (below_sub (by decide) h.esp x hb) hc, t]
      exact fE x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact fun hb => h.bs x hb hc
    · exact f' x fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hx ⟨D.setWidth 64, 16 * n⟩ (by simp)
        · exact hc
        · exact hx (below (s.gpr .esp) 24) (by simp)
  obtain ⟨t, s', e, q⟩ := AesOcb.X86.blk_call (fn := ⟨b.name, b.code⟩) ok nosp stack h
  obtain ⟨t', s'', e', q'⟩ := hB
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, s', e, q, q'⟩

/-- One block of those the call was given. -/
theorem out_block {f : Spec.Aes.State → Spec.Aes.State} {c : List Byte → List Byte}
    (hf : ∀ m p, (f (Spec.Aes.stateAt m p)).toList = c (bytesAt m p 16)) {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map f) {j : Nat} (hj : j < n) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * j)) 16 = c (bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16) := by
  have e := congrArg (·[j]?) (AesXts.blocksAt_of_out h fun p => hf m p)
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show j < (Spec.Cbc.blocksAt m' D n).length by
      rw [length_blocksAt]; exact hj), List.getElem?_eq_getElem (show j < (Spec.Cbc.blocksAt m D n).length by
      rw [length_blocksAt]; exact hj), getElem_blocksAt _ _ hj, Option.map_some, Option.some.injEq] at e
  exact e

section
variable (cbc : Bool) (F : Nat → List Byte → List Byte → List Byte) (s₀ : State)

/-- Block `j` of the data, and the block of `buf` for it, after the call. -/
def xd (j : Nat) : List Byte := if cbc then F (gR s₀) (gK s₀) (ct s₀ j) else ct s₀ j
def xb (j : Nat) : List Byte := if cbc then prev s₀ j else F (gR s₀) (gK s₀) (prev s₀ j)

/-- The mode's plaintext block `j`. -/
def gP (j : Nat) : List Byte := plain cbc (F (gR s₀) (gK s₀)) (prev s₀ j) (ct s₀ j)

theorem gP_eq (j : Nat) : gP cbc F s₀ j = Spec.Cbc.xor (xd cbc F s₀ j) (xb cbc F s₀ j) := by
  cases cbc <;> rfl

/-- After the call, with `i` of the group's blocks XORed. -/
structure XInv (w k i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = d32 s₀ (k + i)
  edi : s.gpr .edi = BitVec.ofNat 32 (gN s₀ - k)
  ebx : s.gpr .ebx = BitVec.ofNat 32 (gm s₀ k)
  esp : s.gpr .esp = gE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (Mut s₀ w) (svMem s₀) s.mem
  data : DataIs s₀ s.mem fun j => if j < k + i then gP cbc F s₀ j else
    if j < k + gm s₀ k then xd cbc F s₀ j else ct s₀ j
  iv : bytesAt s.mem ((gIv s₀).setWidth 64) 16 = prev s₀ (k + gm s₀ k)
  buf : ∀ j < gm s₀ k, bytesAt s.mem (bA s₀ j) 16 = xb cbc F s₀ (k + j)

end

section
variable {cbc : Bool} {F : Nat → List Byte → List Byte → List Byte} {s₀ : State}

theorem call_wp {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks} {w : Nat}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (wok : ∀ s, (Proof.Aes.blocksX86 f).pre s → ∀ t s', Exec isa b.code s t s' → ∀ i, w ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i))
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R k m p, (f R k (Spec.Aes.stateAt m p)).toList = F R k (bytesAt m p 16))
    (hw : w ≤ 2048) (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State} (h : Mid (gP cbc F s₀) w cbc s₀ k s) :
    WP isa (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) s (XInv cbc F s₀ w k 0) := by
  refine WP.mono (blks_call ok wok nosp stack h.bc) fun s' ⟨c, fr⟩ => ?_
  have hm := gm_le s₀ k
  have hfit := gm_fit hk
  have hw' : w ≤ 2176 := by omega_using [hw]
  rw [h.esp] at fr
  obtain d := dst_ok hp hk cbc
  obtain scW : Region.Sub ⟨(gS s₀).setWidth 64, w⟩ (scrR s₀) := Region.sub_prefix hw'
  obtain sched : bytesAt s.mem (w64 (gW s₀)) (16 * (gR s₀ + 1)) = gK s₀ := hp.sched_keep (big_of hw' h.frame)
  obtain out := c.out
  rw [sched] at out
  -- What the call leaves: the regions apart from the blocks.
  obtain keep : ∀ {a : Addr}, (⟨a, 16⟩ : Region).Disjoint ⟨(dst cbc s₀ k).setWidth 64, 16 * gm s₀ k⟩ →
      (⟨a, 16⟩ : Region).Disjoint (scrR s₀) → (⟨a, 16⟩ : Region).Disjoint (stkR s₀) →
      bytesAt s'.mem a 16 = bytesAt s.mem a 16 := fun h₁ h₂ h₃ =>
    Proof.Cmac.bytesAt_frame16 fr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂.sub_right scW
      · exact h₃
  obtain dKeep : ∀ {j : Nat}, j < gN s₀ →
      (⟨dA s₀ j, 16⟩ : Region).Disjoint ⟨(dst cbc s₀ k).setWidth 64, 16 * gm s₀ k⟩ →
      bytesAt s'.mem (dA s₀ j) 16 = bytesAt s.mem (dA s₀ j) 16 := fun hj hd =>
    keep hd (hp.data_scr.sub_left (data_sub1 hj)) (hp.stk_data.symm.sub_left (data_sub1 hj))
  obtain bKeep : ∀ {j : Nat}, j < gm s₀ k →
      (⟨bA s₀ j, 16⟩ : Region).Disjoint ⟨(dst cbc s₀ k).setWidth 64, 16 * gm s₀ k⟩ →
      bytesAt s'.mem (bA s₀ j) 16 = bytesAt s.mem (bA s₀ j) 16 := fun hj hd => by
    obtain sb : Region.Sub ⟨bA s₀ _, 16⟩ (bufR s₀) :=
      fun a ha => blk_buf a (buf_sub1 (Nat.lt_of_lt_of_le hj hm) a ha)
    exact keep hd (hp.scr_buf.symm.sub_left sb) (hp.stk_buf.symm.sub_left sb)
  refine ⟨by rw [c.saved .esi (by simp [calleeSaved]), h.esi]; rfl, by rw [c.saved .edi (by simp [calleeSaved]), h.edi],
    by rw [c.saved .ebx (by simp [calleeSaved]), h.bc.ebx], by rw [c.saved .esp (by simp [calleeSaved]), h.esp],
    by rw [c.rd, h.rd], by rw [c.wr, h.wr], h.frame.trans (fr.sub fun r hr => ?_), fun j hj => ?_, ?_,
    fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · cases cbc
      · exact ⟨blkR s₀, by simp, Region.sub_prefix (by omega_using [hm])⟩
      · refine ⟨dataR s₀, by simp, ?_⟩
        show Region.Sub ⟨(d32 s₀ k).setWidth 64, _⟩ _
        rw [hp.d32_addr hk]; exact data_sub hfit
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · show _ = if j < k + 0 then _ else _
    obtain dj : bytesAt s.mem (dA s₀ j) 16 = if j < k then gP cbc F s₀ j else ct s₀ j := h.data j hj
    rw [Nat.add_zero]
    cases cbc
    · rw [dKeep hj ((hp.data_buf.sub_left (data_sub1 hj)).sub_right (Region.sub_prefix (by omega_using [hm]))), dj]
      by_cases h₁ : j < k
      · rw [ite_eq_left h₁, ite_eq_left h₁]
      · rw [ite_eq_right h₁, ite_eq_right h₁]
        split <;> rfl
    · obtain e : (dst true s₀ k).setWidth 64 = dA s₀ k := hp.d32_addr hk
      by_cases h₁ : k ≤ j ∧ j < k + gm s₀ k
      · rw [ite_eq_right (by omega_using [h₁]), ite_eq_left h₁.2]
        have o := out_block (hf _ _) out (j := j - k) (by omega_using [h₁])
        rw [show w64 (dst true s₀ k) = dA s₀ k from e, Offset.add_add_eq _ (c := 16 * j) (by omega_using [h₁]), dj,
          ite_eq_right (by omega_using [h₁])] at o
        exact o
      · rw [dKeep hj (by
          rw [e]
          have hd := hp.data_fit
          have hd' : 16 * gN s₀ ≤ 2 ^ 32 := by omega_using [hd]
          exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [hj, hd']) (by omega_using [hfit, hd'])), dj]
        by_cases h₂ : j < k
        · rw [ite_eq_left h₂, ite_eq_left h₂]
        · rw [ite_eq_right h₂, ite_eq_right h₂, ite_eq_right (by omega_using [h₁, h₂])]
  · rw [keep (by
      cases cbc
      · exact hp.iv_buf.sub_right (Region.sub_prefix (by omega_using [hm]))
      · show Region.Disjoint _ ⟨(d32 s₀ k).setWidth 64, _⟩
        rw [hp.d32_addr hk]; exact hp.iv_data.sub_right (data_sub hfit)) hp.iv_scr hp.stk_iv.symm, h.iv]
  · cases cbc
    · have o := out_block (hf _ _) out hj
      rw [show w64 (dst false s₀ k) + BitVec.ofNat 64 (16 * j) = bA s₀ j from rfl, h.buf j hj] at o
      exact o
    · rw [bKeep hj (by
        show Region.Disjoint _ ⟨(d32 s₀ k).setWidth 64, _⟩
        rw [hp.d32_addr hk]
        exact ((hp.data_buf.sub_left (data_sub hfit)).sub_right fun a ha =>
          blk_buf a (buf_sub1 (Nat.lt_of_lt_of_le hj hm) a ha)).symm), h.buf j hj]
      rfl

/-! ## `buf` XORed into the data -/

/-- `XInv` in the loop. -/
structure LInv (cbc : Bool) (F : Nat → List Byte → List Byte → List Byte) (s₀ : State) (w k i : Nat) (s : State) :
    Prop where
  x : XInv cbc F s₀ w k i s
  edx : s.gpr .edx = b32 s₀ i
  ecx : s.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i)

theorem XInv.of_eq {w k i : Nat} {s s' : State} (h : XInv cbc F s₀ w k i s)
    (gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) (mem : s'.mem = s.mem) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) : XInv cbc F s₀ w k i s' :=
  ⟨by rw [gpr _ (by decide) (by decide) (by decide), h.esi], by rw [gpr _ (by decide) (by decide) (by decide), h.edi],
    by rw [gpr _ (by decide) (by decide) (by decide), h.ebx], by rw [gpr _ (by decide) (by decide) (by decide), h.esp],
    by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame, by rw [mem]; exact h.data,
    by rw [mem]; exact h.iv, by rw [mem]; exact h.buf⟩

theorem xorPre_wp {w : Nat} (hw : w ≤ 2176) (hp : GPre s₀) {k : Nat} {s : State} (h : XInv cbc F s₀ w k 0 s) :
    WP isa (.block xorPre) s (LInv cbc F s₀ w k 0) := by
  refine wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.arg_keep (big_of hw h.frame) (by decide)) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_
  refine ⟨h.of_eq (fun r _ hc hd => by rw [u₂.other _ hc, u₁.other _ hd]) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]), ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr]; exact (BitVec.add_zero _).symm
  · rw [u₂.gpr, u₁.other _ (by decide), h.ebx]; rfl

theorem xorBody_wp {w : Nat} (hp : GPre s₀) {k i : Nat} (hk : k < gN s₀) (hi : i < gm s₀ k) {s : State}
    (h : LInv cbc F s₀ w k i s) :
    WP isa (.block xorBody) s fun s' => LInv cbc F s₀ w k (i + 1) s' ∧ s'.zf = some (decide (i + 1 = gm s₀ k)) := by
  have hm := gm_le s₀ k
  have hf := gm_fit hk
  have hi64 : i < 64 := by omega_using [hi, hm]
  have hki : k + i < gN s₀ := by omega_using [hi, hf]
  obtain ad : (s.gpr .esi).setWidth 64 = dA s₀ (k + i) := by rw [h.x.esi]; exact hp.d32_addr hki
  obtain ab : (s.gpr .edx).setWidth 64 = bA s₀ i := by rw [h.edx]; exact hp.b32_addr hi64
  obtain rin : InRegions (s.rd ++ s.wr) (dA s₀ (k + i)) 16 := by
    rw [h.x.rd, h.x.wr, hp.rd, hp.wr]; exact inData hki (by simp)
  obtain bin : InRegions (s.rd ++ s.wr) (bA s₀ i) 16 := by
    rw [h.x.rd, h.x.wr, hp.rd, hp.wr]; exact inBuf hi64 (by simp)
  obtain win : InRegions s.wr (dA s₀ (k + i)) 16 := by rw [h.x.wr, hp.wr]; exact inData hki (by simp)
  obtain ⟨s₁, run, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.movdquLoad .xmm0 (at_ .esi 0), .movdquLoad .xmm1 (at_ .edx 0),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .esi 0) .xmm0] s = some s₁ ∧
      s₁.mem = s.mem.writeW (dA s₀ (k + i)) (s.mem.readW (dA s₀ (k + i)) 128 ^^^ s.mem.readW (bA s₀ i) 128) ∧
      s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, State.load128, State.store128, ea_at',
        addr0, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, ad, ab, rin, bin, win, ↓reduceIte, Option.map_some]
      rfl, ?_, by rfl, by rfl, by rfl⟩
    simp only [xmm_setXmm_self, xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]; rfl
  rw [show xorBody = [.movdquLoad .xmm0 (at_ .esi 0), .movdquLoad .xmm1 (at_ .edx 0),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .esi 0) .xmm0] ++ ([.alu .add .esi (.imm 16),
      .alu .add .edx (.imm 16), .alu .sub .ecx (.imm 1)] : List Instr) from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  refine wp_addi fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  obtain f₁ : Frame [⟨dA s₀ (k + i), 16⟩] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain one : ∀ {a : Addr}, (⟨a, 16⟩ : Region).Disjoint ⟨dA s₀ (k + i), 16⟩ →
      bytesAt s₁.mem a 16 = bytesAt s.mem a 16 := fun hd =>
    Proof.Cmac.bytesAt_frame16 f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain keep : ∀ r, r ≠ .esi → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s.gpr r := fun r ha hc hd => by
    rw [u₄.other _ hc, u₃.other _ hd, u₂.other _ ha, g₁]
  obtain c₃ : s₃.gpr .ecx = BitVec.ofNat 32 (gm s₀ k - i) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.ecx]
  obtain ⟨l₁, l₂⟩ := left1 hm hi
  refine ⟨⟨⟨?_, by rw [keep _ (by decide) (by decide) (by decide), h.x.edi],
      by rw [keep _ (by decide) (by decide) (by decide), h.x.ebx],
      by rw [keep _ (by decide) (by decide) (by decide), h.x.esp], by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.x.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.x.wr], ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩, ?_, by rw [u₄.gpr, c₃, l₁]⟩,
    by rw [z₄, c₃, l₂]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁, h.x.esi, add_d32]; rfl
  · rw [m₄]
    exact h.x.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, data_sub1 hki⟩)
  · rw [m₄]
    show _ = if j < k + (i + 1) then _ else _
    obtain dj : bytesAt s.mem (dA s₀ j) 16 = if j < k + i then gP cbc F s₀ j else
      if j < k + gm s₀ k then xd cbc F s₀ j else ct s₀ j := h.x.data j hj
    by_cases hji : j = k + i
    · subst hji
      rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (by omega_using [hi])] at dj
      rw [ite_eq_left (by omega_using []), m₁, bytesAt_writeW_bx, bx_xor, ← bytesAt_bx, ← bytesAt_bx, dj,
        h.x.buf i hi, gP_eq]
    · rw [one (hp.dA_disj hj hki hji), dj]
      by_cases h₁ : j < k + i
      · rw [ite_eq_left h₁, ite_eq_left (by omega_using [h₁])]
      · rw [ite_eq_right h₁, ite_eq_right (show ¬ j < k + (i + 1) by omega_using [h₁, hji])]
  · rw [m₄, one (hp.iv_data.sub_right (data_sub1 hki)), h.x.iv]
  · rw [m₄, one (((hp.data_buf.sub_left (data_sub1 hki)).sub_right blk_buf).sub_right
      (buf_sub1 (Nat.lt_of_lt_of_le hj hm))).symm, h.x.buf j hj]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁, h.edx, add_b32]

theorem xorLoop_wp {w : Nat} (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State} (h : LInv cbc F s₀ w k 0 s) :
    WP isa (.loop (.block xorBody) .ne) s (LInv cbc F s₀ w k (gm s₀ k)) := by
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne) (Q := LInv cbc F s₀ w k (gm s₀ k))
    (fun (n : Nat) (t : State) => ∃ i, n = gm s₀ k - i ∧ i < gm s₀ k ∧ LInv cbc F s₀ w k i t) ?_ (gm s₀ k - 0) s
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
abbrev Next (P : Nat → List Byte) (w : Nat) (s₀ : State) (k : Nat) (s : State) : Prop :=
  GInv P w s₀ (k + gm s₀ k) s ∧ s.zf = some (decide (k + gm s₀ k = gN s₀))

theorem finish_wp {w : Nat} (hw : w ≤ 2176) (hp : GPre s₀) {k : Nat} (hk : k < gN s₀) {s : State}
    (h : XInv cbc F s₀ w k 0 s) : WP isa finish s (Next (gP cbc F s₀) w s₀ k) := by
  have hN := n_lt s₀
  have hfit := gm_fit hk
  have hm := gm_le s₀ k
  refine WP.seq (WP.mono (xorPre_wp hw hp h) fun s₁ h₁ => WP.seq (WP.mono (xorLoop_wp hp hk h₁) fun s₂ h₂ => ?_))
  refine wp_sub fun s₃ u₃ z₃ => WP.block_nil ?_
  obtain e : BitVec.ofNat 32 (gN s₀ - k) - BitVec.ofNat 32 (gm s₀ k) = BitVec.ofNat 32 (gN s₀ - (k + gm s₀ k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_toNat_lt (show gm s₀ k < 2 ^ 32 by omega_using [hm]),
      ofNat_toNat_lt (show gN s₀ - k < 2 ^ 32 by omega_using [hN]),
      ofNat_toNat_lt (show gN s₀ - (k + gm s₀ k) < 2 ^ 32 by omega_using [hN])]
    omega_using [hN, hfit, hm]
  refine ⟨⟨hfit, by rw [u₃.other _ (by decide), h₂.x.esi], by rw [u₃.gpr, h₂.x.edi, h₂.x.ebx, e],
    by rw [u₃.other _ (by decide), h₂.x.esp], by rw [u₃.rd, h₂.x.rd], by rw [u₃.wr, h₂.x.wr],
    by rw [u₃.mem]; exact h₂.x.frame, fun j hj => ?_, by rw [u₃.mem, h₂.x.iv]⟩, ?_⟩
  · rw [u₃.mem, h₂.x.data j hj]
    show (if j < k + gm s₀ k then _ else if j < k + gm s₀ k then _ else _) = if j < k + gm s₀ k then _ else _
    by_cases h₁ : j < k + gm s₀ k
    · rw [ite_eq_left h₁, ite_eq_left h₁]
    · rw [ite_eq_right h₁, ite_eq_right h₁, ite_eq_right h₁]
  · rw [z₃, h₂.x.edi, h₂.x.ebx, e, MdStream.X86.ofNat_beq_zero (show gN s₀ - (k + gm s₀ k) < 2 ^ 32 by omega_using [hN])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hfit]))

end

/-! ## The whole function -/

/-- What `b` needs to be for `groups b cbc` to be the mode: an
implementation of the block function `f`, whose blocks are `F`'s, which
writes no byte of its working space at offset `w` or beyond. -/
structure Fn (b : Impl.Aes.X86.Blocks) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State)
    (F : Nat → List Byte → List Byte → List Byte) (w : Nat) : Prop where
  ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
    ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s'
  ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code
  wok : ∀ s, (Proof.Aes.blocksX86 f).pre s → ∀ t s', Exec isa b.code s t s' → ∀ i, w ≤ i → i < 2048 →
    s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i)
  nosp : NoSp b.code
  stack : stackUse b.code = 0
  le : w ≤ 2048
  eq : ∀ R k m p, (f R k (Spec.Aes.stateAt m p)).toList = F R k (bytesAt m p 16)

section
variable {b : Impl.Aes.X86.Blocks} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {F : Nat → List Byte → List Byte → List Byte} {w : Nat} (hb : Fn b f F w) {cbc : Bool}
include hb

theorem Fn.le' : w ≤ 2176 := Nat.le_trans hb.le (by decide)

variable {s₀ : State} (hp : GPre s₀)
include hp

theorem body_wp {k : Nat} (hk : k < gN s₀) {s : State} (h : GInv (gP cbc F s₀) w s₀ k s) :
    WP isa (body b cbc) s (Next (gP cbc F s₀) w s₀ k) :=
  WP.seq (WP.mono (fill_wp hb.le' cbc hp hk h) fun _ h₁ =>
    WP.seq (WP.mono (call_wp hb.ok hb.wok hb.nosp hb.stack hb.eq hb.le hp hk h₁) fun _ h₂ =>
      finish_wp hb.le' hp hk h₂))

theorem loop_wp (hn : 0 < gN s₀) {s : State} (h : GInv (gP cbc F s₀) w s₀ 0 s) :
    WP isa (.loop (body b cbc) .ne) s (GInv (gP cbc F s₀) w s₀ (gN s₀)) := by
  refine WP.loop (M := isa) (body := body b cbc) (c := .ne) (Q := GInv (gP cbc F s₀) w s₀ (gN s₀))
    (fun (n : Nat) (t : State) => ∃ k, n = gN s₀ - k ∧ k < gN s₀ ∧ GInv (gP cbc F s₀) w s₀ k t) ?_ (gN s₀ - 0) s
    ⟨0, rfl, hn, h⟩
  rintro n t ⟨k, rfl, hk, h⟩
  refine WP.mono (body_wp hb hp hk h) fun s' ⟨h', hz⟩ => ?_
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

theorem mid_wp {s : State} (h : GInv (gP cbc F s₀) w s₀ 0 s) (hz : s.zf = some (decide (gN s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body b cbc) .ne)) s (GInv (gP cbc F s₀) w s₀ (gN s₀)) := by
  obtain ev : isa.eval .e s = some (decide (gN s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, hz]
  by_cases hn : gN s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · exact WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ =>
      loop_wp hb hp (Nat.pos_of_ne_zero hn) h

end

theorem next_blocks (s₀ : State) :
    Spec.Cbc.next (bytesAt s₀.mem ((gIv s₀).setWidth 64) 16) (Spec.Cbc.blocksAt s₀.mem ((gD s₀).setWidth 64) (gN s₀)) =
      prev s₀ (gN s₀) := by
  unfold Spec.Cbc.next prev
  generalize gN s₀ = n
  cases n with
  | zero => rfl
  | succ n =>
    rw [ite_eq_right (Nat.succ_ne_zero n), Spec.Cbc.blocksAt, List.range_succ, List.map_append]
    simp

/-- The contract's postcondition, from the invariant after all the blocks. -/
theorem post_of {M : Mode} {cbc : Bool} {F : Nat → List Byte → List Byte → List Byte} (hM : Par M cbc F) {w : Nat}
    {s₀ : State} (hp : GPre s₀) {s s' : State}
    (h : GInv (gP cbc F s₀) w s₀ (gN s₀) s) (hm : s'.mem = s.mem) : (groupsX86 M w).post s₀ s' := by
  refine ⟨⟨?_, ?_⟩, fun i hi hl => ?_⟩
  · show Spec.Cbc.blocksAt s'.mem ((gD s₀).setWidth 64) (gN s₀) = M.out (gR s₀) (gK s₀)
      (bytesAt s₀.mem ((gIv s₀).setWidth 64) 16) (Spec.Cbc.blocksAt s₀.mem ((gD s₀).setWidth 64) (gN s₀))
    obtain hl₀ : (Spec.Cbc.blocksAt s₀.mem ((gD s₀).setWidth 64) (gN s₀)).length = gN s₀ := length_blocksAt _ _ _
    refine List.ext_getElem? fun j => ?_
    by_cases hj : j < gN s₀
    · rw [List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hj), getElem_blocksAt _ _ hj,
        hM.out _ _ _ _ _ (by rw [hl₀]; exact hj), getElem_blocksAt _ _ hj, hm, h.data j hj]
      refine congrArg some ?_
      show (if j < gN s₀ then gP cbc F s₀ j else _) = _
      rw [ite_eq_left hj, gP]
      refine congrArg (fun c => plain cbc (F (gR s₀) (gK s₀)) c (ct s₀ j)) ?_
      cases j with
      | zero => rfl
      | succ j =>
        have hj' : j < gN s₀ := Nat.lt_of_succ_lt hj
        rw [prev_succ, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hl₀]; exact hj'), getElem_blocksAt _ _ hj', Option.getD_some]
    · rw [List.getElem?_eq_none (by rw [length_blocksAt]; exact Nat.le_of_not_lt hj),
        List.getElem?_eq_none (by rw [M.length_out, hl₀]; exact Nat.le_of_not_lt hj)]
  · show bytesAt s'.mem ((gIv s₀).setWidth 64) 16 = M.chain (gR s₀) (gK s₀)
      (bytesAt s₀.mem ((gIv s₀).setWidth 64) 16) (Spec.Cbc.blocksAt s₀.mem ((gD s₀).setWidth 64) (gN s₀))
    rw [hM.chain, next_blocks, hm, h.iv]
  · show s'.mem ((gS s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((gS s₀).setWidth 64 + BitVec.ofNat 64 i)
    obtain hc : (scrR s₀).Contains ((gS s₀).setWidth 64 + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base _ (by omega_using [hl]) (by omega_using [hl])
    rw [hm, h.frame _ fun r hr hcr => ?_]
    · exact svMem_buf s₀ _ fun r hr hcr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.scr_buf _ hc hcr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.iv_scr _ hcr hc
      · exact hp.data_scr _ hcr hc
      · simp only [Region.Contains] at hcr
        rw [Mem.sub_ofNat_toNat _ (by omega_using [hl])] at hcr
        omega_using [hcr, hi]
      · exact hp.scr_buf _ hc (blk_buf _ hcr)
      · exact hp.stk_scr _ hcr hc

section
variable {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
  {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {F : Nat → List Byte → List Byte → List Byte} {w : Nat} (hM : Par M cbc F) (hb : Fn b f F w)
include hM hb

theorem groups_correct (s : State) (hs : (groupsX86 M w).pre s) :
    ∃ t s', Exec isa (groups b cbc) s t s' ∧ abiPreserved s s' ∧ (groupsX86 M w).post s s' := by
  obtain hp := GPre.of hs
  show WP isa (groups b cbc) s fun s' => abiPreserved s s' ∧ (groupsX86 M w).post s s'
  exact WP.seq (WP.mono (setup_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ z₁) fun s₂ h₂ =>
      WP.mono (restore_wp hb.le' hp h₂) fun s₃ ⟨a, m⟩ => ⟨a, post_of hM hp h₂ m⟩))

end

/-! ## Constant time -/

/-- What two runs agree on at a point between the calls. -/
structure Pt (s₀ s : State) : Prop where
  esp : s.gpr .esp = gE s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

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

theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) : arg s i = arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

theorem fill_taint (cbc : Bool) :
    ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 7)) (fill cbc) h).isSome = true := by
  cases cbc <;> exact ⟨_, by taint_decide⟩

theorem finish_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi, .ebx] (4 + 4 * 7)) finish h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem setup_taint : ∃ h, (sseTaint.check (argTaint [] (4 + 4 * 7)) (.block setup) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (sseTaint.check (argTaint [] (4 + 4 * 7)) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A piece of code the taint analysis checks from the registers `rs`, `esp`
and the stack arguments, which agree in two runs, with what each run
reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (sseTaint.check (argTaint rs (4 + 4 * 7)) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) s₁ s₂)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := sseTaint) (P := P) _ ha ht).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem GInv.pt {P : Nat → List Byte} {w : Nat} (hw : w ≤ 2176) {s₀ : State} (hp : GPre s₀) {k : Nat} {s : State}
    (h : GInv P w s₀ k s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of hw h.frame) hi⟩

theorem XInv.pt {cbc : Bool} {F : Nat → List Byte → List Byte → List Byte} {w : Nat} (hw : w ≤ 2176) {s₀ : State}
    (hp : GPre s₀) {k i : Nat} {s : State} (h : XInv cbc F s₀ w k i s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of hw h.frame) hi⟩

section
variable {M : Mode} {w : Nat} {s₀ s₀' : State} (hq : (groupsX86 M w).pub s₀ s₀')
include hq

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree (hp : GPre s₀) (hp' : GPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂)
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
theorem pub_dst (cbc : Bool) (k : Nat) : dst cbc s₀ k = dst cbc s₀' k := by
  rw [dst, dst, pub_B hq, pub_d32 hq]

end

section
variable {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
  {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
  {F : Nat → List Byte → List Byte → List Byte} {w : Nat} (hb : Fn b f F w)
  {s₀ s₀' : State} (hq : (groupsX86 M w).pub s₀ s₀') (hp : GPre s₀) (hp' : GPre s₀')
include hb hq hp hp'

/-- One group, in two runs. -/
theorem body_rel {k : Nat} (hk : k < gN s₀) :
    RelCT isa (fun a b => GInv (gP cbc F s₀) w s₀ k a ∧ GInv (gP cbc F s₀') w s₀' k b) (body b cbc)
      fun a b => Next (gP cbc F s₀) w s₀ k a ∧ Next (gP cbc F s₀') w s₀' k b := by
  have hk' : k < gN s₀' := by rw [← pub_N hq]; exact hk
  have a := taint_rel [.esi, .edi] (fill_taint cbc)
    (P := fun a b => GInv (gP cbc F s₀) w s₀ k a ∧ GInv (gP cbc F s₀') w s₀' k b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hb.le' hp) (h.2.pt hb.le' hp') fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.esi, h.2.esi, pub_d32 hq]
      · rw [h.1.edi, h.2.edi, pub_N hq])
    (F₁ := Mid (gP cbc F s₀) w cbc s₀ k) (F₂ := Mid (gP cbc F s₀') w cbc s₀' k)
    fun _ _ h => ⟨fill_wp hb.le' cbc hp hk h.1, fill_wp hb.le' cbc hp' hk' h.2⟩
  have c := (RelCT.mono (AesOcb.X86.blk_ct (fn := ⟨b.name, b.code⟩) hb.ok hb.ct
      (I := fun s => BCall s (gW s₀) (dst cbc s₀ k) (gS s₀) (gR s₀) (gm s₀ k) ∧ s.gpr .esp = gE s₀)
      fun _ h => h)
      (P' := fun a b => Mid (gP cbc F s₀) w cbc s₀ k a ∧ Mid (gP cbc F s₀') w cbc s₀' k b)
      (fun _ _ h => ⟨⟨h.1.bc, h.1.esp⟩, by
        rw [pub_W hq, pub_dst hq, pub_S hq, pub_R hq, pub_gm hq, pub_E hq]; exact ⟨h.2.bc, h.2.esp⟩⟩)
      fun _ _ _ => trivial).wp
    (F₁ := XInv cbc F s₀ w k 0) (F₂ := XInv cbc F s₀' w k 0)
    fun _ _ h => ⟨call_wp hb.ok hb.wok hb.nosp hb.stack hb.eq hb.le hp hk h.1,
      call_wp hb.ok hb.wok hb.nosp hb.stack hb.eq hb.le hp' hk' h.2⟩
  have d := taint_rel [.esi, .edi, .ebx] finish_taint
    (P := fun a b => XInv cbc F s₀ w k 0 a ∧ XInv cbc F s₀' w k 0 b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hb.le' hp) (h.2.pt hb.le' hp') fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.esi, h.2.esi, pub_d32 hq]
      · rw [h.1.edi, h.2.edi, pub_N hq]
      · rw [h.1.ebx, h.2.ebx, pub_gm hq])
    (F₁ := Next (gP cbc F s₀) w s₀ k) (F₂ := Next (gP cbc F s₀') w s₀' k)
    fun _ _ h => ⟨finish_wp hb.le' hp hk h.1, finish_wp hb.le' hp' hk' h.2⟩
  exact a.seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq d)

/-- The groups, in two runs. -/
theorem loop_rel (hn : 0 < gN s₀) :
    RelCT isa (fun a b => GInv (gP cbc F s₀) w s₀ 0 a ∧ GInv (gP cbc F s₀') w s₀' 0 b) (.loop (body b cbc) .ne)
      fun a b => GInv (gP cbc F s₀) w s₀ (gN s₀) a ∧ GInv (gP cbc F s₀') w s₀' (gN s₀') b := by
  have hN := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ k, n = gN s₀ - k ∧ k < gN s₀ ∧ GInv (gP cbc F s₀) w s₀ k s₁ ∧ GInv (gP cbc F s₀') w s₀' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (gN s₀ - 0)).mono
    (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hc : n = gN s₀ - k ∧ k < gN s₀
  swap
  · exact RelCT.of_false fun _ _ h => hc ⟨h.1, h.2.1⟩
  obtain ⟨rfl, hk⟩ := hc
  refine (body_rel hb hq hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
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

theorem groups_rel : RelCT isa (fun x y => x = s₀ ∧ y = s₀') (groups b cbc) fun _ _ => True := by
  have hN := pub_N hq
  obtain pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := taint_rel [] setup_taint (P := fun x y => x = s₀ ∧ y = s₀')
    (fun x y h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (F₁ := fun (s : State) => GInv (gP cbc F s₀) w s₀ 0 s ∧ s.zf = some (decide (gN s₀ = 0)))
    (F₂ := fun (s : State) => GInv (gP cbc F s₀') w s₀' 0 s ∧ s.zf = some (decide (gN s₀' = 0)))
    fun x y h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨setup_wp hp, setup_wp hp'⟩
  have c : RelCT isa (fun x y => (GInv (gP cbc F s₀) w s₀ 0 x ∧ x.zf = some (decide (gN s₀ = 0))) ∧
      GInv (gP cbc F s₀') w s₀' 0 y ∧ y.zf = some (decide (gN s₀' = 0)))
      (.ite .e (.block []) (.loop (body b cbc) .ne))
      fun x y => GInv (gP cbc F s₀) w s₀ (gN s₀) x ∧ GInv (gP cbc F s₀') w s₀' (gN s₀') y := by
    refine RelCT.ite (fun x y h => ?_) ?_ ?_
    · show x.zf = y.zf; rw [h.1.2, h.2.2, hN]
    · refine RelCT.block_nil fun x y h => ?_
      obtain h0 : gN s₀ = 0 := by
        have := h.2; change x.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨h0 ▸ h.1.1.1, by rw [← hN, h0]; exact h.1.2.1⟩
    · refine (RelCT.exists_ fun (hn : 0 < gN s₀) => loop_rel hb hq hp hp' hn).mono
        (fun x y h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; change x.zf = _ at this; rw [h.1.1.2] at this
      have : gN s₀ ≠ 0 := by simpa using this
      omega_using [this]
  obtain ⟨_, t₃⟩ := restore_taint
  have d := RelCT.taint (A := sseTaint)
    (P := fun x y => GInv (gP cbc F s₀) w s₀ (gN s₀) x ∧ GInv (gP cbc F s₀') w s₀' (gN s₀') y) _
    (fun _ _ h => Pt.agree (rs := []) hq hp hp' (h.1.pt hb.le' hp) (h.2.pt hb.le' hp') fun r hr => by simp at hr) t₃
  exact a.seq (c.seq d)

end

theorem groups_ct {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
    {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {F : Nat → List Byte → List Byte → List Byte} {w : Nat}
    (hb : Fn b f F w) :
    ConstantTime isa (groupsX86 M w).pre (groupsX86 M w).pub (groups b cbc) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (groups_rel hb hq (GPre.of h₁) (GPre.of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified`, and with `buf` on the stack -/

open VG.Proof.AesCbc.Wipe (pre decPost tailPost vs_eq bufs_eq blocksAt_congr pre_local)
open VG.Proof.AesEcb (agree_of bytesAt_congr n_le)

/-- The mode's postcondition, for the key schedule it is given and 10, 12 or
14 rounds (so that it reads only the schedule's 240 bytes), with the bytes
of `scratch` at offset `w` and beyond unchanged. -/
def modePost (M : Mode) (w : Nat) (pb : Nat) : Spec.Cbc.aesSig.Post pb :=
  fun schedule rounds iv data n scratch m m' _ =>
    ((rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
      Spec.Cbc.blocksAt m' data n.toNat = M.out rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))
          (bytesAt m iv 16) (Spec.Cbc.blocksAt m data n.toNat) ∧
        bytesAt m' iv 16 = M.chain rounds.toNat (bytesAt m schedule (16 * (rounds.toNat + 1)))
          (bytesAt m iv 16) (Spec.Cbc.blocksAt m data n.toNat)) ∧
      ∀ i, w ≤ i → i < 2176 → m' (scratch + BitVec.ofNat 64 i) = m (scratch + BitVec.ofNat 64 i)

/-- The contract the frame needs: `buf`, 1040 bytes, as a seventh argument,
and 24 bytes of stack (the block function's arguments and return address). -/
abbrev groupsContract (M : Mode) (w : Nat) : Contract isa :=
  Sig.scratchContract X86.abi Spec.Cbc.aesSig "buf" .u64 130 (pre X86.abi.ptrBits)
    (modePost M w X86.abi.ptrBits) false 24

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the block at `0x2000`, no data at `0x3000`, the scratch buffer at
`0x4000` and `buf` at `0x5000`, as stack arguments at `0x8004`. -/
def sat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40
    else if a = 0x801d then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x5000, 1040⟩]

theorem groups_implies (M : Mode) (w : Nat) : (groupsX86 M w).Implies (groupsContract M w) := by
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
        Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
    post := by
      intro s s' _ h
      sig_post [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
      exact ⟨fun _ => h.1, h.2⟩
    pub := by
      sig_implies_pub [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
    sat := by
      sig_implies_sat [groupsContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
        Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, groupsX86]
        [a0, a1, a2, a3, a4, a5, a6, e, esp] using sat }

/-- `modePost` reads the memory on entry only within the buffers. -/
theorem modePost_local (M : Mode) (w pb : Nat) :
    ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words pb).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words pb) (modePost M w pb) vs m₁ m' x →
        Curry.apply (Spec.Cbc.aesSig.words pb) (modePost M w pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have hs := agree_of hb.1
  have hd := agree_of hb.2.2.1
  have hf := agree_of hb.2.2.2
  have ed : Spec.Cbc.blocksAt m₂ d (e.setWidth pb).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth pb).toNat :=
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  have ec : bytesAt m₂ c 16 = bytesAt m₁ c 16 := bytesAt_congr (agree_of hb.2.1)
  refine ⟨fun hr => ?_, fun i hi hl => ?_⟩
  · have es : bytesAt m₂ a (16 * ((b.setWidth pb).toNat + 1)) = bytesAt m₁ a (16 * ((b.setWidth pb).toNat + 1)) :=
      bytesAt_congr fun i hi => hs i (by
        have hr' : (b.setWidth pb).toNat = 10 ∨ (b.setWidth pb).toNat = 12 ∨ (b.setWidth pb).toNat = 14 := hr
        rcases hr' with h | h | h <;> omega_using [h, hi])
    have h1 := h.1 hr
    show Spec.Cbc.blocksAt m' d (e.setWidth pb).toNat = M.out (b.setWidth pb).toNat
        (bytesAt m₂ a (16 * ((b.setWidth pb).toNat + 1))) (bytesAt m₂ c 16)
        (Spec.Cbc.blocksAt m₂ d (e.setWidth pb).toNat) ∧
      bytesAt m' c 16 = M.chain (b.setWidth pb).toNat (bytesAt m₂ a (16 * ((b.setWidth pb).toNat + 1)))
        (bytesAt m₂ c 16) (Spec.Cbc.blocksAt m₂ d (e.setWidth pb).toNat)
    rw [es, ec, ed]
    exact h1
  · show m' (f + BitVec.ofNat 64 i) = m₂ (f + BitVec.ofNat 64 i)
    rw [hf i hl]
    exact h.2 i hi hl

/-- `modePost` reads the memory on return only within the buffers. -/
theorem modePost_localOut (M : Mode) (w pb : Nat) :
    ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words pb).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words pb) (modePost M w pb) vs m m₁ x →
        Curry.apply (Spec.Cbc.aesSig.words pb) (modePost M w pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hb h
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
  rw [bufs_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  have hd := agree_of hb.2.2.1
  have hf := agree_of hb.2.2.2
  have ed : Spec.Cbc.blocksAt m₂ d (e.setWidth pb).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth pb).toNat :=
    blocksAt_congr fun i hi => hd i (by have := n_le (pb := pb) e; omega_using [hi, this])
  have ec : bytesAt m₂ c 16 = bytesAt m₁ c 16 := bytesAt_congr (agree_of hb.2.1)
  refine ⟨fun hr => ?_, fun i hi hl => ?_⟩
  · have h1 := h.1 hr
    show Spec.Cbc.blocksAt m₂ d (e.setWidth pb).toNat = M.out (b.setWidth pb).toNat
        (bytesAt m a (16 * ((b.setWidth pb).toNat + 1))) (bytesAt m c 16)
        (Spec.Cbc.blocksAt m d (e.setWidth pb).toNat) ∧
      bytesAt m₂ c 16 = M.chain (b.setWidth pb).toNat (bytesAt m a (16 * ((b.setWidth pb).toNat + 1)))
        (bytesAt m c 16) (Spec.Cbc.blocksAt m d (e.setWidth pb).toNat)
    rw [ec, ed]
    exact h1
  · show m₂ (f + BitVec.ofNat 64 i) = m (f + BitVec.ofNat 64 i)
    rw [hf i hl]
    exact h.2 i hi hl

/-! ## The code's properties -/

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

theorem groups_noSp (b : Impl.Aes.X86.Blocks) (cbc : Bool) (h : NoSp b.code) : NoSp (groups b cbc) := by
  refine NoSp.of_all ?_
  have hb : b.code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    simp [h i hi]
  simp only [groups, body, Impl.AesOcb.X86.blocksFrame, Code.allInstrs, hb]
  cases cbc <;> decide +kernel

theorem groups_stack (b : Impl.Aes.X86.Blocks) (cbc : Bool) (h : stackUse b.code = 0) :
    stackUse (groups b cbc) ≤ 24 := by
  simp only [groups, body, Impl.AesOcb.X86.blocksFrame, stackUse, h]
  cases cbc <;> decide +kernel

theorem framed_noSp (b : Impl.Aes.X86.Blocks) (cbc : Bool) (h : NoSp b.code) : NoSp (framed b cbc) := by
  refine NoSp.of_all ?_
  have hb : (groups b cbc).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    simp [groups_noSp b cbc h i hi]
  simp only [framed, Impl.StackScratch.X86.withStackScratch, Code.allInstrs, hb]
  decide +kernel

theorem framed_stack (b : Impl.Aes.X86.Blocks) (cbc : Bool) (h : stackUse b.code = 0) :
    stackUse (framed b cbc) ≤ 1108 := by
  have hs := groups_stack b cbc h
  have e : frameBytes (.alloc bufFrame) = 1084 := by decide
  simp only [framed, Impl.StackScratch.X86.withStackScratch, stackUse, e]
  exact Nat.add_le_add_right (Nat.max_le.mpr ⟨Nat.zero_le _, hs⟩) 1084

theorem framed_spSafe (b : Impl.Aes.X86.Blocks) (cbc : Bool) (h : b.code.all (fun i => !isa.writesSp i) = true) :
    (framed b cbc).all (fun i => !isa.writesSp i) = true := by
  simp only [framed, Impl.StackScratch.X86.withStackScratch, groups, body, Impl.AesOcb.X86.blocksFrame, Code.all, h]
  cases cbc <;> decide +kernel

/-! ## `Verified` -/

theorem frameSat_pre (post : Spec.Cbc.aesSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cbc.aesSig.contract X86.abi (pre := pre X86.abi.ptrBits) (post := post) (stack := 1108)).pre
      s := by
  obtain a0 : arg AesCbc.X86.sat 0 = 0x1000 := by decide
  obtain a1 : arg AesCbc.X86.sat 1 = 10 := by decide
  obtain a2 : arg AesCbc.X86.sat 2 = 0x2000 := by decide
  obtain a3 : arg AesCbc.X86.sat 3 = 0x3000 := by decide
  obtain a4 : arg AesCbc.X86.sat 4 = 0 := by decide
  obtain a5 : arg AesCbc.X86.sat 5 = 0x4000 := by decide
  obtain e : argAddr AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Cbc.aesSig, pre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using AesCbc.X86.sat

/-- With `buf` on the stack: 1084 bytes of frame, and 24 for the block
function's arguments and return address. -/
theorem framed_verified {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
    {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {F : Nat → List Byte → List Byte → List Byte} {w : Nat}
    (hM : Par M cbc F) (hb : Fn b f F w) :
    Verified X86.target (framed b cbc)
      (Spec.Cbc.aesSig.contract X86.abi (pre X86.abi.ptrBits) (modePost M w X86.abi.ptrBits) false 1108 none) :=
  X86.Verified.stackScratch (sig := Spec.Cbc.aesSig) (nm := "buf") (e := .u64) (n := 130)
    (pre := pre X86.abi.ptrBits) (post := modePost M w X86.abi.ptrBits) (wa := false) (stack := 24)
    (bytes := bufFrame)
    (Verified.of_correct (groups_correct hM hb) (groups_ct hb) (groups_implies M w)) (by decide)
    (by
      rw [Code.allInstrs_eq, List.all_eq_true]
      intro i hi
      simp [groups_noSp b cbc hb.nosp i hi])
    (groups_stack b cbc hb.stack) (pre_local _) (modePost_local M w _)
    (fun vs m m₁ m₂ x hl _ => modePost_localOut M w _ vs m m₁ m₂ x hl) (frameSat_pre _)

/-- `modeX86K`, with the return address apart from the key schedule too, as
the shared contracts have it. -/
def wholeX86 (M : Mode) (k : Nat) : Contract isa :=
  { modeX86K M k with
    pre := fun s => (modeX86K M k).pre s ∧
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 240⟩ }

/-- CBC decryption's contract without its clause on `scratch`, which is
unchanged from offset `w` on, from `modePost`. -/
theorem cbc_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w : Nat}
    (h : Verified T c (Spec.Cbc.aesSig.contract A (pre A.ptrBits) (modePost (cbcMode false) w A.ptrBits) false stack
      none)) :
    Verified T c (Spec.Cbc.aesSig.contract A (pre A.ptrBits) (tailPost A.ptrBits w (decPost A.ptrBits)) false stack
      none) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp => by
    dsimp only [modePost] at hp
    refine ⟨fun key ⟨hk, hr, hw⟩ => ?_, hp.2⟩
    have h' := hp.1 (by rw [hr]; rcases hk with h | h | h <;> rw [h] <;> decide)
    rw [hw, hr] at h'
    exact h'

/-- CFB128 decryption's contract, from `modePost`. -/
theorem cfb_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack w : Nat}
    (h : Verified T c (Spec.Cbc.aesSig.contract A (pre A.ptrBits) (modePost (AesCfb.cfbMode false) w A.ptrBits) false
      stack none)) : Verified T c (Spec.Cfb.aesDecryptContract A stack) :=
  Verified.post_mono (post := modePost (AesCfb.cfbMode false) w A.ptrBits) h
    fun _ _ _ _ _ _ _ _ _ hp key ⟨hk, hr, hw⟩ => by
      dsimp only [modePost] at hp
      have h' := hp.1 (by rw [hr]; rcases hk with h | h | h <;> rw [h] <;> decide)
      rw [hw, hr] at h'
      exact h'

/-- What `wholeX86` asks for is what the shared contract does. -/
theorem framed_pre {M : Mode} {w : Nat} (s : State) (h : (wholeX86 M 1108).pre s) :
    (Spec.Cbc.aesSig.contract X86.abi (pre X86.abi.ptrBits) (modePost M w X86.abi.ptrBits) false 1108 none).pre s := by
  sig_pre [Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25⟩, a26⟩ := h
  have e : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [a24])
  have ra : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩ := by
    rw [e]; exact Offset.base_disjoint _ (Nat.le_refl _) (by decide)
  have sa : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 1108, 1108⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩ := by
    rw [e]; exact Offset.disjoint_below_above _ (by decide)
  have a9' := a9.symm
  have a10' := a10.symm
  have a11' := a11.symm
  simp only [Nat.mul_comm (arg s 4).toNat 16]
  exact ⟨a23, by omega_using [a24], a1, a2, a3, a4, a5, a6, a7, a9', a8, a10', a11', a26, a12, a13, a14, ra, a15, a16,
    a17, a18, sa, a19, a20, a21, a22, a25⟩

/-- The framed code runs to the modes' contract on their own states. -/
theorem framed_correct {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
    {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {F : Nat → List Byte → List Byte → List Byte} {w : Nat}
    (hM : Par M cbc F) (hb : Fn b f F w) (s : State) (hs : (wholeX86 M 1108).pre s) :
    ∃ t s', Exec isa (framed b cbc) s t s' ∧ abiPreserved s s' ∧ (wholeX86 M 1108).post s s' := by
  obtain ⟨t, s', he, ha, hq⟩ := (framed_verified hM hb).1 s (framed_pre s hs)
  refine ⟨t, s', he, ha, ?_⟩
  revert hq
  sig_post [Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  intro hq
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hr⟩, -⟩ := hs
  exact hq.1 hr

theorem framed_ct {M : Mode} {cbc : Bool} {b : Impl.Aes.X86.Blocks}
    {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {F : Nat → List Byte → List Byte → List Byte} {w : Nat}
    (hM : Par M cbc F) (hb : Fn b f F w) :
    ConstantTime isa (wholeX86 M 1108).pre (wholeX86 M 1108).pub (framed b cbc) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  refine (framed_verified hM hb).2.1 s₁ s₂ t₁ t₂ s₁' s₂' (framed_pre s₁ h₁) (framed_pre s₂ h₂) ?_ e₁ e₂
  sig_pub_keep [Spec.Cbc.aesSig, pre, modePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  exact ⟨hq.1, hq.2 0 (by decide), hq.2 1 (by decide), hq.2 2 (by decide), hq.2 3 (by decide), hq.2 4 (by decide),
    hq.2 5 (by decide)⟩

/-! ## The implementations of the block functions -/

/-- `v`'s `vg_aes_decrypt_blocks`, for CBC. -/
theorem fn_dec (v : BlocksImpl) : Fn v.dec Spec.Aes.invCipher (ciphOf false) v.decWritten :=
  ⟨v.decOk, v.decCt, v.decWrittenOk, v.decNosp, v.decStack, v.decWrittenLe, fun R k m p => (aesInvWith_state R k m p).symm⟩

/-- `v`'s `vg_aes_encrypt_blocks`, for CFB128. -/
theorem fn_enc (v : BlocksImpl) : Fn v.enc Spec.Aes.cipher Spec.Cbc.aesWith v.encWritten :=
  ⟨v.encOk, v.encCt, v.encWrittenOk, v.encNosp, v.encStack, v.encWrittenLe, fun R k m p => (aesWith_state R k m p).symm⟩

end VG.Proof.AesCbc.X86.Groups
