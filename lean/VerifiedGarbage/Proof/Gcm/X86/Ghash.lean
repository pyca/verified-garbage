module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Gcm.X86
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Gcm.X86
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Aes.X86.Common
meta import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Gcm.X86.GhashCT`, which this module and modules that import it used -/

section

/-!
# GHASH on x86 (32-bit): the contract, and constant time

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of `y` and the scratch buffer. The data pointer and the counters live in
public slots of the scratch buffer, and every other store goes through
`edi` (the scratch buffer) or the `y` pointer, which keeps them.
-/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16],
data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`, whose arguments are
on the stack: replaces the block `Y` at `y` with `GHASH_H` continued from `Y`
over the `n` blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes), `data` (`16 n` bytes) and the arguments
(20 bytes above the return address), and read and write `y` (16 bytes) and
`scratch` (256 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the other buffers, the arguments or the
return address; nothing may wrap around the end of the (32-bit) address
space. `esp` and the arguments are public; `H`, `Y` and the data are
secret. -/
def ghashX86 : Contract X86.isa where
  pre s :=
    let h : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let y : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [h, data, args] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint y ∧ args.Disjoint scratch ∧ ret.Disjoint y ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    blockAt s'.mem ((arg s 1).setWidth 64) =
      ghashFrom (blockAt s.mem ((arg s 0).setWidth 64)) (blockAt s.mem ((arg s 1).setWidth 64))
        (blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Gcm

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Proof.Aes.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev hP : BitVec 32 := arg s 0
abbrev yP : BitVec 32 := arg s 1
abbrev dP : BitVec 32 := arg s 2
abbrev nBlk : Nat := (arg s 3).toNat
abbrev sP : BitVec 32 := arg s 4
abbrev hR : Region := reg32 (hP s) 16
abbrev yR : Region := reg32 (yP s) 16
abbrev dR : Region := reg32 (dP s) (16 * nBlk s)
abbrev sR : Region := reg32 (sP s) 256
abbrev aR : Region := ⟨argAddr s 0, 20⟩
abbrev rR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `ghashX86.pre`, by name. -/
structure GPre (s : State) : Prop where
  rd : s.rd = [hR s, dR s, aR s]
  wr : s.wr = [yR s, sR s]
  dHY : (hR s).Disjoint (yR s)
  dHS : (hR s).Disjoint (sR s)
  dYD : (yR s).Disjoint (dR s)
  dYS : (yR s).Disjoint (sR s)
  dDS : (dR s).Disjoint (sR s)
  aY : (aR s).Disjoint (yR s)
  aS : (aR s).Disjoint (sR s)
  rY : (rR s).Disjoint (yR s)
  rS : (rR s).Disjoint (sR s)
  fH : (hP s).toNat + 16 ≤ 2 ^ 32
  fY : (yP s).toNat + 16 ≤ 2 ^ 32
  fD : (dP s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fS : (sP s).toNat + 256 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem GPre.of {s : State} (h : Proof.Gcm.ghashX86.pre s) : GPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding `y`
and `scratch` known to be the base addresses of the writable regions. -/
def ghτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 256], argLen := 24,
    argBases := [(8, 0), (20, 1)] }

theorem gh_wf₀ {s : State} (hp : GPre s) : VG.X86.Taint.Wf ghτ₀ s := by
  have hY := hp.fY; have hS := hp.fS; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ghτ₀]; omega_using [hs], ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨hp.dYS, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.rY hp.aY
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.rS hp.aS
  · intro p hp'
    simp only [ghτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem gh_agree₀ {s₁ s₂ : State} (h₁ : Proof.Gcm.ghashX86.pre s₁) (h₂ : Proof.Gcm.ghashX86.pre s₂)
    (hpub : Proof.Gcm.ghashX86.pub s₁ s₂) : VG.X86.Taint.Agree ghτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := GPre.of h₁; have hp₂ := GPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, gh_wf₀ hp₁, gh_wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ghτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [yR, sR, yP, sP, ha 1 (by decide), ha 4 (by decide)]
  · simp only [ghτ₀] at hk
    rw [show VG.X86.Taint.depth ghτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86.pre Proof.Gcm.ghashX86.pub Impl.Gcm.X86.ghash :=
  VG.Taint.constantTime (A := VG.X86.taint) ghτ₀ (fun _ _ h₁ h₂ hp => gh_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Gcm.X86

end

end

/-! ### `Gcm.X86.Step`, which only this module used -/

section

/-!
# GHASH on x86 (32-bit): one step of Algorithm 1

What the instructions of a step (`Impl.Gcm.X86.step`) compute on the four
words of `V` (in registers) and of `Z` (in the scratch buffer), stated on the
whole 128-bit values, and the 128 steps of a multiplication.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Impl.Gcm.X86 VG.Proof.Gcm VG.Proof.Aes.X86
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_add wp_addi wp_subi wp_ldm wp_xorm wp_stm wp_shr wp_ror
  wp_and wp_andi wp_or wp_xor wp_sbb_self ofNat_pred ofNat_beq_zero)
open VG.Spec.Gcm (Block)

/-! ## 128-bit values as four words -/

/-- A block from four words, the first the most significant. -/
def cat4 (a b c d : BitVec 32) : Block := a ++ b ++ c ++ d

theorem getLsbD_cat4 (a b c d : BitVec 32) (i : Nat) :
    (cat4 a b c d).getLsbD i =
      if i < 32 then d.getLsbD i else if i < 64 then c.getLsbD (i - 32)
      else if i < 96 then b.getLsbD (i - 64) else a.getLsbD (i - 96) := by
  simp only [cat4, BitVec.getLsbD_append]
  by_cases h1 : i < 32
  · simp [h1]
  · by_cases h2 : i < 64
    · simp [h1, h2, show i - 32 < 32 by omega_arith]
    · by_cases h3 : i < 96
      · simp [h1, h2, h3, show ¬ i - 32 < 32 by omega_arith, show i - 32 - 32 = i - 64 by omega_arith,
          show i - 64 < 32 by omega_arith]
      · simp [h1, h2, h3, show ¬ i - 32 < 32 by omega_arith, show i - 32 - 32 = i - 64 by omega_arith,
          show ¬ i - 64 < 32 by omega_arith, show i - 64 - 32 = i - 96 by omega_arith]

/-- The mask `sbb r, r` makes from a carry. -/
abbrev msk (c : Bool) : BitVec 32 := if c then BitVec.allOnes 32 else 0

/-- `Z ^= V & m`, word by word. -/
theorem z_update (z0 z1 z2 z3 v0 v1 v2 v3 : BitVec 32) (c : Bool) :
    cat4 ((v0 &&& msk c) ^^^ z0) ((v1 &&& msk c) ^^^ z1) ((v2 &&& msk c) ^^^ z2) ((v3 &&& msk c) ^^^ z3) =
      if c then cat4 z0 z1 z2 z3 ^^^ cat4 v0 v1 v2 v3 else cat4 z0 z1 z2 z3 := by
  cases c
  · simp [msk]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [msk, ite_true, BitVec.and_allOnes, BitVec.getLsbD_xor, getLsbD_cat4]
    split <;> [exact Bool.xor_comm _ _; split <;> [exact Bool.xor_comm _ _; split <;> exact Bool.xor_comm _ _]]

theorem topBit_bit {i : Nat} (hi : i < 32) : topBit.getLsbD i = decide (i = 31) := by
  obtain h : ∀ i < 32, topBit.getLsbD i = decide (i = 31) := by decide
  exact h i hi

/-- The lowest bit of `p`, moved to the top. -/
theorem carry_bit (p : BitVec 32) {i : Nat} (hi : i < 32) :
    (p.rotateRight 1 &&& topBit).getLsbD i = (decide (i = 31) && p.getLsbD 0) := by
  rw [BitVec.getLsbD_and, topBit_bit hi, BitVec.getLsbD_rotateRight]
  by_cases h : i = 31
  · subst h; simp
  · simp [h]

/-- One word's lowest bit moved into the top of the next, and both shifted. -/
theorem shr1 {n : Nat} (x : BitVec n) (y p : BitVec 32) (hp : p.getLsbD 0 = x.getLsbD 0) :
    x >>> 1 ++ (y >>> 1 ||| (p.rotateRight 1 &&& topBit)) = (x ++ y) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  by_cases h1 : i < 32
  · rw [ite_eq_left h1, carry_bit p h1]
    by_cases h2 : i = 31
    · subst h2; simp only [BitVec.getLsbD_of_ge y 32 (by decide)]; simpa using hp
    · simp [h2, show 1 + i < 32 by omega_arith]
  · rw [ite_eq_right h1, ite_eq_right (show ¬ 1 + i < 32 by omega_arith)]
    congr 1; omega_arith

theorem xor_top (a b c d m : BitVec 32) : cat4 (a ^^^ m) b c d = cat4 a b c d ^^^ cat4 m 0 0 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_cat4]
  split <;> [simp; split <;> [simp; split <;> simp]]

theorem R_eq : Spec.Gcm.R = cat4 rTop 0 0 0 := by decide

/-- `V := (V >> 1) ⊕ (R ∧ m)`, word by word. -/
theorem v_update (a b c d : BitVec 32) :
    cat4 ((a >>> 1) ^^^ (msk (d.getLsbD 0) &&& rTop)) ((b >>> 1) ||| (a.rotateRight 1 &&& topBit))
        ((c >>> 1) ||| (b.rotateRight 1 &&& topBit)) ((d >>> 1) ||| (c.rotateRight 1 &&& topBit)) =
      if (cat4 a b c d).getLsbD 0 then (cat4 a b c d >>> 1) ^^^ Spec.Gcm.R else cat4 a b c d >>> 1 := by
  obtain e : cat4 (a >>> 1) ((b >>> 1) ||| (a.rotateRight 1 &&& topBit))
      ((c >>> 1) ||| (b.rotateRight 1 &&& topBit)) ((d >>> 1) ||| (c.rotateRight 1 &&& topBit)) =
      cat4 a b c d >>> 1 := by
    unfold cat4
    rw [shr1 a b a rfl, shr1 (a ++ b) c b (by rw [BitVec.getLsbD_append]; rfl),
      shr1 (a ++ b ++ c) d c (by rw [BitVec.getLsbD_append]; rfl)]
  obtain h0 : (cat4 a b c d).getLsbD 0 = d.getLsbD 0 := by rw [getLsbD_cat4]; rfl
  rw [xor_top, e, h0, R_eq]
  cases d.getLsbD 0
  · simp only [msk, Bool.false_eq_true, ite_false]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_xor, getLsbD_cat4]
    split <;> [simp; split <;> [simp; split <;> simp]]
  · simp only [msk, ite_true, BitVec.allOnes_and]

/-! ## The bits of `X` -/

theorem add_self_carry (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.msb := by
  rw [BitVec.msb_eq_decide]
  simp only [Nat.add_one_sub_one, decide_eq_decide]
  omega_arith

theorem add_self (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1; omega_arith

/-- Word `w` of a block, the first the most significant. -/
def xw (x : Block) (w : Nat) : BitVec 32 := x.extractLsb' (32 * (3 - w)) 32

theorem msb_xw (x : Block) {w k : Nat} (hw : w < 4) (hk : k < 32) :
    ((xw x w) <<< k).msb = x.getMsbD (32 * w + k) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, xw, BitVec.getLsbD_extractLsb',
    BitVec.getMsbD]
  simp only [show 32 - 1 < 32 by decide, decide_true, Bool.true_and, show ¬ 32 - 1 < k by omega_arith,
    decide_false, Bool.not_false, show 32 * w + k < 128 by omega_arith, show 32 - 1 - k < 32 by omega_arith]
  congr 1; omega_arith

/-! ## The instructions of a step -/

/-- `V`, in `eax`, `ebx`, `ecx` and `edx`. -/
def vOf (s : State) : Block := cat4 (s.gpr .eax) (s.gpr .ebx) (s.gpr .ecx) (s.gpr .edx)

/-- Word `k` of `Z`, in the scratch buffer at `B`. -/
abbrev zw (m : Mem) (B : BitVec 32) (k : Nat) : BitVec 32 := m.readW (addr B (zOff k)) 32

/-- `Z`. -/
def zOf (m : Mem) (B : BitVec 32) : Block := cat4 (zw m B 0) (zw m B 1) (zw m B 2) (zw m B 3)

theorem vReg_ne_esi (k : Nat) : vReg k ≠ .esi := by unfold vReg; split <;> decide
section
variable {s : State} {B : BitVec 32} {P : State → Prop}

/-- `m := −xᵢ`, and the first word of `X` shifted left. -/
theorem head_wp (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32) (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B 0) (s.mem.readW (addr B 0) 32 <<< 1) →
      s'.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block [.mov .esi (.mem (at_ .edi 0)), .alu .add .esi (.reg .esi), .store (at_ .edi 0) .esi,
      .alu .sbb .ebp (.reg .ebp)]) s P := by
  refine wp_ldm hb (in_rd (in_reg hw fit (by decide) (by decide))) fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ c₂ => ?_
  refine wp_stm (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hw fit (by decide) (by decide)) fun s₃ u₃ => ?_
  obtain c₃ : s₃.cf = some (s.mem.readW (addr B 0) 32).msb := by
    rw [u₃.cf, c₂, u₁.gpr, add_self_carry]
  refine wp_sbb_self c₃ fun s₄ u₄ => WP.block_nil ?_
  refine h s₄ ?_ u₄.gpr (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, add_self, u₂.mem, u₁.mem]
  · rw [u₄.other r h2, u₃.gpr, u₂.other r h1, u₁.other r h1]

/-- `Z ^= V & m`, word `k`. -/
theorem zUpd_wp (k : Nat) (hk : k < 4) (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32)
    (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B (zOff k)) ((s.gpr (vReg k) &&& s.gpr .ebp) ^^^ zw s.mem B k) →
      (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (zUpd k)) s P := by
  obtain hz : zOff k + 4 ≤ 256 := by simp only [zOff]; omega_arith
  refine wp_mov fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  refine wp_xorm (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_rd (in_reg hw fit hz (by decide))) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in_reg hw fit hz (by decide)) fun s₄ u₄ => WP.block_nil ?_
  refine h s₄ ?_ (fun r hr => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₄.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ebp (by decide), u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr]

/-- `edx >>= 1`, and `m := −LSB₁(V)`. -/
theorem mid_wp
    (h : ∀ s', s'.gpr .edx = s.gpr .edx >>> 1 → s'.gpr .ebp = msk ((s.gpr .edx).getLsbD 0) →
      (∀ r, r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      P s') :
    WP isa (.block [.shift .shr .edx 1, .alu .sbb .ebp (.reg .ebp)]) s P := by
  refine wp_shr (by decide) fun s₁ u₁ c₁ => wp_sbb_self c₁ fun s₂ u₂ => WP.block_nil ?_
  refine h s₂ (by rw [u₂.other _ (by decide), u₁.gpr]) (by rw [u₂.gpr])
    (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

theorem vReg_succ_ne {k : Nat} (hk : k < 3) : vReg (k + 1) ≠ vReg k := by
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- Word `k + 1 := (word k + 1 >> 1) | (word k << 31)` (its shift is done
already), and `word k >>= 1`. -/
theorem vCarry_wp (k : Nat) (hk : k < 3)
    (h : ∀ s', s'.gpr (vReg (k + 1)) = s.gpr (vReg (k + 1)) ||| ((s.gpr (vReg k)).rotateRight 1 &&& topBit) →
      s'.gpr (vReg k) = s.gpr (vReg k) >>> 1 →
      (∀ r, r ≠ .esi → r ≠ vReg k → r ≠ vReg (k + 1) → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (vCarry k)) s P := by
  obtain n1 := vReg_succ_ne hk
  refine wp_mov fun s₁ u₁ => wp_ror (by decide) fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_or fun s₄ u₄ => ?_
  refine wp_shr (by decide) fun s₅ u₅ _ => WP.block_nil ?_
  refine h s₅ ?_ ?_ (fun r h1 h2 h3 => ?_) (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.other _ n1, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.other _ (vReg_ne_esi _), u₂.other _ (vReg_ne_esi _),
      u₁.other _ (vReg_ne_esi _)]
  · rw [u₅.gpr, u₄.other _ n1.symm, u₃.other _ (vReg_ne_esi _), u₂.other _ (vReg_ne_esi _),
      u₁.other _ (vReg_ne_esi _)]
  · rw [u₅.other r h2, u₄.other r h3, u₃.other r h1, u₂.other r h1, u₁.other r h1]

/-- `V ^= R & m` (in its top word). -/
theorem tail_wp
    (h : ∀ s', s'.gpr .eax = s.gpr .eax ^^^ (s.gpr .ebp &&& rTop) → (∀ r, r ≠ .eax → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block [.alu .and .ebp (.imm rTop), .alu .xor .eax (.reg .ebp)]) s P := by
  refine wp_andi fun s₁ u₁ => wp_xor fun s₂ u₂ => WP.block_nil ?_
  refine h s₂ (by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)]) (fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

/-- What a step writes: the first word of `X`, and `Z`. -/
abbrev stepRegions (B : BitVec 32) : List Region := [⟨addr B 0, 4⟩, ⟨addr B 16, 16⟩]

theorem step_eq : step = ((((((((([.mov .esi (.mem (at_ .edi 0)), .alu .add .esi (.reg .esi),
    .store (at_ .edi 0) .esi, .alu .sbb .ebp (.reg .ebp)] : List Instr) ++ zUpd 0) ++ zUpd 1) ++ zUpd 2) ++
    zUpd 3) ++ ([.shift .shr .edx 1, .alu .sbb .ebp (.reg .ebp)] : List Instr)) ++ vCarry 2) ++ vCarry 1) ++
    vCarry 0) ++ ([.alu .and .ebp (.imm rTop), .alu .xor .eax (.reg .ebp)] : List Instr) := rfl

/-- One step of Algorithm 1: `Z` and `V` as `mulStep` updates them, for the
top bit of the first word of `X`, which is shifted out. -/
theorem step_ok (hb : s.gpr .edi = B) (fit : B.toNat + 256 ≤ 2 ^ 32) (hw : reg32 B 256 ∈ s.wr)
    (h : ∀ s', zOf s'.mem B = (if (s.mem.readW (addr B 0) 32).msb then zOf s.mem B ^^^ vOf s else zOf s.mem B) →
      vOf s' = (if (vOf s).getLsbD 0 then (vOf s >>> 1) ^^^ Spec.Gcm.R else vOf s >>> 1) →
      s'.mem.readW (addr B 0) 32 = s.mem.readW (addr B 0) 32 <<< 1 →
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → Frame (stepRegions B) s.mem s'.mem → P s') :
    WP isa (.block step) s P := by
  rw [step_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine head_wp hb fit hw fun s₁ m₁ e₁ g₁ rd₁ wr₁ => ?_
  obtain b₁ : s₁.gpr .edi = B := (g₁ _ (by decide) (by decide)).trans hb
  refine zUpd_wp 0 (by decide) b₁ fit (wr₁ ▸ hw) fun s₂ m₂ g₂ rd₂ wr₂ => ?_
  obtain b₂ : s₂.gpr .edi = B := (g₂ _ (by decide)).trans b₁
  refine zUpd_wp 1 (by decide) b₂ fit (wr₂ ▸ wr₁ ▸ hw) fun s₃ m₃ g₃ rd₃ wr₃ => ?_
  obtain b₃ : s₃.gpr .edi = B := (g₃ _ (by decide)).trans b₂
  refine zUpd_wp 2 (by decide) b₃ fit (wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₄ m₄ g₄ rd₄ wr₄ => ?_
  obtain b₄ : s₄.gpr .edi = B := (g₄ _ (by decide)).trans b₃
  refine zUpd_wp 3 (by decide) b₄ fit (wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₅ m₅ g₅ rd₅ wr₅ => ?_
  refine mid_wp fun s₆ edx₆ ebp₆ g₆ m₆ rd₆ wr₆ => ?_
  refine vCarry_wp 2 (by decide) fun s₇ edx₇ ecx₇ g₇ m₇ rd₇ wr₇ => ?_
  refine vCarry_wp 1 (by decide) fun s₈ ecx₈ ebx₈ g₈ m₈ rd₈ wr₈ => ?_
  refine vCarry_wp 0 (by decide) fun s₉ ebx₉ eax₉ g₉ m₉ rd₉ wr₉ => ?_
  refine tail_wp fun s₁₀ eax₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ => ?_
  -- The registers through the updates of `Z`.
  obtain g₅ : ∀ r, r ≠ .esi → r ≠ .ebp → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₅ r h1, g₄ r h1, g₃ r h1, g₂ r h1, g₁ r h1 h2]
  obtain ebp₅ : ∀ j ≤ 4, ∀ t : State, (∀ r, r ≠ .esi → t.gpr r = s₁.gpr r) → t.gpr .ebp =
      msk (s.mem.readW (addr B 0) 32).msb := fun _ _ t ht => by rw [ht _ (by decide), e₁]
  obtain x₁ : ∀ k, (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) → s₁.gpr (vReg k) = s.gpr (vReg k) := fun k hk => by
    rcases hk with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  refine h s₁₀ ?_ ?_ ?_ ?_ (by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁])
    (by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_
  · have r₄ : ∀ r, r ≠ .esi → r ≠ .ebp → s₄.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₄ r h1, g₃ r h1, g₂ r h1, g₁ r h1 h2]
    obtain r₃ : ∀ r, r ≠ .esi → r ≠ .ebp → s₃.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₃ r h1, g₂ r h1, g₁ r h1 h2]
    obtain r₂ : ∀ r, r ≠ .esi → r ≠ .ebp → s₂.gpr r = s.gpr r := fun r h1 h2 => by
      rw [g₂ r h1, g₁ r h1 h2]
    obtain p₄ : s₄.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₄ _ (by decide), g₃ _ (by decide),
      g₂ _ (by decide), e₁]
    obtain p₃ : s₃.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₃ _ (by decide),
      g₂ _ (by decide), e₁]
    obtain p₂ : s₂.gpr .ebp = msk (s.mem.readW (addr B 0) 32).msb := by rw [g₂ _ (by decide), e₁]
    rw [m₁₀, m₉, m₈, m₇, m₆]
    have fit' := fit
    simp (disch := decide) only [zOf, zw, zOff, m₅, m₄, m₃, m₂, m₁, rd_wr_ne fit', Mem.readW_writeW_self32,
      Nat.reduceMul, Nat.reduceAdd, vReg, r₄, r₃, r₂, g₁, p₄, p₃, p₂, e₁]
    rw [z_update]; rfl
  · have eax₉' : s₉.gpr .eax = s₈.gpr .eax >>> 1 := eax₉
    have ebx₉' : s₉.gpr .ebx = s₈.gpr .ebx ||| ((s₈.gpr .eax).rotateRight 1 &&& topBit) := ebx₉
    have ebx₈' : s₈.gpr .ebx = s₇.gpr .ebx >>> 1 := ebx₈
    have ecx₈' : s₈.gpr .ecx = s₇.gpr .ecx ||| ((s₇.gpr .ebx).rotateRight 1 &&& topBit) := ecx₈
    have ecx₇' : s₇.gpr .ecx = s₆.gpr .ecx >>> 1 := ecx₇
    have edx₇' : s₇.gpr .edx = s₆.gpr .edx ||| ((s₆.gpr .ecx).rotateRight 1 &&& topBit) := edx₇
    obtain v₅ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .edx → s₆.gpr r = s.gpr r := fun r h1 h2 h3 => by
      rw [g₆ r h3 h2, g₅ r h1 h2]
    obtain p₉ : s₉.gpr .ebp = msk ((s.gpr .edx).getLsbD 0) := by
      rw [g₉ _ (by decide) (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide),
        g₇ _ (by decide) (by decide) (by decide), ebp₆, g₅ _ (by decide) (by decide)]
    obtain e : vOf s₁₀ = cat4 ((s.gpr .eax >>> 1) ^^^ (msk ((s.gpr .edx).getLsbD 0) &&& rTop))
        ((s.gpr .ebx >>> 1) ||| ((s.gpr .eax).rotateRight 1 &&& topBit))
        ((s.gpr .ecx >>> 1) ||| ((s.gpr .ebx).rotateRight 1 &&& topBit))
        ((s.gpr .edx >>> 1) ||| ((s.gpr .ecx).rotateRight 1 &&& topBit)) := by
      unfold vOf
      rw [eax₁₀, g₁₀ .ebx (by decide) (by decide), g₁₀ .ecx (by decide) (by decide),
        g₁₀ .edx (by decide) (by decide), p₉, eax₉', ebx₉', g₉ .ecx (by decide) (by decide) (by decide),
        g₉ .edx (by decide) (by decide) (by decide), g₈ .eax (by decide) (by decide) (by decide), ebx₈', ecx₈',
        g₈ .edx (by decide) (by decide) (by decide), g₇ .eax (by decide) (by decide) (by decide),
        g₇ .ebx (by decide) (by decide) (by decide), ecx₇', edx₇', edx₆, v₅ .eax (by decide) (by decide)
        (by decide), v₅ .ebx (by decide) (by decide) (by decide), v₅ .ecx (by decide) (by decide) (by decide),
        g₅ .edx (by decide) (by decide)]
    rw [e, v_update]; rfl
  · rw [m₁₀, m₉, m₈, m₇, m₆]
    have fit' := fit
    simp (disch := decide) only [zOff, m₅, m₄, m₃, m₂, m₁, rd_wr_ne fit', Mem.readW_writeW_self32,
      Nat.reduceMul, Nat.reduceAdd]
  · intro r h1 h2 h3 h4 h5 h6
    rw [g₁₀ r h1 h6, g₉ r h5 h1 h2, g₈ r h5 h2 h3, g₇ r h5 h3 h4, g₆ r h4 h6, g₅ r h5 h6]
  · rw [m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    obtain h0 : (⟨addr B 0, 4⟩ : Region) ∈ stepRegions B := List.mem_cons_self ..
    obtain hz : (⟨addr B 16, 16⟩ : Region) ∈ stepRegions B := by simp
    obtain c : ∀ k < 4, (⟨addr B 16, 16⟩ : Region).Contains (addr B (zOff k)) (32 / 8) := fun k hk =>
      part_contains fit (by decide) (by simp only [zOff]; omega_arith) (by simp only [zOff]; omega_arith) (by decide)
    exact (((((Frame.refl _ _).writeW h0 _ (Region.contains_self _ _)).writeW hz _ (c 0 (by decide))).writeW
      hz _ (c 1 (by decide))).writeW hz _ (c 2 (by decide))).writeW hz _ (c 3 (by decide))

end

/-! ## The 128 steps -/

/-- What a multiplication writes of the scratch buffer: `X`'s words, `Z`,
and the counters of words and steps. -/
abbrev mRegions (B : BitVec 32) : List Region := [reg32 B 32, ⟨addr B wcOff, 8⟩]

/-- After `k` steps of word `w` of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (B : BitVec 32) (sB : State) (w k : Nat) (s : State) : Prop where
  fit : B.toNat + 256 ≤ 2 ^ 32
  scr : reg32 B 256 ∈ sB.wr
  zv : (zOf s.mem B, vOf s) = mulSteps x h (32 * w + k)
  x0 : s.mem.readW (addr B 0) 32 = xw x w <<< k
  xs : ∀ j, 1 ≤ j → w + j ≤ 3 → s.mem.readW (addr B (4 * j)) 32 = xw x (w + j)
  wc : s.mem.readW (addr B wcOff) 32 = BitVec.ofNat 32 (4 - w)
  edi : s.gpr .edi = B
  esp : s.gpr .esp = sB.gpr .esp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame (mRegions B) sB.mem s.mem

/-- After the 128 steps. -/
structure MDone (x h : Block) (B : BitVec 32) (sB : State) (s : State) : Prop where
  zv : (zOf s.mem B, vOf s) = mulSteps x h 128
  edi : s.gpr .edi = B
  esp : s.gpr .esp = sB.gpr .esp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame (mRegions B) sB.mem s.mem

section
variable {x h : Block} {B : BitVec 32} {sB : State}

theorem Inner.stepFrame {w k : Nat} {s : State} (hi : Inner x h B sB w k s) {o : Nat} (ho : o + 4 ≤ 256)
    (h1 : 4 ≤ o) (h2 : o + 4 ≤ 16 ∨ 32 ≤ o) : ∀ r ∈ stepRegions B, Region.Disjoint ⟨addr B o, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact part_disj hi.fit ho (by decide) (.inr (by omega_arith))
  · exact part_disj hi.fit ho (by decide) (by omega_arith)

theorem inner_step {w k : Nat} (hw : w < 4) (hk : k < 32) {s : State} (hi : Inner x h B sB w k s) :
    WP isa (.block step) s fun s' => Inner x h B sB w (k + 1) s' ∧
      s'.mem.readW (addr B scOff) 32 = s.mem.readW (addr B scOff) 32 := by
  have fit := hi.fit
  refine step_ok hi.edi fit (hi.wr ▸ hi.scr) fun s' hz hv hx g rd wr f => ?_
  obtain hm : (s.mem.readW (addr B 0) 32).msb = x.getMsbD (32 * w + k) := by rw [hi.x0, msb_xw x hw hk]
  refine ⟨⟨fit, hi.scr, ?_, ?_, fun j h1 h2 => ?_, ?_, (g _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hi.edi, (g _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hi.esp, rd.trans hi.rd, wr.trans hi.wr, hi.frame.trans (f.sub fun r hr => ?_)⟩, ?_⟩
  · rw [show 32 * w + (k + 1) = 32 * w + k + 1 by omega_arith, mulSteps_succ, ← hi.zv, hz, hv, hm]; rfl
  · rw [hx, hi.x0, ← BitVec.shiftLeft_add]
  · rw [f.readW (Region.contains_self _ _) (hi.stepFrame (by omega_arith) (by omega_arith) (.inl (by omega_arith)))
      (by decide), hi.xs j h1 h2]
  · rw [f.readW (Region.contains_self _ _) (hi.stepFrame (by simp only [wcOff]; omega_arith)
      (by simp only [wcOff]; omega_arith) (.inr (by simp only [wcOff]; omega_arith))) (by decide), hi.wc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg32 B 32, by simp, part_sub_reg (N := 32) (by omega_arith) (by decide)⟩
    · exact ⟨reg32 B 32, by simp, part_sub_reg (N := 32) (by omega_arith) (by decide)⟩
  · exact f.readW (Region.contains_self _ _) (hi.stepFrame (by simp only [scOff]; omega_arith)
      (by simp only [scOff]; omega_arith) (.inr (by simp only [scOff]; omega_arith))) (by decide)

/-- A write to the step counter keeps the rest. -/
theorem Inner.sc {w k : Nat} {s s' : State} (hi : Inner x h B sB w k s) {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (addr B scOff) v) (hg : ∀ r, r ≠ .esi → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inner x h B sB w k s' := by
  have fit := hi.fit
  obtain e : ∀ o, o + 4 ≤ 256 → o % 4 = 0 → o ≠ scOff → s'.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 h3 => by rw [hm, rd_wr_ne fit _ _ h1 (by decide) h2 (by decide) h3]
  refine ⟨fit, hi.scr, ?_, ?_, fun j h1 h2 => ?_, ?_, (hg _ (by decide)).trans hi.edi,
    (hg _ (by decide)).trans hi.esp, hrd.trans hi.rd, hwr.trans hi.wr, ?_⟩
  · have hv : vOf s' = vOf s := by
      simp only [vOf, hg .eax (by decide), hg .ebx (by decide), hg .ecx (by decide), hg .edx (by decide)]
    rw [← hi.zv, hv]
    simp only [zOf, zw, zOff]
    rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
      e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide)]
  · rw [e 0 (by decide) (by decide) (by decide), hi.x0]
  · rw [e (4 * j) (by omega_arith) (by omega_arith) (by simp only [scOff]; omega_arith), hi.xs j h1 h2]
  · rw [e wcOff (by decide) (by decide) (by decide), hi.wc]
  · rw [hm]
    exact hi.frame.writeW (r := ⟨addr B wcOff, 8⟩) (by simp) _
      (part_contains fit (by simp only [wcOff]; omega_arith) (by simp only [wcOff, scOff]; omega_arith)
        (by simp only [wcOff, scOff]; omega_arith) (by decide))

/-- `unroll` steps, and the count. -/
theorem steps_ok {w j : Nat} (hw : w < 4) (hj : j < 4) {s : State} (hi : Inner x h B sB w (8 * j) s)
    (hc : s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - j)) :
    WP isa (.block steps) s fun s' => Inner x h B sB w (8 * (j + 1)) s' ∧
      s'.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - (j + 1)) ∧
      s'.zf = some (decide (4 - (j + 1) = 0)) := by
  have fit := hi.fit
  rw [steps, WP.block_append_iff (M := isa)]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h B sB w (8 * j + k) s' ∧
      s'.mem.readW (addr B scOff) 32 = s.mem.readW (addr B scOff) 32)
    (fun k s' hk ⟨hs', hc'⟩ => WP.mono (inner_step hw (by simp only [unroll] at hk; omega_arith) hs')
      fun _ ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll (Nat.le_refl _) s ⟨hi, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  rw [show 8 * j + unroll = 8 * (j + 1) by simp only [unroll]; omega_arith] at hs₁
  obtain hin : InRegions s₁.wr (addr B scOff) 4 := by
    rw [hs₁.wr]; exact in_reg hs₁.scr fit (by simp only [scOff]; omega_arith) (by decide)
  refine wp_ldm hs₁.edi (in_rd hin) fun s₂ u₂ => wp_subi fun s₃ u₃ _ z₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact hs₁.edi)
    (by rw [u₃.wr, u₂.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
  obtain v₃ : s₃.gpr .esi = BitVec.ofNat 32 (4 - (j + 1)) := by
    rw [u₃.gpr, u₂.gpr, hc₁, hc, ofNat_pred (by omega_arith)]; rfl
  refine ⟨hs₁.sc (by rw [u₄.mem, u₃.mem, u₂.mem, v₃]) (fun r hr => by
      rw [u₄.gpr, u₃.other r hr, u₂.other r hr]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]),
    by rw [u₄.mem, Mem.readW_writeW_self32, v₃], ?_⟩
  rw [u₄.zf, z₃, u₂.gpr, hc₁, hc, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]; rfl

/-- The 32 steps of a word. -/
theorem stepsLoop_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 0 s)
    (hc : s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 4) :
    WP isa (.loop (.block steps) .ne) s (Inner x h B sB w 32) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = 4 - j ∧ j < 4 ∧ Inner x h B sB w (8 * j) s ∧
      s.mem.readW (addr B scOff) 32 = BitVec.ofNat 32 (4 - j))
    (fun m s ⟨j, hm, hj, hs, hc⟩ => WP.mono (steps_ok hw hj hs hc) fun s' ⟨hs', hc', z⟩ => ?_) _ s
    ⟨0, rfl, by decide, hi, hc⟩
  by_cases hl : j + 1 = 4
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at hs'; exact hs'
  · exact .inr ⟨by simp [X86.eval, z]; omega_arith, _, by omega_arith, j + 1, rfl, by omega_arith, hs', hc'⟩

theorem nextWord_eq : nextWord = [.mov .esi (.mem (at_ .edi 4)), .store (at_ .edi 0) .esi,
    .mov .esi (.mem (at_ .edi 8)), .store (at_ .edi 4) .esi,
    .mov .esi (.mem (at_ .edi 12)), .store (at_ .edi 8) .esi,
    .mov .esi (.mem (at_ .edi 56)), .alu .sub .esi (.imm 1), .store (at_ .edi 56) .esi] := rfl

/-- Move the next words of `X` down, and count the word. -/
theorem nextWord_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 32 s) :
    WP isa (.block nextWord) s fun s' => (s'.zf = some false ∧ w + 1 < 4 ∧ Inner x h B sB (w + 1) 0 s') ∨
      (s'.zf = some true ∧ MDone x h B sB s') := by
  have fit := hi.fit
  obtain hin : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht, hi.wr]; exact in_reg hi.scr fit ho (by decide)
  rw [nextWord_eq]
  refine wp_ldm hi.edi (in_rd (hin _ rfl 4 (by decide))) fun s₁ u₁ => ?_
  obtain e₁ : s₁.gpr .edi = B := by rw [u₁.other _ (by decide)]; exact hi.edi
  refine wp_stm e₁ (hin _ u₁.wr 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.gpr]; exact e₁) (in_rd (hin _ (by rw [u₂.wr, u₁.wr]) 8 (by decide))) fun s₃ u₃ => ?_
  obtain e₃ : s₃.gpr .edi = B := by rw [u₃.other _ (by decide), u₂.gpr]; exact e₁
  refine wp_stm e₃ (hin _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.gpr]; exact e₃) (in_rd (hin _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 12 (by decide)))
    fun s₅ u₅ => ?_
  obtain e₅ : s₅.gpr .edi = B := by rw [u₅.other _ (by decide), u₄.gpr]; exact e₃
  obtain w₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_stm e₅ (hin _ w₅ 8 (by decide)) fun s₆ u₆ => ?_
  refine wp_ldm (by rw [u₆.gpr]; exact e₅) (in_rd (hin _ (by rw [u₆.wr, w₅]) 56 (by decide))) fun s₇ u₇ => ?_
  refine wp_subi fun s₈ u₈ _ z₈ => ?_
  refine wp_stm (B := B) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; exact e₅)
    (hin _ (by rw [u₈.wr, u₇.wr, u₆.wr, w₅]) 56 (by decide)) fun s₉ u₉ => WP.block_nil ?_
  let m := s.mem
  let M := (((m.writeW (addr B 0) (m.readW (addr B 4) 32)).writeW (addr B 4) (m.readW (addr B 8) 32)).writeW
    (addr B 8) (m.readW (addr B 12) 32)).writeW (addr B 56) (m.readW (addr B 56) 32 - 1)
  have fit' := fit
  obtain m₉ : s₉.mem = M := by
    rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.mem,
      u₁.gpr, u₁.mem]
    simp (disch := decide) only [M, m, rd_wr_ne fit']
  obtain g₉ : ∀ r, r ≠ .esi → s₉.gpr r = s.gpr r := fun r hr => by
    rw [u₉.gpr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr, u₄.gpr, u₃.other r hr, u₂.gpr,
      u₁.other r hr]
  obtain wc : s₉.mem.readW (addr B wcOff) 32 = BitVec.ofNat 32 (4 - (w + 1)) := by
    rw [m₉]; simp only [M, wcOff, Mem.readW_writeW_self32]
    rw [show (56 : Nat) = wcOff from rfl, hi.wc, ofNat_pred (by omega_arith), Nat.sub_sub]
  obtain zf : s₉.zf = some (decide (4 - (w + 1) = 0)) := by
    obtain r56 : s₆.mem.readW (addr B 56) 32 = BitVec.ofNat 32 (4 - w) := by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      simp (disch := decide) only [rd_wr_ne fit']
      exact hi.wc
    rw [u₉.zf, z₈, u₇.gpr, r56, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith), Nat.sub_sub]
  obtain zv : (zOf s₉.mem B, vOf s₉) = mulSteps x h (32 * (w + 1) + 0) := by
    obtain hv : vOf s₉ = vOf s := by
      simp only [vOf, g₉ .eax (by decide), g₉ .ebx (by decide), g₉ .ecx (by decide), g₉ .edx (by decide)]
    rw [show 32 * (w + 1) + 0 = 32 * w + 32 by omega_arith, ← hi.zv, hv, m₉]
    simp (disch := decide) only [zOf, zw, zOff, M, rd_wr_ne fit', Nat.reduceMul, Nat.reduceAdd]
    rfl
  obtain fr : Frame (mRegions B) sB.mem s₉.mem := by
    rw [m₉]
    obtain h32 : reg32 B 32 ∈ mRegions B := List.mem_cons_self ..
    obtain hwc : (⟨addr B wcOff, 8⟩ : Region) ∈ mRegions B := by simp
    exact (((hi.frame.writeW h32 _ (reg_contains (by omega_arith) (by decide) (by decide))).writeW h32 _
      (reg_contains (by omega_arith) (by decide) (by decide))).writeW h32 _
      (reg_contains (by omega_arith) (by decide) (by decide))).writeW hwc _
      (part_contains fit (by simp only [wcOff]; omega_arith) (by simp only [wcOff]; omega_arith)
        (by simp only [wcOff]; omega_arith) (by decide))
  obtain edi₉ : s₉.gpr .edi = B := (g₉ _ (by decide)).trans hi.edi
  obtain esp₉ : s₉.gpr .esp = sB.gpr .esp := (g₉ _ (by decide)).trans hi.esp
  obtain rd₉ : s₉.rd = sB.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  obtain wr₉ : s₉.wr = sB.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅, hi.wr]
  by_cases hl : w + 1 = 4
  · refine .inr ⟨by rw [zf, hl]; rfl, ?_, edi₉, esp₉, rd₉, wr₉, fr⟩
    rw [zv, hl]
  · refine .inl ⟨by rw [zf]; simp; omega_arith, by omega_arith, fit, hi.scr, zv, ?_, fun j h1 h2 => ?_, wc, edi₉, esp₉, rd₉, wr₉, fr⟩
    · rw [m₉, BitVec.shiftLeft_zero]
      simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32]
      exact hi.xs 1 (by decide) (by omega_arith)
    · rw [m₉]
      rcases (by omega_arith : j = 1 ∨ j = 2) with rfl | rfl
      · simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
        rw [hi.xs 2 (by decide) (by omega_arith)]
      · simp (disch := decide) only [M, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
        rw [hi.xs 3 (by decide) (by omega_arith)]

/-- A word of `X`: 32 steps. -/
theorem word_ok {w : Nat} (hw : w < 4) {s : State} (hi : Inner x h B sB w 0 s) :
    WP isa Impl.Gcm.X86.word s fun s' => (s'.zf = some false ∧ w + 1 < 4 ∧ Inner x h B sB (w + 1) 0 s') ∨
      (s'.zf = some true ∧ MDone x h B sB s') := by
  have fit := hi.fit
  unfold Impl.Gcm.X86.word
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => wp_stm (B := B) (by rw [u₁.other _ (by decide)]; exact hi.edi)
    (by rw [u₁.wr, hi.wr]; exact in_reg hi.scr fit (by simp only [scOff]; omega_arith) (by decide))
    fun s₂ u₂ => WP.block_nil ?_
  obtain h₂ : Inner x h B sB w 0 s₂ := hi.sc (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.gpr, u₁.other r hr])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  refine WP.seq (WP.mono (stepsLoop_ok hw h₂ (by rw [u₂.mem, Mem.readW_writeW_self32, u₁.gpr]; rfl))
    fun s₃ h₃ => nextWord_ok hw h₃)

/-- The four words: all 128 steps. -/
theorem mul_ok {s : State} (hi : Inner x h B sB 0 0 s) : WP isa (.loop word .ne) s (MDone x h B sB) := by
  refine WP.loop (M := isa) (fun m s => ∃ w, m = 4 - w ∧ w < 4 ∧ Inner x h B sB w 0 s)
    (fun m s ⟨w, hm, hw, hs⟩ => WP.mono (word_ok hw hs) fun s' hr => ?_) _ s ⟨0, rfl, by decide, hi⟩
  rcases hr with ⟨z, hl, d⟩ | ⟨z, d⟩
  · exact .inr ⟨by simp [X86.eval, z], _, by omega_arith, w + 1, rfl, hl, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩

end

end VG.Proof.Gcm.X86

end

end

/-!
# GHASH on x86 (32-bit): the whole function

Each block loads `Y ⊕ X` (big-endian words, `bswap`) into the scratch
buffer, `Z := 0` and `V := H`, runs the 128 steps (`Step.lean`), and
stores `Z` as the new `Y`. The prologue saves the callee-saved registers
in the scratch buffer with the data pointer and the count, and the
epilogue restores them. Constant time is `GhashCT.lean`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Impl.Gcm.X86 VG.Proof.Gcm VG.Proof.Aes.X86
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_add wp_addi wp_subi wp_ldm wp_xorm wp_stm wp_xor wp_test
  wp_bswap ofNat_pred ofNat_beq_zero)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Blocks as big-endian words -/

theorem bswap_word_bit (m : Mem) {P : BitVec 32} (hP : P.toNat + 16 ≤ 2 ^ 32) {v k j : Nat} (hv : v < 4)
    (hk : k < 4) (hj : j < 8) :
    (bswap (m.readW (addr P (4 * v)) 32)).getLsbD (8 * k + j) =
      (blockAt m (P.setWidth 64)).getLsbD (32 * (3 - v) + (8 * k + j)) := by
  rw [bswap_bit _ hk hj, readW_bit _ _ (by omega_arith) hj, addr_add64 (by omega_arith), addr_eq (by omega_arith),
    show 32 * (3 - v) + (8 * k + j) = 8 * (15 - (4 * v + (3 - k))) + j by omega_arith,
    Proof.Aes.blockAt_bit _ _ (by omega_arith) hj]

/-- A block is its four big-endian words. -/
theorem blockAt_words (m : Mem) {P : BitVec 32} (hP : P.toNat + 16 ≤ 2 ^ 32) :
    blockAt m (P.setWidth 64) = cat4 (bswap (m.readW (addr P 0) 32)) (bswap (m.readW (addr P 4) 32))
      (bswap (m.readW (addr P 8) 32)) (bswap (m.readW (addr P 12) 32)) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [getLsbD_cat4]
  obtain e : ∀ v < 4, 32 * (3 - v) ≤ t → t < 32 * (3 - v) + 32 →
      (blockAt m (P.setWidth 64)).getLsbD t =
        (bswap (m.readW (addr P (4 * v)) 32)).getLsbD (t - 32 * (3 - v)) := fun v hv h1 h2 => by
    rw [show t - 32 * (3 - v) = 8 * ((t - 32 * (3 - v)) / 8) + (t - 32 * (3 - v)) % 8 by omega_arith,
      bswap_word_bit m hP hv (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  split
  · exact e 3 (by decide) (by omega_arith) (by omega_arith)
  · split
    · exact e 2 (by decide) (by omega_arith) (by omega_arith)
    · split
      · exact e 1 (by decide) (by omega_arith) (by omega_arith)
      · exact e 0 (by decide) (by omega_arith) (by omega_arith)

theorem bswap_bswap (v : BitVec 32) : bswap (bswap v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [show t = 8 * (t / 8) + t % 8 by omega_arith, bswap_bit _ (by omega_arith) (by omega_arith),
    bswap_bit _ (by omega_arith) (by omega_arith)]
  congr 1; omega_arith

theorem xw_cat4 (a b c d : BitVec 32) :
    xw (cat4 a b c d) 0 = a ∧ xw (cat4 a b c d) 1 = b ∧ xw (cat4 a b c d) 2 = c ∧ xw (cat4 a b c d) 3 = d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply BitVec.eq_of_getLsbD_eq; intro t ht) <;>
    simp only [xw, BitVec.getLsbD_extractLsb', getLsbD_cat4, ht, decide_true, Bool.true_and] <;>
    (repeat' split) <;> first | omega_arith | (congr 1; omega_arith)

theorem xw_cat4_0 (a b c d : BitVec 32) : xw (cat4 a b c d) 0 = a := (xw_cat4 a b c d).1
theorem xw_cat4_1 (a b c d : BitVec 32) : xw (cat4 a b c d) 1 = b := (xw_cat4 a b c d).2.1
theorem xw_cat4_2 (a b c d : BitVec 32) : xw (cat4 a b c d) 2 = c := (xw_cat4 a b c d).2.2.1
theorem xw_cat4_3 (a b c d : BitVec 32) : xw (cat4 a b c d) 3 = d := (xw_cat4 a b c d).2.2.2

theorem xw_xor (x y : Block) (w : Nat) : xw (x ^^^ y) w = xw x w ^^^ xw y w := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [xw, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor]
  cases decide (t < 32) <;> simp

/-! ## Loading a block -/

/-- `V`'s word `k`, from `H`. -/
def vLoad (k : Nat) : List Instr := [.mov (vReg k) (.mem (at_ .ebp (4 * k))), .bswap (vReg k)]

/-- The start of `load`: `Y ⊕ X`, `Z := 0`, and `ebp := h`. -/
def loadHead : List Instr :=
  ((((([.mov .esi (.mem (at_ .edi 48)), .mov .ebp (.mem (at_ .esp 8))] : List Instr) ++ loadX 0) ++ loadX 1) ++
    loadX 2) ++ loadX 3) ++
  ([.mov .eax (.imm 0), .store (at_ .edi 16) .eax, .store (at_ .edi 20) .eax, .store (at_ .edi 24) .eax,
    .store (at_ .edi 28) .eax, .mov .ebp (.mem (at_ .esp 4))] : List Instr)

theorem load_eq : load = ((((loadHead ++ vLoad 0) ++ vLoad 1) ++ vLoad 2) ++ vLoad 3) ++
    ([.mov .esi (.imm 4), .store (at_ .edi 56) .esi] : List Instr) := rfl

/-- Word `w` of `Y ⊕ X`. -/
def vX (m : Mem) (Yp Xp : BitVec 32) (w : Nat) : BitVec 32 :=
  bswap (m.readW (addr Yp (4 * w)) 32) ^^^ bswap (m.readW (addr Xp (4 * w)) 32)

/-- The memory after `loadHead`. -/
def headMem (m : Mem) (B Yp Xp : BitVec 32) : Mem :=
  (((((((m.writeW (addr B (4 * 0)) (vX m Yp Xp 0)).writeW (addr B (4 * 1)) (vX m Yp Xp 1)).writeW
    (addr B (4 * 2)) (vX m Yp Xp 2)).writeW (addr B (4 * 3)) (vX m Yp Xp 3)).writeW (addr B 16) (0 : BitVec 32)).writeW
    (addr B 20) (0 : BitVec 32)).writeW (addr B 24) (0 : BitVec 32)).writeW (addr B 28) (0 : BitVec 32)

section
variable {s : State} {P : State → Prop}

/-- Word `w` of `Y ⊕ X`. -/
theorem loadX_wp (w : Nat) {B Yp Xp : BitVec 32} (hb : s.gpr .edi = B) (hy : s.gpr .ebp = Yp)
    (hx : s.gpr .esi = Xp) (iy : InRegions (s.rd ++ s.wr) (addr Yp (4 * w)) 4)
    (ix : InRegions (s.rd ++ s.wr) (addr Xp (4 * w)) 4) (ib : InRegions s.wr (addr B (4 * w)) 4)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B (4 * w))
        (bswap (s.mem.readW (addr Yp (4 * w)) 32) ^^^ bswap (s.mem.readW (addr Xp (4 * w)) 32)) →
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (loadX w)) s P := by
  refine wp_ldm hy iy fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_ldm (B := Xp) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hx)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ix) fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  refine wp_xor fun s₅ u₅ => wp_stm (B := B) (by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]; exact hb)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact ib) fun s₆ u₆ => WP.block_nil ?_
  refine h s₆ ?_ (fun r h1 h2 => ?_) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₆.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.other r h1, u₄.other r h2, u₃.other r h2, u₂.other r h1, u₁.other r h1]

/-- `V`'s word `k`. -/
theorem vLoad_wp (k : Nat) {Hp : BitVec 32} (hp : s.gpr .ebp = Hp)
    (ih : InRegions (s.rd ++ s.wr) (addr Hp (4 * k)) 4)
    (h : ∀ s', s'.gpr (vReg k) = bswap (s.mem.readW (addr Hp (4 * k)) 32) →
      (∀ r, r ≠ vReg k → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (vLoad k)) s P := by
  refine wp_ldm hp ih fun s₁ u₁ => wp_bswap fun s₂ u₂ => WP.block_nil ?_
  exact h s₂ (by rw [u₂.gpr, u₁.gpr]) (fun r hr => by rw [u₂.other r hr, u₁.other r hr])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

end

/-! ## Storing `Y` -/

/-- Word `k` of `Z`, big-endian, to `Y`. -/
def zStore (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (zOff k))), .bswap .eax, .store (at_ .esi (4 * k)) .eax]

/-- The memory after the new `Y` is stored. -/
def yMem (m : Mem) (B Yp : BitVec 32) : Mem :=
  (((m.writeW (addr Yp (4 * 0)) (bswap (zw m B 0))).writeW (addr Yp (4 * 1)) (bswap (zw m B 1))).writeW
    (addr Yp (4 * 2)) (bswap (zw m B 2))).writeW (addr Yp (4 * 3)) (bswap (zw m B 3))

theorem store_eq : store = (((([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ zStore 0) ++ zStore 1) ++
    zStore 2) ++ zStore 3 ++ ([.mov .esi (.mem (at_ .edi 48)), .alu .add .esi (.imm 16),
      .store (at_ .edi 48) .esi, .mov .esi (.mem (at_ .edi 52)), .alu .sub .esi (.imm 1),
      .store (at_ .edi 52) .esi] : List Instr) := rfl

/-! ## The loop over the blocks -/

/-- The setting of the loop over the blocks, from the state `s₁` after the
prologue: `H` at `Hp`, `Y` at `Yp`, the `n` blocks at `Dp`, the scratch
buffer at `B`, and the arguments above `E`. -/
structure BSetup (s₁ : State) (Hp Yp Dp B E : BitVec 32) (n : Nat) : Prop where
  hR : reg32 Hp 16 ∈ s₁.rd
  dR : reg32 Dp (16 * n) ∈ s₁.rd
  yW : reg32 Yp 16 ∈ s₁.wr
  sW : reg32 B 256 ∈ s₁.wr
  fH : Hp.toNat + 16 ≤ 2 ^ 32
  fY : Yp.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * n ≤ 2 ^ 32
  fB : B.toNat + 256 ≤ 2 ^ 32
  dHY : (reg32 Hp 16).Disjoint (reg32 Yp 16)
  dHS : (reg32 Hp 16).Disjoint (reg32 B 256)
  dYD : (reg32 Yp 16).Disjoint (reg32 Dp (16 * n))
  dYS : (reg32 Yp 16).Disjoint (reg32 B 256)
  dDS : (reg32 Dp (16 * n)).Disjoint (reg32 B 256)
  fE : E.toNat + 24 ≤ 2 ^ 32
  argIn : ∀ i < 2, InRegions s₁.rd (addr E (4 + 4 * i)) 4
  argH : s₁.mem.readW (addr E 4) 32 = Hp
  argY : s₁.mem.readW (addr E 8) 32 = Yp
  aY : (⟨addr E 4, 8⟩ : Region).Disjoint (reg32 Yp 16)
  aS : (⟨addr E 4, 8⟩ : Region).Disjoint (reg32 B 256)

/-- What the loop writes. -/
abbrev bRegions (Yp B : BitVec 32) : List Region := [reg32 Yp 16, reg32 B 32, ⟨addr B dOff, 16⟩]

/-- Before block `b`. -/
structure BInv (s₁ : State) (Hp Yp Dp B E : BitVec 32) (n b : Nat) (s : State) : Prop where
  hb : b ≤ n
  edi : s.gpr .edi = B
  esp : s.gpr .esp = E
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  dslot : s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (16 * b)
  nslot : s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - b)
  y : blockAt s.mem (Yp.setWidth 64) = ghashFrom (blockAt s₁.mem (Hp.setWidth 64))
    (blockAt s₁.mem (Yp.setWidth 64)) (blocksAt s₁.mem (Dp.setWidth 64) b)
  frame : Frame (bRegions Yp B) s₁.mem s.mem

section
variable {s₁ : State} {Hp Yp Dp B E : BitVec 32} {n : Nat} (hs : BSetup s₁ Hp Yp Dp B E n)
include hs

theorem BSetup.rY (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16) :
    (m.writeW (addr B o) v).readW (addr Yp e) 32 = m.readW (addr Yp e) 32 :=
  rd_wr_other hs.dYS (reg_contains hs.fY he (by decide)) (reg_contains hs.fB ho (by decide))

theorem BSetup.rD (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16 * n) :
    (m.writeW (addr B o) v).readW (addr Dp e) 32 = m.readW (addr Dp e) 32 :=
  rd_wr_other hs.dDS (reg_contains hs.fD he (by decide)) (reg_contains hs.fB ho (by decide))

theorem BSetup.rB (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16) :
    (m.writeW (addr Yp e) v).readW (addr B o) 32 = m.readW (addr B o) 32 :=
  rd_wr_other hs.dYS.symm (reg_contains hs.fB ho (by decide)) (reg_contains hs.fY he (by decide))

theorem BSetup.fX {b : Nat} (hb : b < n) : (Dp + BitVec.ofNat 32 (16 * b)).toNat + 16 ≤ 2 ^ 32 := by
  have fD := hs.fD
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * b) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem BSetup.argC {o : Nat} (h1 : 4 ≤ o) (h2 : o + 4 ≤ 12) :
    (⟨addr E 4, 8⟩ : Region).Contains (addr E o) (32 / 8) :=
  part_contains (N := 12) (by have := hs.fE; omega_arith) (by decide) h1 (by omega_arith) (by decide)

theorem BSetup.dA : ∀ r ∈ bRegions Yp B, Region.Disjoint ⟨addr E 4, 8⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.aY
  · exact hs.aS.sub_right (Region.sub_prefix (by decide))
  · exact hs.aS.sub_right (part_sub_reg hs.fB (by simp only [dOff]; omega_arith))

theorem BSetup.dM {R : Region} (hR : R.Disjoint (reg32 B 256)) : ∀ r ∈ mRegions B, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hR.sub_right (Region.sub_prefix (by decide))
  · exact hR.sub_right (part_sub_reg hs.fB (by simp only [wcOff]; omega_arith))

theorem BSetup.headMem_frame (m : Mem) (Xp : BitVec 32) : Frame (mRegions B) m (headMem m B Yp Xp) := by
  obtain h32 : reg32 B 32 ∈ mRegions B := List.mem_cons_self ..
  obtain c : ∀ o, o + 4 ≤ 32 → (reg32 B 32).Contains (addr B o) (32 / 8) := fun o ho =>
    reg_contains (by have := hs.fB; omega_arith) ho (by decide)
  exact (((((((Frame.refl _ _).writeW h32 _ (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _
    (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _
    (c _ (by decide))).writeW h32 _ (c _ (by decide)) |>.writeW h32 _ (c _ (by decide))

/-- `Y ⊕ X` of block `b`, `Z := 0`, and `ebp := h`. -/
theorem head_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa (.block loadHead) s fun t =>
      t.mem = headMem s.mem B Yp (Dp + BitVec.ofNat 32 (16 * b)) ∧ t.gpr .edi = B ∧ t.gpr .ebp = Hp ∧
        t.gpr .esp = E ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain fB := hs.fB; have fY := hs.fY; have fD := hs.fD
  obtain hbn : 16 * b + 16 ≤ 16 * n := by omega_arith
  let Xp := Dp + BitVec.ofNat 32 (16 * b)
  obtain inB : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht, hi.wr]; exact in_reg hs.sW fB ho (by decide)
  obtain inY : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Yp e) 4 :=
    fun t h1 h2 e he => by rw [h1, h2, hi.wr]; exact in_rd (in_reg hs.yW fY he (by decide))
  obtain inX : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Xp e) 4 :=
    fun t h1 h2 e he => by
      rw [h1, h2, hi.rd, addr_add]; exact in_rd_left (in_reg hs.dR fD (by omega_arith) (by decide))
  obtain inA : ∀ (t : State), t.rd = s.rd → ∀ i < 2, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi' => by rw [ht, hi.rd]; exact in_rd_left (hs.argIn i hi')
  obtain rX : ∀ (m : Mem) (v : BitVec 32) (o e : Nat), o + 4 ≤ 256 → e + 4 ≤ 16 →
      (m.writeW (addr B o) v).readW (addr Xp e) 32 = m.readW (addr Xp e) 32 := fun m v o e ho he => by
    rw [addr_add]; exact hs.rD m v ho (by omega_arith)
  unfold loadHead
  repeat rw [WP.block_append_iff (M := isa)]
  refine wp_ldm hi.edi (in_rd (inB _ rfl 48 (by decide))) fun t₁ u₁ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₁.other _ (by decide)]; exact hi.esp) (inA _ u₁.rd 1 (by decide))
    fun t₂ u₂ => WP.block_nil ?_
  obtain esi₂ : t₂.gpr .esi = Xp := by rw [u₂.other _ (by decide), u₁.gpr]; exact hi.dslot
  obtain ebp₂ : t₂.gpr .ebp = Yp := by
    rw [u₂.gpr, u₁.mem, ← hs.argY]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)
  obtain edi₂ : t₂.gpr .edi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hi.edi]
  obtain rd₂ : t₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : t₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain m₂ : t₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  -- `Y ⊕ X`.
  refine loadX_wp 0 edi₂ ebp₂ esi₂ (inY _ rd₂ wr₂ _ (by decide)) (inX _ rd₂ wr₂ _ (by decide))
    (inB _ wr₂ _ (by decide)) fun t₃ m₃ g₃ rd₃ wr₃ => ?_
  have k₃ : ∀ r, r ≠ .eax → r ≠ .ebx → t₃.gpr r = t₂.gpr r := g₃
  obtain rd₃' : t₃.rd = s.rd := rd₃.trans rd₂
  obtain wr₃' : t₃.wr = s.wr := wr₃.trans wr₂
  obtain m₃' : t₃.mem = s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0) := by rw [m₃, m₂]; rfl
  refine loadX_wp 1 (by rw [k₃ _ (by decide) (by decide), edi₂]) (by rw [k₃ _ (by decide) (by decide), ebp₂])
    (by rw [k₃ _ (by decide) (by decide), esi₂]) (inY _ rd₃' wr₃' _ (by decide)) (inX _ rd₃' wr₃' _ (by decide))
    (inB _ wr₃' _ (by decide)) fun t₄ m₄ g₄ rd₄ wr₄ => ?_
  obtain k₄ : ∀ r, r ≠ .eax → r ≠ .ebx → t₄.gpr r = t₂.gpr r := fun r h1 h2 => (g₄ r h1 h2).trans (k₃ r h1 h2)
  obtain rd₄' : t₄.rd = s.rd := rd₄.trans rd₃'
  obtain wr₄' : t₄.wr = s.wr := wr₄.trans wr₃'
  obtain m₄' : t₄.mem = (s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1) := by
    rw [m₄, m₃', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  refine loadX_wp 2 (by rw [k₄ _ (by decide) (by decide), edi₂]) (by rw [k₄ _ (by decide) (by decide), ebp₂])
    (by rw [k₄ _ (by decide) (by decide), esi₂]) (inY _ rd₄' wr₄' _ (by decide)) (inX _ rd₄' wr₄' _ (by decide))
    (inB _ wr₄' _ (by decide)) fun t₅ m₅ g₅ rd₅ wr₅ => ?_
  obtain k₅ : ∀ r, r ≠ .eax → r ≠ .ebx → t₅.gpr r = t₂.gpr r := fun r h1 h2 => (g₅ r h1 h2).trans (k₄ r h1 h2)
  obtain rd₅' : t₅.rd = s.rd := rd₅.trans rd₄'
  obtain wr₅' : t₅.wr = s.wr := wr₅.trans wr₄'
  obtain m₅' : t₅.mem = ((s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1)).writeW (addr B (4 * 2)) (vX s.mem Yp Xp 2) := by
    rw [m₅, m₄', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  refine loadX_wp 3 (by rw [k₅ _ (by decide) (by decide), edi₂]) (by rw [k₅ _ (by decide) (by decide), ebp₂])
    (by rw [k₅ _ (by decide) (by decide), esi₂]) (inY _ rd₅' wr₅' _ (by decide)) (inX _ rd₅' wr₅' _ (by decide))
    (inB _ wr₅' _ (by decide)) fun t₆ m₆ g₆ rd₆ wr₆ => ?_
  obtain k₆ : ∀ r, r ≠ .eax → r ≠ .ebx → t₆.gpr r = t₂.gpr r := fun r h1 h2 => (g₆ r h1 h2).trans (k₅ r h1 h2)
  obtain wr₆' : t₆.wr = s.wr := wr₆.trans wr₅'
  obtain m₆' : t₆.mem = (((s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1)).writeW (addr B (4 * 2)) (vX s.mem Yp Xp 2)).writeW (addr B (4 * 3)) (vX s.mem Yp Xp 3) := by
    rw [m₆, m₅', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  -- `Z := 0`.
  obtain edi₆ : t₆.gpr .edi = B := by rw [k₆ _ (by decide) (by decide), edi₂]
  refine wp_movi fun t₇ u₇ => ?_
  obtain edi₇ : t₇.gpr .edi = B := by rw [u₇.other _ (by decide), edi₆]
  refine wp_stm edi₇ (inB _ (by rw [u₇.wr, wr₆']) _ (by decide)) fun t₈ u₈ => ?_
  refine wp_stm (by rw [u₈.gpr]; exact edi₇) (inB _ (by rw [u₈.wr, u₇.wr, wr₆']) _ (by decide)) fun t₉ u₉ => ?_
  refine wp_stm (by rw [u₉.gpr, u₈.gpr]; exact edi₇) (inB _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆']) _ (by decide))
    fun t₁₀ u₁₀ => ?_
  refine wp_stm (by rw [u₁₀.gpr, u₉.gpr, u₈.gpr]; exact edi₇)
    (inB _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆']) _ (by decide)) fun t₁₁ u₁₁ => ?_
  obtain esp₁₁ : t₁₁.gpr .esp = E := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), k₆ _ (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.esp]
  obtain rd₁₁ : t₁₁.rd = s.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅']
  obtain wr₁₁ : t₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆']
  obtain m₁₁ : t₁₁.mem = headMem s.mem B Yp Xp := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, u₇.mem, m₆']; rfl
  refine wp_ldm (B := E) (o := 4) esp₁₁ (inA _ rd₁₁ 0 (by decide)) fun t₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨by rw [u₁₂.mem, m₁₁], ?_, ?_, by rw [u₁₂.other _ (by decide), esp₁₁], by rw [u₁₂.rd, rd₁₁],
    by rw [u₁₂.wr, wr₁₁]⟩
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, edi₇]
  · rw [u₁₂.gpr, m₁₁, (hs.headMem_frame s.mem Xp).readW (hs.argC (by decide) (by decide)) (hs.dM hs.aS)
      (by decide), ← hs.argH]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)

/-- Block `b`'s `Y ⊕ X`, `Z := 0`, `V := H`. -/
theorem load_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa (.block load) s fun s' =>
      Inner (blockAt s.mem (Yp.setWidth 64) ^^^ blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64))
        (blockAt s₁.mem (Hp.setWidth 64)) B s' 0 0 s' ∧
      Frame (mRegions B) s.mem s'.mem ∧ s'.gpr .esp = E ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
  obtain fB := hs.fB; have fH := hs.fH; have fY := hs.fY
  let Xp := Dp + BitVec.ofNat 32 (16 * b)
  obtain fX : Xp.toNat + 16 ≤ 2 ^ 32 := hs.fX hb
  let x := blockAt s.mem (Yp.setWidth 64) ^^^ blockAt s.mem (Xp.setWidth 64)
  obtain inH : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Hp e) 4 :=
    fun t h1 h2 e he => by rw [h1, h2, hi.rd]; exact in_rd_left (in_reg hs.hR fH he (by decide))
  obtain hH : ∀ k < 4, (headMem s.mem B Yp Xp).readW (addr Hp (4 * k)) 32 =
      s₁.mem.readW (addr Hp (4 * k)) 32 := fun k hk => by
    obtain c : (reg32 Hp 16).Contains (addr Hp (4 * k)) (32 / 8) := reg_contains fH (by omega_arith) (by decide)
    rw [(hs.headMem_frame s.mem Xp).readW c (hs.dM hs.dHS) (by decide)]
    refine hi.frame.readW c (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.dHY
    · exact hs.dHS.sub_right (Region.sub_prefix (by decide))
    · exact hs.dHS.sub_right (part_sub_reg fB (by simp only [dOff]; omega_arith))
  rw [load_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine WP.mono (head_ok hs hi hb) fun t ⟨m₀, edi₀, ebp₀, esp₀, rd₀, wr₀⟩ => ?_
  refine vLoad_wp 0 ebp₀ (inH _ rd₀ wr₀ _ (by decide)) fun t₁ a₁ g₁ m₁ rd₁ wr₁ => ?_
  refine vLoad_wp 1 (by rw [g₁ _ (by decide), ebp₀]) (inH _ (by rw [rd₁, rd₀]) (by rw [wr₁, wr₀]) _
    (by decide)) fun t₂ a₂ g₂ m₂ rd₂ wr₂ => ?_
  refine vLoad_wp 2 (by rw [g₂ _ (by decide), g₁ _ (by decide), ebp₀])
    (inH _ (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀]) _ (by decide)) fun t₃ a₃ g₃ m₃ rd₃ wr₃ => ?_
  refine vLoad_wp 3 (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), ebp₀])
    (inH _ (by rw [rd₃, rd₂, rd₁, rd₀]) (by rw [wr₃, wr₂, wr₁, wr₀]) _ (by decide))
    fun t₄ a₄ g₄ m₄ rd₄ wr₄ => ?_
  obtain edi₄ : t₄.gpr .edi = B := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), edi₀]
  obtain wr₄' : t₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁, wr₀]
  refine wp_movi fun t₅ u₅ => wp_stm (B := B) (by rw [u₅.other _ (by decide), edi₄])
    (by rw [u₅.wr, wr₄', hi.wr]; exact in_reg hs.sW fB (by decide) (by decide)) fun t₆ u₆ => WP.block_nil ?_
  obtain mh : ∀ {t' : State}, t'.mem = t.mem → t'.mem = headMem s.mem B Yp Xp := fun h => h.trans m₀
  obtain m₆ : t₆.mem = (headMem s.mem B Yp Xp).writeW (addr B 56) (4 : BitVec 32) := by
    rw [u₆.mem, u₅.gpr, u₅.mem, mh (m₄.trans (m₃.trans (m₂.trans m₁)))]
  obtain rv : ∀ k < 4, t₆.gpr (vReg k) = bswap (s₁.mem.readW (addr Hp (4 * k)) 32) := by
    intro k hk
    rw [u₆.gpr, u₅.other _ (vReg_ne_esi k), ← hH k hk]
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), a₁, mh rfl]
    · rw [g₄ _ (by decide), g₃ _ (by decide), a₂, mh m₁]
    · rw [g₄ _ (by decide), a₃, mh (m₂.trans m₁)]
    · rw [a₄, mh (m₃.trans (m₂.trans m₁))]
  have fit' := fB
  obtain xv : ∀ w < 4, vX s.mem Yp Xp w = xw x w := by
    intro w hw
    simp only [x, xw_xor, blockAt_words s.mem fY, blockAt_words s.mem fX]
    rcases (by omega_arith : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;>
      simp only [vX, xw_cat4_0, xw_cat4_1, xw_cat4_2, xw_cat4_3, Nat.reduceMul]
  obtain rdM : ∀ w < 4, t₆.mem.readW (addr B (4 * w)) 32 = xw x w := by
    intro w hw
    rw [m₆, ← xv w hw]
    rcases (by omega_arith : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [headMem, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
  refine ⟨⟨fB, by rw [u₆.wr, u₅.wr, wr₄']; rw [hi.wr]; exact hs.sW, ?_, ?_, fun j h1 h2 => ?_, ?_,
    by rw [u₆.gpr, u₅.other _ (by decide), edi₄], rfl, rfl, rfl, Frame.refl _ _⟩, ?_, ?_, ?_, ?_⟩
  · rw [mulSteps_zero]
    refine Prod.ext ?_ ?_
    · show zOf t₆.mem B = 0
      rw [m₆]
      simp (disch := decide) only [zOf, zw, zOff, headMem, rd_wr_ne fit', Mem.readW_writeW_self32,
        Nat.reduceMul, Nat.reduceAdd]
      decide
    · show vOf t₆ = _
      rw [blockAt_words s₁.mem fH]
      simp only [vOf]
      rw [show Reg.eax = vReg 0 from rfl, show Reg.ebx = vReg 1 from rfl, show Reg.ecx = vReg 2 from rfl,
        show Reg.edx = vReg 3 from rfl, rv 0 (by decide), rv 1 (by decide), rv 2 (by decide), rv 3 (by decide)]
  · rw [BitVec.shiftLeft_zero, show (0 : Nat) = 4 * 0 from rfl, rdM 0 (by decide)]
  · rw [rdM j (by omega_arith), Nat.zero_add]
  · rw [m₆]; exact Mem.readW_writeW_self32 _ _ _
  · rw [m₆]
    exact (hs.headMem_frame s.mem Xp).writeW (r := ⟨addr B wcOff, 8⟩) (by simp) _
      (part_contains fB (by simp only [wcOff]; omega_arith) (by simp only [wcOff]; omega_arith)
        (by simp only [wcOff]; omega_arith) (by decide))
  · rw [u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide), esp₀]
  · rw [u₆.rd, u₅.rd, rd₄, rd₃, rd₂, rd₁, rd₀, hi.rd]
  · rw [u₆.wr, u₅.wr, wr₄', hi.wr]

theorem zStore_wp {s : State} {P : State → Prop} (k : Nat) (hk : k < 4) (hb : s.gpr .edi = B)
    (hy : s.gpr .esi = Yp) (hwY : reg32 Yp 16 ∈ s.wr) (hwB : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr Yp (4 * k)) (bswap (zw s.mem B k)) →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (zStore k)) s P := by
  refine wp_ldm hb (in_rd (in_reg hwB hs.fB (by simp only [zOff]; omega_arith) (by decide))) fun s₁ u₁ => ?_
  refine wp_bswap fun s₂ u₂ => wp_stm (B := Yp) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hy])
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwY hs.fY (by omega_arith) (by decide)) fun s₃ u₃ => WP.block_nil ?_
  exact h s₃ (by rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem])
    (fun r hr => by rw [u₃.gpr, u₂.other r hr, u₁.other r hr]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])

/-- `Y := Z`, and on to the next block (ZF is set after the last one). -/
theorem store_ok {b : Nat} {s s₃ : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n)
    (F : Frame (mRegions B) s.mem s₃.mem) (edi₃ : s₃.gpr .edi = B) (esp₃ : s₃.gpr .esp = E)
    (rd₃ : s₃.rd = s₁.rd) (wr₃ : s₃.wr = s₁.wr)
    (hz : zOf s₃.mem B = mul (blockAt s.mem (Yp.setWidth 64) ^^^
      blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64)) (blockAt s₁.mem (Hp.setWidth 64))) :
    WP isa (.block store) s₃ fun s' =>
      s'.zf = some (decide (n - (b + 1) = 0)) ∧ BInv s₁ Hp Yp Dp B E n (b + 1) s' := by
  obtain fB := hs.fB; have fY := hs.fY; have fD := hs.fD
  obtain hwY : reg32 Yp 16 ∈ s₃.wr := by rw [wr₃]; exact hs.yW
  obtain hwB : reg32 B 256 ∈ s₃.wr := by rw [wr₃]; exact hs.sW
  -- The slots of the data pointer and the count, and the arguments, are as in `s`.
  obtain slot : ∀ o, 48 ≤ o → o + 4 ≤ 56 → s₃.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 => F.readW (r := ⟨addr B o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← addr_zero]; exact part_disj fB (by omega_arith) (by decide) (.inr (by omega_arith))
      · exact part_disj fB (by omega_arith) (by simp only [wcOff]; omega_arith) (.inl (by simp only [wcOff]; omega_arith)))
      (by decide)
  rw [store_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine wp_ldm (B := E) (o := 8) esp₃ (by rw [rd₃]; exact in_rd_left (hs.argIn 1 (by decide)))
    fun t₁ u₁ => WP.block_nil ?_
  obtain esi₁ : t₁.gpr .esi = Yp := by
    rw [u₁.gpr, F.readW (hs.argC (by decide) (by decide)) (hs.dM hs.aS) (by decide), ← hs.argY]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)
  obtain edi₁ : t₁.gpr .edi = B := by rw [u₁.other _ (by decide), edi₃]
  refine zStore_wp hs 0 (by decide) edi₁ esi₁ (by rw [u₁.wr]; exact hwY) (by rw [u₁.wr]; exact hwB)
    fun t₂ m₂ g₂ rd₂ wr₂ => ?_
  refine zStore_wp hs 1 (by decide) (by rw [g₂ _ (by decide), edi₁]) (by rw [g₂ _ (by decide), esi₁])
    (by rw [wr₂, u₁.wr]; exact hwY) (by rw [wr₂, u₁.wr]; exact hwB) fun t₃ m₃ g₃ rd₃' wr₃' => ?_
  refine zStore_wp hs 2 (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide), edi₁])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), esi₁]) (by rw [wr₃', wr₂, u₁.wr]; exact hwY)
    (by rw [wr₃', wr₂, u₁.wr]; exact hwB) fun t₄ m₄ g₄ rd₄ wr₄ => ?_
  refine zStore_wp hs 3 (by decide) (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), edi₁])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), esi₁])
    (by rw [wr₄, wr₃', wr₂, u₁.wr]; exact hwY) (by rw [wr₄, wr₃', wr₂, u₁.wr]; exact hwB)
    fun t₅ m₅ g₅ rd₅ wr₅ => ?_
  obtain m₅' : t₅.mem = yMem s₃.mem B Yp := by
    rw [m₅, m₄, m₃, m₂, u₁.mem]
    simp only [zw, zOff, hs.rB _ _ (by decide : 16 + 4 * 1 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 2 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 2 + 4 ≤ 256) (by decide : 4 * 1 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 1 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 2 + 4 ≤ 16)]
    rfl
  obtain yB : ∀ o, o + 4 ≤ 256 → (yMem s₃.mem B Yp).readW (addr B o) 32 = s₃.mem.readW (addr B o) 32 :=
    fun o ho => by
      simp only [yMem]
      rw [hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide)]
  obtain edi₅ : t₅.gpr .edi = B := by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), edi₁]
  obtain wr₅' : t₅.wr = s₃.wr := by rw [wr₅, wr₄, wr₃', wr₂, u₁.wr]
  obtain inB : ∀ (t : State), t.wr = s₃.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  refine wp_ldm edi₅ (in_rd (inB _ wr₅' 48 (by decide))) fun t₆ u₆ => wp_addi fun t₇ u₇ => ?_
  refine wp_stm (B := B) (by rw [u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (inB _ (by rw [u₇.wr, u₆.wr, wr₅']) 48 (by decide)) fun t₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (in_rd (inB _ (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅']) 52 (by decide))) fun t₉ u₉ => wp_subi fun t₁₀ u₁₀ _ z₁₀ => ?_
  refine wp_stm (B := B) (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (inB _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅']) 52 (by decide)) fun t₁₁ u₁₁ => WP.block_nil ?_
  have fit' := fB
  obtain d₇ : t₇.gpr .esi = Dp + BitVec.ofNat 32 (16 * (b + 1)) := by
    rw [u₇.gpr, u₆.gpr, m₅', yB _ (by decide), slot 48 (by decide) (by decide)]
    rw [show (48 : Nat) = dOff from rfl, hi.dslot, BitVec.add_assoc]
    congr 1
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
  obtain n₉ : t₉.gpr .esi = BitVec.ofNat 32 (n - b) := by
    rw [u₉.gpr, u₈.mem, u₇.mem, u₆.mem, m₅', rd_wr_ne fit' _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), yB _ (by decide), slot 52 (by decide) (by decide)]
    exact hi.nslot
  let M := ((yMem s₃.mem B Yp).writeW (addr B 48) (Dp + BitVec.ofNat 32 (16 * (b + 1)))).writeW (addr B 52)
    (BitVec.ofNat 32 (n - (b + 1)))
  obtain m₁₁ : t₁₁.mem = M := by
    rw [u₁₁.mem, u₁₀.gpr, n₉, ofNat_pred (by omega_arith), Nat.sub_sub, u₁₀.mem, u₉.mem, u₈.mem, d₇, u₇.mem, u₆.mem,
      m₅']
  have fY' := fY
  obtain hbn : 16 * b + 16 ≤ 16 * n := by omega_arith
  -- The new `Y`.
  obtain hy : blockAt M (Yp.setWidth 64) = zOf s₃.mem B := by
    rw [blockAt_words M fY]
    simp only [M]
    rw [hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide)]
    simp (disch := decide) only [yMem, rd_wr_ne fY', Mem.readW_writeW_self32, Nat.reduceMul, bswap_bswap]
    rfl
  -- The block `X`.
  obtain hx : blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64) =
      blockAt s₁.mem (Dp.setWidth 64 + BitVec.ofNat 64 (16 * b)) := by
    rw [← addr_eq (by omega_arith)]
    refine Proof.Gcm.blockAt_congr fun i hi' => ?_
    refine hi.frame.bytes (R := ⟨addr Dp (16 * b), 16⟩) (fun r hr => ?_) (by show 16 ≤ 2 ^ 64; decide) hi'
    obtain d : Region.Disjoint ⟨addr Dp (16 * b), 16⟩ (reg32 B 256) := hs.dDS.sub_left (part_sub_reg fD hbn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hs.dYD.sub_right (part_sub_reg fD hbn)).symm
    · exact d.sub_right (Region.sub_prefix (by decide))
    · exact d.sub_right (part_sub_reg fB (by simp only [dOff]; omega_arith))
  obtain fr : Frame (bRegions Yp B) s₁.mem M := by
    obtain f₃ : Frame (bRegions Yp B) s₁.mem s₃.mem := hi.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨reg32 B 32, by simp, fun _ h => h⟩
      · exact ⟨⟨addr B dOff, 16⟩, by simp, part_sub fB (by simp only [dOff]; omega_arith)
          (by simp only [dOff, wcOff]; omega_arith) (by simp only [dOff, wcOff]; omega_arith)⟩)
    obtain hY : reg32 Yp 16 ∈ bRegions Yp B := List.mem_cons_self ..
    obtain hD : (⟨addr B dOff, 16⟩ : Region) ∈ bRegions Yp B := by simp
    obtain cY : ∀ k < 4, (reg32 Yp 16).Contains (addr Yp (4 * k)) (32 / 8) := fun k hk =>
      reg_contains fY (by omega_arith) (by decide)
    obtain cD : ∀ o, 48 ≤ o → o + 4 ≤ 64 → (⟨addr B dOff, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
      fun o h1 h2 => part_contains fB (by simp only [dOff]; omega_arith) (by simp only [dOff]; omega_arith)
        (by simp only [dOff]; omega_arith) (by decide)
    exact (((((f₃.writeW hY _ (cY 0 (by decide))).writeW hY _ (cY 1 (by decide))).writeW hY _
      (cY 2 (by decide))).writeW hY _ (cY 3 (by decide))).writeW hD _ (cD 48 (by decide) (by decide))).writeW hD _
      (cD 52 (by decide) (by decide))
  refine ⟨?_, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₁₁]; exact fr⟩
  · rw [u₁₁.zf, z₁₀, n₉, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith), Nat.sub_sub]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), edi₅]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      u₁.other _ (by decide), esp₃]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄, rd₃', rd₂, u₁.rd, rd₃]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅', wr₃]
  · rw [m₁₁]; simp (disch := decide) only [M, dOff, rd_wr_ne fit', Mem.readW_writeW_self32]
  · rw [m₁₁]; simp only [M, nOff, Mem.readW_writeW_self32]
  · rw [m₁₁, hy, hz, ghashFrom_blocksAt_succ, ← hi.y, hx]

/-- One block. -/
theorem body_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa body s fun s' => s'.zf = some (decide (n - (b + 1) = 0)) ∧ BInv s₁ Hp Yp Dp B E n (b + 1) s' := by
  unfold body
  refine WP.seq (WP.mono (load_ok hs hi hb) fun s₂ ⟨hin, F₂, esp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hin) fun s₃ hd => ?_)
  refine store_ok hs hi hb (F₂.trans hd.frame) hd.edi (hd.esp.trans esp₂) (hd.rd.trans rd₂) (hd.wr.trans wr₂) ?_
  rw [mul_eq, ← hd.zv]

/-- The loop over the blocks. -/
theorem blocks_ok {s : State} (hi : BInv s₁ Hp Yp Dp B E n 0 s) (hn : 0 < n) :
    WP isa (.loop body .ne) s (BInv s₁ Hp Yp Dp B E n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ b, k = n - b ∧ b < n ∧ BInv s₁ Hp Yp Dp B E n b s)
    (fun k s ⟨b, hk, hb, hs'⟩ => WP.mono (body_ok hs hs' hb) fun s' ⟨z, d⟩ => ?_) n s ⟨0, rfl, hn, hi⟩
  by_cases hl : b + 1 = n
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at d; exact d
  · exact .inr ⟨by simp [X86.eval, z]; omega_arith, n - (b + 1), by omega_arith, b + 1, rfl, by omega_arith, d⟩

end

/-! ## The prologue and the epilogue -/

/-- After the prologue. -/
structure GP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = sP s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  zf : s.zf = some (decide (nBlk s₀ = 0))
  dslot : s.mem.readW (addr (sP s₀) dOff) 32 = dP s₀
  nslot : s.mem.readW (addr (sP s₀) nOff) 32 = arg s₀ 3
  frame : Frame [⟨addr (sP s₀) 32, 24⟩] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr (sP s₀)) s₀.gpr savedRegs

theorem savedRegs_bound : ∀ p ∈ savedRegs, 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by decide

theorem prologue_eq : prologue = .mov .eax (.mem (at_ .esp 20)) :: (Spill.saveCode .eax savedRegs ++
    ([.mov .edi (.reg .eax), .mov .eax (.mem (at_ .esp 12)), .store (at_ .edi 48) .eax,
      .mov .eax (.mem (at_ .esp 16)), .store (at_ .edi 52) .eax, .alu .test .eax (.reg .eax)] : List Instr)) :=
  rfl

theorem argC {s₀ : State} (hp : GPre s₀) {i : Nat} (hi : i < 5) :
    (aR s₀).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
  show (⟨addr (s₀.gpr .esp) 4, 20⟩ : Region).Contains _ _
  exact part_contains (N := 24) (by have := hp.fSp; omega_arith) (by decide) (by omega_arith) (by omega_arith) (by decide)

theorem prologue_ok {s₀ : State} (hp : GPre s₀) : WP isa (.block prologue) s₀ (GP1 s₀) := by
  have fB : (sP s₀).toNat + 256 ≤ 2 ^ 32 := hp.fS
  let B := sP s₀
  let E := s₀.gpr .esp
  obtain hwB : reg32 B 256 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain hrA : aR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  obtain argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨aR s₀, List.mem_append_left _ (ht ▸ hrA), argC hp hi⟩
  obtain bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  obtain hm : (⟨addr B 32, 24⟩ : Region) ∈ [(⟨addr B 32, 24⟩ : Region)] := List.mem_singleton_self _
  obtain cB : ∀ o, 32 ≤ o → o + 4 ≤ 56 → (⟨addr B 32, 24⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by decide) h1 (by omega_arith) (by decide)
  obtain dA : ∀ r ∈ [(⟨addr B 32, 24⟩ : Region)], (aR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aS.sub_right (part_sub_reg fB (by decide))
  rw [prologue_eq]
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by decide)) fun s₁ u₁ => ?_
  obtain e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine Spill.save_ok savedRegs (fun p h => by
    rw [e₁]; exact bIn _ u₁.wr _ (by have := savedRegs_bound p h; omega_arith)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  obtain g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₁.other r h1]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₁.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₁.wr]
  obtain edi₆ : s₆.gpr .edi = B := by rw [u₆.gpr, u₅.gpr]; exact e₁
  obtain esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  let M := Spill.saveMem s₀.mem (addr B) s₀.gpr savedRegs
  obtain m₆ : s₆.mem = M := by
    rw [u₆.mem, u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain f₆ : Frame [⟨addr B 32, 24⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact Spill.saveMem_frame hm _ _ _ _ fun p h => cB _ (savedRegs_bound p h).1 (by have := savedRegs_bound p h; omega_arith)
  refine wp_ldm (B := E) (o := 12) esp₆ (argIn _ rd₆ 2 (by decide)) fun s₇ u₇ => ?_
  refine wp_stm (B := B) (by rw [u₇.other _ (by decide), edi₆]) (bIn _ (by rw [u₇.wr, wr₆]) 48 (by decide))
    fun s₈ u₈ => ?_
  obtain f₈ : Frame [⟨addr B 32, 24⟩] s₀.mem s₈.mem := by
    rw [u₈.mem, u₇.mem]; exact f₆.writeW hm _ (cB 48 (by decide) (by decide))
  refine wp_ldm (B := E) (o := 16) (by rw [u₈.gpr, u₇.other _ (by decide), esp₆])
    (argIn _ (by rw [u₈.rd, u₇.rd, rd₆]) 3 (by decide)) fun s₉ u₉ => ?_
  refine wp_stm (B := B) (by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), edi₆])
    (bIn _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 52 (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_test fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  obtain a₇ : s₇.gpr .eax = dP s₀ := by
    rw [u₇.gpr]; exact f₆.readW (argC hp (i := 2) (by decide)) dA (by decide)
  obtain a₉ : s₉.gpr .eax = arg s₀ 3 := by
    rw [u₉.gpr]; exact f₈.readW (argC hp (i := 3) (by decide)) dA (by decide)
  have fit' : B.toNat + 256 ≤ 2 ^ 32 := fB
  let M' := (M.writeW (addr B 48) (dP s₀)).writeW (addr B 52) (arg s₀ 3)
  obtain m₁₁ : s₁₁.mem = M' := by
    rw [u₁₁.mem, u₁₀.mem, a₉, u₉.mem, u₈.mem, a₇, u₇.mem, m₆]
  refine ⟨?_, ?_, by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆], by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆],
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), esp₆]
  · rw [u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), edi₆]
  · rw [z₁₁, u₁₀.gpr, a₉, BitVec.and_self]
    by_cases h : arg s₀ 3 = 0
    · simp [h, nBlk]
    · have : (arg s₀ 3).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (arg s₀ 3 == 0) = false from beq_eq_false_iff_ne.mpr h]
      simp [nBlk, this]
  · rw [m₁₁]; show M'.readW (addr B 48) 32 = _
    simp (disch := decide) only [M', rd_wr_ne fit', Mem.readW_writeW_self32]
  · rw [m₁₁]; show M'.readW (addr B 52) 32 = _
    simp only [M', Mem.readW_writeW_self32]
  · rw [m₁₁]
    have := (f₆.writeW hm (dP s₀) (cB 48 (by decide) (by decide))).writeW hm (arg s₀ 3) (cB 52 (by decide) (by decide))
    rwa [m₆] at this
  · rw [m₁₁]
    exact ((Spill.saveMem_saved_addr s₀.mem s₀.gpr (l := savedRegs) (n := 256) (by decide) fit').writeW_addr fit'
      (by decide) (by decide) (by decide) _).writeW_addr fit' (by decide) (by decide) (by decide) _

theorem restore_ok {s : State} {B : BitVec 32} {g : Reg → BitVec 32} (hb : s.gpr .edi = B)
    (hfit : B.toNat + 256 ≤ 2 ^ 32) (hw : reg32 B 256 ∈ s.wr) (hs : Spill.Saved s.mem (addr B) g savedRegs) :
    WP isa (.block restore) s (Spill.Restored s · g ([(.ebx, 32), (.esi, 36), (.ebp, 44)] ++ [(.edi, 40)])) := by
  rw [show restore = Spill.restoreCode .edi ([(.ebx, 32), (.esi, 36), (.ebp, 44)] ++ [(.edi, 40)]) ++ [] from rfl]
  exact Spill.restoreBase_ok _ (by decide)
    (fun p h => have := savedRegs_bound p (by revert p h; decide); by
      rw [hb]; exact in_rd (in_reg hw hfit (by omega_arith) (by decide)))
    (by rw [hb]; exact hs.sub (by decide)) fun s' r => WP.block_nil r

/-! ## The whole function -/

theorem blocksAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 16 * n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    blocksAt m' p n = blocksAt m p n := by
  unfold blocksAt
  refine List.map_congr_left fun i hi => Proof.Gcm.blockAt_congr fun j hj => ?_
  rw [List.mem_range] at hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega_arith)

theorem gh_correct {s₀ : State} (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.ghash s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  let Hp := hP s₀
  let Yp := yP s₀
  let Dp := dP s₀
  let B := sP s₀
  let E := s₀.gpr .esp
  let n := nBlk s₀
  have fH : Hp.toNat + 16 ≤ 2 ^ 32 := hp.fH
  have fY : Yp.toNat + 16 ≤ 2 ^ 32 := hp.fY
  have fD : Dp.toNat + 16 * n ≤ 2 ^ 32 := hp.fD
  have fB : B.toNat + 256 ≤ 2 ^ 32 := hp.fS
  have fE : E.toNat + 24 ≤ 2 ^ 32 := hp.fSp
  unfold Impl.Gcm.X86.ghash
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain d₁ : ∀ {R : Region}, R.Disjoint (sR s₀) → ∀ r ∈ [(⟨addr B 32, 24⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (part_sub_reg fB (by decide))
  obtain aSub : Region.Sub ⟨addr E 4, 8⟩ (aR s₀) := Region.sub_prefix (by decide)
  obtain hs : BSetup s₁ Hp Yp Dp B E n :=
    { hR := by rw [h₁.rd, hp.rd]; exact List.mem_cons_self ..
      dR := by rw [h₁.rd, hp.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      yW := by rw [h₁.wr, hp.wr]; exact List.mem_cons_self ..
      sW := by rw [h₁.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      fH, fY, fD, fB, fE
      dHY := hp.dHY, dHS := hp.dHS, dYD := hp.dYD, dYS := hp.dYS, dDS := hp.dDS
      argIn := fun i hi => ⟨aR s₀, by rw [h₁.rd, hp.rd]; simp, argC hp (by omega_arith)⟩
      argH := h₁.frame.readW (argC hp (i := 0) (by decide)) (d₁ hp.aS) (by decide)
      argY := h₁.frame.readW (argC hp (i := 1) (by decide)) (d₁ hp.aS) (by decide)
      aY := hp.aY.sub_left aSub
      aS := hp.aS.sub_left aSub }
  obtain bi : BInv s₁ Hp Yp Dp B E n 0 s₁ :=
    { hb := Nat.zero_le _
      edi := h₁.edi
      esp := h₁.esp
      rd := rfl
      wr := rfl
      dslot := by
        rw [Nat.mul_zero, show Dp + BitVec.ofNat 32 0 = Dp from BitVec.add_zero _]; exact h₁.dslot
      nslot := by rw [Nat.sub_zero]; rw [h₁.nslot]; simp [n]
      y := rfl
      frame := Frame.refl _ _ }
  refine WP.seq (WP.mono (Q := BInv s₁ Hp Yp Dp B E n n) (WP.ite (decide (n = 0))
    (by simp only [X86.eval, h₁.zf]; rfl) (fun h => WP.block_nil ?_) (fun h => blocks_ok hs bi ?_)) fun s₄ h₄ => ?_)
  · have : n = 0 := by simpa using h
    rw [this] at bi ⊢; exact bi
  · have : n ≠ 0 := by simpa using h
    omega_arith
  -- What the whole function writes.
  obtain F : Frame [reg32 Yp 16, reg32 B 256] s₀.mem s₄.mem :=
    (h₁.frame.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)⟩).trans
    (h₄.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨reg32 Yp 16, by simp, fun _ h => h⟩
      · exact ⟨reg32 B 256, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨reg32 B 256, by simp, part_sub_reg fB (by simp only [dOff]; omega_arith)⟩)
  obtain saved : Spill.Saved s₄.mem (addr B) s₀.gpr savedRegs := h₁.saved.of_readW fun p hp' => by
    obtain h2 := savedRegs_bound p hp'
    exact h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.dYS.sub_right (part_sub_reg fB (by omega_arith))).symm
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← addr_zero]; exact part_disj fB (by omega_arith) (by decide) (.inr (by omega_arith))
      · exact part_disj fB (by omega_arith) (by simp only [dOff]; omega_arith) (.inl (by simp only [dOff]; omega_arith)))
      (by decide)
  refine WP.mono (restore_ok h₄.edi fB (by rw [h₄.wr]; exact hs.sW) saved) fun s₅ r₅ => ?_
  refine ⟨⟨r₅.abi (by decide) (by decide) h₄.esp, ?_⟩, ?_⟩
  · rw [r₅.mem]
    exact F.readW (r := rR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rY
      · exact hp.rS) (by decide)
  · show blockAt s₅.mem (Yp.setWidth 64) =
      ghashFrom (blockAt s₀.mem (Hp.setWidth 64)) (blockAt s₀.mem (Yp.setWidth 64))
        (blocksAt s₀.mem (Dp.setWidth 64) n)
    obtain eB : ∀ {R : Region}, R.Disjoint (sR s₀) → R.len ≤ 2 ^ 64 → ∀ i < R.len,
        s₁.mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) :=
      fun hR hl i hi => h₁.frame.bytes (d₁ hR) hl hi
    rw [r₅.mem, h₄.y]
    rw [Proof.Gcm.blockAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Hp.setWidth 64)
        fun i hi => eB (R := hR s₀) hp.dHS (by show 16 ≤ 2 ^ 64; decide) i hi,
      Proof.Gcm.blockAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Yp.setWidth 64)
        fun i hi => eB (R := yR s₀) hp.dYS (by show 16 ≤ 2 ^ 64; decide) i hi,
      blocksAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Dp.setWidth 64)
        fun i hi => eB (R := dR s₀) hp.dDS (by show 16 * n ≤ 2 ^ 64; omega_arith) i hi]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86.post s s' :=
  (gh_correct (GPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

end VG.Proof.Gcm.X86
