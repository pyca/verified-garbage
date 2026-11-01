module

public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# GHASH on RISC-V: the multiplications

Untrusted: everything here is checked by Lean. A block as its high and low
64-bit words (`w2`), and what the instructions of `Impl/Gcm/RISCV64.lean`
compute on them, stated on whole blocks: the step of Algorithm 1's `V`
(`vstep`, `tab_step`), the masks (`mask_shl`), a masked accumulation
(`acc_mask`) and the shift of `x` by a byte (`w2_shl8`). The values of `V`
do not depend on the factor `x` (`mulSteps_snd`), so a table of them serves
every block.

The table the code writes to its frame at `B` (`Tab`: entry `j`, `Vⱼ`, at
`B + 16 j`), one entry at a time (`tabStep_ok`), eight per iteration
(`tabBody_ok`), and all 128 (`table_ok`). The frame is the only memory
written (`Out`), and the code writes only its temporaries (`TKeep`).

With the table `Tab` in the frame at `B`, a step of Algorithm 1
(`mulStep_ok`: `Z := Z ⊕ Vᵢ` if bit `i` of `x` is set), a byte of `x`
(`mulBody_ok`), and the product (`mul_loop`).
-/

@[expose] public section

/-! ## Blocks as two words -/

namespace VG.Proof.Gcm.RISCV64

open VG.Spec.Gcm (Block R mul)
open VG.Proof.Gcm

/-! ## Algorithm 1 with the values of `V` given -/

/-- Algorithm 1's step of `V`. -/
def vstep (v : Block) : Block := if v.getLsbD 0 then (v >>> 1) ^^^ R else v >>> 1

/-- `Vᵢ`, from `V₀ = H`. -/
def vs (h : Block) : Nat → Block
  | 0 => h
  | i + 1 => vstep (vs h i)

theorem mulSteps_snd (x h : Block) : ∀ i, (mulSteps x h i).2 = vs h i
  | 0 => rfl
  | i + 1 => by rw [mulSteps_succ, mulStep, mulSteps_snd x h i]; rfl

theorem mulSteps_fst_succ (x h : Block) (i : Nat) :
    (mulSteps x h (i + 1)).1 =
      if x.getMsbD i then (mulSteps x h i).1 ^^^ vs h i else (mulSteps x h i).1 := by
  rw [mulSteps_succ, mulStep, mulSteps_snd]

/-! ## Two words -/

/-- The block of the high word `a` and the low word `b`. -/
abbrev w2 (a b : BitVec 64) : Block := a ++ b

theorem getLsbD_w2 (a b : BitVec 64) (i : Nat) :
    (w2 a b).getLsbD i = if i < 64 then b.getLsbD i else a.getLsbD (i - 64) := by
  simp only [w2, BitVec.getLsbD_append]

theorem w2_xor (a b c d : BitVec 64) : w2 a b ^^^ w2 c d = w2 (a ^^^ c) (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_w2, getLsbD_w2, getLsbD_w2]
  split <;> simp [BitVec.getLsbD_xor]

theorem w2_zero : w2 0 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_w2]; split <;> simp

/-- The high word's bits, from the left, are the block's first 64. -/
theorem getMsbD_w2 (a b : BitVec 64) {k : Nat} (hk : k < 64) : (w2 a b).getMsbD k = a.getMsbD k := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getMsbD_eq_getLsbD, getLsbD_w2]
  simp only [show k < 64 + 64 by omega, hk, decide_true, Bool.true_and]
  rw [ite_eq_right (show ¬ 128 - 1 - k < 64 by omega)]
  congr 1
  omega

/-! ## Masks -/

/-- `0` or all ones. -/
abbrev mask (c : Bool) : BitVec 64 := if c then BitVec.allOnes 64 else 0

/-- `srai 63` of `x << k` is all ones exactly when bit `k` (from the left) of `x` is set. -/
theorem mask_shl (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (x <<< k).sshiftRight 63 = mask (x.getMsbD k) := by
  have hm : (x <<< k).msb = x.getMsbD k := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getMsbD_eq_getLsbD]
    simp [hk, show ¬ 64 - 1 < k by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  simp only [show ¬ 64 ≤ i by omega, decide_false, Bool.not_false, Bool.true_and]
  have he : (if 63 + i < 64 then (x <<< k).getLsbD (63 + i) else (x <<< k).msb) = (x <<< k).msb := by
    split
    · rw [show 63 + i = 64 - 1 by omega, BitVec.msb_eq_getLsbD_last]
    · rfl
  rw [he, hm]
  cases x.getMsbD k
  · simp [mask]
  · simp only [mask, ite_true, BitVec.getLsbD_allOnes, hi, decide_true]

/-- `srai 63` of `x << 63` is all ones exactly when the lowest bit of `x` is set. -/
theorem mask_lsb (x : BitVec 64) : (x <<< 63).sshiftRight 63 = mask (x.getLsbD 0) := by
  rw [mask_shl x (by decide), BitVec.getMsbD_eq_getLsbD]; rfl

/-- `Z := Z ⊕ (U ∧ M)`, word by word, for the mask of `c`. -/
theorem acc_mask (z0 z1 u0 u1 : BitVec 64) (c : Bool) :
    w2 (z0 ^^^ (u0 &&& mask c)) (z1 ^^^ (u1 &&& mask c)) = if c then w2 z0 z1 ^^^ w2 u0 u1 else w2 z0 z1 := by
  cases c
  · simp [mask]
  · simp only [mask, ite_true, BitVec.and_allOnes, w2_xor]

/-! ## The step of `V` -/

/-- `R`'s high word, as the code builds it (`li -31`, `slli 56`). -/
theorem rr_eq : BitVec.ofInt 64 (-31) <<< 56 = 0xE100000000000000#64 := by decide

theorem R_w2 : R = w2 0xE100000000000000#64 0 := by decide

/-- The shifts and `or` shift the two words right by one bit. -/
theorem w2_shr1 (a b : BitVec 64) : w2 (a >>> 1) (b >>> 1 ||| a <<< 63) = w2 a b >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, getLsbD_w2, getLsbD_w2]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 63 ∨ i = 63 ∨ (64 ≤ i ∧ i < 127) ∨ i = 127) with h | h | h | h
  · simp [h, show i < 64 by omega, show 1 + i < 64 by omega]
  · subst h; simp
  · simp [show ¬ i < 64 by omega, show ¬ 1 + i < 64 by omega, show 1 + (i - 64) = 1 + i - 64 by omega]
  · subst h; simp

/-- `tabStep`'s computation of the next `V`. -/
theorem tab_step (a b : BitVec 64) :
    w2 (a >>> 1 ^^^ ((b <<< 63).sshiftRight 63 &&& BitVec.ofInt 64 (-31) <<< 56)) (b >>> 1 ||| a <<< 63) =
      vstep (w2 a b) := by
  have h0 : (w2 a b).getLsbD 0 = b.getLsbD 0 := by rw [getLsbD_w2]; rfl
  rw [vstep, h0, ← w2_shr1, mask_lsb, rr_eq, R_w2]
  cases b.getLsbD 0
  · simp [mask]
  · simp only [mask, ite_true, BitVec.allOnes_and, w2_xor]; simp

/-! ## The shift of `x` -/

theorem w2_shl8 (a b : BitVec 64) : w2 (a <<< 8 ||| b >>> 56) (b <<< 8) = w2 a b <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, getLsbD_w2, getLsbD_w2]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 72) ∨ 72 ≤ i) with h | h | h | h
  · simp [h, show i < 64 by omega]
  · simp [show i < 64 by omega, show ¬ i < 8 by omega, hi, show i - 8 < 64 by omega]
  · simp [show ¬ i < 64 by omega, show i - 64 < 8 by omega, show ¬ i < 8 by omega, hi,
      show 56 + (i - 64) = i - 8 by omega, show i - 8 < 64 by omega]
  · simp [show ¬ i < 64 by omega, show ¬ i - 64 < 8 by omega, show ¬ i < 8 by omega, hi,
      show i - 64 - 8 = i - 8 - 64 by omega, show ¬ i - 8 < 64 by omega, show i - 64 < 64 by omega,
      BitVec.getLsbD_of_ge b (56 + (i - 64)) (by omega)]

/-- Bit `k` of the top byte of `x <<< 8j` is bit `8j + k` of `x`. -/
theorem getMsbD_shl8 (x : Block) (j k : Nat) :
    (x <<< (8 * j)).getMsbD k = x.getMsbD (8 * j + k) := by
  rw [BitVec.getMsbD_shiftLeft]
  simp [Nat.add_comm]

end VG.Proof.Gcm.RISCV64

/-! ## The table of `V` -/

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block)

/-! ## The words of a block -/

/-- The high word of a block. -/
abbrev hi (v : Block) : BitVec 64 := v.extractLsb' 64 64
/-- The low word of a block. -/
abbrev lo (v : Block) : BitVec 64 := v.extractLsb' 0 64

theorem hi_w2 (a b : BitVec 64) : hi (w2 a b) = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  rw [BitVec.getLsbD_extractLsb', getLsbD_w2]
  simp [hlt, show ¬ 64 + i < 64 by omega]

theorem lo_w2 (a b : BitVec 64) : lo (w2 a b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  rw [BitVec.getLsbD_extractLsb', getLsbD_w2]
  simp [hlt]

theorem w2_hi_lo (v : Block) : w2 (hi v) (lo v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  rw [getLsbD_w2]
  split
  · rw [BitVec.getLsbD_extractLsb']; simp [*]
  · rw [BitVec.getLsbD_extractLsb']
    simp only [show i - 64 < 64 by omega, decide_true, Bool.true_and]
    congr 1; omega

/-! ## Rules for the instructions `Steps` lacks -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_sra {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

end

/-! ## Addresses in the frame -/

/-- The frame of 2048 bytes at `B`, writable, 16-byte aligned, not wrapping. -/
structure FrameOk (B : Addr) (s : State) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 2048 ≤ 2 ^ 64
  wr : (⟨B, 2048⟩ : Region) ∈ s.wr

theorem FrameOk.of_wr {B : Addr} {s s' : State} (h : FrameOk B s) (hw : s'.wr = s.wr) : FrameOk B s' :=
  ⟨h.al, h.fit, hw ▸ h.wr⟩

theorem FrameOk.al8 {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2048) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Wp.al8 h.al hd (by omega)

theorem FrameOk.inW {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.wr, Offset.contains_base _ hd (by omega)⟩

theorem FrameOk.inR {B : Addr} {s : State} (h : FrameOk B s) {d : Nat} (hd : d + 8 ≤ 2048) :
    InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8 := by
  obtain ⟨r, hr, hc⟩ := h.inW hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ptr_off (B : Addr) (j k : Nat) :
    B + BitVec.ofNat 64 (128 * j) + BitVec.ofNat 64 k = B + BitVec.ofNat 64 (128 * j + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The table -/

/-- Entries `j < i` of the table at `B` hold `Vⱼ`, high word first. -/
def Tab (h : Block) (B : Addr) (m : Mem) (i : Nat) : Prop :=
  ∀ j < i, m.readW (B + BitVec.ofNat 64 (16 * j)) 64 = hi (vs h j) ∧
    m.readW (B + BitVec.ofNat 64 (16 * j + 8)) 64 = lo (vs h j)

/-- Memory outside the frame at `B` is that of `m`. -/
def Out (B : Addr) (m m' : Mem) : Prop := ∀ x, ¬ (x - B).toNat < 2048 → m' x = m x

theorem Out.refl (B : Addr) (m : Mem) : Out B m m := fun _ _ => rfl

theorem Out.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Out B m₁ m₂) (h₂ : Out B m₂ m₃) : Out B m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Out.writeW {B : Addr} {m m' : Mem} (h : Out B m m') {d : Nat} (hd : d + 8 ≤ 2048) (v : BitVec 64) :
    Out B m (m'.writeW (B + BitVec.ofNat 64 d) v) := by
  intro x hx
  rw [Mem.writeW, Mem.write_apply, h x hx]
  intro hlt
  apply hx
  have e : x - B = (x - (B + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- A table entry is still there after a write elsewhere in the frame. -/
theorem readW_writeW_frame {m : Mem} {B : Addr} {a b : Nat} (v : BitVec 64) (hab : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a + 8 ≤ 2048) (hb : b + 8 ≤ 2048) :
    (m.writeW (B + BitVec.ofNat 64 b) v).readW (B + BitVec.ofNat 64 a) 64 =
      m.readW (B + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep B hab (by omega) (by omega)) (by decide)

theorem Tab.write2 {h : Block} {B : Addr} {m : Mem} {i : Nat} (ht : Tab h B m i) (hi128 : i < 128) :
    Tab h B ((m.writeW (B + BitVec.ofNat 64 (16 * i)) (hi (vs h i))).writeW
      (B + BitVec.ofNat 64 (16 * i + 8)) (lo (vs h i))) (i + 1) := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨h1, h2⟩ := ht j hj
    refine ⟨?_, ?_⟩
    · rw [readW_writeW_frame _ (by omega) (by omega) (by omega),
        readW_writeW_frame _ (by omega) (by omega) (by omega), h1]
    · rw [readW_writeW_frame _ (by omega) (by omega) (by omega),
        readW_writeW_frame _ (by omega) (by omega) (by omega), h2]
  · refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
    rw [readW_writeW_frame _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]

/-- The registers the table writes. -/
def tabRegs : List Reg := [X0, X1, M, T, P, E, RR]

/-- The state after `i` entries, at the start of iteration `i / 8` (`P` at
entry `8 (i / 8)`). -/
structure TabInv (h : Block) (B : Addr) (sB : State) (i : Nat) (s : State) : Prop where
  v : w2 (s.gpr X0) (s.gpr X1) = vs h i
  rr : s.gpr RR = BitVec.ofInt 64 (-31) <<< 56
  e : s.gpr E = B + BitVec.ofNat 64 2048
  tab : Tab h B s.mem i
  out : Out B sB.mem s.mem
  keep : ∀ r, r ∉ tabRegs → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem tabStep_ok {h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) {j k : Nat} (hj : j < 16)
    (hk : k < 8) {s : State} (hs : TabInv h B sB (8 * j + k) s)
    (hp : s.gpr P = B + BitVec.ofNat 64 (128 * j)) :
    WP isa (.block (tabStep k)) s fun s' =>
      TabInv h B sB (8 * j + k + 1) s' ∧ s'.gpr P = s.gpr P := by
  have hF' : FrameOk B s := hF.of_wr hs.wr
  have a₁ : s.gpr P + BitVec.ofNat 64 (16 * k) = B + BitVec.ofNat 64 (16 * (8 * j + k)) := by
    rw [hp, ptr_off]; congr 2; omega
  have a₂ : s.gpr P + BitVec.ofNat 64 (16 * k + 8) = B + BitVec.ofNat 64 (16 * (8 * j + k) + 8) := by
    rw [hp, ptr_off]; congr 2; omega
  refine wp_sd (by omega) a₁ (hF.al8 (by omega) (by omega)) (hF'.inW (by omega)) fun s₁ u₁ => ?_
  refine wp_sd (by omega) (by rw [u₁.gpr]; exact a₂) (hF.al8 (by omega) (by omega))
    (by rw [u₁.wr]; exact hF'.inW (by omega)) fun s₂ u₂ => ?_
  refine wp_sll (by decide) fun s₃ u₃ => wp_sra (by decide) fun s₄ u₄ => wp_and fun s₅ u₅ =>
    wp_sll (by decide) fun s₆ u₆ => wp_srl (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ =>
    wp_srl (by decide) fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => WP.block_nil ?_
  -- Registers through the writes.
  have g₂ : s₂.gpr = s.gpr := by rw [u₂.gpr, u₁.gpr]
  have a : s₂.gpr X0 = s.gpr X0 := by rw [g₂]
  have b : s₂.gpr X1 = s.gpr X1 := by rw [g₂]
  have x0 : s₁₀.gpr X0 = s.gpr X0 >>> 1 ^^^
      ((s.gpr X1 <<< 63).sshiftRight 63 &&& BitVec.ofInt 64 (-31) <<< 56) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), a,
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.gpr, u₃.gpr, u₄.other _ (by decide), u₃.other _ (by decide), b, g₂, hs.rr]
  have x1 : s₁₀.gpr X1 = s.gpr X1 >>> 1 ||| s.gpr X0 <<< 63 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₇.other _ (by decide),
      u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), a, b]
  have g10 : ∀ r, r ≠ X0 → r ≠ X1 → r ≠ M → r ≠ T → s₁₀.gpr r = s.gpr r := fun r h0 h1 hm ht => by
    rw [u₁₀.other _ h0, u₉.other _ h0, u₈.other _ h1, u₇.other _ h1, u₆.other _ ht,
      u₅.other _ hm, u₄.other _ hm, u₃.other _ hm, g₂]
  have go : ∀ r, r ∉ tabRegs → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [tabRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g10 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1
  have mm : s₁₀.mem = (s.mem.writeW (B + BitVec.ofNat 64 (16 * (8 * j + k))) (s.gpr X0)).writeW
      (B + BitVec.ofNat 64 (16 * (8 * j + k) + 8)) (s.gpr X1) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  have rd : s₁₀.rd = s.rd := by
    rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp : s₁₀.sp = s.sp := by
    rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have hv := hs.v
  have e0 : s.gpr X0 = hi (vs h (8 * j + k)) := by rw [← hv, hi_w2]
  have e1 : s.gpr X1 = lo (vs h (8 * j + k)) := by rw [← hv, lo_w2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun r hr => (go r hr).trans (hs.keep r hr), rd.trans hs.rd,
    wr.trans hs.wr, sp.trans hs.sp⟩, g10 P (by decide) (by decide) (by decide) (by decide)⟩
  · rw [x0, x1, tab_step, hv]; rfl
  · rw [g10 _ (by decide) (by decide) (by decide) (by decide), hs.rr]
  · rw [g10 _ (by decide) (by decide) (by decide) (by decide), hs.e]
  · rw [mm, e0, e1]; exact hs.tab.write2 (by omega)
  · rw [mm]; exact (hs.out.writeW (by omega) _).writeW (by omega) _

theorem tabBody_ok {h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) {j : Nat} (hj : j < 16)
    {s : State} (hs : TabInv h B sB (8 * j) s) (hp : s.gpr P = B + BitVec.ofNat 64 (128 * j)) :
    WP isa (.block tabBody) s fun s' =>
      TabInv h B sB (8 * (j + 1)) s' ∧ s'.gpr P = B + BitVec.ofNat 64 (128 * (j + 1)) := by
  rw [tabBody, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k s' => TabInv h B sB (8 * j + k) s' ∧ s'.gpr P = B + BitVec.ofNat 64 (128 * j))
    (fun k s' hk ⟨hi, hp'⟩ => WP.mono (tabStep_ok hF hj hk hi hp') fun s'' ⟨hi', hp''⟩ =>
      ⟨hi', hp''.trans hp'⟩) 8 (Nat.le_refl _) s ⟨by simpa using hs, hp⟩) fun s₁ ⟨h₁, p₁⟩ => ?_
  refine wp_addi (by decide) fun s₂ u₂ => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, u₂.mem ▸ h₁.tab, u₂.mem ▸ h₁.out, fun r hr => ?_, u₂.rd.trans h₁.rd,
      u₂.wr.trans h₁.wr, u₂.sp.trans h₁.sp⟩
    · rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact h₁.v
    · rw [u₂.other _ (by decide)]; exact h₁.rr
    · rw [u₂.other _ (by decide)]; exact h₁.e
    · rw [u₂.other _ (fun e => hr (by rw [e]; decide))]; exact h₁.keep r hr
  · rw [u₂.gpr, p₁, ptr_off]; congr 2

/-- `B + 128 (j + 1)` is the end of the frame exactly when `j + 1 = 16`. -/
theorem end_ne (B : Addr) {j : Nat} (hj : j < 16) :
    (B + BitVec.ofNat 64 (128 * (j + 1)) != B + BitVec.ofNat 64 2048) = decide (j + 1 ≠ 16) := by
  by_cases h : j + 1 = 16
  · rw [h]; simp
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg (fun x => (x - B).toNat) e
    simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem table_loop {h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) {s : State}
    (hs : TabInv h B sB 0 s) (hp : s.gpr P = B) :
    WP isa (.loop (.block tabBody) (.ne P E)) s (TabInv h B sB 128) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ j, n = 16 - j ∧ j < 16 ∧ TabInv h B sB (8 * j) s' ∧
      s'.gpr P = B + BitVec.ofNat 64 (128 * j))
    (fun n s' ⟨j, hn, hj, hi, hp'⟩ => WP.mono (tabBody_ok hF hj hi hp') fun s'' ⟨hi', hp''⟩ => ?_)
    16 s ⟨0, rfl, by decide, hs, by rw [hp]; simp⟩
  have hev : isa.eval (.ne P E) s'' = some (decide (j + 1 ≠ 16)) := by
    show some (s''.gpr P != s''.gpr E) = _
    rw [hp'', hi'.e, end_ne B hj]
  by_cases hl : j + 1 = 16
  · refine .inl ⟨by rw [hev]; simp [hl], ?_⟩
    have e : 8 * (j + 1) = 128 := by omega
    rw [← e]; exact hi'
  · exact .inr ⟨by rw [hev, decide_eq_true hl], 16 - (j + 1), by omega, j + 1, rfl, by omega, hi', hp''⟩

/-- Two big-endian words read a byte at a time: `loadBE64` twice, into `d₀`
and `d₁` through `tmp`, from `n`. -/
theorem load2_ok {d₀ d₁ tmp n : Reg} (h0n : d₀ ≠ n) (h1n : d₁ ≠ n) (htn : tmp ≠ n) (h0t : d₀ ≠ tmp)
    (h1t : d₁ ≠ tmp) (h01 : d₀ ≠ d₁) {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr n) 16)
    (k : ∀ s', s'.gpr d₀ = ByteLoad.be64 s.mem (s.gpr n) 0 → s'.gpr d₁ = ByteLoad.be64 s.mem (s.gpr n) 8 →
      (∀ r, r ≠ d₀ → r ≠ d₁ → r ≠ tmp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 d₀ tmp n 0 ++ Impl.Words.RISCV64.loadBE64 d₁ tmp n 8 ++ is)) s Q := by
  have hin8 : ∀ off, off + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8 :=
    fun off ho => CallLay.inRegions_sub hin ho (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok h0n htn h0t (by decide) (hin8 0 (by decide))) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.loadBE64_ok h1n htn h1t (by decide) ?_) fun s₂ e₂ => ?_
  · simpa [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, Ne.symm htn, Ne.symm h0n] using hin8 8 (by decide)
  · subst e₂
    refine k _ ?_ ?_ ?_ rfl rfl rfl rfl
    · simp [RegUpd.gpr_write, h01, h0t, Ne.symm h0n, Ne.symm htn]
    · simp [RegUpd.gpr_write, RegUpd.mem_write, Ne.symm h0n, Ne.symm htn]
    · intro r r0 r1 rt
      simp [RegUpd.gpr_write, r0, r1, rt]

/-- The block of `H`, from its 16 bytes at `p`. -/
abbrev hOf (m : Mem) (p : Addr) : Block := w2 (ByteLoad.be64 m p 0) (ByteLoad.be64 m p 8)

/-- The table, written to the frame at the stack pointer, from `H` at `h`. -/
theorem table_ok {sB : State} (hF : FrameOk sB.sp sB) (hin : InRegions (sB.rd ++ sB.wr) (sB.gpr HP) 16) :
    WP isa table sB fun s => TabInv (hOf sB.mem (sB.gpr HP)) sB.sp sB 128 s := by
  refine WP.seq ?_
  rw [tabInit, List.append_assoc]
  refine load2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hin
    fun s₁ h0 h1 g₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine WP.cons (exec_li (by decide)) ?_
  refine wp_sll (by decide) fun s₃ u₃ => wp_addSp (by decide) fun s₄ u₄ =>
    wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ => WP.block_nil ?_
  refine table_loop hF ⟨?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), ?_, fun r hr => ?_,
    ?_, ?_, ?_⟩ ?_
  · simp only [vs]
    rw [u₆.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h0, h1]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      RegUpd.gpr_write_self]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.sp, RegUpd.sp_write, sp₁, BitVec.add_zero, BitVec.add_assoc]
    rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, RegUpd.mem_write, m₁]; exact Out.refl _ _
  · simp only [tabRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2.2.2.1, u₅.other _ hr.2.2.2.2.2.1, u₄.other _ hr.2.2.2.2.1,
      u₃.other _ hr.2.2.2.2.2.2, RegUpd.gpr_write_of_ne _ _ hr.2.2.2.2.2.2, g₁ _ hr.1 hr.2.1 hr.2.2.2.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, RegUpd.rd_write, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, RegUpd.wr_write, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, RegUpd.sp_write, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.sp, RegUpd.sp_write, sp₁,
      BitVec.add_zero]

end VG.Proof.Gcm.RISCV64

/-! ## The multiplications -/

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (mulSteps)

/-- The registers the multiplication writes. -/
def mulRegs : List Reg := [Z0, Z1, X0, X1, U0, U1, M, T, P]

/-- After `j` bytes of `x • h`, from the state `sB` (where the table is in
memory): `Z` is Algorithm 1's after `8 j` steps, `x` is shifted left by
`j` bytes, and `P` is at entry `8 j`. -/
structure MulInv (x h : Block) (B : Addr) (sB : State) (j : Nat) (s : State) : Prop where
  z : w2 (s.gpr Z0) (s.gpr Z1) = (mulSteps x h (8 * j)).1
  x : w2 (s.gpr X0) (s.gpr X1) = x <<< (8 * j)
  p : s.gpr P = B + BitVec.ofNat 64 (128 * j)
  e : s.gpr E = B + BitVec.ofNat 64 2048
  mem : s.mem = sB.mem
  keep : ∀ r, r ∉ mulRegs → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

/-- Within byte `j`, after `k` of its steps. -/
structure StepInv (x h : Block) (B : Addr) (sB : State) (j k : Nat) (s : State) : Prop where
  z : w2 (s.gpr Z0) (s.gpr Z1) = (mulSteps x h (8 * j + k)).1
  x : w2 (s.gpr X0) (s.gpr X1) = x <<< (8 * j)
  p : s.gpr P = B + BitVec.ofNat 64 (128 * j)
  e : s.gpr E = B + BitVec.ofNat 64 2048
  mem : s.mem = sB.mem
  keep : ∀ r, r ∉ mulRegs → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem mulStep_ok {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {j k : Nat} (hj : j < 16) (hk : k < 8) {s : State} (hs : StepInv x h B sB j k s) :
    WP isa (.block (Impl.Gcm.RISCV64.mulStep k)) s (StepInv x h B sB j (k + 1)) := by
  have hF' : FrameOk B s := hF.of_wr hs.wr
  have a₁ : s.gpr P + BitVec.ofNat 64 (16 * k) = B + BitVec.ofNat 64 (16 * (8 * j + k)) := by
    rw [hs.p, ptr_off]; congr 2; omega
  have a₂ : s.gpr P + BitVec.ofNat 64 (16 * k + 8) = B + BitVec.ofNat 64 (16 * (8 * j + k) + 8) := by
    rw [hs.p, ptr_off]; congr 2; omega
  refine wp_sll (by omega) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => ?_
  refine wp_ld (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₁)
    (hF.al8 (by omega) (by omega)) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hF'.inR (by omega))
    fun s₃ u₃ => ?_
  refine wp_ld (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₂)
    (hF.al8 (by omega) (by omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hF'.inR (by omega)) fun s₄ u₄ => ?_
  refine wp_and fun s₅ u₅ => wp_and fun s₆ u₆ => wp_xor fun s₇ u₇ => wp_xor fun s₈ u₈ =>
    WP.block_nil ?_
  have mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, mem₃]
  have hm : s₂.gpr M = mask ((x <<< (8 * j)).getMsbD k) := by
    rw [u₂.gpr, u₁.gpr, mask_shl _ (by omega), ← hs.x, getMsbD_w2 _ _ (by omega)]
  have hm₄ : s₄.gpr M = mask (x.getMsbD (8 * j + k)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), hm, getMsbD_shl8]
  have hu0 : s₄.gpr U0 = hi (Proof.Gcm.RISCV64.vs h (8 * j + k)) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, hs.mem]; exact (ht _ (by omega)).1
  have hu1 : s₄.gpr U1 = lo (Proof.Gcm.RISCV64.vs h (8 * j + k)) := by
    rw [u₄.gpr, mem₃, hs.mem]; exact (ht _ (by omega)).2
  have g₄ : ∀ r, r ≠ M → r ≠ U0 → r ≠ U1 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h1]
  have z0 : s₈.gpr Z0 = s.gpr Z0 ^^^ (hi (vs h (8 * j + k)) &&& mask (x.getMsbD (8 * j + k))) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, hu0, hm₄, g₄ _ (by decide) (by decide) (by decide)]
  have z1 : s₈.gpr Z1 = s.gpr Z1 ^^^ (lo (vs h (8 * j + k)) &&& mask (x.getMsbD (8 * j + k))) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₅.other _ (by decide), hu1, hm₄, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄ _ (by decide) (by decide) (by decide)]
  have g₈ : ∀ r, r ≠ M → r ≠ U0 → r ≠ U1 → r ≠ Z0 → r ≠ Z1 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₈.other _ h5, u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, g₄ _ h1 h2 h3]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [z0, z1, acc_mask, hs.z, w2_hi_lo, ← Proof.Gcm.RISCV64.mulSteps_fst_succ]; rfl
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.x
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.p
  · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.e
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, mem₄]; exact hs.mem
  · simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈ _ hr.2.2.2.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.1 hr.2.1]; exact hs.keep r
      (by simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hs.rd
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hs.wr
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; exact hs.sp

theorem mulBody_ok {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {j : Nat} (hj : j < 16) {s : State} (hs : MulInv x h B sB j s) :
    WP isa (.block mulBody) s (MulInv x h B sB (j + 1)) := by
  rw [mulBody, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) (StepInv x h B sB j)
    (fun k s' hk hi => mulStep_ok hF ht hj hk hi) 8 (Nat.le_refl _) s
    ⟨by simpa using hs.z, hs.x, hs.p, hs.e, hs.mem, hs.keep, hs.rd, hs.wr, hs.sp⟩) fun s₁ h₁ => ?_
  refine wp_sll (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ => wp_or fun s₄ u₄ =>
    wp_sll (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ X0 → r ≠ X1 → r ≠ T → r ≠ P → s₆.gpr r = s₁.gpr r := fun r a b c d => by
    rw [u₆.other _ d, u₅.other _ b, u₄.other _ a, u₃.other _ c, u₂.other _ a]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), h₁.z]; rfl
  · rw [u₆.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide), u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w2_shl8, h₁.x, ← BitVec.shiftLeft_add,
      Nat.mul_succ]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), h₁.p, ptr_off]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₁.e
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact h₁.mem
  · simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g _ hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]
    exact h₁.keep r (by simp only [mulRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact h₁.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact h₁.wr
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact h₁.sp

theorem mul_loop {x h : Block} {B : Addr} {sB : State} (hF : FrameOk B sB) (ht : Tab h B sB.mem 128)
    {s : State} (hs : MulInv x h B sB 0 s) :
    WP isa (.loop (.block mulBody) (.ne P E)) s (MulInv x h B sB 16) := by
  refine WP.loop (M := isa) (fun n s' => ∃ j, n = 16 - j ∧ j < 16 ∧ MulInv x h B sB j s')
    (fun n s' ⟨j, hn, hj, hi⟩ => WP.mono (mulBody_ok hF ht hj hi) fun s'' hi' => ?_) 16 s
    ⟨0, rfl, by decide, hs⟩
  have hev : isa.eval (.ne P E) s'' = some (decide (j + 1 ≠ 16)) := by
    show some (s''.gpr P != s''.gpr E) = _
    rw [hi'.p, hi'.e, end_ne B hj]
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hev, decide_eq_true hl], 16 - (j + 1), by omega, j + 1, rfl, by omega, hi'⟩

end VG.Proof.Gcm.RISCV64
