module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Blake2.RISCV64.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Blake2.RISCV64.Round

/-!
# Streaming BLAKE2 on RISC-V: `init`

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE.Stream.Init`),
for the operand size `z` of the words (as `Proof/Blake2/RISCV64/Compress.lean`):
`initState` stores the initial hash value a byte at a time (`initState_ok`);
for a key, `keyBlock` zeroes the buffer (`zero_ok`) and copies the key into
it (`keyLoop_ok`). `init` is a leaf function writing only `a2`, `a3`,
`t1`–`t3` and `t6`.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream.Init

open VG VG.RISCV64 VG.Spec.Blake2
open VG.Impl.Blake2.RISCV64.Stream (N B initState)
open VG.Impl.Blake2.RISCV64 (ws movImm stLE T)
open VG.Proof.Blake2 (initRISCV64 bufOff repr_keyBlock stateAt_congr)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_li wp_addi wp_lbu wp_sb)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

/-! ## Sizes -/

section
variable (z : Size)

theorem bufOff_eq : bufOff z.bits = 8 * zB z := by cases z <;> rfl

theorem bb_eq : blockBytes z.bits = 16 * zB z := by cases z <;> rfl

theorem word_in {j : Nat} (hj : j < 8) : zB z * j + zB z ≤ bufOff z.bits := by
  rw [bufOff_eq]; have := zB_mul_le z hj; omega

theorem word_sep {j k : Nat} (h : j ≠ k) :
    zB z * j + zB z ≤ zB z * k ∨ zB z * k + zB z ≤ zB z * j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; exact zB_mul_le z h
  · right; exact zB_mul_le z h

theorem sizes : bufOff z.bits + blockBytes z.bits < 2048 ∧ bufOff z.bits ≤ 64 ∧ 0 < zB z ∧ zB z ≤ 8 ∧
    blockBytes z.bits < 2 ^ (z.bits - 8) := by
  cases z <;> decide

/-- A shift left keeps the low bits of the shifted low bits. -/
theorem setWidth_shl (x : BitVec 64) : (x <<< 8).setWidth z.bits = x.setWidth z.bits <<< 8 := by
  have := bits_le z
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 8 <;> simp [h, hi, show i - 8 < z.bits by omega, show i < 64 by omega]

/-- The low bits of a register holding `n`. -/
theorem ofNat_toNat_w (x : BitVec 64) : x.setWidth z.bits = BitVec.ofNat z.bits x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp

end

/-! ## The initial hash value -/

section
variable {z : Size} (P : Params z.bits)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec z.bits := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  movImm z.bits .t1 ((ivAt P (k + 1)).setWidth 64) ++ stLE z.bits .t1 .t2 .t3 .a0 (ws z.bits * (k + 1))

theorem initState_eq : initState P = (List.range 7).flatMap (ivStep P) ++
    (movImm z.bits .t1 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
    (([.shift .sll .d .t2 .a3 8, .logic .xor .t1 .t1 .t2, .logic .xor .t1 .t1 .a1] : List Instr) ++
      stLE z.bits .t1 .t2 .t3 .a0 0)) := by
  rw [initState, List.append_assoc, List.append_assoc]
  rfl

/-- The registers `initState` writes. -/
abbrev Clob (r : Reg) : Prop := r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ T

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, Clob r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .a0, bufOff z.bits⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .a0 + BitVec.ofNat 64 (zB z * (j + 1))) z.bits = ivAt P (j + 1)

variable {P}

theorem iv_step {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .a0, bufOff z.bits⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hs := sizes z
  have hin : (⟨s₀.gpr .a0, bufOff z.bits⟩ : Region).Contains
      (s₀.gpr .a0 + BitVec.ofNat 64 (zB z * (k + 1))) (zB z) :=
    Offset.contains_base _ (word_in z (by omega)) (by have := word_in z (j := k + 1) (by omega); omega)
  have ha0 : s.gpr .a0 = s₀.gpr .a0 := h.gpr _ (by decide)
  unfold ivStep
  rw [WP.block_append_iff]
  refine WP.mono (movImm_ok (by decide) _) fun s₁ ⟨hv₁, ho₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [ws_bits]
  refine WP.mono (stLE_ok (z := z) (v := .t1) (tmp := .t2) (tmp2 := .t3) (n := .a0) (by decide)
    (by decide) (by decide) (by decide) (by have := word_in z (j := k + 1) (by omega); omega)
    (by rw [ho₁ _ (by decide) (by decide), ha0, hwr₁, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩))
    fun s₂ ⟨ho₂, hm₂, hrd₂, hwr₂⟩ => ?_
  rw [ho₁ _ (by decide) (by decide), ha0, hv₁, hm₁] at hm₂
  refine ⟨fun r hr => by rw [ho₂ r hr.2.1 hr.2.2.1, ho₁ r hr.1 hr.2.2.2, h.gpr r hr],
    by rw [hrd₂, hrd₁, h.rd], by rw [hwr₂, hwr₁, h.wr], ?_, fun j hj => ?_⟩
  · rw [hm₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [bits_div]; exact hin)
  · rw [hm₂]
    by_cases e : j = k
    · subst e; exact readW_writeW_self z _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [bits_div]; exact word_sep z (fun h => e (by omega)))
        (by rw [bits_div]; have := word_in z (j := j + 1) (by omega); omega)
        (by rw [bits_div]; have := word_in z (j := k + 1) (by omega); omega))
        (by rw [bits_div]; omega)]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, Clob r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .a0, bufOff z.bits⟩] s₀.mem s.mem
  state : stateAt z.bits s.mem (s₀.gpr .a0) =
    Spec.Blake2.init P (s₀.gpr .a1).toNat (s₀.gpr .a3).toNat

theorem initState_ok {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .a0, bufOff z.bits⟩] a n → InRegions s₀.wr a n) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  have hs := sizes z
  have hle := bits_le z
  rw [initState_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (iv_step hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .a0, bufOff z.bits⟩ : Region).Contains (s₀.gpr .a0 + BitVec.ofNat 64 0) (zB z) :=
    Offset.contains_base _ (by have := word_in z (j := 0) (by omega); omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (movImm_ok (by decide) _) fun s₁ ⟨hv₁, ho₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine wp_sll (show 8 < 64 by decide) fun s₂ u₂ => Wp.wp_xor fun s₃ u₃ => Wp.wp_xor fun s₄ u₄ =>
    WP.block_nil ?_
  have g₄ : ∀ r, Clob r → s₄.gpr r = s₀.gpr r := fun r hr => by
    rw [u₄.other r hr.1, u₃.other r hr.1, u₂.other r hr.2.1, ho₁ r hr.1 hr.2.2.2, h₇.gpr r hr]
  -- The word stored.
  have hv : (s₄.gpr .t1).setWidth z.bits = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat z.bits (s₀.gpr .a3).toNat <<< 8) ^^^ BitVec.ofNat z.bits (s₀.gpr .a1).toNat := by
    rw [u₄.gpr, u₃.other .a1 (by decide), u₃.gpr, u₂.other .t1 (by decide), u₂.gpr,
      u₂.other .a1 (by decide), ho₁ .a1 (by decide) (by decide), ho₁ .a3 (by decide) (by decide),
      h₇.gpr .a1 (by decide), h₇.gpr .a3 (by decide), lo_xor, lo_xor, hv₁,
      setWidth_shl, ofNat_toNat_w, ofNat_toNat_w]
    rfl
  have ha0 : s₄.gpr .a0 = s₀.gpr .a0 := g₄ _ (by decide)
  refine WP.mono (stLE_ok (z := z) (v := .t1) (tmp := .t2) (tmp2 := .t3) (n := .a0) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [ha0, u₄.wr, u₃.wr, u₂.wr, hwr₁, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩))
    fun s₅ ⟨ho₅, hm₅, hrd₅, hwr₅⟩ => ?_
  have hm : s₅.mem = s₇.mem.writeW (s₀.gpr .a0 + BitVec.ofNat 64 0) ((s₄.gpr .t1).setWidth z.bits) := by
    rw [hm₅, ha0, u₄.mem, u₃.mem, u₂.mem, hm₁]
  refine ⟨fun r hr => by rw [ho₅ r hr.2.1 hr.2.2.1, g₄ r hr], by rw [hrd₅, u₄.rd, u₃.rd, u₂.rd, hrd₁, h₇.rd],
    by rw [hwr₅, u₄.wr, u₃.wr, u₂.wr, hwr₁, h₇.wr], ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ (by rw [bits_div]; exact hin)
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only [bits_div]
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, readW_writeW_self, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .a0 + BitVec.ofNat 64 (zB z * (j + 1))) (z.bits / 8)
          (s₀.gpr .a0 + BitVec.ofNat 64 0) (z.bits / 8) := by
        rw [bits_div]
        exact Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := word_in z (j := j + 1) hj; omega) (by have := word_in z (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep (by rw [bits_div]; omega), h₇.words j (by omega)]
      simp only [ivAt, hj, ↓reduceDIte]

end

/-! ## The key block -/

section
variable {z : Size}

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx : xs.length ≤ n) (hz : ∀ i < n, m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega), List.getElem_replicate]

/-- After zeroing `j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = writeBytes σ.mem (σ.gpr .a0 + BitVec.ofNat 64 (bufOff z.bits)) (List.replicate j 0)

theorem zero_ok {σ : State} (ht1 : σ.gpr .t1 = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .a0, bufOff z.bits + blockBytes z.bits⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (B z.bits)).flatMap fun j => [.store .b .t1 .a0 (N z.bits + j)])) σ
      (ZInv (z := z) σ (blockBytes z.bits)) := by
  have hs := sizes z
  refine wp_range_flatMap (M := isa) (ZInv (z := z) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  refine wp_sb (a := σ.gpr .a0 + BitVec.ofNat 64 (bufOff z.bits + j)) (by rw [N_eq]; omega)
    (by rw [h.gpr, N_eq]) ?_ fun s' g' => WP.block_nil ⟨g'.gpr.trans h.gpr, g'.rd.trans h.rd,
      g'.wr.trans h.wr, ?_⟩
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [g'.mem, h.mem, h.gpr, ht1, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate, Offset.add_ofNat_add_ofNat]
    rfl

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev kp : Addr := s₀.gpr .a2
abbrev kk : Nat := (s₀.gpr .a3).toNat
abbrev buf (w : Nat) : Addr := st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨kp s₀, kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (kp s₀) (kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ kk s₀
  a2 : s.gpr .a2 = kp s₀ + BitVec.ofNat 64 j
  t2 : s.gpr .t2 = buf s₀ z.bits + BitVec.ofNat 64 j
  a3 : s.gpr .a3 = BitVec.ofNat 64 (kk s₀ - j)
  other : ∀ r, Clob r → r ≠ .a2 → r ≠ .a3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes Z (buf s₀ z.bits) ((key s₀).take j)

theorem keyLoop_ok {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ z.bits]) (hd : (kR s₀).Disjoint (stR s₀ z.bits))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes z.bits) (hZ : Frame [stR s₀ z.bits] s₀.mem Z)
    (hσ : KInv (z := z) s₀ Z 0 σ) :
    WP isa (.loop (.block [.load .b .t1 .a2 0, .store .b .t1 .t2 0, .addi .a2 .a2 1, .addi .t2 .t2 1,
        .addi .a3 .a3 (-1)]) (.nonzero .a3)) σ
      (KInv (z := z) s₀ Z (kk s₀)) := by
  have hs := sizes z
  have hkl : kk s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = kk s₀ - j ∧ j < kk s₀ ∧ KInv (z := z) s₀ Z j s)
    ?_ (kk s₀) σ ⟨0, by omega, by omega, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [stR s₀ z.bits] s₀.mem (writeBytes Z (buf s₀ z.bits) ((key s₀).take j)) :=
      hZ.trans (writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega) (by omega)))
    exact hf.bytes (R := kR s₀) (by simpa using hd) (by simp; omega) hj
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (buf s₀ z.bits + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_lbu (a := kp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.a2]; simp) hin fun s₁ u₁ => ?_
  refine wp_sb (a := buf s₀ z.bits + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), h.t2]; simp)
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_addi (imm := 1) (by decide) fun s₄ u₄ =>
    wp_dec fun s₅ u₅ => WP.block_nil ?_
  have hr6 : s₅.gpr .a3 = BitVec.ofNat 64 (kk s₀ - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.a3,
      sub_ofNat (by omega), Nat.sub_sub]
  have hI : KInv (z := z) s₀ Z (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hr6, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.a2,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t2,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other r h3, u₄.other r h1.2.1, u₃.other r h2, g₂.gpr, u₁.other r h1.1, h.other r h1 h2 h3]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · have hj' : j < (key s₀).length := by simp [bytesAt]; omega
      have hl : (List.take j (key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = kk s₀
  · exact .inl ⟨by rw [nonzero_iff s₅ hr6 (by omega)]; simp; omega, hjk ▸ hI⟩
  · exact .inr ⟨by rw [nonzero_iff s₅ hr6 (by omega)]; simp; omega,
      kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

end

section
variable {z : Size} {P : Params z.bits}

theorem keyBlock_eq : Impl.Blake2.RISCV64.Stream.keyBlock (w := z.bits) =
    .seq (.block ((.li .t1 0 :: (List.range (B z.bits)).flatMap fun j =>
        ([.store .b .t1 .a0 (N z.bits + j)] : List Instr)) ++ ([.addi .t2 .a0 (N z.bits : Nat)] : List Instr)))
      (.loop (.block [.load .b .t1 .a2 0, .store .b .t1 .t2 0, .addi .a2 .a2 1, .addi .t2 .t2 1,
        .addi .a3 .a3 (-1)]) (.nonzero .a3)) := by
  rw [Impl.Blake2.RISCV64.Stream.keyBlock, List.map_eq_flatMap]

theorem keyBlock_ok {s₀ σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ z.bits]) (hd : (kR s₀).Disjoint (stR s₀ z.bits))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes z.bits) (hσ : StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.RISCV64.Stream.keyBlock (w := z.bits)) σ fun s =>
      (∀ r, Clob r → r ≠ .a2 → r ≠ .a3 → s.gpr r = s₀.gpr r) ∧
      Frame [⟨buf s₀ z.bits, blockBytes z.bits⟩] σ.mem s.mem ∧
      bytesAt s.mem (buf s₀ z.bits) (blockBytes z.bits) = key s₀ ++ List.replicate (blockBytes z.bits - kk s₀) 0 := by
  have hs := sizes z
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes z.bits → (stR s₀ z.bits).Contains (buf s₀ z.bits) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσ0 : σ.gpr .a0 = st s₀ := hσ.gpr _ (by decide)
  rw [keyBlock_eq]
  refine WP.seq (wp_li (imm := 0) (by decide) fun σ₁ u₁ => ?_)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (zero_ok (z := z) (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_) fun s₂ h₂ => ?_
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσ0]; exact fun _ _ h => h
  have hZ : s₂.mem = writeBytes σ.mem (buf s₀ z.bits) (List.replicate (blockBytes z.bits) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσ0, u₁.mem]
  have hfZ : Frame [stR s₀ z.bits] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ z.bits, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine wp_addi (by rw [N_eq]; omega) fun s₃ u₃ => WP.block_nil ?_
  refine WP.mono (keyLoop_ok hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, ?_, ?_, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide)]; simp
  · rw [u₃.gpr, h₂.gpr, u₁.other _ (by decide), hσ0, N_eq]; simp
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3
    rw [u₃.other r h1.2.1, h₂.gpr, u₁.other r h1.1, hσ.gpr r h1]
  · rw [u₃.mem, List.take_zero, writeBytes_nil]
  have hm : s.mem = writeBytes (writeBytes σ.mem (buf s₀ z.bits) (List.replicate (blockBytes z.bits) 0))
      (buf s₀ z.bits) (key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, ?_, ?_⟩
  · rw [hm]
    exact (writeBytes_frame _ _ _ (contains_prefix _ (by simp))).trans
      (writeBytes_frame _ _ _ (contains_prefix _ (by omega)))
  · rw [hm, bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [writeBytes_at _ _ _ (by omega)]
    simp [hi]

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {z : Size} {P : Params z.bits} {s₀ : State} (hP : Ok P) (hp : (initRISCV64 P).pre s₀) :
    WP isa (Impl.Blake2.RISCV64.Stream.init P) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ (initRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, -, -, hkk⟩ := hp
  have hs := sizes z
  have hkb : kk s₀ ≤ blockBytes z.bits := Nat.le_trans hkk hP.max
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hcs : ∀ r ∈ .ra :: preserved, Clob r ∧ r ≠ .a2 ∧ r ≠ .a3 := by decide
  unfold Impl.Blake2.RISCV64.Stream.init
  refine WP.seq (WP.mono (initState_ok (P := P) (fun a n h => ?_)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  have ha3 : σ.gpr .a3 = BitVec.ofNat 64 (kk s₀) := by
    rw [hσ.gpr _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.ite _ (zero_iff σ ha3 (s₀.gpr .a3).isLt) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun r hr => hσ.gpr r (hcs r (.tail _ hr)).1, hσ.gpr _ (hcs _ (.head _)).1, ?_⟩
    exact repr_keyBlock P hP.pos (hxs ▸ hkb) hσ.state fun h => absurd (hxs ▸ hb) h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (keyBlock_ok hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hf, hb'⟩ => ?_
    refine ⟨fun r hr => hg r (hcs r (.tail _ hr)).1 (hcs r (.tail _ hr)).2.1 (hcs r (.tail _ hr)).2.2,
      hg _ (hcs _ (.head _)).1 (hcs _ (.head _)).2.1 (hcs _ (.head _)).2.2, ?_⟩
    refine repr_keyBlock P hP.pos (hxs ▸ hkb) ?_ fun _ => by rw [hxs]; exact hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨st s₀, bufOff z.bits⟩)
      (by simpa using Offset.base_disjoint (st s₀) (Nat.le_refl (bufOff z.bits)) (n := blockBytes z.bits) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.RISCV64.Stream.Init
