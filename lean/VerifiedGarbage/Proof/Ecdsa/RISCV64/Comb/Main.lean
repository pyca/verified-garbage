module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulFn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-!
# The comb on RISC-V: the body

The pieces of `vg_p256_mul_g`'s body and their proofs, in order:

* The scan of a table's entries: a selection `pick a b m` by a mask `maskOf c` (all ones or zero) leaves `b`
  in `a` if `c`, else `a` (`wp_pick`). A tree of them by the masks of the bits
  of a number `t` (`tree_ok`) leaves the quadword of the entry whose number is
  `t`'s low bits, without a secret address; `scanWord_ok` puts the two halves
  of a table's 64 entries together, by bit 5.

* The window, the digit and the masks: `window` leaves `k_j`, the bits `7j … 7j + 6` of `k` (`combWin 7 k j`), in
  `t2` (`window_ok`): bit `i` of the funnel shift of the two words holding
  them is bit `r + i` of the first, or `r + i - 64` of the second
  (`funnel_bit`), for `r = 7j mod 64`. `digit` and the masks leave the masks
  of the digit's sign and of its magnitude being zero in `PT`'s slot, and in
  `a1`–`a6` the masks of the bits of the entry's number (`digit_ok`,
  `masks_ok`).

* The entry: the table at `T` (`TabOk`: its words, its alignment, readable, apart from
  the working space) is read a row at a time: `scans_ok` leaves in `D` the
  `2 n` quadwords of the entry of the row whose number is the low six bits of
  `t`, from the table's words as they were.

* A step: `step` takes `R` from `[combEW (j + 1)]G` to `[combEW j]G`
  (`Proof/Weierstrass/CombW.lean`): the entry it selects, with `y` negated for
  a negative digit, represents the digit's signed point (`entry_rep`), and the
  complete addition gives the sum (`Rep.add`, `combW_add`).

* The body: `body` copies `k` to `KC` with a zero word after it, sets `R` to the start
  `[64 Σ_j 2^(7j)]G` (affine, `Z = 1`), and runs the 37 steps (`step_ok`),
  which leave `R` representing `[combEW 0]G = [k]G` (`body_ok`).

-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Comb

/-! ## The scan of a table's entries -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sd_ws)
open VG.Impl.Ecdsa.RISCV64 (DX)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem upd_keep {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_sra {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

end

/-- A selection by a mask. -/
theorem pick_mask (a b : BitVec 64) (c : Bool) : a ^^^ ((b ^^^ a) &&& maskOf c) = if c then b else a := by
  cases c
  · show a ^^^ ((b ^^^ a) &&& 0#64) = a
    rw [BitVec.and_zero, BitVec.xor_zero]
  · simp only [maskOf, ↓reduceIte, BitVec.and_allOnes]
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `pick a b m`: `a` := `b` if the mask `m` is all ones, else `a`. -/
theorem wp_pick {is : List Instr} {s : State} {Q : State → Prop} {a b m : Reg} (hab : a ≠ b)
    (hbm : b ≠ m) {c : Bool} (hm : s.gpr m = maskOf c)
    (k : ∀ s', s'.gpr a = (if c then s.gpr b else s.gpr a) → Keep [b, a] s s' →
      s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (pick a b m ++ is)) s Q := by
  unfold pick
  simp only [List.cons_append, List.nil_append]
  refine wp_xor fun s₁ u₁ => wp_and fun s₂ u₂ => wp_xor fun s₃ u₃ => k s₃ ?_ ?_ ?_
  · rw [u₃.gpr, u₂.gpr, u₂.other _ hab, u₁.other _ hab, u₁.gpr, u₁.other _ hbm.symm, hm, pick_mask]
  · exact ((upd_keep u₁ |>.trans (upd_keep u₂)).trans (upd_keep u₃)).mono (by simp)
  · rw [u₃.mem, u₂.mem, u₁.mem]

/-- `n % 2 ^ (L + 1)` from `n % 2 ^ L` and bit `L`. -/
theorem mod_two_pow_succ' (n L : Nat) :
    n % 2 ^ (L + 1) = (if n.testBit L then 2 ^ L else 0) + n % 2 ^ L := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq, Nat.add_comm]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ L) with h | h <;> simp [h]

/-- The selection among the `2 ^ L` quadwords at `base + o + stride e` by
the masks of the bits below `L` of `t`: the first register holds the
quadword at `e = t % 2 ^ L`. -/
theorem tree_ok (base : Reg) (stride : Nat) (t : Nat) (L : Nat) :
    ∀ (o : Nat) (a : Reg) (rs : List Reg) (s : State),
    L ≤ rs.length → (a :: rs).Nodup → (∀ r ∈ a :: rs, r ≠ base ∧ ∀ c < L, r ≠ maskReg c) →
    (∀ c < L, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    o + stride * (2 ^ L - 1) < 2048 →
    (∀ e < 2 ^ L, (s.gpr base + BitVec.ofNat 64 (o + stride * e)).toNat % 8 = 0 ∧
      InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (o + stride * e)) 8) →
    WP isa (.block (tree base stride L o (a :: rs))) s fun s' =>
      s'.gpr a = s.mem.readW (s.gpr base + BitVec.ofNat 64 (o + stride * (t % 2 ^ L))) 64 ∧
      Keep (a :: rs) s s' ∧ s'.mem = s.mem := by
  induction L with
  | zero =>
    intro o a rs s _ _ hne _ ho hal
    have h0 := hal 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    unfold tree
    refine wp_ld (by omega) rfl h0.1 h0.2 fun s' u => WP.block_nil ⟨?_, (upd_keep u).mono (by simp), u.mem⟩
    rw [u.gpr, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  | succ L ih =>
    intro o a rs s hlen hnd hne hm ho hal
    obtain ⟨b, rs, rfl⟩ : ∃ b rs', rs = b :: rs' := by
      cases rs with
      | nil => simp at hlen
      | cons b rs' => exact ⟨b, rs', rfl⟩
    simp only [List.length_cons] at hlen
    have hab : a ≠ b := fun e => by subst e; simp at hnd
    have hb := hne b (by simp)
    have hp : stride * 2 ^ L ≤ stride * (2 ^ (L + 1) - 1) := by
      apply Nat.mul_le_mul_left; rw [Nat.pow_succ]; have := Nat.two_pow_pos L; omega
    have hp' : stride * (2 ^ L - 1) ≤ stride * 2 ^ L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    unfold tree
    rw [WP.block_append_iff, WP.block_append_iff]
    -- The low half, into `a`.
    refine WP.mono (ih o a (b :: rs) s (by simp; omega) hnd
      (fun r hr => ⟨(hne r hr).1, fun c hc => (hne r hr).2 c (by omega)⟩)
      (fun c hc => hm c (by omega)) (by omega)
      (fun e he => hal e (by rw [Nat.pow_succ]; omega))) fun s₁ ⟨ta, tk, tm⟩ => ?_
    have tep : s₁.gpr base = s.gpr base := tk.gpr (by simpa using fun h => (hne base h).1 rfl)
    have tmk (c : Nat) (hc : c < L + 1) : s₁.gpr (maskReg c) = s.gpr (maskReg c) :=
      tk.gpr fun h => (hne _ h).2 c hc rfl
    -- The high half, into `b`.
    have hp2 : stride * 2 ^ L + stride * (2 ^ L - 1) = stride * (2 ^ (L + 1) - 1) := by
      rw [← Nat.mul_add, Nat.pow_succ]; congr 1; have := Nat.two_pow_pos L; omega
    refine WP.mono (ih (o + stride * 2 ^ L) b rs s₁ (by omega) (List.nodup_cons.mp hnd).2
      (fun r hr => ⟨(hne r (by simp [hr])).1, fun c hc => (hne r (by simp [hr])).2 c (by omega)⟩)
      (fun c hc => by rw [tmk c (by omega)]; exact hm c (by omega)) (by omega)
      (fun e he => by
        rw [tep, tk.2.1, tk.2.2, show o + stride * 2 ^ L + stride * e = o + stride * (2 ^ L + e) by
          rw [Nat.mul_add, Nat.add_assoc]]
        exact hal _ (by rw [Nat.pow_succ]; omega))) fun s₂ ⟨ub, uk, um⟩ => ?_
    have ua : s₂.gpr a = s₁.gpr a := uk.gpr (List.nodup_cons.mp hnd).1
    have umk : s₂.gpr (maskReg L) = maskOf (t.testBit L) := by
      rw [uk.gpr fun h => (hne _ (by simp [h])).2 L (by omega) rfl, tmk L (by omega), hm L (by omega)]
    have hbm : b ≠ maskReg L := hb.2 L (by omega)
    -- The selection by bit `L`.
    refine wp_pick hab hbm umk fun s₃ va vk vm => WP.block_nil ⟨?_, ?_, by rw [vm, um, tm]⟩
    · rw [va, ub, ua, ta, tep, tm, mod_two_pow_succ']
      split
      · rw [Nat.mul_add, Nat.add_assoc]
      · rw [Nat.zero_add]
    · exact ((tk.trans uk).trans vk).mono (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h | h) | h | h) | h | h <;> simp only [h, true_or, or_true])


/-- The address of quadword `q` of entry `e` of the row at `T`. -/
abbrev entAddr (T : Addr) (q e : Nat) : Addr := T + BitVec.ofNat 64 (8 * q + 64 * e)

/-- What the scan needs of the row at `a0` (`a7 = a0 + 2048`): each
quadword `q` of its 64 entries aligned and readable. -/
structure RowOk (s : State) (q : Nat) : Prop where
  a7 : s.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 2048
  ent : ∀ e < 64, (entAddr (s.gpr .a0) q e).toNat % 8 = 0 ∧ InRegions (s.rd ++ s.wr) (entAddr (s.gpr .a0) q e) 8

/-- Quadword `q` of entry `t % 64` of the row at `a0`, by the masks of
`t`'s bits, to `D`'s word `q`. -/
theorem scanWord_ok {s : State} {base : Addr} (hw : WsReg s base) {q t : Nat} (hq : q < 8)
    (hm : ∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) (hr : RowOk s q) :
    WP isa (.block (Impl.Ecdsa.RISCV64.Comb.Cfg.scanWord Impl.Ecdsa.RISCV64.p256 q)) s fun s' =>
      s'.mem = s.mem.writeW (off base (Impl.Ecdsa.RISCV64.p256.sl DX + 8 * q))
        (s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Keep treeRegs s s' := by
  have heb : Impl.Ecdsa.RISCV64.Comb.Cfg.eb Impl.Ecdsa.RISCV64.p256 = 64 := rfl
  unfold Impl.Ecdsa.RISCV64.Comb.Cfg.scanWord
  rw [heb, List.append_assoc, List.append_assoc]
  have hne : ∀ (b : Reg), b = .a0 ∨ b = .a7 → ∀ r ∈ treeRegs, r ≠ b ∧ ∀ c < 5, r ≠ maskReg c := by
    intro b hb r hr
    simp only [treeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨?_, fun c hc => ?_⟩
    · rcases hb with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- The low half.
  refine WP.block_append (WP.mono (tree_ok .a0 64 t 5 (8 * q) .t0 [.t1, .t2, .t3, .t4, .t5, .t6] s (by decide)
    (by decide) (hne .a0 (.inl rfl)) (fun c hc => hm c (by omega)) (by omega)
    (fun e he => by
      have := hr.ent e (by omega)
      exact this)) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (by decide)
  have e7 : s₁.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 2048 := by rw [k₁.gpr (by decide), hr.a7]
  have hhi : ∀ e, s₁.gpr .a7 + BitVec.ofNat 64 (8 * q + 64 * e) = entAddr (s.gpr .a0) q (32 + e) := by
    intro e
    rw [e7, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
    omega
  have hmk : ∀ c < 5, s₁.gpr (maskReg c) = s.gpr (maskReg c) := fun c hc => k₁.gpr (by
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide)
  -- The high half.
  refine WP.block_append (WP.mono (tree_ok .a7 64 t 5 (8 * q) .t1 [.t2, .t3, .t4, .t5, .t6] s₁ (by decide)
    (by decide) (fun r hr => hne .a7 (.inr rfl) r (by simp only [treeRegs]; exact List.mem_cons_of_mem _ hr))
    (fun c hc => by rw [hmk c hc]; exact hm c (by omega)) (by omega)
    (fun e he => by
      rw [hhi, k₁.2.1, k₁.2.2]
      exact hr.ent (32 + e) (by omega))) fun s₂ ⟨v₂, k₂, m₂⟩ => ?_)
  have a6 : s₂.gpr .a6 = maskOf (t.testBit 5) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact hm 5 (by decide)
  have t0₂ : s₂.gpr .t0 = s₁.gpr .t0 := k₂.gpr (by decide)
  refine WP.block_append (wp_pick (by decide) (by decide) a6 fun s₃ v₃ k₃ m₃ => WP.block_nil ?_)
  have hw₃ : WsReg s₃ base := ⟨by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hw.s0],
    by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
  have hDX : Impl.Ecdsa.RISCV64.p256.sl DX = 608 := rfl
  refine sd_ws hw₃ (by omega) (by omega) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₄.mem, m₃, m₂, m₁, v₃, v₂, t0₂, v₁, m₁, mod_two_pow_succ' t 5]
    split
    · rw [hhi]
    · rw [Nat.zero_add]
  · exact ⟨fun r hr => by
      rw [u₄.gpr, k₃.gpr (fun h => hr (by simp only [List.mem_cons] at h ⊢; simp only [treeRegs]; rcases h with
        rfl | rfl | h <;> simp_all)), k₂.gpr (fun h => hr (by simp only [treeRegs]; exact List.mem_cons_of_mem _ h)),
        k₁.gpr (by simpa only [treeRegs] using hr)],
      by rw [u₄.rd, k₃.2.1, k₂.2.1, k₁.2.1], by rw [u₄.wr, k₃.2.2, k₂.2.2, k₁.2.2]⟩

end

/-! ## The window, the digit and the masks -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sd_ws ld_ws testBit_wordsVal wp_srlReg)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Weierstrass (combWin magH)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_sllReg {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n <<< ((s.gpr m).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftReg .sll .d d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write _ _ _))

theorem wp_xori {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

end

/-- A bit of the funnel shift of `a` and `b` by `r`. -/
theorem funnel_bit (a b : BitVec 64) {r i : Nat} (hr : r < 64) (hi : i < 7) :
    ((a >>> r) ||| ((b <<< 1) <<< (63 - r))).getLsbD i =
      if r + i < 64 then a.getLsbD (r + i) else b.getLsbD (r + i - 64) := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  have i64 : i < 64 := by omega
  by_cases h : r + i < 64
  · have e1 : i - (63 - r) < 1 := by omega
    have e0 : ¬ 64 ≤ i + r := by omega
    simp [e0, e1, Nat.add_comm r i]
  · have e2 : ¬ i - (63 - r) < 1 := by omega
    have e3 : ¬ i < 63 - r := by omega
    have e5 : i - (63 - r) < 64 := by omega
    simp [h, e2, e3, e5, i64, BitVec.getLsbD_of_ge a (r + i) (by omega),
      show i - (63 - r) - 1 = r + i - 64 by omega]

/-- The shift of the high word. -/
theorem shamt_eq : ∀ j < 37, (BitVec.ofNat 64 (7 * j) ^^^ BitVec.ofInt 64 63).toNat % 64 = 63 - 7 * j % 64 := by
  decide

/-- `8 j - j`. -/
theorem seven_mul {j : Nat} (hj : j < 37) :
    BitVec.ofNat 64 j <<< 3 - BitVec.ofNat 64 j = BitVec.ofNat 64 (7 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := hj
  omega

/-- The slot of the copy of `k`. -/
theorem kc_eq : p256.sl KC = 1536 := rfl

/-- The window's value from the bits of the five words at `KC`. -/
theorem window_bits {K : Nat} {a b : BitVec 64} {j : Nat}
    (hbit : ∀ i < 7, K.testBit (7 * j + i) =
      if 7 * j % 64 + i < 64 then a.getLsbD (7 * j % 64 + i) else b.getLsbD (7 * j % 64 + i - 64)) :
    ((a >>> (7 * j % 64)) ||| ((b <<< 1) <<< (63 - 7 * j % 64))) &&& BitVec.ofInt 64 127 =
      BitVec.ofNat 64 (combWin 7 K j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, combWin, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    show (BitVec.ofInt 64 127) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h7 : i < 7
  · rw [funnel_bit a b (by omega) h7, ← hbit i h7, Nat.add_comm i]
    simp [h7, hi]
  · simp [h7]

/-- `t2 = k_j`, for `j` in `s1`, from the copy of `k` at `KC` and its zero word. -/
theorem window_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 37)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (hz : word s.mem base (p256.sl KC + 32) = 0) :
    WP isa (.block (Cfg.window p256)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 (combWin 7 (wordsVal s.mem base (p256.sl KC) 4) j) ∧
        Rest [.t0, .t1, .t2, .t3, .t4] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : 7 * j / 64 ≤ 3 := by omega
  rw [Cfg.window, kc_eq] at *
  refine wp_sll (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => ?_
  have e₂ : s₂.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .s1 (by decide), h1, seven_mul hj]
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have e₅' : s₅.gpr .t1 = base + BitVec.ofNat 64 (8 * (7 * j / 64)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other .s0 (by decide), u₃.gpr, u₃.other .s0 (by decide),
      u₂.other .s0 (by decide), u₁.other .s0 (by decide), hw.s0, e₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : 7 * j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 7 * j / 64 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (7 * j / 64) < 18446744073709551616)]
    omega
  have e₅ : ∀ d, s₅.gpr .t1 + BitVec.ofNat 64 d = off base (d + 8 * (7 * j / 64)) := by
    intro d
    rw [e₅', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₅ : Rest [.t0, .t1] s s₅ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have inr : ∀ d, d + 8 ≤ 8192 → InRegions (s₅.rd ++ s₅.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ (r₅.wr ▸ hw.wr), Offset.contains_base base hd (by omega)⟩
  have alg : ∀ d, d % 8 = 0 → d < 8192 → (off base d).toNat % 8 = 0 := fun d h8 hd => by
    simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine wp_ld (by omega) (e₅ 1536) (alg _ (by omega) (by omega)) (inr _ (by omega)) fun s₆ u₆ => ?_
  refine wp_ld (by omega) (by rw [u₆.other .t1 (by decide)]; exact e₅ 1544) (alg _ (by omega) (by omega))
    (by rw [u₆.rd, u₆.wr]; exact inr _ (by omega)) fun s₇ u₇ => ?_
  refine wp_srlReg fun s₈ u₈ => wp_xori (by decide) fun s₉ u₉ => wp_sll (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_sllReg fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => wp_andi (by decide) fun s₁₃ u₁₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t0₈ : s₈.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
      rw [u₈.other .t0 (by decide), u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide),
        u₄.other .t0 (by decide), u₃.other .t0 (by decide)]
      exact e₂
    have sh : (s₉.gpr .t4).toNat % 64 = 63 - 7 * j % 64 := by
      rw [u₉.gpr, t0₈]; exact shamt_eq j hj
    have sh7 : (s₇.gpr .t0).toNat % 64 = 7 * j % 64 := by
      rw [u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide), u₄.other .t0 (by decide),
        u₃.other .t0 (by decide), e₂, BitVec.toNat_ofNat]
      omega
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₁.other .t2 (by decide), u₁₀.gpr, u₁₀.other .t2 (by decide),
      u₁₀.other .t4 (by decide), sh, u₉.other .t2 (by decide), u₉.other .t3 (by decide), u₈.gpr,
      u₈.other .t3 (by decide), sh7, u₇.gpr, u₇.other .t2 (by decide), u₆.gpr, u₆.mem, m₅]
    refine window_bits fun i hi => ?_
    have e5 : wordsVal s.mem base 1536 5 = wordsVal s.mem base 1536 4 := by
      rw [wordsVal_succ_top s.mem base 1536 4, show 1536 + 8 * 4 = 1536 + 32 from rfl, hz]; simp
    rw [← e5, ← testBit_wordsVal s.mem base 5 1536 (7 * j + i) (by omega)]
    by_cases h : 7 * j % 64 + i < 64
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 by omega, show (7 * j + i) % 64 = 7 * j % 64 + i by omega,
        ← BitVec.testBit_toNat, show 1536 + 8 * (7 * j / 64) = 1536 + 8 * (7 * j / 64) from rfl]
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 + 1 by omega,
        show (7 * j + i) % 64 = 7 * j % 64 + i - 64 by omega, ← BitVec.testBit_toNat,
        show 1536 + 8 * (7 * j / 64 + 1) = 1544 + 8 * (7 * j / 64) by omega]
  · exact (r₅.mono (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
      ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
        ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans (u₁₃.rest (by decide)))))))))
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]


/-! ## The digit and the masks -/

/-- From the window `v`: the digit's sign's mask, the mask of its magnitude
being zero, and the entry's number, its magnitude less one. -/
theorem digit_facts : ∀ v < 128,
    (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63 = maskOf (decide (v < 64)) ∧
    ((((BitVec.ofNat 64 v - BitVec.ofNat 64 64) ^^^ (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) -
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) - BitVec.ofNat 64 1).sshiftRight 63 =
      maskOf (decide (magH 64 v = 0)) ∧
    (magH 64 v ≠ 0 → ((((BitVec.ofNat 64 v - BitVec.ofNat 64 64) ^^^
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) -
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) - BitVec.ofNat 64 1).toNat = magH 64 v - 1) := by
  decide

/-- The mask of bit `c` of `x`: bit `c` shifted to the top, arithmetically down. -/
theorem mask_bit (x : BitVec 64) {c : Nat} (hc : c < 64) :
    (x <<< (63 - c)).sshiftRight 63 = maskOf (x.getLsbD c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hm : (x <<< (63 - c)).msb = x.getLsbD c := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
    simp only [show 64 - 1 = 63 from rfl, show 63 - (63 - c) = c by omega]
    simp
  have hl : (x <<< (63 - c)).getLsbD 63 = x.getLsbD c := by
    rw [← hm, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0; simp only [Nat.add_zero, show (63 : Nat) < 64 from by omega, ↓reduceIte, hl]
    cases x.getLsbD c <;> simp [maskOf]
  · simp only [show ¬ 63 + i < 64 by omega, ↓reduceIte, hm]
    cases x.getLsbD c
    · simp only [maskOf, Bool.false_eq_true, ↓reduceIte, Bool.and_false]
      exact (BitVec.getLsbD_zero (w := 64) (i := i)).symm
    · simp only [maskOf, ↓reduceIte, BitVec.getLsbD_allOnes, Bool.and_true]
      simp only [hi, decide_true, show ¬ 64 ≤ i by omega, decide_false, Bool.not_false]

theorem pt_eq : p256.sl PT = 1024 := rfl

/-- The digit of the window `v` in `t2`: the masks to `PT`'s slot, the
entry's number in `t2`. -/
theorem digit_ok {s : State} {base : Addr} (hw : WsReg s base) {v : Nat} (hv : v < 128)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 v) :
    WP isa (.block (Cfg.digit p256)) s fun s' =>
      (magH 64 v ≠ 0 → (s'.gpr .t2).toNat = magH 64 v - 1) ∧
      word s'.mem base (p256.sl PT) = maskOf (decide (v < 64)) ∧
      word s'.mem base (p256.sl PT + 8) = maskOf (decide (magH 64 v = 0)) ∧
      Outside base (p256.sl PT) 16 s.mem s'.mem ∧ Rest [.t2, .t3, .t4] s s' := by
  have hn := hw.nowrap
  obtain ⟨f1, f2, f3⟩ := digit_facts v hv
  rw [Cfg.digit, pt_eq]
  refine wp_subi (imm := 64) (by decide) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_sub fun s₄ u₄ => wp_subi (imm := 1) (by decide) fun s₅ u₅ => wp_sra (by decide) fun s₆ u₆ => ?_
  have r₆ : Rest [.t2, .t3, .t4] s s₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  have e3 : s₆.gpr .t3 = (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63 := by
    rw [u₆.other .t3 (by decide), u₅.other .t3 (by decide), u₄.other .t3 (by decide), u₃.other .t3 (by decide),
      u₂.gpr, u₁.gpr, h2]
  have e5 : s₅.gpr .t2 = (((BitVec.ofNat 64 v - BitVec.ofNat 64 64) ^^^
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) -
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) - BitVec.ofNat 64 1 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .t3 (by decide), u₂.gpr, u₂.other .t2 (by decide), u₁.gpr, h2]
  have e2 : s₆.gpr .t2 = s₅.gpr .t2 := u₆.other .t2 (by decide)
  have e4 : s₆.gpr .t4 = maskOf (decide (magH 64 v = 0)) := by rw [u₆.gpr, e5]; exact f2
  have hw₆ : WsReg s₆ base := hw.of_rest r₆
  refine sd_ws hw₆ (by decide) (by decide) fun s₇ u₇ => ?_
  refine sd_ws (hw₆.of_rest (u₇.rest [])) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hz; rw [u₈.gpr, u₇.gpr, e2, e5]; exact f3 hz
  · rw [u₈.mem, (writeW_outside s₇.mem base (d := 1032) (s₇.gpr .t4) (by omega)).word (d := 1024) (by omega)
      (by omega), u₇.mem, word_writeW_self, e3, f1]
  · rw [u₈.mem, word_writeW_self, u₇.gpr, e4]
  · intro x hx
    rw [u₈.mem, writeW_outside s₇.mem base (d := 1032) (s₇.gpr .t4) (by omega) x (by omega), u₇.mem,
      writeW_outside s₆.mem base (d := 1024) (s₆.gpr .t3) (by omega) x (by omega)]
    rw [show s₆.mem = s.mem by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
  · exact r₆.trans ((u₇.rest _).trans (u₈.rest _))

/-- The mask of bit `b` of `t2`. -/
theorem maskOfBit_ok {is : List Instr} {s : State} {Q : State → Prop} {b : Nat} (hb : b < 6)
    (k : ∀ s', s'.gpr (maskReg b) = maskOf ((s.gpr .t2).getLsbD b) → Rest [maskReg b] s s' → s'.mem = s.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block (Cfg.maskOfBit b ++ is)) s Q := by
  have hne : maskReg b ≠ .t2 := by
    have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [Cfg.maskOfBit, List.cons_append, List.cons_append, List.nil_append]
  refine wp_sll (by omega) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => k s₂ ?_ ?_ ?_
  · rw [u₂.gpr, u₁.gpr]; exact mask_bit _ (by omega)
  · exact (u₁.rest (by simp)).trans (u₂.rest (by simp))
  · rw [u₂.mem, u₁.mem]

/-- The masks of the bits `0 … 5` of `t2` into `a1`–`a6`. -/
theorem masks_ok {s : State} :
    WP isa (.block ((List.range 6).flatMap Cfg.maskOfBit)) s fun s' =>
      (∀ c < 6, s'.gpr (maskReg c) = maskOf ((s.gpr .t2).getLsbD c)) ∧
        Rest [.a1, .a2, .a3, .a4, .a5, .a6] s s' ∧ s'.mem = s.mem := by
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil]
  refine maskOfBit_ok (b := 0) (by decide) fun s₁ v₁ r₁ m₁ => ?_
  refine maskOfBit_ok (b := 1) (by decide) fun s₂ v₂ r₂ m₂ => ?_
  refine maskOfBit_ok (b := 2) (by decide) fun s₃ v₃ r₃ m₃ => ?_
  refine maskOfBit_ok (b := 3) (by decide) fun s₄ v₄ r₄ m₄ => ?_
  refine maskOfBit_ok (b := 4) (by decide) fun s₅ v₅ r₅ m₅ => ?_
  refine maskOfBit_ok (b := 5) (by decide) fun s₆ v₆ r₆ m₆ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [maskReg] at v₁ v₂ v₃ v₄ v₅ v₆ r₁ r₂ r₃ r₄ r₅ r₆
    have t1 : s₁.gpr .t2 = s.gpr .t2 := r₁.gpr .t2 (by decide)
    have t2 : s₂.gpr .t2 = s.gpr .t2 := (r₂.gpr .t2 (by decide)).trans t1
    have t3 : s₃.gpr .t2 = s.gpr .t2 := (r₃.gpr .t2 (by decide)).trans t2
    have t4 : s₄.gpr .t2 = s.gpr .t2 := (r₄.gpr .t2 (by decide)).trans t3
    have t5 : s₅.gpr .t2 = s.gpr .t2 := (r₅.gpr .t2 (by decide)).trans t4
    intro c hc
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [maskReg]
    · rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), r₃.gpr _ (by decide),
        r₂.gpr _ (by decide), v₁]
    · rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), r₃.gpr _ (by decide), v₂, t1]
    · rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), v₃, t2]
    · rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), v₄, t3]
    · rw [r₆.gpr _ (by decide), v₅, t4]
    · rw [v₆, t5]
  · exact (r₁.mono (by simp [maskReg])).trans ((r₂.mono (by simp [maskReg])).trans ((r₃.mono (by simp [maskReg])).trans
      ((r₄.mono (by simp [maskReg])).trans ((r₅.mono (by simp [maskReg])).trans (r₆.mono (by simp [maskReg]))))))
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]

/-- The row: `a0 = s4 + 4096 j`, `a7 = a0 + 2048`. -/
theorem row_ok {s : State} {j : Nat} (hj : j < 37) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block Cfg.row) s fun s' =>
      s'.gpr .a0 = s.gpr .s4 + BitVec.ofNat 64 (4096 * j) ∧
      s'.gpr .a7 = s'.gpr .a0 + BitVec.ofNat 64 2048 ∧ Rest [.t0, .a0, .a7] s s' ∧ s'.mem = s.mem := by
  rw [Cfg.row]
  refine wp_sll (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addi (imm := 2047) (by decide) fun s₃ u₃ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₄.other .a0 (by decide), u₃.other .a0 (by decide), u₂.gpr, u₁.gpr, u₁.other .s4 (by decide), h1]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := hj
    omega
  · rw [u₄.gpr, u₃.gpr, u₄.other .a0 (by decide), u₃.other .a0 (by decide), BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · exact (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      (u₄.rest (by decide))))
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end

/-! ## The entry -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg copy_ok sel_ok ld_ws)
open VG.Proof.Weierstrass (Unch combWin magH)
open VG.Proof.X25519.RISCV64 (Rest)

/-- The words of P-256's tables. -/
abbrev tabWords : List (BitVec 64) := Impl.Weierstrass.tcombWords 4 (2 ^ 256) Spec.P256.curve.p Impl.P256.p256Comb7

/-- What the comb needs of the table at `T`, for the working space at `base`. -/
structure TabOk (s : State) (base T : Addr) : Prop where
  held : ∀ i < 18944, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = tabWords.getD i 0
  al : T.toNat % 64 = 0
  rd : (⟨T, 151552⟩ : Region) ∈ s.rd
  fit : T.toNat + 151552 ≤ 2 ^ 64
  far : ∀ d < 151552, 8192 ≤ ofs base (T + BitVec.ofNat 64 d)

/-- Memory changed only in the working space keeps the table. -/
theorem TabOk.of_mem {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabOk s' base T where
  held i hi := by
    rw [← h.held i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega)
  al := h.al
  rd := hrd ▸ h.rd
  fit := h.fit
  far := h.far

theorem TabOk.of_outside {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd) {o n : Nat}
    (hon : o + n ≤ 8192) (ho : Outside base o n s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => ho x (.inr (by omega))

/-- The address of quadword `q` of entry `e` of row `j`. -/
theorem entAddr_row (T : Addr) (j q e : Nat) :
    entAddr (T + BitVec.ofNat 64 (4096 * j)) q e = T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 4)) + e * (2 * 4) + q)) := by
  rw [entAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega

/-- What the scan of row `j` needs. -/
theorem rowOk_of_tab {s : State} {base T : Addr} (h : TabOk s base T) {j q : Nat} (hj : j < 37) (hq : q < 8)
    (h0 : s.gpr .a0 = T + BitVec.ofNat 64 (4096 * j)) (h7 : s.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 2048) :
    RowOk s q where
  a7 := h7
  ent e he := by
    rw [h0, entAddr_row]
    have hd : 8 * (j * (64 * (2 * 4)) + e * (2 * 4) + q) + 8 ≤ 151552 := by omega
    refine ⟨?_, ⟨_, List.mem_append_left _ h.rd, Offset.contains_base T hd (by omega)⟩⟩
    have hf := h.fit
    have e : (T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 4)) + e * (2 * 4) + q))).toNat =
        T.toNat + 8 * (j * (64 * (2 * 4)) + e * (2 * 4) + q) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * (j * (64 * (2 * 4)) + e * (2 * 4) + q) <
        2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    have := h.al
    rw [e]
    omega

theorem dx_eq : p256.sl DX = 608 := rfl

/-- The `2 n` quadwords of entry `t % 64` of row `j` to `D`. -/
theorem scans_ok {base T : Addr} {j t : Nat} (hj : j < 37) : ∀ n ≤ 8, ∀ {s : State}, WsReg s base → TabOk s base T →
    s.gpr .a0 = T + BitVec.ofNat 64 (4096 * j) → s.gpr .a7 = s.gpr .a0 + BitVec.ofNat 64 2048 →
    (∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    WP isa (.block ((List.range n).flatMap (Cfg.scanWord p256))) s fun s' =>
      (∀ q < n, word s'.mem base (608 + 8 * q) = s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Outside base 608 (8 * n) s.mem s'.mem ∧ Keep treeRegs s s'
  | 0, _, s, _, _, _, _, _ => WP.block_nil ⟨fun q hq => absurd hq (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn, s, hw, hT, h0, h7, hm => by
    have hnw := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok hj n (by omega) hw hT h0 h7 hm) fun s₁ ⟨v₁, O₁, k₁⟩ => ?_)
    have ne : ∀ r ∈ [Reg.s0, .a0, .a7, .a1, .a2, .a3, .a4, .a5, .a6], r ∉ treeRegs := by decide
    have e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (ne _ (by simp))
    have e7 : s₁.gpr .a7 = s.gpr .a7 := k₁.gpr (ne _ (by simp))
    have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (ne _ (by simp)), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
    have hT₁ : TabOk s₁ base T := hT.of_outside k₁.2.1 (by omega) O₁
    have hm₁ : ∀ c < 6, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
      rw [k₁.gpr (by
        have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact hm c hc
    refine WP.mono (scanWord_ok hw₁ (q := n) (by omega) hm₁
      (rowOk_of_tab hT₁ hj (by omega) (by rw [e0, h0]) (by rw [e7, e0, h7]))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [dx_eq, e0] at m₂
    -- The entry's quadword, as the table held it.
    have hr : s₁.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 = s.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 := by
      refine Mem.readW_congr fun b hb => O₁ _ (.inr ?_)
      rw [h0, entAddr_row, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      have := hT.far (8 * (j * (64 * (2 * 4)) + t % 64 * (2 * 4) + n) + b) (by
        have := Nat.mod_lt t (show 64 > 0 by decide); omega)
      omega
    have O₂ : Outside base (608 + 8 * n) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun q hq => ?_, ?_, k₁.trans k₂ |>.mono (by simp [treeRegs])⟩
    · by_cases hqn : q < n
      · rw [O₂.word (by omega) (by omega), v₁ q hqn]
      · obtain rfl : q = n := by omega
        rw [m₂, word_writeW_self, hr]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))


/-! ## The entry's words -/

theorem comb7_len : Impl.P256.p256Comb7.length = 37 := by decide

theorem comb7_lenH : ∀ j < 37, (Impl.P256.p256Comb7.getD j []).length = 64 := by decide

/-- `x R mod p`. -/
abbrev montP (x : Nat) : Nat := x * 2 ^ 256 % Spec.P256.curve.p

/-- Entry `e` of row `j`. -/
abbrev entOf (j e : Nat) : Nat × Nat := Proof.Weierstrass.combAt Impl.P256.p256Comb7 j e

/-- Quadword `q` of entry `e` of row `j`: the words of `x`, then of `y`, in
Montgomery's form. -/
theorem entry_word {s : State} {base T : Addr} (hT : TabOk s base T) {j e q : Nat} (hj : j < 37) (he : e < 64)
    (hq : q < 8) :
    s.mem.readW (entAddr (T + BitVec.ofNat 64 (4096 * j)) q e) 64 =
      if q < 4 then Impl.Weierstrass.wordOf (montP (entOf j e).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j e).2) (q - 4) := by
  rw [entAddr_row, hT.held _ (by omega)]
  exact Proof.Weierstrass.tcombWords_getD comb7_len comb7_lenH hj he hq


/-- The scalar: the copy of `k`. -/
abbrev kOf (m : Mem) (base : Addr) : Nat := wordsVal m base 1536 4

/-- The registers the entry's selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- Memory but the working space keeps the table. -/
theorem TabOk.of_unch {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    {W : List (Nat × Nat)} (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) (hu : Unch base W s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega

/-- The entry of digit `j` in `D`: `(x R, y R, R)` for the magnitude `m ≠ 0`
of the digit, `(0, R, 0)` for `m = 0`, and the mask of the digit's sign in
`PT`'s first word. -/
theorem select_ok {s : State} {base T : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 37)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (h2 : s.gpr .s4 = T) (hT : TabOk s base T)
    (hz : word s.mem base (1536 + 32) = 0) (hZ : wordsVal s.mem base 160 4 = 0) :
    WP isa (.block (Cfg.select p256)) s fun s' =>
      wordsVal s'.mem base 608 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).1) ∧
      wordsVal s'.mem base 640 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then wordsVal s.mem base 224 4
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).2) ∧
      wordsVal s'.mem base 672 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else wordsVal s.mem base 224 4) ∧
      word s'.mem base 1024 = maskOf (decide (combWin 7 (kOf s.mem base) j < 64)) ∧
      Unch base [(608, 96), (1024, 16)] s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  generalize hv : combWin 7 (kOf s.mem base) j = v
  have hv128 : v < 128 := hv ▸ Proof.Weierstrass.combWin_lt 7 _ j
  generalize hg : magH 64 v = mg
  have hmg : mg ≤ 64 := hg ▸ Proof.Weierstrass.magH_le (by omega)
  rw [Cfg.select]
  simp only [List.append_assoc]
  -- The window.
  refine WP.block_append (WP.mono (window_ok hw hj h1 (by rw [kc_eq]; exact hz)) fun s₁ ⟨t₁, r₁, m₁⟩ => ?_)
  rw [kc_eq, show wordsVal s.mem base 1536 4 = kOf s.mem base from rfl, hv] at t₁
  have hw₁ := hw.of_rest r₁
  -- The digit.
  refine WP.block_append (WP.mono (digit_ok hw₁ hv128 t₁) fun s₂ ⟨t₂, pt₂, pz₂, O₂, r₂⟩ => ?_)
  rw [hg] at t₂ pz₂
  rw [pt_eq] at pt₂ pz₂ O₂
  have hw₂ := hw₁.of_rest r₂
  -- The masks.
  refine WP.block_append (WP.mono masks_ok fun s₃ ⟨v₃, r₃, m₃⟩ => ?_)
  -- The row.
  have e1 : s₃.gpr .s1 = BitVec.ofNat 64 j := by
    rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h1]
  have e2 : s₃.gpr .s4 = T := by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (row_ok hj e1) fun s₄ ⟨a₄, a7₄, r₄, m₄⟩ => ?_)
  rw [e2] at a₄
  have hw₄ := (hw₂.of_rest r₃).of_rest r₄
  have U₄ : Unch base [(1024, 16)] s.mem s₄.mem := by
    rw [m₄, m₃]; rw [m₁] at O₂; exact O₂.unch
  have hT₄ : TabOk s₄ base T :=
    hT.of_unch (by rw [r₄.rd, r₃.rd, r₂.rd, r₁.rd]) (by simp) U₄
  have hm₄ : ∀ c < 6, s₄.gpr (maskReg c) = maskOf ((s₂.gpr .t2).toNat.testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), v₃ c hc, BitVec.testBit_toNat]
  -- The scans.
  refine WP.block_append (WP.mono (WP.rdwr (scans_ok hj 8 (Nat.le_refl _) hw₄ hT₄ a₄ a7₄ hm₄))
    fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_)
  have r₅ : Rest treeRegs s₄ s₅ := ⟨k₅.1, rd₅, wr₅, sp₅⟩
  have hw₅ := hw₄.of_rest r₅
  -- `Z = 1`.
  refine WP.block_append (WP.mono (copy_ok 4 hw₅ (o := 672) (a := 224) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  -- The mask of `m = 0`.
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₆ (d := 1032) (by decide) (by decide) fun s₇ u₇ => ?_
  have a7₇ : s₇.gpr .a7 = maskOf (decide (mg = 0)) := by
    rw [u₇.gpr, O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), m₄, m₃]; exact pz₂
  have hw₇ := hw₆.of_rest (u₇.rest (ws := [.a7]) (by decide))
  -- The point at infinity for `m = 0`.
  refine WP.block_append (WP.mono (sel_ok (decide (mg = 0)) 4 hw₇ a7₇ (o := 608) (a := 608) (b := 160)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₈ ⟨e₈, r₈, O₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  refine WP.block_append (WP.mono (sel_ok (decide (mg = 0)) 4 hw₈ (by rw [r₈.gpr _ (by decide)]; exact a7₇)
    (o := 640) (a := 640) (b := 224)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₉ ⟨e₉, r₉, O₉⟩ => ?_)
  have hw₉ := hw₈.of_rest r₉
  refine WP.mono (sel_ok (decide (mg = 0)) 4 hw₉ (by rw [r₉.gpr _ (by decide), r₈.gpr _ (by decide)]; exact a7₇)
    (o := 672) (a := 672) (b := 160)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₁₀ ⟨e₁₀, r₁₀, O₁₀⟩ => ?_
  -- What the slots hold.
  have U₇ : Unch base [(1024, 16), (608, 64), (672, 32)] s.mem s₇.mem := by
    rw [u₇.mem]; exact (U₄.trans O₅.unch).trans O₆.unch
  have hZ₇ : wordsVal s₇.mem base 160 4 = 0 := by rw [U₇.wordsVal (by simp) (by omega), hZ]
  have hO₇ : wordsVal s₇.mem base 224 4 = wordsVal s.mem base 224 4 := U₇.wordsVal (by simp) (by omega)
  have hD : mg ≠ 0 → ∀ q < 8, word s₇.mem base (608 + 8 * q) =
      if q < 4 then Impl.Weierstrass.wordOf (montP (entOf j (mg - 1)).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j (mg - 1)).2) (q - 4) := by
    intro h0 q hq
    have ht : (s₂.gpr .t2).toNat % 64 = mg - 1 := by rw [t₂ h0]; omega
    rw [u₇.mem, O₆.word (by omega) (by omega), v₅ q hq, a₄, ht, entry_word hT₄ hj (by omega) hq]
  have hpx : mg ≠ 0 → montP (entOf j (mg - 1)).1 < 2 ^ 256 := fun _ => by
    have := Nat.mod_lt ((entOf j (mg - 1)).1 * 2 ^ 256) (show 0 < Spec.P256.curve.p by decide)
    exact Nat.lt_trans this (by decide)
  have hpy : mg ≠ 0 → montP (entOf j (mg - 1)).2 < 2 ^ 256 := fun _ => by
    have := Nat.mod_lt ((entOf j (mg - 1)).2 * 2 ^ 256) (show 0 < Spec.P256.curve.p by decide)
    exact Nat.lt_trans this (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₁₀.wordsVal (by omega) (by omega), O₉.wordsVal (by omega) (by omega), e₈]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hZ₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ (hpx h0) fun i hi => ?_
      rw [hD h0 i (by omega)]; simp only [show i < 4 from hi, ↓reduceIte]; rfl
  · rw [O₁₀.wordsVal (by omega) (by omega), e₉, O₈.wordsVal (by omega) (by omega),
      O₈.wordsVal (by omega) (by omega)]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hO₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ (hpy h0) fun i hi => ?_
      rw [show 640 + 8 * i = 608 + 8 * (i + 4) by omega, hD h0 (i + 4) (by omega)]
      simp only [show ¬ i + 4 < 4 by omega, ↓reduceIte, Nat.add_sub_cancel]; rfl
  · have e224 : wordsVal s₅.mem base 224 4 = wordsVal s.mem base 224 4 := by
      rw [← O₆.wordsVal (d := 224) (by omega) (by omega), ← u₇.mem]; exact hO₇
    rw [e₁₀, O₉.wordsVal (by omega) (by omega), O₈.wordsVal (by omega) (by omega),
      O₉.wordsVal (by omega) (by omega), O₈.wordsVal (by omega) (by omega)]
    by_cases h0 : mg = 0
    · simp only [h0, decide_true, ↓reduceIte]; exact hZ₇
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]; rw [u₇.mem, e₆, e224]
  · rw [O₁₀.word (by omega) (by omega), O₉.word (by omega) (by omega), O₈.word (by omega) (by omega), u₇.mem,
      O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), m₄, m₃, pt₂]
  · exact ((((U₄.trans O₅.unch).trans O₆.unch).trans (by rw [← u₇.mem]; exact O₈.unch)).trans
      (O₉.unch.trans O₁₀.unch)).cover (by decide)
  · exact (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans
      ((r₄.mono (by decide)).trans ((r₅.mono (by decide)).trans ((r₆.mono (by decide)).trans
      (((u₇.rest (ws := [.a7]) (by decide)).mono (by decide)).trans ((r₈.mono (by decide)).trans ((r₉.mono (by decide)).trans
      (r₁₀.mono (by decide))))))))))

end

/-! ## A step -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W field_ok unit mul_zero_pt)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- `R mod p`, one in Montgomery's form. -/
abbrev oneM : Nat := 2 ^ 256 % W.p

/-- The value in `D.y` before the negation. -/
abbrev yDig (i v : Nat) : Nat := if magH 64 v = 0 then oneM else montP (entOf i (magH 64 v - 1)).2

theorem toM_montP (x : Nat) : toM W.p (2 ^ 256) (montP x) = Fin.ofNat W.p x := toM_mont unit

/-- The entry of digit `i`, `y` negated for a negative digit, represents the
digit's signed point. -/
theorem entry_rep (hL : Law W) {k i : Nat} (hi : i < 37) :
    Rep W (toM W.p (2 ^ 256) (if magH 64 (combWin 7 k i) = 0 then 0
        else montP (entOf i (magH 64 (combWin 7 k i) - 1)).1))
      (toM W.p (2 ^ 256) (if combWin 7 k i < 64 then (0 + W.p - yDig i (combWin 7 k i)) % W.p
        else yDig i (combWin 7 k i)))
      (toM W.p (2 ^ 256) (if magH 64 (combWin 7 k i) = 0 then 0 else oneM))
      (signedPtW W 7 k i) := by
  have hC := P256.combOk7 hL
  have hv := combWin_lt 7 k i
  unfold signedPtW yDig
  generalize combWin 7 k i = v at hv ⊢
  simp only [show 2 ^ (7 - 1) = 64 from rfl]
  by_cases h64 : 64 ≤ v
  · have hmg : magH 64 v = v - 64 := by unfold magH; simp [h64]
    simp only [h64, ↓reduceIte, show ¬ v < 64 by omega, hmg]
    by_cases h0 : v - 64 = 0
    · simp only [h0, ↓reduceIte, toM_zero, combPtW, Nat.zero_mul, mul_zero_pt]
      rw [toM_one unit]; exact rep_infinity' hL
    · obtain ⟨m, hm⟩ : ∃ m, v - 64 = m + 1 := ⟨v - 64 - 1, by omega⟩
      simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, combPtW, Nat.add_sub_cancel]
      rw [hC.entry i hi m (by simp; omega), toM_montP, toM_montP, toM_one unit]
      exact rep_affine' hL _ _
  · have hmg : magH 64 v = 64 - v := by unfold magH; simp [h64]
    obtain ⟨m, hm⟩ : ∃ m, 64 - v = m + 1 := ⟨64 - v - 1, by omega⟩
    simp only [h64, ↓reduceIte, show v < 64 by omega, hmg, hm, Nat.add_one_ne_zero, combPtW, Nat.add_sub_cancel]
    rw [hC.entry i hi m (by simp; omega), toM_montP, toM_one unit,
      toM_sub (A := 0) (B := montP (entOf i m).2) (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.mod_lt _ (by decide)) (Nat.le_of_eq (Nat.zero_add _).symm))),
      toM_zero, toM_montP]
    have := rep_affine' hL (Fin.ofNat W.p (entOf i m).1) (-Fin.ofNat W.p (entOf i m).2)
    simp only [negPt]
    rwa [show (0 : Fe W) - Fin.ofNat W.p (entOf i m).2 = -Fin.ofNat W.p (entOf i m).2 by grind]


/-! ## The negation and the addition -/

/-- `y = -y` by the sign's mask in `PT`. -/
theorem negate_ok {s : State} {base : Addr} (hw : WsReg s base) (hZ : wordsVal s.mem base 160 4 = 0)
    (hY : wordsVal s.mem base 640 4 < W.p) {c : Bool} (hPT : word s.mem base 1024 = maskOf c) :
    WP isa (Cfg.negate p256) s fun s' =>
      wordsVal s'.mem base 640 4 = (if c then (0 + W.p - wordsVal s.mem base 640 4) % W.p
        else wordsVal s.mem base 640 4) ∧
      Unch base [(992, 32), (3840, 256), (640, 32)] s.mem s'.mem ∧ Kp s s' := by
  have hn := hw.nowrap
  rw [Cfg.negate]
  refine WP.seq (WP.mono (subCall_ok field_ok hw (o := p256.sl ACC) (a := p256.sl ZERO) (b := p256.sl DY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show wordsVal s.mem base 160 4 < _; rw [hZ]; decide) hY) fun s₁ ⟨K₁, v₁⟩ => ?_)
  have hw₁ := hw.of_kp K₁.kp
  have U₁ : Unch base [(992, 32), (3840, 256)] s.mem s₁.mem := fun x hx => K₁.mem x hx
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₁ (d := 1024) (by decide) (by decide) fun s₂ u₂ => ?_
  have a7 : s₂.gpr .a7 = maskOf c := by
    rw [u₂.gpr, U₁.word (by simp) (by omega), hPT]
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.a7]) (by decide))
  refine WP.mono (sel_ok c 4 hw₂ a7 (o := 640) (a := 640) (b := 992) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_⟩
  · have hacc : wordsVal s₂.mem base 992 4 = (0 + W.p - wordsVal s.mem base 640 4) % W.p := by
      rw [u₂.mem]
      have : wordsVal s₁.mem base 992 4 =
          (wordsVal s.mem base 160 4 + W.p - wordsVal s.mem base 640 4) % W.p := v₁
      rw [hZ] at this
      exact this
    have hy : wordsVal s₂.mem base 640 4 = wordsVal s.mem base 640 4 := by
      rw [u₂.mem]; exact U₁.wordsVal (by simp) (by omega)
    rw [e₃, hacc, hy]
  · have O₃' := O₃; rw [u₂.mem] at O₃'; exact U₁.trans O₃'.unch
  · exact K₁.kp.trans (Kp.of_rest ((u₂.rest (ws := [.a7]) (by decide)).mono (by decide) |>.trans
      (r₃.mono (by decide))) (ws := [.a7, .t0, .t1]) (by decide))

/-- The slots of the addition. -/
abbrev combSl : List Nat :=
  [256, 288, 512, 544, 576, 608, 640, 672, 704, 736, 768, 800, 832, 864, 896, 928, 960]

theorem combLay : Lay p256.MP' (own 4) (· ∈ combSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ combSl, ∀ y ∈ combSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

/-- The slots the addition reads. -/
abbrev addV : List Nat := [256, 288, 512, 544, 576, 608, 640, 672]

/-- `T = R + D` by the complete addition, then `R = T`. -/
theorem addR_ok {s : State} {base : Addr} (hw : WsReg s base) (hlt : ∀ x ∈ addV, wordsVal s.mem base x 4 < W.p) :
    WP isa (.seq (fprog p256.FP (rcb p256.rcbSlots (p256.pt RX RY RZ) (p256.pt DX DY DZ) (p256.pt TX TY TZ)))
      (.block (copy 4 (p256.sl RX) (p256.sl TX) ++ copy 4 (p256.sl RY) (p256.sl TY) ++
        copy 4 (p256.sl RZ) (p256.sl TZ)))) s fun s' =>
      Kp s s' ∧ Unch base [(512, 512), (3840, 256)] s.mem s'.mem ∧
      (∀ x ∈ [512, 544, 576], wordsVal s'.mem base x 4 < W.p) ∧
      (tmv W 4 base s' 512, tmv W 4 base s' 544, tmv W 4 base s' 576) =
        rcbAdd (tmv W 4 base s 256) (tmv W 4 base s 288) (tmv W 4 base s 512) (tmv W 4 base s 544)
          (tmv W 4 base s 576) (tmv W 4 base s 608) (tmv W 4 base s 640) (tmv W 4 base s 672) := by
  have hn := hw.nowrap
  have hI : Inv 4 base W.p (· ∈ combSl) addV (fun x => tmv W 4 base s x) s :=
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (rcb_ok (M := p256.MP') (F := p256Field) field_ok rfl combLay
    (fun x hx => by have := (by decide : ∀ x ∈ combSl, x < 2048) x hx; exact this) unit
    (S := p256.rcbSlots) (p := p256.pt RX RY RZ) (q := p256.pt DX DY DZ) (o := p256.pt TX TY TZ)
    ⟨by decide, by decide⟩ (by decide) hI (by decide)) fun s₁ ⟨K₁, I₁, v₁, _⟩ => ?_)
  have hw₁ := hw.of_kp K₁.kp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := 512) (a := 704) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := 544) (a := 736) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.mono (copy_ok 4 hw₃ (o := 576) (a := 768) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨e₄, r₄, O₄⟩ => ?_
  have tx : wordsVal s₄.mem base 512 4 = wordsVal s₁.mem base 704 4 := by
    rw [O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), e₂]
  have ty : wordsVal s₄.mem base 544 4 = wordsVal s₁.mem base 736 4 := by
    rw [O₄.wordsVal (by omega) (by omega), e₃, O₂.wordsVal (by omega) (by omega)]
  have tz : wordsVal s₄.mem base 576 4 = wordsVal s₁.mem base 768 4 := by
    rw [e₄, O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega)]
  have hT : ∀ x ∈ [704, 736, 768], x ∈ rcbW p256.rcbSlots (p256.pt TX TY TZ) ++ addV := by decide
  refine ⟨K₁.kp.trans (Kp.of_rest ((r₂.trans r₃).trans r₄)), ?_, ?_, ?_⟩
  · have U₁ : Unch base ((rcbW p256.rcbSlots (p256.pt TX TY TZ)).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])
        s.mem s₁.mem := fun x hx => K₁.mem x hx
    exact (((U₁.trans O₂.unch).trans O₃.unch).trans O₄.unch).cover (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [tx]; exact I₁.lt 704 (hT 704 (by simp))
    · rw [ty]; exact I₁.lt 736 (hT 736 (by simp))
    · rw [tz]; exact I₁.lt 768 (hT 768 (by simp))
  · simp only [tmv]
    have h704 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 704 4) = _ := I₁.val 704 (hT 704 (by simp))
    have h736 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 736 4) = _ := I₁.val 736 (hT 736 (by simp))
    have h768 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 768 4) = _ := I₁.val 768 (hT 768 (by simp))
    rw [tx, ty, tz, h704, h736, h768]
    exact v₁


/-! ## A step -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure CombPre (base T : Addr) (s₀ : State) : Prop where
  s4 : s₀.gpr .s4 = T
  kz : word s₀.mem base (1536 + 32) = 0
  zero : wordsVal s₀.mem base 160 4 = 0
  one : wordsVal s₀.mem base 224 4 = oneM
  a : tmv W 4 base s₀ 256 = Fin.ofNat W.p W.a
  b : tmv W 4 base s₀ 288 = Fin.ofNat W.p (3 * W.b)
  alt : wordsVal s₀.mem base 256 4 < W.p
  blt : wordsVal s₀.mem base 288 4 < W.p

/-- What the steps write. -/
abbrev stepW : List (Nat × Nat) := [(512, 544), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[combEW j]G`, for the
scalar the start holds. -/
structure CombInv (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  tab : TabOk s base T
  lt : ∀ x ∈ [512, 544, 576], wordsVal s.mem base x 4 < W.p
  rep : Rep W (tmv W 4 base s 512) (tmv W 4 base s 544) (tmv W 4 base s 576)
    (Spec.Weierstrass.mul (combEW 7 (kOf s₀.mem base) 37 j) (Spec.Weierstrass.G W))

theorem signed_onCurve (hL : Law W) (k i : Nat) : Spec.Weierstrass.onCurve W (signedPtW W 7 k i) = true := by
  unfold signedPtW combPtW
  split
  · exact hL.onCurve_mul P256.onCurve_G _
  · exact onCurve_negPt (hL.onCurve_mul P256.onCurve_G _)

/-- A step: from `[combEW j]G` to `[combEW (j - 1)]G`. -/
theorem step_ok (hL : Law W) {base T : Addr} {s₀ : State} (hP : CombPre base T s₀) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ 37) {s : State} (hI : CombInv base T s₀ s j) :
    WP isa (Cfg.step p256) s fun s' => CombInv base T s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hk : kOf s.mem base = kOf s₀.mem base := uS 1536 (by omega) (by omega)
  rw [Cfg.step]
  -- `s1 -= 1` and the entry.
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr
    (by rw [u₁.other _ (by decide), hI.keep.gpr _ (by decide) (by decide), hP.s4])
    (hI.tab.of_mem u₁.rd fun x _ => by rw [u₁.mem])
    (by rw [u₁.mem, hI.unch.word (by simp) (by omega), hP.kz])
    (by rw [u₁.mem, uS 160 (by omega) (by omega), hP.zero])) fun s₂ ⟨dx₂, dy₂, dz₂, pt₂, U₂, r₂⟩ => ?_
  rw [u₁.mem, hk] at dx₂ dy₂ dz₂ pt₂
  rw [u₁.mem] at U₂
  rw [uS 224 (by omega) (by omega), hP.one] at dy₂ dz₂
  have hw₂ := hw₁.of_rest r₂
  generalize hv : combWin 7 (kOf s₀.mem base) (j - 1) = v at dx₂ dy₂ dz₂ pt₂
  have hv128 : v < 128 := hv ▸ combWin_lt 7 _ _
  -- What the slots hold so far.
  have uS₂ : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' => by
    rw [U₂.wordsVal (by simp; omega) (by omega), uS d h h']
  have hR₂ : ∀ d ∈ [512, 544, 576], wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 := by
    intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact U₂.wordsVal (by simp) (by omega)
  have hlt1 : oneM < W.p := Nat.mod_lt _ (by decide)
  have hlty : yDig (j - 1) v < W.p := by
    unfold yDig; split
    · exact hlt1
    · exact Nat.mod_lt _ (by decide)
  -- The negation.
  refine WP.seq (WP.mono (negate_ok hw₂ (by rw [uS₂ 160 (by omega) (by omega), hP.zero])
    (by rw [dy₂]; exact hlty) pt₂) fun s₃ ⟨dy₃, U₃, K₃⟩ => ?_)
  rw [dy₂] at dy₃
  have hw₃ := hw₂.of_kp K₃
  have e₃ : ∀ d, (d + 32 ≤ 640 ∨ 672 ≤ d) → (d + 32 ≤ 992 ∨ 1024 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := fun d h1 h2 h3 =>
    U₃.wordsVal (by simp; omega) (by omega)
  -- The addition.
  have hlt₃ : ∀ x ∈ addV, wordsVal s₃.mem base x 4 < W.p := by
    intro x hx
    simp only [addV, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.alt
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.blt
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 512 (by simp)]; exact hI.lt 512 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 544 (by simp)]; exact hI.lt 544 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 576 (by simp)]; exact hI.lt 576 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), dx₂]; split
      · decide
      · exact Nat.mod_lt _ (by decide)
    · rw [dy₃]; split
      · exact Nat.mod_lt _ (by decide)
      · exact hlty
    · rw [e₃ _ (by omega) (by omega) (by omega), dz₂]; split
      · decide
      · exact hlt1
  refine WP.mono (addR_ok hw₃ hlt₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  -- The invariant.
  have hU : Unch base stepW s₀.mem s₄.mem :=
    (((hI.unch.trans U₂).trans U₃).trans U₄).cover (by decide)
  refine ⟨hw₃.of_kp K₄, ?_, ?_, hU, ?_, lt₄, ?_⟩
  · rw [K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans
      (Kc.of_rest r₂)).trans (K₃.kc.trans K₄.kc)
  · exact (hI.tab.of_unch (by rw [K₄.rd, K₃.rd, r₂.rd, u₁.rd]) (W := [(608, 96), (1024, 16)] ++
      [(992, 32), (3840, 256), (640, 32)] ++ [(512, 512), (3840, 256)]) (by decide)
      ((U₂.trans U₃).trans U₄))
  · -- `T = R + D`, with `D` the signed entry.
    have ea : tmv W 4 base s₃ 256 = Fin.ofNat W.p W.a := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.a
    have eb : tmv W 4 base s₃ 288 = Fin.ofNat W.p (3 * W.b) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.b
    have eR : ∀ d ∈ [512, 544, 576], tmv W 4 base s₃ d = tmv W 4 base s d := by
      intro d hd
      simp only [tmv]
      have := hR₂ d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [e₃ d (by omega) (by omega) (by omega), this]
    have hD := entry_rep hL (k := kOf s₀.mem base) (i := j - 1) (by omega)
    rw [hv] at hD
    have ex : tmv W 4 base s₃ 608 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0
        else montP (entOf (j - 1) (magH 64 v - 1)).1) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dx₂]
    have ey : tmv W 4 base s₃ 640 = toM W.p (2 ^ 256) (if v < 64 then (0 + W.p - yDig (j - 1) v) % W.p
        else yDig (j - 1) v) := by
      simp only [tmv]; rw [dy₃]; simp only [decide_eq_true_eq, yDig]
    have ez : tmv W 4 base s₃ 672 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0 else oneM) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dz₂]
    rw [ea, eb, eR 512 (by simp), eR 544 (by simp), eR 576 (by simp), ex, ey, ez] at v₄
    have hS := Rep.add hL (hL.onCurve_mul P256.onCurve_G _) (signed_onCurve hL (kOf s₀.mem base) (j - 1))
      hI.rep hD v₄.symm
    have hadd := combW_add hL P256.onCurve_G (w := 7) (k := kOf s₀.mem base) (J := 37) (j := j - 1) (by omega)
    rw [Nat.sub_add_cancel hj1] at hadd
    unfold signedPtW at hS
    rw [hadd] at hS
    exact hS

end

/-! ## The body -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W field_ok unit mul_zero_pt)
open VG.Proof.X25519.RISCV64 (Rest)


/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(1536, 40), (512, 544), (3840, 256)]

/-- The body: `R = [k]G`, for the number `k` at `K`'s slot. -/
theorem body_ok (hL : Law W) {s : State} {base T : Addr} (hw : WsReg s base) (h2 : s.gpr .s4 = T)
    (hT : TabOk s base T) (hz : wordsVal s.mem base 160 4 = 0) (hone : wordsVal s.mem base 224 4 = oneM)
    (ha : tmv W 4 base s 256 = Fin.ofNat W.p W.a) (hb : tmv W 4 base s 288 = Fin.ofNat W.p (3 * W.b))
    (hap : wordsVal s.mem base 256 4 < W.p) (hbp : wordsVal s.mem base 288 4 < W.p) :
    WP isa (Cfg.body p256 Impl.P256.p256Comb7Start) s fun s' =>
      Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧ TabOk s' base T ∧
      (∀ x ∈ [512, 544, 576], wordsVal s'.mem base x 4 < W.p) ∧
      Rep W (tmv W 4 base s' 512) (tmv W 4 base s' 544) (tmv W 4 base s' 576)
        (Spec.Weierstrass.mul (wordsVal s.mem base 1056 4) (Spec.Weierstrass.G W)) := by
  have hn := hw.nowrap
  have hC := P256.combOk7 hL
  rw [Cfg.body]
  simp only [List.append_assoc]
  -- The copy of `k`, and its zero word.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := 1536) (a := 1056) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  refine sd_ws hw₂ (d := 1568) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_rest (u₃.rest [])
  have O₃ : Outside base 1568 8 s₂.mem s₃.mem := by rw [u₃.mem]; exact writeW_outside _ _ _ (by omega)
  -- `R = S`.
  refine WP.block_append (WP.mono (setConst_ok 4 hw₃ (o := 512) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p256
    Impl.P256.p256Comb7Start.1) (by decide) (by decide)) fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.block_append (WP.mono (setConst_ok 4 hw₄ (o := 544) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p256
    Impl.P256.p256Comb7Start.2) (by decide) (by decide)) fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  refine WP.block_append (WP.mono (copy_ok 4 hw₅ (o := 576) (a := 224) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  refine wp_li (imm := 37) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have r₇ : Rest [.t0, .t1] s s₆ :=
    ((r₁.mono (by decide)).trans ((u₂.rest (ws := [.t0, .t1]) (by decide)).trans (u₃.rest _))).trans
      ((r₄.trans r₅).trans (r₆.mono (by decide)))
  have hw₇ : WsReg s₇ base := hw₆.of_kc (Kc.of_rest (u₇.rest (ws := [.s1]) (by decide)))
  have U₆ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₆.mem := by
    have O₃' : Outside base 1568 8 s₁.mem s₃.mem := by rw [← u₂.mem]; exact O₃
    exact (((O₁.unch.trans O₃'.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch
  have U₇ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₇.mem := by
    rw [u₇.mem]; exact U₆
  have e7 : ∀ d, (d + 32 ≤ 512 ∨ 608 ≤ d) → (d + 32 ≤ 1536 ∨ 1576 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₇.mem base d 4 = wordsVal s.mem base d 4 := fun d h1 h2 h3 =>
    U₇.wordsVal (by simp; omega) (by omega)
  -- The loop's start.
  have hP : CombPre base T s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), r₇.gpr _ (by decide), h2]
    · show word s₇.mem base 1568 = 0
      rw [u₇.mem, O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), O₄.word (by omega) (by omega),
        u₃.mem, word_writeW_self, u₂.gpr]; rfl
    · rw [e7 160 (by omega) (by omega) (by omega)]; exact hz
    · rw [e7 224 (by omega) (by omega) (by omega)]; exact hone
    · simp only [tmv]; rw [e7 256 (by omega) (by omega) (by omega)]; exact ha
    · simp only [tmv]; rw [e7 288 (by omega) (by omega) (by omega)]; exact hb
    · rw [e7 256 (by omega) (by omega) (by omega)]; exact hap
    · rw [e7 288 (by omega) (by omega) (by omega)]; exact hbp
  have hk : kOf s₇.mem base = wordsVal s.mem base 1056 4 := by
    show wordsVal s₇.mem base 1536 4 = _
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega),
      O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), u₂.mem, e₁]
  have hT₇ : TabOk s₇ base T := hT.of_unch (by rw [u₇.rd, r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂.rd, r₁.rd])
    (by decide) U₇
  have ex : wordsVal s₇.mem base 512 4 = montP Impl.P256.p256Comb7Start.1 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega), e₄]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ey : wordsVal s₇.mem base 544 4 = montP Impl.P256.p256Comb7Start.2 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), e₅]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ez : wordsVal s₇.mem base 576 4 = oneM := by
    rw [u₇.mem, e₆, O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega),
      O₃.wordsVal (by omega) (by omega), u₂.mem, O₁.wordsVal (by omega) (by omega)]; exact hone
  have hI : CombInv base T s₇ s₇ 37 := by
    refine ⟨hw₇, u₇.gpr, Kc.refl _, Unch.refl _ _ _, hT₇, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [ex]; exact Nat.mod_lt _ (by decide)
      · rw [ey]; exact Nat.mod_lt _ (by decide)
      · rw [ez]; exact Nat.mod_lt _ (by decide)
    · simp only [tmv]
      rw [ex, ey, ez, toM_montP, toM_montP, show 2 ^ (64 * 4) = 2 ^ 256 from rfl, toM_one unit,
        combEW_top, show 7 - 1 = 6 from rfl, show 2 ^ 6 = 2 ^ (7 - 1) from rfl, hC.start]
      exact rep_affine' hL _ _
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => CombInv base T s₇ s' j) (n := 37) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(Kc.of_rest r₇).trans ((Kc.of_rest (u₇.rest (ws := [.s1]) (by decide))).trans hi.keep),
    ((U₇.trans hi.unch).cover (by decide)), hi.tab, hi.lt, ?_⟩
  have hr := hi.rep
  rw [hk, combEW_zero (by have := wordsVal_lt s.mem base 1056 4; omega)] at hr
  exact hr

end

end VG.Proof.Ecdsa.RISCV64.Comb
