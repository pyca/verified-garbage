module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulVerified
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulVerified
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.P521.Comb7Shape
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.P521.Comb7
meta import VerifiedGarbage.Proof.P521.Comb7Shape
meta import VerifiedGarbage.Proof.P521.Point
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-! ### `Ecdsa.RISCV64.P521.Comb`, which only this module used -/

section

/-!
# The comb on RISC-V over P-521, in 58-bit limbs: the body

`vg_p521_mul_g`'s body (`Impl/Ecdsa/RISCV64/CombU.lean`), as
`Proof/Ecdsa/RISCV64/P384/Comb.lean` proves P-384's, from the lemmas of
`Proof/Ecdsa/RISCV64/Comb/Main.lean` that do not depend on the curve (the
selections, `tree_ok`, the window's bits, the digit's facts and the masks),
on `vg_p521_mul`'s limbs (`Proof/Ecdsa/RISCV64/P521/MulVerified.lean`: `PtOk`,
`addPt_ok`, and the conversions of `MulVerified.lean`). What differs from
P-384's:

* The scan: quadword `q` of the entry is selected among eight groups of
  eight entries of 144 bytes, each by `tree_ok` over bits 0 to 2 at `a7`,
  which steps through them, and the groups by bits 3 to 5 (`groups_ok`).
* The masks of the digit are kept past the copy of `k` (`digit_ok`).
* The rows are `9216` bytes, `8192 j + 1024 j` (`row_ok`).
* The entry goes to limbs (`toU_ok`), its negation is the limbs'
  subtraction, and the addition is `addPt_ok`'s (`entry_ok`).
* The 83 steps, the nine-word slots and the table of 83 rows.
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P521.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (upd_keep wp_and wp_sra pick_mask wp_pick mod_two_pow_succ' tree_ok wp_sllReg
  wp_xori funnel_bit window_bits digit_facts mask_bit maskOfBit_ok masks_ok)

/-! ## The scan of a table's entries -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sd_ws)
open VG.Impl.Ecdsa.RISCV64 (DX)
open VG.Impl.Ecdsa.RISCV64.WindowU (c)

/-- The address of quadword `q` of entry `e` of the row at `T`. -/
abbrev entAddr (T : Addr) (q e : Nat) : Addr := T + BitVec.ofNat 64 (8 * q + 144 * e)

/-- What the scan needs of the row at `A`: each quadword `q` of its 64
entries aligned and readable. -/
def RowOk (s : State) (A : Addr) (q : Nat) : Prop :=
  ∀ e < 64, (entAddr A q e).toNat % 8 = 0 ∧ InRegions (s.rd ++ s.wr) (entAddr A q e) 8

/-- The selections' registers are apart from the bases' and the masks'. -/
theorem treeRegs_ne : ∀ r ∈ treeRegs, r ≠ .a7 ∧ r ≠ .a0 ∧ r ≠ .s0 ∧ ∀ c, c < 6 → r ≠ maskReg c := by decide

theorem maskReg_ne : ∀ c, c < 6 → maskReg c ≠ .a7 ∧ maskReg c ≠ .a0 ∧ maskReg c ∉ treeRegs := by decide

/-- The selection of quadword `q` among the `2 ^ L` groups from group `g`
on, `a7` at group `g`: the first register holds the quadword of entry
`8 g + t % 2 ^ (3 + L)`, and `a7` is at group `g + 2 ^ L`. -/
theorem groups_ok {q t : Nat} (hq : q < 18) {A : Addr} (L : Nat) :
    ∀ (g : Nat) (a : Reg) (rs : List Reg) (s : State), g + 2 ^ L ≤ 8 →
    3 + L ≤ rs.length → (a :: rs).Nodup → (∀ r ∈ a :: rs, r ∈ treeRegs) →
    (∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    s.gpr .a7 = A + BitVec.ofNat 64 (1152 * g) → RowOk s A q →
    WP isa (.block (groups q L (a :: rs))) s fun s' =>
      s'.gpr a = s.mem.readW (entAddr A q (8 * g + t % 2 ^ (3 + L))) 64 ∧
      s'.gpr .a7 = A + BitVec.ofNat 64 (1152 * (g + 2 ^ L)) ∧
      Keep (a :: rs ++ ([.a7] : List Reg)) s s' ∧ s'.mem = s.mem := by
  induction L with
  | zero =>
    intro g a rs s hg hlen hnd hin hm h7 hr
    obtain hne : ∀ r ∈ a :: rs, r ≠ .a7 ∧ ∀ c < 3, r ≠ maskReg c := fun r hr' =>
      ⟨(treeRegs_ne r (hin r hr')).1, fun c hc => (treeRegs_ne r (hin r hr')).2.2.2 c (by omega_using [hc])⟩
    obtain hadr : ∀ e, s.gpr .a7 + BitVec.ofNat 64 (8 * q + 144 * e) = entAddr A q (8 * g + e) := fun e => by
      rw [h7, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []
    show WP isa (.block (tree .a7 144 3 (8 * q) (a :: rs) ++ [.addi .a7 .a7 (1152 : Nat)])) s _
    refine WP.block_append (WP.mono (tree_ok .a7 144 t 3 (8 * q) a rs s (by omega_using [hlen]) hnd hne
      (fun c hc => hm c (by omega_using [hc])) (by omega_using [hq])
      (fun e he => by rw [hadr]; exact hr _ (by omega_using [hg, he]))) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
    obtain a7₁ : s₁.gpr .a7 = s.gpr .a7 := k₁.gpr fun h => (hne _ h).1 rfl
    refine wp_addi (by decide) fun s₂ u₂ => WP.block_nil ⟨?_, ?_, k₁.trans (upd_keep u₂), ?_⟩
    · rw [u₂.other _ (hne a (by simp)).1, v₁, hadr]
    · rw [u₂.gpr, a7₁, h7, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2
    · rw [u₂.mem, m₁]
  | succ L ih =>
    intro g a rs s hg hlen hnd hin hm h7 hr
    obtain ⟨b, rs, rfl⟩ : ∃ b rs', rs = b :: rs' := by
      cases rs with
      | nil => simp at hlen
      | cons b rs' => exact ⟨b, rs', rfl⟩
    simp only [List.length_cons] at hlen
    obtain hp : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [Nat.pow_succ]; omega_using []
    obtain hab : a ≠ b := fun e => by subst e; simp at hnd
    obtain hb := treeRegs_ne b (hin b (by simp))
    obtain ha := treeRegs_ne a (hin a (by simp))
    obtain hL3 : 3 + L < 6 := by
      obtain h8 : 2 ^ (L + 1) ≤ 2 ^ 3 := by omega_using [hg]
      have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h8
      omega_using [this]
    show WP isa (.block (groups q L (a :: b :: rs) ++ groups q L (b :: rs) ++ pick a b (maskReg (3 + L)))) s _
    rw [List.append_assoc]
    -- The low half, into `a`.
    refine WP.block_append (WP.mono (ih g a (b :: rs) s (by omega_using [hg, hp]) (by simp; omega_using [hlen]) hnd hin hm
      h7 hr) fun s₁ ⟨v₁, a7₁, k₁, m₁⟩ => ?_)
    obtain hmk : ∀ {s' : State} {l : List Reg}, Keep l s s' → (∀ r ∈ l, r ∈ treeRegs ∨ r = .a7) →
        ∀ c < 6, s'.gpr (maskReg c) = maskOf (t.testBit c) := fun k hl c hc => by
      rw [k.gpr fun h => by
        rcases hl _ h with h' | h'
        · exact (maskReg_ne c hc).2.2 h'
        · exact (maskReg_ne c hc).1 h']
      exact hm c hc
    obtain hl₁ : ∀ r ∈ a :: b :: rs ++ ([.a7] : List Reg), r ∈ treeRegs ∨ r = .a7 := fun r hr' => by
      rcases List.mem_append.mp hr' with h | h
      · exact .inl (hin r h)
      · exact .inr (List.mem_singleton.mp h)
    -- The high half, into `b`.
    refine WP.block_append (WP.mono (ih (g + 2 ^ L) b rs s₁ (by omega_using [hg, hp]) (by omega_using [hlen])
      (List.nodup_cons.mp hnd).2 (fun r hr' => hin r (List.mem_cons_of_mem _ hr')) (hmk k₁ hl₁) a7₁
      (fun e he => by rw [k₁.2.1, k₁.2.2]; exact hr e he)) fun s₂ ⟨v₂, a7₂, k₂, m₂⟩ => ?_)
    rw [m₁] at v₂
    obtain ua : s₂.gpr a = s₁.gpr a := k₂.gpr fun h => by
      rcases List.mem_append.mp h with h | h
      · exact (List.nodup_cons.mp hnd).1 h
      · exact ha.1 (List.mem_singleton.mp h)
    obtain hl₂ : ∀ r ∈ (a :: b :: rs ++ ([.a7] : List Reg)) ++ (b :: rs ++ ([.a7] : List Reg)), r ∈ treeRegs ∨ r = .a7 :=
      fun r hr' => by
        rcases List.mem_append.mp hr' with h | h
        · exact hl₁ r h
        · exact hl₁ r (by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h)
    obtain k₁₂ := k₁.trans k₂
    rw [← List.append_nil (pick a b (maskReg (3 + L)))]
    refine wp_pick hab (hb.2.2.2 _ hL3) (hmk k₁₂ hl₂ _ hL3) fun s₃ v₃ k₃ m₃ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · rw [v₃, ua, v₁, v₂, show 3 + (L + 1) = 3 + L + 1 from rfl, mod_two_pow_succ' t (3 + L)]
      obtain e8 : 2 ^ (3 + L) = 8 * 2 ^ L := by rw [Nat.pow_add]
      by_cases hbit : t.testBit (3 + L)
      · simp only [hbit, ↓reduceIte]
        rw [show 8 * (g + 2 ^ L) + t % 2 ^ (3 + L) = 8 * g + (2 ^ (3 + L) + t % 2 ^ (3 + L)) by omega_using [e8]]
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    · rw [k₃.gpr (fun h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact hb.1 h.symm
        · exact ha.1 h.symm), a7₂, show g + 2 ^ L + 2 ^ L = g + 2 ^ (L + 1) by omega_using [hp]]
    · exact (k₁₂.trans k₃).mono fun r hr' => by
        rcases List.mem_append.mp hr' with h | h
        · rcases List.mem_append.mp h with h | h
          · exact h
          · rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp
    · rw [m₃, m₂, m₁]

/-- Quadword `q` of entry `t % 64` of the row at `a0`, by the masks of
`t`'s bits, to `D`'s word `q`. -/
theorem scanWord_ok {s : State} {base : Addr} (hw : WsReg s base) {q t : Nat} (hq : q < 18)
    (hm : ∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) (hr : RowOk s (s.gpr .a0) q) :
    WP isa (.block (scanWord q)) s fun s' =>
      s'.mem = s.mem.writeW (off base (1288 + 8 * q)) (s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Keep (treeRegs ++ ([.a7] : List Reg)) s s' := by
  rw [scanWord, show c.sl DX = 1288 from rfl]
  refine wp_mv fun s₁ u₁ => ?_
  obtain k₁ := upd_keep u₁
  obtain hm₁ : ∀ c < 6, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
    rw [u₁.other _ (maskReg_ne c hc).1]; exact hm c hc
  refine WP.block_append (WP.mono (groups_ok (t := t) hq (A := s.gpr .a0) 3 0 Reg.t0 ([.t1, .t2, .t3, .t4, .t5, .t6] : List Reg) s₁
    (by decide) (by decide) (by decide) (fun r hr' => hr') hm₁
    (by rw [u₁.gpr]; simp) (fun e he => by rw [u₁.rd, u₁.wr]; exact hr e he)) fun s₂ ⟨v₂, _, k₂, m₂⟩ => ?_)
  obtain K₂ : Keep (treeRegs ++ ([.a7] : List Reg)) s s₂ := (k₁.trans k₂).mono (by simp [treeRegs])
  obtain hw₂ : WsReg s₂ base := ⟨by rw [K₂.gpr (by decide), hw.s0], by rw [K₂.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
  refine sd_ws hw₂ (by omega_using [hq]) (by omega_using []) fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · have e64 : 8 * 0 + t % 2 ^ (3 + 3) = t % 64 := by rw [Nat.mul_zero, Nat.zero_add]
    rw [u₃.mem, m₂, u₁.mem, v₂, u₁.mem, e64]
  · exact ⟨fun r hr' => by rw [u₃.gpr, K₂.gpr hr'], by rw [u₃.rd, K₂.2.1], by rw [u₃.wr, K₂.2.2]⟩

end

/-! ## The window, the digit and the masks -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont
open VG.Impl.Ecdsa.RISCV64.WindowU (c)
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg sdAt_ws testBit_wordsVal wp_srlReg)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Weierstrass (combWin magH)

/-- The shift of the high word. -/
theorem shamt_eq : ∀ j < 83, (BitVec.ofNat 64 (7 * j) ^^^ BitVec.ofInt 64 63).toNat % 64 = 63 - 7 * j % 64 := by
  decide

/-- `8 j - j`. -/
theorem seven_mul {j : Nat} (hj : j < 83) :
    BitVec.ofNat 64 j <<< 3 - BitVec.ofNat 64 j = BitVec.ofNat 64 (7 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := hj
  omega_using []

/-- The slot of the copy of `k`. -/
theorem kc_eq : c.sl KC = 3376 := rfl

/-- `t2 = k_j`, for `j` in `s1`, from the copy of `k` at `KC` and its zero word. -/
theorem window_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 83)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (hz : word s.mem base (c.sl KC + 72) = 0) :
    WP isa (.block (Cfg.window c)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 (combWin 7 (wordsVal s.mem base (c.sl KC) 9) j) ∧
        Rest [.t0, .t1, .t2, .t3, .t4] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  obtain hq : 7 * j / 64 ≤ 8 := by omega_using [hj]
  rw [Cfg.window, kc_eq] at *
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_sll (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => ?_
  obtain e₂ : s₂.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .s1 (by decide), h1, seven_mul hj]
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  obtain e₅' : s₅.gpr .t1 = base + BitVec.ofNat 64 (8 * (7 * j / 64)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other .s0 (by decide), u₃.gpr, u₃.other .s0 (by decide),
      u₂.other .s0 (by decide), u₁.other .s0 (by decide), hw.s0, e₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega_using [hj] : 7 * j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega_using [hj] : 7 * j / 64 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega_using [hj] : 8 * (7 * j / 64) < 18446744073709551616)]
    omega_using []
  obtain e₅ : ∀ d, s₅.gpr .t1 + BitVec.ofNat 64 d = off base (d + 8 * (7 * j / 64)) := by
    intro d
    rw [e₅', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  obtain r₅ : Rest [.t0, .t1] s s₅ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain inr : ∀ d, d + 8 ≤ 8192 → InRegions (s₅.rd ++ s₅.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ (r₅.wr ▸ hw.wr), Offset.contains_base base hd (by omega_using [hd])⟩
  obtain alg : ∀ d, d % 8 = 0 → d < 8192 → (off base d).toNat % 8 = 0 := fun d h8 hd => by
    simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hal, h8]
  refine VG.Proof.Weierstrass.RISCV64.wp_ldAt (by omega_using []) (e₅ 3376) (alg _ (by omega_using []) (by omega_using [hj])) (inr _ (by omega_using [hj]))
    fun s₆ u₆ => ?_
  refine VG.Proof.Weierstrass.RISCV64.wp_ldAt (by omega_using []) (by rw [u₆.other .t1 (by decide)]; exact e₅ 3384)
    (alg _ (by omega_using []) (by omega_using [hj]))
    (by rw [u₆.rd, u₆.wr]; exact inr _ (by omega_using [hj])) fun s₇ u₇ => ?_
  refine wp_srlReg fun s₈ u₈ => wp_xori (by decide) fun s₉ u₉ => wp_sll (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_sllReg fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => wp_andi (by decide) fun s₁₃ u₁₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t0₈ : s₈.gpr .t0 = BitVec.ofNat 64 (7 * j) := by
      rw [u₈.other .t0 (by decide), u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide),
        u₄.other .t0 (by decide), u₃.other .t0 (by decide)]
      exact e₂
    obtain sh : (s₉.gpr .t4).toNat % 64 = 63 - 7 * j % 64 := by
      rw [u₉.gpr, t0₈]; exact shamt_eq j hj
    obtain sh7 : (s₇.gpr .t0).toNat % 64 = 7 * j % 64 := by
      rw [u₇.other .t0 (by decide), u₆.other .t0 (by decide), u₅.other .t0 (by decide), u₄.other .t0 (by decide),
        u₃.other .t0 (by decide), e₂, BitVec.toNat_ofNat]
      omega_using []
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₁.other .t2 (by decide), u₁₀.gpr, u₁₀.other .t2 (by decide),
      u₁₀.other .t4 (by decide), sh, u₉.other .t2 (by decide), u₉.other .t3 (by decide), u₈.gpr,
      u₈.other .t3 (by decide), sh7, u₇.gpr, u₇.other .t2 (by decide), u₆.gpr, u₆.mem, m₅]
    refine window_bits fun i hi => ?_
    obtain e5 : wordsVal s.mem base 3376 10 = wordsVal s.mem base 3376 9 := by
      rw [wordsVal_succ_top s.mem base 3376 9, show 3376 + 8 * 9 = 3376 + 72 from rfl, hz]; simp
    rw [← e5, ← testBit_wordsVal s.mem base 10 3376 (7 * j + i) (by omega_using [hj, hi])]
    by_cases h : 7 * j % 64 + i < 64
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 by omega_using [h], show (7 * j + i) % 64 = 7 * j % 64 + i by omega_using [h],
        ← BitVec.testBit_toNat, show 3376 + 8 * (7 * j / 64) = 3376 + 8 * (7 * j / 64) from rfl]
    · simp only [h, ↓reduceIte]
      rw [show (7 * j + i) / 64 = 7 * j / 64 + 1 by omega_using [hi, h],
        show (7 * j + i) % 64 = 7 * j % 64 + i - 64 by omega_using [hi, h], ← BitVec.testBit_toNat,
        show 3376 + 8 * (7 * j / 64 + 1) = 3384 + 8 * (7 * j / 64) by omega_using []]
  · exact (r₅.mono (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
      ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
        ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans (u₁₃.rest (by decide)))))))))
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]


/-! ## The digit and the masks -/

theorem ms_eq : MS = 3456 := rfl
theorem mz_eq : MZ = 3464 := rfl

/-- The digit of the window `v` in `t2`: the masks to `MS` and `MZ`, the
entry's number in `t2`. -/
theorem digit_ok {s : State} {base : Addr} (hw : WsReg s base) {v : Nat} (hv : v < 128)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 v) :
    WP isa (.block digit) s fun s' =>
      (magH 64 v ≠ 0 → (s'.gpr .t2).toNat = magH 64 v - 1) ∧
      word s'.mem base MS = maskOf (decide (v < 64)) ∧
      word s'.mem base MZ = maskOf (decide (magH 64 v = 0)) ∧
      Outside base MS 16 s.mem s'.mem ∧ Rest [.t2, .t3, .t4] s s' := by
  have hn := hw.nowrap
  obtain ⟨f1, f2, f3⟩ := digit_facts v hv
  rw [digit, ms_eq, mz_eq]
  simp only [List.cons_append, List.nil_append]
  rw [← List.append_nil (Impl.Weierstrass.RISCV64.sdAt .t4 _ _)]
  refine wp_subi (imm := 64) (by decide) fun s₁ u₁ => wp_sra (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_sub fun s₄ u₄ => wp_subi (imm := 1) (by decide) fun s₅ u₅ => wp_sra (by decide) fun s₆ u₆ => ?_
  obtain r₆ : Rest [.t2, .t3, .t4] s s₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  obtain e3 : s₆.gpr .t3 = (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63 := by
    rw [u₆.other .t3 (by decide), u₅.other .t3 (by decide), u₄.other .t3 (by decide), u₃.other .t3 (by decide),
      u₂.gpr, u₁.gpr, h2]
  obtain e5 : s₅.gpr .t2 = (((BitVec.ofNat 64 v - BitVec.ofNat 64 64) ^^^
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) -
      (BitVec.ofNat 64 v - BitVec.ofNat 64 64).sshiftRight 63) - BitVec.ofNat 64 1 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .t3 (by decide), u₂.gpr, u₂.other .t2 (by decide), u₁.gpr, h2]
  obtain e2 : s₆.gpr .t2 = s₅.gpr .t2 := u₆.other .t2 (by decide)
  obtain e4 : s₆.gpr .t4 = maskOf (decide (magH 64 v = 0)) := by rw [u₆.gpr, e5]; exact f2
  obtain hw₆ : WsReg s₆ base := hw.of_rest r₆
  refine sdAt_ws hw₆ (by decide) (d := 3456) (by decide) (by decide) fun s₇ u₇ => ?_
  refine sdAt_ws (hw₆.of_rest (u₇.rest [])) (by decide) (d := 3464) (by decide) (by decide) fun s₈ u₈ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hz; rw [u₈.gpr, u₇.gpr, e2, e5]; exact f3 hz
  · rw [u₈.mem, (writeW_outside s₇.mem base (d := 3464) (s₇.gpr .t4) (by omega_using [])).word (d := 3456) (by omega_using [])
      (by omega_using []), u₇.mem, word_writeW_self, e3, f1]
  · rw [u₈.mem, word_writeW_self, u₇.gpr, e4]
  · intro x hx
    rw [u₈.mem, writeW_outside s₇.mem base (d := 3464) (s₇.gpr .t4) (by omega_using []) x (by omega_using [hx]), u₇.mem,
      writeW_outside s₆.mem base (d := 3456) (s₆.gpr .t3) (by omega_using []) x (by omega_using [hx])]
    rw [show s₆.mem = s.mem by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
  · exact r₆.trans ((u₇.rest _).trans (u₈.rest _))

/-- The row: `a0 = s4 + 9216 j`. -/
theorem row_ok {s : State} {j : Nat} (hj : j < 83) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block row) s fun s' =>
      s'.gpr .a0 = s.gpr .s4 + BitVec.ofNat 64 (9216 * j) ∧ Rest [.t0, .t1, .a0] s s' ∧ s'.mem = s.mem := by
  rw [row]
  refine wp_sll (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other .s4 (by decide), u₂.other .s4 (by decide), u₁.other .s4 (by decide), u₃.gpr,
      u₂.other .t0 (by decide), u₁.gpr, u₂.gpr, u₁.other .s1 (by decide), h1]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have := hj
    omega_using []
  · exact (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      (u₄.rest (by decide))))
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end

/-! ## The entry -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont
open VG.Impl.Ecdsa.RISCV64.WindowU (c)
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg copy_ok sel_ok ld_ws)
open VG.Proof.Weierstrass (Unch combWin magH)
open VG.Proof.X25519.RISCV64 (Rest)

/-- The words of P-521's tables. -/
abbrev tabWords : List (BitVec 64) := Impl.Weierstrass.tcombWords 9 (2 ^ 576) Spec.P521.curve.p Impl.P521.p521Comb7

/-- What the comb needs of the table at `T`, for the working space at `base`. -/
structure TabOk (s : State) (base T : Addr) : Prop where
  held : ∀ i < 95616, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = tabWords.getD i 0
  al : T.toNat % 64 = 0
  rd : (⟨T, 764928⟩ : Region) ∈ s.rd
  fit : T.toNat + 764928 ≤ 2 ^ 64
  far : ∀ d < 764928, 8192 ≤ ofs base (T + BitVec.ofNat 64 d)

/-- Memory changed only in the working space keeps the table. -/
theorem TabOk.of_mem {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabOk s' base T where
  held i hi := by
    rw [← h.held i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega_using [hi, hb])
  al := h.al
  rd := hrd ▸ h.rd
  fit := h.fit
  far := h.far

theorem TabOk.of_outside {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd) {o n : Nat}
    (hon : o + n ≤ 8192) (ho : Outside base o n s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => ho x (.inr (by omega_using [hon, hx]))

/-- The address of quadword `q` of entry `e` of row `j`. -/
theorem entAddr_row (T : Addr) (j q e : Nat) :
    entAddr (T + BitVec.ofNat 64 (9216 * j)) q e = T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 9)) + e * (2 * 9) + q)) := by
  rw [entAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  omega_using []

/-- What the scan of row `j` needs. -/
theorem rowOk_of_tab {s : State} {base T : Addr} (h : TabOk s base T) {j q : Nat} (hj : j < 83) (hq : q < 18) :
    RowOk s (T + BitVec.ofNat 64 (9216 * j)) q := by
    intro e he
    rw [entAddr_row]
    obtain hd : 8 * (j * (64 * (2 * 9)) + e * (2 * 9) + q) + 8 ≤ 764928 := by omega_using [hj, hq, he]
    refine ⟨?_, ⟨_, List.mem_append_left _ h.rd, Offset.contains_base T hd (by omega_using [hj, hq, he])⟩⟩
    have hf := h.fit
    obtain e : (T + BitVec.ofNat 64 (8 * (j * (64 * (2 * 9)) + e * (2 * 9) + q))).toNat =
        T.toNat + 8 * (j * (64 * (2 * 9)) + e * (2 * 9) + q) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * (j * (64 * (2 * 9)) + e * (2 * 9) + q) <
        2 ^ 64 by omega_using [hj, hq, he]), Nat.mod_eq_of_lt (by omega_using [hj, hq, he, hf])]
    have := h.al
    rw [e]
    omega_using [this]

/-- The `2 n` quadwords of entry `t % 64` of row `j` to `D`. -/
theorem scans_ok {base T : Addr} {j t : Nat} (hj : j < 83) : ∀ n ≤ 18, ∀ {s : State}, WsReg s base → TabOk s base T →
    s.gpr .a0 = T + BitVec.ofNat 64 (9216 * j) →
    (∀ c < 6, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    WP isa (.block ((List.range n).flatMap scanWord)) s fun s' =>
      (∀ q < n, word s'.mem base (1288 + 8 * q) = s.mem.readW (entAddr (s.gpr .a0) q (t % 64)) 64) ∧
      Outside base 1288 (8 * n) s.mem s'.mem ∧ Keep (treeRegs ++ ([.a7] : List Reg)) s s'
  | 0, _, s, _, _, _, _ => WP.block_nil ⟨fun q hq => absurd hq (by omega_using []), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn, s, hw, hT, h0, hm => by
    have hnw := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scans_ok hj n (by omega_using [hn]) hw hT h0 hm) fun s₁ ⟨v₁, O₁, k₁⟩ => ?_)
    obtain ne : ∀ r ∈ [Reg.s0, .a0, .a1, .a2, .a3, .a4, .a5, .a6], r ∉ treeRegs ++ ([.a7] : List Reg) := by decide
    obtain e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (ne _ (by simp))
    obtain hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (ne _ (by simp)), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
    obtain hT₁ : TabOk s₁ base T := hT.of_outside k₁.2.1 (by omega_using [hn]) O₁
    obtain hm₁ : ∀ c < 6, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
      rw [k₁.gpr (by
        have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega_using [hc]
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      exact hm c hc
    refine WP.mono (scanWord_ok hw₁ (q := n) (by omega_using [hn]) hm₁
      (by rw [e0, h0]; exact rowOk_of_tab hT₁ hj (by omega_using [hn]))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [e0] at m₂
    -- The entry's quadword, as the table held it.
    obtain hr : s₁.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 = s.mem.readW (entAddr (s.gpr .a0) n (t % 64)) 64 := by
      refine Mem.readW_congr fun b hb => O₁ _ (.inr ?_)
      rw [h0, entAddr_row, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      have := hT.far (8 * (j * (64 * (2 * 9)) + t % 64 * (2 * 9) + n) + b) (by
        have := Nat.mod_lt t (show 64 > 0 by decide); omega_using [hj, hn, hb])
      omega
    obtain O₂ : Outside base (1288 + 8 * n) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega_using [hn])
    refine ⟨fun q hq => ?_, ?_, k₁.trans k₂ |>.mono (fun r hr => (List.mem_append.mp hr).elim id id)⟩
    · by_cases hqn : q < n
      · rw [O₂.word (by omega_using [hqn]) (by omega_using [hn, hq]), v₁ q hqn]
      · obtain rfl : q = n := by omega_using [hq, hqn]
        rw [m₂, word_writeW_self, hr]
    · exact (O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))


/-! ## The entry's words -/

theorem comb7_len : Impl.P521.p521Comb7.length = 83 := Proof.P521.p521Comb7_length

theorem comb7_lenH : ∀ j < 83, (Impl.P521.p521Comb7.getD j []).length = 64 := Proof.P521.p521Comb7_rows

/-- `x R mod p`. -/
abbrev montP (x : Nat) : Nat := x * 2 ^ 576 % Spec.P521.curve.p

/-- Entry `e` of row `j`. -/
abbrev entOf (j e : Nat) : Nat × Nat := Proof.Weierstrass.combAt Impl.P521.p521Comb7 j e

/-- Quadword `q` of entry `e` of row `j`: the words of `x`, then of `y`, in
Montgomery's form. -/
theorem entry_word {s : State} {base T : Addr} (hT : TabOk s base T) {j e q : Nat} (hj : j < 83) (he : e < 64)
    (hq : q < 18) :
    s.mem.readW (entAddr (T + BitVec.ofNat 64 (9216 * j)) q e) 64 =
      if q < 9 then Impl.Weierstrass.wordOf (montP (entOf j e).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j e).2) (q - 9) := by
  rw [entAddr_row, hT.held _ (by omega_using [hj, he, hq])]
  exact Proof.Weierstrass.tcombWords_getD comb7_len comb7_lenH hj he hq


/-- The scalar: the copy of `k`. -/
abbrev kOf (m : Mem) (base : Addr) : Nat := wordsVal m base 3376 9

/-- The registers the entry's selection writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- Memory but the working space keeps the table. -/
theorem TabOk.of_unch {s s' : State} {base T : Addr} (h : TabOk s base T) (hrd : s'.rd = s.rd)
    {W : List (Nat × Nat)} (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) (hu : Unch base W s.mem s'.mem) : TabOk s' base T :=
  h.of_mem hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega_using [hx, this]

/-- The entry of digit `j`, in Montgomery's form, in `D`'s first two slots:
entry `m - 1` of row `j` for the magnitude `m ≠ 0` of the digit (some entry
for `m = 0`), and the masks of the digit's sign and of `m = 0` at `MS` and
`MZ`. -/
theorem select_ok {s : State} {base T : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 83)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (h2 : s.gpr .s4 = T) (hT : TabOk s base T)
    (hz : word s.mem base (3376 + 72) = 0) :
    WP isa (.block select) s fun s' =>
      (∃ e < 64, (magH 64 (combWin 7 (kOf s.mem base) j) ≠ 0 → e = magH 64 (combWin 7 (kOf s.mem base) j) - 1) ∧
        wordsVal s'.mem base 1288 9 = montP (entOf j e).1 ∧ wordsVal s'.mem base 1360 9 = montP (entOf j e).2) ∧
      word s'.mem base 3456 = maskOf (decide (combWin 7 (kOf s.mem base) j < 64)) ∧
      word s'.mem base 3464 = maskOf (decide (magH 64 (combWin 7 (kOf s.mem base) j) = 0)) ∧
      Unch base [(1288, 144), (3456, 16)] s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  generalize hv : combWin 7 (kOf s.mem base) j = v
  obtain hv128 : v < 128 := hv ▸ Proof.Weierstrass.combWin_lt 7 _ j
  generalize hg : magH 64 v = mg
  obtain hmg : mg ≤ 64 := hg ▸ Proof.Weierstrass.magH_le (by omega_using [hv128])
  rw [select]
  simp only [List.append_assoc]
  -- The window.
  refine WP.block_append (WP.mono (window_ok hw hj h1 (by rw [kc_eq]; exact hz)) fun s₁ ⟨t₁, r₁, m₁⟩ => ?_)
  rw [kc_eq, show wordsVal s.mem base 3376 9 = kOf s.mem base from rfl, hv] at t₁
  obtain hw₁ := hw.of_rest r₁
  -- The digit.
  refine WP.block_append (WP.mono (digit_ok hw₁ hv128 t₁) fun s₂ ⟨t₂, pt₂, pz₂, O₂, r₂⟩ => ?_)
  rw [hg] at t₂ pz₂
  rw [ms_eq] at pt₂ O₂
  rw [mz_eq] at pz₂
  obtain hw₂ := hw₁.of_rest r₂
  -- The masks.
  refine WP.block_append (WP.mono masks_ok fun s₃ ⟨v₃, r₃, m₃⟩ => ?_)
  -- The row.
  obtain e1 : s₃.gpr .s1 = BitVec.ofNat 64 j := by
    rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h1]
  obtain e2 : s₃.gpr .s4 = T := by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (row_ok hj e1) fun s₄ ⟨a₄, r₄, m₄⟩ => ?_)
  rw [e2] at a₄
  obtain hw₄ := (hw₂.of_rest r₃).of_rest r₄
  obtain U₄ : Unch base [(3456, 16)] s.mem s₄.mem := by
    rw [m₄, m₃]; rw [m₁] at O₂; exact O₂.unch
  obtain hT₄ : TabOk s₄ base T :=
    hT.of_unch (by rw [r₄.rd, r₃.rd, r₂.rd, r₁.rd]) (by simp) U₄
  obtain hm₄ : ∀ c < 6, s₄.gpr (maskReg c) = maskOf ((s₂.gpr .t2).toNat.testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega_using [hc]
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), v₃ c hc, BitVec.testBit_toNat]
  -- The scans.
  refine WP.mono (WP.rdwr (scans_ok hj 18 (Nat.le_refl _) hw₄ hT₄ a₄ hm₄))
    fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  obtain r₅ : Rest (treeRegs ++ ([.a7] : List Reg)) s₄ s₅ := ⟨k₅.1, rd₅, wr₅, sp₅⟩
  obtain he : (s₂.gpr .t2).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain hD : ∀ q < 18, word s₅.mem base (1288 + 8 * q) =
      if q < 9 then Impl.Weierstrass.wordOf (montP (entOf j ((s₂.gpr .t2).toNat % 64)).1) q
      else Impl.Weierstrass.wordOf (montP (entOf j ((s₂.gpr .t2).toNat % 64)).2) (q - 9) := by
    intro q hq
    rw [v₅ q hq, a₄, entry_word hT₄ hj he hq]
  obtain hpx : montP (entOf j ((s₂.gpr .t2).toNat % 64)).1 < 2 ^ 576 :=
    Nat.lt_trans (Nat.mod_lt _ (show 0 < Spec.P521.curve.p by decide)) (by decide)
  obtain hpy : montP (entOf j ((s₂.gpr .t2).toNat % 64)).2 < 2 ^ 576 :=
    Nat.lt_trans (Nat.mod_lt _ (show 0 < Spec.P521.curve.p by decide)) (by decide)
  refine ⟨⟨(s₂.gpr .t2).toNat % 64, he, fun h0 => by rw [t₂ h0]; omega_using [hmg], ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ hpx fun i hi => ?_
    rw [hD i (by omega_using [hi])]; simp only [show i < 9 from hi, ↓reduceIte]; rfl
  · refine Proof.Weierstrass.wordsVal_of_shifts _ _ _ _ _ hpy fun i hi => ?_
    rw [show 1360 + 8 * i = 1288 + 8 * (i + 9) by omega_using [], hD (i + 9) (by omega_using [hi])]
    simp only [show ¬ i + 9 < 9 by omega_using [], ↓reduceIte, Nat.add_sub_cancel]; rfl
  · rw [O₅.word (by omega_using []) (by omega_using []), m₄, m₃, pt₂]
  · rw [O₅.word (by omega_using []) (by omega_using []), m₄, m₃, pz₂]
  · exact (U₄.trans O₅.unch).cover (by decide)
  · exact (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans
      ((r₄.mono (by decide)).trans (r₅.mono (by decide)))))

end

/-! ## The entry in limbs -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight uv wv usubCall_ok uf_sub uv_le)
open VG.Proof.Ecdsa.RISCV64.P521.Window (PtOk ev addPt_ok copyPt_ok tight_zero uf_zero)
open VG.Impl.Ecdsa.RISCV64.WindowU (c F addPt toU UONE UC)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- What the entry's conversion writes: `D`, `T`'s first slot and the
functions' own working space. -/
abbrev entryW : List (Nat × Nat) := [(1288, 216), (1504, 72), (7616, 576)]

theorem montP_lt (x : Nat) : montP x < 2 ^ 522 :=
  Nat.lt_trans (Nat.mod_lt _ (show 0 < Spec.P521.curve.p by decide)) (by decide)

/-- The limbs' element, times `2⁴⁶⁶`, of a number in Montgomery's form. -/
theorem ofNat_montP (x : Nat) : (Fin.ofNat W.p (montP x * 2 ^ 466) : Fe W) = Fin.ofNat W.p x := by
  rw [show montP x = 2 ^ 576 * x % W.p by rw [montP, Nat.mul_comm]]; exact ofNat_in x

/-- The entry in `D`'s first two slots, in Montgomery's form, to limbs, with
`Z = 1`; `(0 : 1 : 0)` for a zero digit, and `y` negated for a negative one,
by the masks at `MZ` and `MS`. -/
theorem entry_ok {s : State} {base : Addr} (hw : WsReg s base) (hK : Window.KC base s)
    (hCt : Tight (wv base s 3808)) (hCv : uv (wv base s 3808) = 2 ^ 466)
    {x y : Nat} {c0 cs : Bool} (hx : wv base s 1288 = montP x) (hy : wv base s 1360 = montP y)
    (hms : word s.mem base 3456 = maskOf cs) (hmz : word s.mem base 3464 = maskOf c0) :
    WP isa entry s fun s' => Kp s s' ∧ Unch base entryW s.mem s'.mem ∧
      Tight (wv base s' 1288) ∧ Tight (wv base s' 1360) ∧ Tight (wv base s' 1432) ∧
      ev base s' 1288 = (if c0 then 0 else Fin.ofNat W.p x) ∧
      ev base s' 1360 = (if cs then -(if c0 then 1 else Fin.ofNat W.p y) else (if c0 then 1 else Fin.ofNat W.p y)) ∧
      ev base s' 1432 = (if c0 then 0 else 1) := by
  have hn := hw.nowrap
  obtain wm : ∀ {t t' : State}, t'.mem = t.mem → ∀ d, wv base t' d = wv base t d := fun h d => by
    show wordsVal _ base d 9 = wordsVal _ base d 9; rw [h]
  have hz : wv base s 280 = 0 := hK.zero
  have hot : Tight (wv base s 3736) := hK.to
  have hov : uf (wv base s 3736) = 1 := hK.vo
  show WP isa (.seq (toU 1288 1288) (.seq (toU 1360 1360) (.seq (.block (ldAt .a7 .s0 3464 ++ sel 9 1288 1288 280 ++
    sel 9 1360 1360 3736 ++ sel 9 1432 3736 280)) (.seq (subCall F 1504 280 1360)
      (.block (ldAt .a7 .s0 3456 ++ sel 9 1360 1360 1504)))))) s _
  -- `x` to limbs.
  refine WP.seq (WP.mono (toU_ok hw (o := 1288) (a := 1288) (by decide) (by decide) (by decide)
    (by rw [hx]; exact montP_lt x) hCt hCv) fun s₁ ⟨k₁, t₁, v₁⟩ => ?_)
  rw [hx, ofNat_montP] at v₁
  obtain hw₁ := hw.of_kp k₁.kp
  obtain e₁ : ∀ d, d + 72 ≤ 1288 ∨ 1360 ≤ d → d + 72 ≤ 7616 → wv base s₁ d = wv base s d :=
    fun d h h' => keepR_wv k₁ (by simp only [List.mem_singleton, forall_eq]; omega_using [h]) h'
  obtain U₁ : Unch base [(1288, 72), (7616, 576)] s.mem s₁.mem := fun a ha => k₁.mem a ha
  -- `y` to limbs.
  refine WP.seq (WP.mono (toU_ok hw₁ (o := 1360) (a := 1360) (by decide) (by decide) (by decide)
    (by rw [e₁ _ (by decide) (by decide), hy]; exact montP_lt y)
    (by rw [e₁ _ (by decide) (by decide)]; exact hCt) (by rw [e₁ _ (by decide) (by decide)]; exact hCv))
    fun s₂ ⟨k₂, t₂, v₂⟩ => ?_)
  rw [e₁ _ (by decide) (by decide), hy, ofNat_montP] at v₂
  obtain hw₂ := hw₁.of_kp k₂.kp
  obtain e₂ : ∀ d, d + 72 ≤ 1360 ∨ 1432 ≤ d → d + 72 ≤ 7616 → wv base s₂ d = wv base s₁ d :=
    fun d h h' => keepR_wv k₂ (by simp only [List.mem_singleton, forall_eq]; omega_using [h]) h'
  obtain U₂ : Unch base [(1360, 72), (7616, 576)] s₁.mem s₂.mem := fun a ha => k₂.mem a ha
  obtain U₁₂ := U₁.trans U₂
  obtain z₂ : wv base s₂ 280 = 0 := by rw [e₂ _ (by decide) (by decide), e₁ _ (by decide) (by decide), hz]
  obtain o₂ : wv base s₂ 3736 = wv base s 3736 := by rw [e₂ _ (by decide) (by decide), e₁ _ (by decide) (by decide)]
  obtain x₂ : wv base s₂ 1288 = wv base s₁ 1288 := e₂ _ (by decide) (by decide)
  -- A zero digit's point.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine ldAt_ws hw₂ (d := 3464) (by decide) (by decide) fun s₃ u₃ => ?_
  obtain a7₃ : s₃.gpr .a7 = maskOf c0 := by
    rw [u₃.gpr, U₁₂.word (by decide) (by decide), hmz]
  obtain hw₃ := hw₂.of_rest (u₃.rest (ws := [.a7]) (by decide))
  refine WP.block_append (WP.mono (sel_ok c0 9 hw₃ a7₃ (o := 1288) (a := 1288) (b := 280)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, r₄, O₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  refine WP.block_append (WP.mono (sel_ok c0 9 hw₄ (by rw [r₄.gpr _ (by decide)]; exact a7₃)
    (o := 1360) (a := 1360) (b := 3736)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨e₅, r₅, O₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine WP.mono (sel_ok c0 9 hw₅ (by rw [r₅.gpr _ (by decide), r₄.gpr _ (by decide)]; exact a7₃)
    (o := 1432) (a := 3736) (b := 280)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨e₆, r₆, O₆⟩ => ?_
  obtain hw₆ := hw₅.of_rest r₆
  obtain m₃ : ∀ d, wv base s₃ d = wv base s₂ d := wm u₃.mem
  obtain o₄ : ∀ d, d + 72 ≤ 1288 ∨ 1360 ≤ d → d + 72 ≤ 8192 → wv base s₄ d = wv base s₃ d := fun d h h' =>
    O₄.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain o₅ : ∀ d, d + 72 ≤ 1360 ∨ 1432 ≤ d → d + 72 ≤ 8192 → wv base s₅ d = wv base s₄ d := fun d h h' =>
    O₅.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain o₆ : ∀ d, d + 72 ≤ 1432 ∨ 1504 ≤ d → d + 72 ≤ 8192 → wv base s₆ d = wv base s₅ d := fun d h h' =>
    O₆.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain X₆ : wv base s₆ 1288 = if c0 then 0 else wv base s₁ 1288 := by
    rw [o₆ _ (by decide) (by decide), o₅ _ (by decide) (by decide),
      show wv base s₄ 1288 = if c0 then wv base s₃ 280 else wv base s₃ 1288 from e₄, m₃, m₃, z₂, x₂]
  obtain Y₆ : wv base s₆ 1360 = if c0 then wv base s 3736 else wv base s₂ 1360 := by
    rw [o₆ _ (by decide) (by decide),
      show wv base s₅ 1360 = if c0 then wv base s₄ 3736 else wv base s₄ 1360 from e₅,
      o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), m₃, m₃, o₂]
  obtain Z₆ : wv base s₆ 1432 = if c0 then 0 else wv base s 3736 := by
    rw [show wv base s₆ 1432 = if c0 then wv base s₅ 280 else wv base s₅ 3736 from e₆,
      o₅ _ (by decide) (by decide), o₅ _ (by decide) (by decide), o₄ _ (by decide) (by decide),
      o₄ _ (by decide) (by decide), m₃, m₃, z₂, o₂]
  obtain z₆ : wv base s₆ 280 = 0 := by
    rw [o₆ _ (by decide) (by decide), o₅ _ (by decide) (by decide), o₄ _ (by decide) (by decide), m₃, z₂]
  obtain tY₆ : Tight (wv base s₆ 1360) := by rw [Y₆]; cases c0 <;> [exact t₂; exact hot]
  obtain vY₆ : uf (wv base s₆ 1360) = if c0 then 1 else Fin.ofNat W.p y := by
    rw [Y₆]; cases c0 <;> [exact v₂; exact hov]
  -- `-y`.
  refine WP.seq (WP.mono (usubCall_ok hw₆ (o := 1504) (a := 280) (b := 1360) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [z₆]; exact tight_zero) tY₆) fun s₇ ⟨K₇, t₇, v₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp K₇.kp
  obtain k₇ := KeepR.of_call K₇
  obtain e₇ : ∀ d, d + 72 ≤ 1504 ∨ 1576 ≤ d → d + 72 ≤ 7616 → wv base s₇ d = wv base s₆ d :=
    fun d h h' => keepR_wv k₇ (by simp only [List.mem_singleton, forall_eq]; omega_using [h]) h'
  obtain U₇ : Unch base [(1504, 72), (7616, 576)] s₆.mem s₇.mem := fun a ha => k₇.mem a ha
  obtain vT : uf (wv base s₇ 1504) = -(if c0 then 1 else Fin.ofNat W.p y) := by
    have := uf_sub (uv_le tY₆) v₇
    rw [z₆, uf_zero, vY₆] at this
    rw [this]; grind
  -- The sign.
  obtain U₆ : Unch base [(1288, 72), (7616, 576), (1360, 72), (7616, 576), (1288, 72), (1360, 72), (1432, 72)]
      s.mem s₆.mem := by
    obtain h := ((U₁₂.trans (show Unch base [(1288, 8 * 9)] s₂.mem s₄.mem by
      rw [← u₃.mem]; exact O₄.unch)).trans O₅.unch).trans O₆.unch
    exact h
  refine ldAt_ws hw₇ (d := 3456) (by decide) (by decide) fun s₈ u₈ => ?_
  obtain a7₈ : s₈.gpr .a7 = maskOf cs := by
    rw [u₈.gpr, U₇.word (by decide) (by decide), U₆.word (by decide) (by decide), hms]
  obtain hw₈ := hw₇.of_rest (u₈.rest (ws := [.a7]) (by decide))
  refine WP.mono (sel_ok cs 9 hw₈ a7₈ (o := 1360) (a := 1360) (b := 1504)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₉ ⟨e₉, r₉, O₉⟩ => ?_
  obtain m₈ : ∀ d, wv base s₈ d = wv base s₇ d := wm u₈.mem
  obtain o₉ : ∀ d, d + 72 ≤ 1360 ∨ 1432 ≤ d → d + 72 ≤ 8192 → wv base s₉ d = wv base s₈ d := fun d h h' =>
    O₉.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain X₉ : wv base s₉ 1288 = if c0 then 0 else wv base s₁ 1288 := by
    rw [o₉ _ (by decide) (by decide), m₈, e₇ _ (by decide) (by decide), X₆]
  obtain Z₉ : wv base s₉ 1432 = if c0 then 0 else wv base s 3736 := by
    rw [o₉ _ (by decide) (by decide), m₈, e₇ _ (by decide) (by decide), Z₆]
  obtain Y₉ : wv base s₉ 1360 = if cs then wv base s₇ 1504 else wv base s₆ 1360 := by
    rw [show wv base s₉ 1360 = if cs then wv base s₈ 1504 else wv base s₈ 1360 from e₉, m₈, m₈,
      e₇ 1360 (by decide) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact k₁.kp.trans (k₂.kp.trans ((Kp.of_rest (((u₃.rest (ws := [.a7]) (by decide)).mono (by decide)).trans
      ((r₄.mono (by decide)).trans ((r₅.mono (by decide)).trans (r₆.mono (by decide))))) (ws := [.a7, .t0, .t1])).trans
      (K₇.kp.trans (Kp.of_rest (((u₈.rest (ws := [.a7]) (by decide)).mono (by decide)).trans (r₉.mono (by decide)))
        (ws := [.a7, .t0, .t1])))))
  · exact ((U₆.trans U₇).trans (show Unch base [(1360, 8 * 9)] s₇.mem s₉.mem by
      rw [← u₈.mem]; exact O₉.unch)).cover (by decide)
  · rw [X₉]; cases c0 <;> [exact t₁; exact tight_zero]
  · rw [Y₉]; cases cs <;> [exact tY₆; exact t₇]
  · rw [Z₉]; cases c0 <;> [exact hot; exact tight_zero]
  · show uf (wv base s₉ 1288) = _
    rw [X₉]; cases c0 <;> [exact v₁; exact uf_zero]
  · show uf (wv base s₉ 1360) = _
    rw [Y₉]; cases cs <;> [exact vY₆; exact vT]
  · show uf (wv base s₉ 1432) = _
    rw [Z₉]; cases c0 <;> [exact hov; exact uf_zero]

end

/-! ## A step -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight uv wv)
open VG.Proof.Ecdsa.RISCV64.P521.Window (PtOk ev addPt_ok copyPt_ok tight_zero uf_zero)
open VG.Impl.Ecdsa.RISCV64.WindowU (c F addPt toU UONE UA UB UC convIn)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The entry of digit `i`, `y` negated for a negative digit, represents the
digit's signed point: entry `e` of row `i`, the digit's magnitude less one
(any entry for a zero digit). -/
theorem entry_rep (hL : Law W) {k i : Nat} (hi : i < 83) {e : Nat}
    (he : magH 64 (combWin 7 k i) ≠ 0 → e = magH 64 (combWin 7 k i) - 1) :
    Rep W (if magH 64 (combWin 7 k i) = 0 then 0 else Fin.ofNat W.p (entOf i e).1)
      (if combWin 7 k i < 64 then -(if magH 64 (combWin 7 k i) = 0 then 1 else Fin.ofNat W.p (entOf i e).2)
        else (if magH 64 (combWin 7 k i) = 0 then 1 else Fin.ofNat W.p (entOf i e).2))
      (if magH 64 (combWin 7 k i) = 0 then 0 else 1)
      (signedPtW W 7 k i) := by
  obtain hC := VG.Proof.P521.combOk7 hL
  obtain hv := combWin_lt 7 k i
  unfold signedPtW
  generalize combWin 7 k i = v at hv he ⊢
  simp only [show 2 ^ (7 - 1) = 64 from rfl]
  by_cases h64 : 64 ≤ v
  · have hmg : magH 64 v = v - 64 := by unfold magH; simp [h64]
    rw [hmg] at he ⊢
    simp only [h64, ↓reduceIte, show ¬ v < 64 by omega_using [h64]]
    by_cases h0 : v - 64 = 0
    · simp only [h0, ↓reduceIte, combPtW, Nat.zero_mul, Window.mul_zero']
      exact rep_infinity' hL
    · obtain ⟨m, hm⟩ : ∃ m, v - 64 = m + 1 := ⟨v - 64 - 1, by omega_using [h0]⟩
      obtain rfl : e = m := by rw [he h0, hm]; rfl
      simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, combPtW]
      rw [hC.entry i hi e (by simp; omega_using [hv, hm])]
      exact rep_affine' hL _ _
  · have hmg : magH 64 v = 64 - v := by unfold magH; simp [h64]
    obtain ⟨m, hm⟩ : ∃ m, 64 - v = m + 1 := ⟨64 - v - 1, by omega_using [h64]⟩
    rw [hmg] at he ⊢
    obtain rfl : e = m := by rw [he (by omega_using [hm]), hm]; rfl
    simp only [h64, ↓reduceIte, show v < 64 by omega_using [h64], hm, Nat.add_one_ne_zero, combPtW]
    rw [hC.entry i hi e (by simp; omega_using [hm])]
    exact rep_affine' hL _ _

theorem signed_onCurve (hL : Law W) (k i : Nat) : Spec.Weierstrass.onCurve W (signedPtW W 7 k i) = true := by
  unfold signedPtW combPtW
  split
  · exact hL.onCurve_mul VG.Proof.P521.onCurve_G _
  · exact onCurve_negPt (hL.onCurve_mul VG.Proof.P521.onCurve_G _)

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure CombPre (base T : Addr) (s₀ : State) : Prop where
  s4 : s₀.gpr .s4 = T
  kz : word s₀.mem base (3376 + 72) = 0
  kc : Window.KC base s₀
  ct : Tight (wv base s₀ 3808)
  cv : uv (wv base s₀ 3808) = 2 ^ 466

/-- What the steps write: `R`, `D`, `T` and the temporaries, the masks, and
the functions' own working space. -/
abbrev stepW : List (Nat × Nat) := [(1072, 1080), (3456, 16), (7616, 576)]

/-- The loop's invariant at `s1 = j`: `R` represents `[combEW j]G`, for the
scalar the start holds. -/
structure CombInv (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  tab : TabOk s base T
  rep : PtOk base s (c.pt RX RY RZ)
    (Spec.Weierstrass.mul (combEW 7 (kOf s₀.mem base) 83 j) (Spec.Weierstrass.G W))

/-- A step: from `[combEW j]G` to `[combEW (j - 1)]G`. -/
theorem step_ok (hL : Law W) {base T : Addr} {s₀ : State} (hP : CombPre base T s₀) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ 83) {s : State} (hI : CombInv base T s₀ s j) :
    WP isa step s fun s' => CombInv base T s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  obtain uS : ∀ d, d + 72 ≤ 1072 ∨ 2152 ≤ d → d + 72 ≤ 3456 ∨ 3472 ≤ d → d + 72 ≤ 7616 →
      wv base s d = wv base s₀ d := fun d h1 h2 h3 =>
    hI.unch.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2, h3])
      (by omega_using [h3])
  obtain hk : kOf s.mem base = kOf s₀.mem base := uS 3376 (.inr (by decide)) (.inl (by decide)) (by decide)
  rw [step]
  -- `s1 -= 1` and the entry.
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  obtain hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega_using [hj]) u₁.gpr
    (by rw [u₁.other _ (by decide), hI.keep.gpr _ (by decide) (by decide), hP.s4])
    (hI.tab.of_mem u₁.rd fun x _ => by rw [u₁.mem])
    (by rw [u₁.mem, hI.unch.word (by decide) (by decide), hP.kz]))
    fun s₂ ⟨⟨e, _, he, dx₂, dy₂⟩, ms₂, mz₂, U₂, r₂⟩ => ?_
  rw [u₁.mem, hk] at he ms₂ mz₂
  rw [u₁.mem] at U₂
  obtain hw₂ := hw₁.of_rest r₂
  obtain e₂ : ∀ d, d + 72 ≤ 1072 ∨ 2152 ≤ d → d + 72 ≤ 3456 ∨ 3472 ≤ d → d + 72 ≤ 7616 →
      wv base s₂ d = wv base s₀ d := fun d h1 h2 h3 => by
    rw [show wv base s₂ d = wv base s d from U₂.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2])
      (by omega_using [h3]), uS d h1 h2 h3]
  obtain hK₂ : Window.KC base s₂ := hP.kc.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₂ _ (by decide) (by decide) (by decide)
  obtain pR₂ : PtOk base s₂ (c.pt RX RY RZ) _ :=
    hI.rep.of_eq (U₂.wordsVal (by decide) (by decide)) (U₂.wordsVal (by decide) (by decide))
      (U₂.wordsVal (by decide) (by decide))
  -- The entry in limbs.
  refine WP.seq (WP.mono (entry_ok hw₂ hK₂ (by rw [e₂ _ (by decide) (by decide) (by decide)]; exact hP.ct)
    (by rw [e₂ _ (by decide) (by decide) (by decide)]; exact hP.cv) dx₂ dy₂ ms₂ mz₂)
    fun s₃ ⟨K₃, U₃, tx, ty, tz, vx, vy, vz⟩ => ?_)
  obtain hw₃ := hw₂.of_kp K₃
  obtain e₃ : ∀ d, d + 72 ≤ 1288 ∨ 1576 ≤ d → d + 72 ≤ 7616 → wv base s₃ d = wv base s₂ d := fun d h1 h2 =>
    U₃.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2])
      (by omega_using [h2])
  obtain hK₃ : Window.KC base s₃ := hK₂.of_eq fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> exact e₃ _ (by decide) (by decide)
  obtain pR₃ : PtOk base s₃ (c.pt RX RY RZ) _ :=
    pR₂.of_eq (e₃ _ (by decide) (by decide)) (e₃ _ (by decide) (by decide)) (e₃ _ (by decide) (by decide))
  obtain hD := entry_rep hL (k := kOf s₀.mem base) (i := j - 1) (by omega_using [hj]) he
  simp only [decide_eq_true_eq] at vx vy vz
  obtain pD : PtOk base s₃ (c.pt DX DY DZ) (signedPtW W 7 (kOf s₀.mem base) (j - 1)) :=
    ⟨by show Rep W (ev base s₃ 1288) (ev base s₃ 1360) (ev base s₃ 1432) _; rw [vx, vy, vz]; exact hD, tx, ty, tz⟩
  -- `T = R + D`.
  obtain hX := hL.onCurve_mul VG.Proof.P521.onCurve_G (combEW 7 (kOf s₀.mem base) 83 j)
  refine WP.seq (WP.mono (addPt_ok hL hw₃ hK₃ (p := c.pt RX RY RZ) (q := c.pt DX DY DZ)
    (o := c.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide) hX (signed_onCurve hL _ _) pR₃ pD)
    fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₄ (o := c.pt RX RY RZ) (p := c.pt TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ ⟨x₅, y₅, z₅, r₅, U₅⟩ => ?_
  obtain UU : Unch base stepW s.mem s₅.mem := (((U₂.trans U₃).trans U₄).trans U₅).cover (by decide)
  refine ⟨hw₄.of_rest r₅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans (Kc.of_rest r₅)))
  · exact (hI.unch.trans UU).cover (by decide)
  · exact hI.tab.of_unch (by rw [r₅.rd, K₄.rd, K₃.rd, r₂.rd, u₁.rd]) (by decide) UU
  · have hadd := combW_add hL VG.Proof.P521.onCurve_G (w := 7) (k := kOf s₀.mem base) (J := 83) (j := j - 1)
      (by omega_using [hj])
    rw [Nat.sub_add_cancel hj1] at hadd
    obtain pT' := pT.move x₅ y₅ z₅
    unfold signedPtW at pT'
    rw [hadd] at pT'
    exact pT'

/-! ## The body -/

/-- What the body writes. -/
abbrev bodyW : List (Nat × Nat) := [(1072, 1080), (3376, 96), (3592, 288), (7616, 576)]

/-- The body: `R = [k]G` in limbs, for the number `k` at `K`'s slot, from
the constants in Montgomery's form. -/
theorem body_ok (hL : Law W) {s : State} {base T : Addr} (hw : WsReg s base) (h2 : s.gpr .s4 = T)
    (hT : TabOk s base T) (hz : wv base s 280 = 0) (hone : wv base s (c.sl ONEP) = 2 ^ 576 % W.p)
    (ha : wv base s (c.sl AP) = 2 ^ 576 * W.a % W.p) (hb3 : wv base s (c.sl B3P) = 2 ^ 576 * (3 * W.b) % W.p) :
    WP isa (body Impl.P521.p521Comb7Start) s fun s' =>
      Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧
      PtOk base s' (c.pt RX RY RZ) (Spec.Weierstrass.mul (wv base s 2296) (Spec.Weierstrass.G W)) := by
  have hn := hw.nowrap
  obtain hC := VG.Proof.P521.combOk7 hL
  obtain hp0 : 0 < W.p := by decide
  obtain m522 : ∀ x, x % W.p < 2 ^ 522 := fun x => Nat.lt_trans (Nat.mod_lt _ hp0) (by decide)
  rw [body]
  simp only [List.append_assoc]
  -- The copy of `k`, and its zero word.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := 3376) (a := 2296) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  obtain hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  refine VG.Proof.Weierstrass.RISCV64.sdAt_ws hw₂ (by decide) (d := 3448) (by decide) (by decide) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂.of_rest (u₃.rest [])
  obtain O₃ : Outside base 3448 8 s₂.mem s₃.mem := by rw [u₃.mem]; exact writeW_outside _ _ _ (by omega_using [])
  -- The start.
  refine WP.block_append (WP.mono (setConst_ok 9 hw₃ (o := 1072) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont c
    Impl.P521.p521Comb7Start.1) (by decide) (by decide)) fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  refine WP.mono (setConst_ok 9 hw₄ (o := 1144) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont c
    Impl.P521.p521Comb7Start.2) (by decide) (by decide)) fun s₅ ⟨r₅, O₅, e₅⟩ => ?_
  obtain hw₅ := hw₄.of_rest r₅
  obtain r₀₅ : Rest [.t0, .t1] s s₅ :=
    ((r₁.mono (by decide)).trans ((u₂.rest (ws := [.t0, .t1]) (by decide)).trans (u₃.rest _))).trans (r₄.trans r₅)
  obtain U₅ : Unch base [(3376, 72), (3448, 8), (1072, 72), (1144, 72)] s.mem s₅.mem := by
    obtain O₃' : Outside base 3448 8 s₁.mem s₃.mem := by rw [← u₂.mem]; exact O₃
    exact ((O₁.unch.trans O₃'.unch).trans O₄.unch).trans O₅.unch
  obtain e5 : ∀ d, d + 72 ≤ 1072 ∨ 1216 ≤ d → d + 72 ≤ 3376 ∨ 3456 ≤ d → d + 72 ≤ 8192 →
      wv base s₅ d = wv base s d := fun d h1 h2 h3 =>
    U₅.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2])
      (by omega_using [h3])
  obtain ex : wv base s₅ 1072 = montP Impl.P521.p521Comb7Start.1 := by
    rw [show wv base s₅ 1072 = wv base s₄ 1072 from O₅.wordsVal (by decide) (by decide)]
    exact e₄.trans (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) (by decide)))
  obtain ey : wv base s₅ 1144 = montP Impl.P521.p521Comb7Start.2 :=
    e₅.trans (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp0) (by decide)))
  obtain hk₅ : kOf s₅.mem base = wv base s 2296 := by
    show wv base s₅ 3376 = _
    rw [show wv base s₅ 3376 = wv base s₄ 3376 from O₅.wordsVal (by decide) (by decide),
      show wv base s₄ 3376 = wv base s₃ 3376 from O₄.wordsVal (by decide) (by decide),
      show wv base s₃ 3376 = wv base s₂ 3376 from O₃.wordsVal (by decide) (by decide)]
    show wordsVal s₂.mem base 3376 9 = _
    rw [u₂.mem]; exact e₁
  obtain kz₅ : word s₅.mem base 3448 = 0 := by
    rw [O₅.word (by decide) (by decide), O₄.word (by decide) (by decide), u₃.mem, word_writeW_self, u₂.gpr]; rfl
  -- To limbs.
  refine WP.seq (WP.mono (convInC_ok hw₅ (by rw [show wordsVal s₅.mem base (c.sl ZERO) 9 = wv base s₅ 280 from rfl,
      e5 _ (by decide) (by decide) (by decide)]; exact hz)
    (by rw [show wv base s₅ (c.sl RX) = wv base s₅ 1072 from rfl, ex]; exact montP_lt _)
    (by rw [show wv base s₅ (c.sl RY) = wv base s₅ 1144 from rfl, ey]; exact montP_lt _)
    (by rw [e5 _ (by decide) (by decide) (by decide), hone]; exact m522 _)
    (by rw [e5 _ (by decide) (by decide) (by decide), ha]; exact m522 _)
    (by rw [e5 _ (by decide) (by decide) (by decide), hb3]; exact m522 _))
    fun s₆ ⟨K₆, U₆, cv₆, tc₆, vc₆⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₆
  obtain ⟨⟨tx₆, vx₆⟩, ⟨ty₆, vy₆⟩, ⟨to₆, vo₆⟩, ⟨ta₆, va₆⟩, ⟨tb₆, vb₆⟩⟩ := cv₆
  rw [show wv base s₅ (c.sl RX) = wv base s₅ 1072 from rfl, ex, ofNat_montP] at vx₆
  rw [show wv base s₅ (c.sl RY) = wv base s₅ 1144 from rfl, ey, ofNat_montP] at vy₆
  rw [e5 _ (by decide) (by decide) (by decide), hone, ← Nat.mul_one (2 ^ 576), ofNat_in] at vo₆
  rw [e5 _ (by decide) (by decide) (by decide), ha, ofNat_in] at va₆
  rw [e5 _ (by decide) (by decide) (by decide), hb3, ofNat_in] at vb₆
  have vx' : uf (wv base s₆ 1072) = Fin.ofNat W.p Impl.P521.p521Comb7Start.1 := vx₆
  have vy' : uf (wv base s₆ 1144) = Fin.ofNat W.p Impl.P521.p521Comb7Start.2 := vy₆
  have vo' : uf (wv base s₆ 3736) = 1 := vo₆
  obtain hw₆ := hw₅.of_kp K₆
  obtain e₆ : ∀ d, d + 72 ≤ 1072 ∨ 1216 ≤ d → d + 72 ≤ 3592 ∨ 3880 ≤ d → d + 72 ≤ 7616 →
      wv base s₆ d = wv base s₅ d := fun d h1 h2 h3 =>
    U₆.wordsVal (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_using [h1, h2, h3])
      (by omega_using [h3])
  -- `Z = 1`, and the counter.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 9 hw₆ (o := 1216) (a := 3736) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₇ ⟨e₇, r₇, O₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  refine wp_li (imm := 83) (by decide) fun s₈ u₈ => WP.block_nil ?_
  obtain hw₈ : WsReg s₈ base := hw₇.of_kc (Kc.of_rest (u₈.rest (ws := [.s1]) (by decide)))
  obtain o₈ : ∀ d, d + 72 ≤ 1216 ∨ 1288 ≤ d → d + 72 ≤ 8192 → wv base s₈ d = wv base s₆ d := fun d h h' => by
    show wordsVal s₈.mem base d 9 = _
    rw [u₈.mem]; exact O₇.wordsVal (by omega_using [h]) (by omega_using [h'])
  obtain U₈ : Unch base ([(3376, 72), (3448, 8), (1072, 72), (1144, 72)] ++ cinW ++ [(1216, 72)])
      s.mem s₈.mem := by
    rw [u₈.mem]; exact (U₅.trans U₆).trans O₇.unch
  obtain hP : CombPre base T s₈ := by
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [u₈.other _ (by decide), r₇.gpr _ (by decide), K₆.gpr _ (by decide), r₀₅.gpr _ (by decide), h2]
    · show word s₈.mem base 3448 = 0
      rw [u₈.mem, O₇.word (by decide) (by decide), U₆.word (by decide) (by decide), kz₅]
    · show Tight (wv base s₈ (c.sl UA)); rw [o₈ _ (by decide) (by decide)]; exact ta₆
    · show uf (wv base s₈ (c.sl UA)) = _; rw [o₈ _ (by decide) (by decide)]; exact va₆
    · show Tight (wv base s₈ (c.sl UB)); rw [o₈ _ (by decide) (by decide)]; exact tb₆
    · show uf (wv base s₈ (c.sl UB)) = _; rw [o₈ _ (by decide) (by decide)]; exact vb₆
    · show wv base s₈ 280 = 0
      rw [o₈ _ (by decide) (by decide), e₆ _ (by decide) (by decide) (by decide),
        e5 _ (by decide) (by decide) (by decide)]; exact hz
    · show Tight (wv base s₈ (c.sl UONE)); rw [o₈ _ (by decide) (by decide)]; exact to₆
    · show uf (wv base s₈ (c.sl UONE)) = _; rw [o₈ _ (by decide) (by decide)]; exact vo₆
    · rw [o₈ _ (by decide) (by decide)]; exact tc₆
    · rw [o₈ _ (by decide) (by decide)]; exact vc₆
  obtain hk₈ : kOf s₈.mem base = wv base s 2296 := by
    show wv base s₈ 3376 = _
    rw [o₈ _ (by decide) (by decide), e₆ _ (by decide) (by decide) (by decide)]; exact hk₅
  obtain hT₈ : TabOk s₈ base T := hT.of_unch (by rw [u₈.rd, r₇.rd, K₆.rd, r₀₅.rd]) (by decide) U₈
  obtain rz₈ : wv base s₈ 1216 = wv base s₆ 3736 := by
    show wordsVal s₈.mem base 1216 9 = _; rw [u₈.mem]; exact e₇
  obtain hI : CombInv base T s₈ s₈ 83 := by
    refine ⟨hw₈, u₈.gpr, Kc.refl _, Unch.refl _ _ _, hT₈, ⟨?_, ?_, ?_, ?_⟩⟩
    · show Rep W (uf (wv base s₈ 1072)) (uf (wv base s₈ 1144)) (uf (wv base s₈ 1216)) _
      rw [o₈ _ (by decide) (by decide), o₈ _ (by decide) (by decide), rz₈, vx', vy', vo',
        combEW_top, show 7 - 1 = 6 from rfl, show 2 ^ 6 = 2 ^ (7 - 1) from rfl, hC.start]
      exact rep_affine' hL _ _
    · show Tight (wv base s₈ 1072); rw [o₈ _ (by decide) (by decide)]; exact tx₆
    · show Tight (wv base s₈ 1144); rw [o₈ _ (by decide) (by decide)]; exact ty₆
    · show Tight (wv base s₈ 1216); rw [rz₈]; exact to₆
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => CombInv base T s₈ s' j) (n := 83) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨((Kc.of_rest r₀₅).trans (K₆.kc.trans (Kc.of_rest r₇))).trans
      ((Kc.of_rest (u₈.rest (ws := [.s1]) (by decide))).trans hi.keep),
    ((U₈.trans hi.unch).cover (by decide)), ?_⟩
  have hr := hi.rep
  rw [hk₈, combEW_zero (Nat.lt_of_lt_of_le (wordsVal_lt s.mem base 2296 9)
    (Nat.pow_le_pow_right (by decide) (by decide)))] at hr
  exact hr

end

end VG.Proof.Ecdsa.RISCV64.P521.Comb

end

end

/-!
# `vg_p521_mul_g` on RISC-V: the contract, and ECDH's `tail` with it

`vg_p521_mul_g(ws = a0)`, an internal function: `vg_p521_mul`'s contract
(`mulRVc`) for `Q = G`, with the table of the comb (`VG_P521_COMB`, its only
readable region): `mulGRVc`, which `mulG_rv` proves from `body_ok` around the
table's address (`lla`), the saves past the numbered slots (at `3304`, by
`sdAt`), the result's conversion from limbs (`convOut_ok`) and the loads.
`tailG_ok` is ECDH's `tail` with `R = [k]G` by a call of it, for P-521's
signatures and public keys, as `Proof/Ecdsa/RISCV64/P384/CombVerified.lean`
gives P-384's.
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P521.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (WP.mono_syms WP.of_syms wp_syms_frame)

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The table's region, at the address `lla` gives its symbol. -/
abbrev tabRegion (s : State) : Region := ⟨s.syms p521Sym, 764928⟩

/-- `vg_p521_mul_g(ws = a0)`: the table its only readable region, its words
there, at a multiple of 64, apart from the working space. -/
def mulGRVc : Contract isa where
  pre s := s.rd = [tabRegion s] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧
    (∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0) ∧
    (s.syms p521Sym).toNat % 64 = 0 ∧ (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64 ∧
    Region.Disjoint (tabRegion s) ⟨s.gpr .a0, 8192⟩
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (Spec.Weierstrass.G W) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.syms p521Sym = s₂.syms p521Sym

theorem combWords_eq : p521CombWords = tabWords := by unfold p521CombWords; rfl

/-- The table, apart from the working space. -/
theorem tabOk_of_pre {s : State} {base : Addr} (hrd : (tabRegion s) ∈ s.rd)
    (hheld : ∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0)
    (hal : (s.syms p521Sym).toNat % 64 = 0) (hfit : (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64)
    (hd : Region.Disjoint (tabRegion s) ⟨base, 8192⟩) : TabOk s base (s.syms p521Sym) where
  held i hi := by rw [hheld i hi, combWords_eq]
  al := hal
  rd := hrd
  fit := hfit
  far d hd' := by
    obtain hc : (tabRegion s).Contains (s.syms p521Sym + BitVec.ofNat 64 d) 1 :=
      Offset.contains_base _ (by omega_using [hd']) (by omega_using [hd'])
    have := hd _ hc
    simp only [Region.Contains, Nat.not_le] at this
    simp only [ofs]; omega_using [this]

/-- The saves, at `mulSave = 3304`. -/
abbrev savesG : List (Nat × Nat) := [(3304, 8), (3312, 8), (3320, 8), (3328, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keepsG_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (savesG ++ (bodyW ++ coutW)) m m') :
    MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ savesG ++ (bodyW ++ coutW), (1072 ≤ w.1 ∧ w.1 + w.2 ≤ 2296) ∨ 3304 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p521, true_and] at hown hp
  omega_using [hp, hw', hown]



/-- `vg_p521_mul_g` meets `mulGRVc`, given the group law. -/
theorem mulG_rv (hL : Law W) (s : State) (hs : mulGRVc.pre s) :
    ∃ t s', Exec isa mulGP521 s t s' ∧ abiPreserved s s' ∧ mulGRVc.post s s' := by
  obtain ⟨hrd, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, hheld, htal, htfit, hdisj⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hdisj
  obtain hT₀ : TabOk s base (s.syms p521Sym) :=
    tabOk_of_pre (by rw [hrd]; exact List.mem_singleton_self _) hheld htal htfit hdisj
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  obtain hp0 : 0 < W.p := by decide
  obtain ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 9 :=
    fun m _ ho => coordAt_eq m base (by omega_using [ho])
  obtain dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 576) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  suffices h : WP isa mulGP521 s fun s' => abiPreserved s s' ∧ mulGRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulGP521, show WindowU.c.mulSave = 3304 from rfl]
  simp only [List.singleton_append, List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 3304)]
  refine WP.seq (WP.cons exec_lla ?_)
  generalize hs₀ : s.write .t0 (s.syms p521Sym) = s₀
  obtain u₀ : Upd s s₀ .t0 (s.syms p521Sym) := hs₀ ▸ Upd.write _ _ _
  obtain b₀ : s₀.gpr .a0 = base := by rw [u₀.other _ (by decide), hb]
  refine sdAt_a0 b₀ (by rw [u₀.wr]; exact hwr') hal (by decide) (d := 3304) (by decide)
    (by decide) fun s₁ u₁ => ?_
  refine sdAt_a0 (by rw [u₁.gpr]; exact b₀) (by rw [u₁.wr, u₀.wr]; exact hwr') hal
    (by decide) (d := 3312) (by decide) (by decide) fun s₂ u₂ => ?_
  refine sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₂.wr, u₁.wr, u₀.wr]; exact hwr')
    hal (by decide) (d := 3320) (by decide) (by decide) fun s₃ u₃ => ?_
  refine sdAt_a0 (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact b₀)
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal (by decide) (d := 3328) (by decide) (by decide)
    fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain g₆ : ∀ r, r ≠ .s0 → r ≠ .s4 → s₆.gpr r = s₀.gpr r := fun r h0 h2 => by
    rw [u₆.other r h2, u₅.other r h0, g₄]
  obtain hw₆ : WsReg s₆ base := ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, b₀],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr', hfit, hal⟩
  obtain m₄ : s₄.mem = (((s.mem.writeW (off base 3304) (s.gpr .s0)).writeW (off base 3312) (s.gpr .s1)).writeW
      (off base 3320) (s.gpr .ra)).writeW (off base 3328) (s.gpr .s4) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.mem]
    rw [u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide)]
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  obtain O₄ : Unch base savesG s.mem s₆.mem := by
    rw [m₆, m₄]
    exact ((((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch).trans (writeW_outside _ _ _ (by omega_using [])).unch)
  obtain sv₆ : ∀ i, i < 45 → sv base s₆ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [savesG, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p521.sl i + 72 ≤ 3304 := by simp only [Cfg.sl, slot, p521]; omega_using [hi]
      rcases hw with rfl | rfl | rfl | rfl <;> (simp only; omega_using [this]))
      (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  obtain cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p521.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  obtain hT₆ : TabOk s₆ base (s.syms p521Sym) :=
    hT₀.of_unch (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]) (by decide) O₄
  -- The slots' values, from the contract's.
  obtain hz' : sv base s₆ ZERO = 0 := by rw [sv₆ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  obtain hone' : sv base s₆ ONEP = 2 ^ 576 % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  obtain ha' : sv base s₆ AP = 2 ^ 576 * W.a % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  obtain hb3' : sv base s₆ B3P = 2 ^ 576 * (3 * W.b) % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  -- The body.
  refine WP.seq (WP.mono (body_ok hL hw₆ (by rw [u₆.gpr, u₅.other _ (by decide), g₄, u₀.gpr]) hT₆ hz' hone' ha' hb3')
    fun q₇ ⟨K₇, U₇, pR₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kc K₇
  obtain z₇ : wordsVal q₇.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₇.wordsVal (by decide) (by decide)]; exact hz'
  -- Back to Montgomery's form.
  refine WP.seq (WP.mono (convOut_ok hw₇ z₇ pR₇.x pR₇.y pR₇.z) fun q₈ ⟨K₈, U₈, cv₈⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₈
  obtain ⟨ox₈, oy₈, oz₈⟩ := cv₈
  have R₇ := pR₇.rep
  obtain KK : Kc s₆ q₈ := K₇.trans K₈.kc
  obtain UU : Unch base (bodyW ++ coutW) s₆.mem q₈.mem := U₇.trans U₈
  -- The loads.
  obtain hw₈ := hw₆.of_kc KK
  obtain far : ∀ d ∈ [3304, 3312, 3320, 3328], word q₈.mem base d = word s₄.mem base d := fun d hd => by
    rw [UU.word (fun w hw => by
      have := (by decide : ∀ w ∈ bodyW ++ coutW, w.1 + w.2 ≤ 3304 ∨ 3376 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega_using [this, hd]) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd]), m₆]
  obtain w28 : word q₈.mem base 3328 = s.gpr .s4 := by rw [far 3328 (by simp), m₄, word_writeW_self]
  obtain w20 : word q₈.mem base 3320 = s.gpr .ra := by
    rw [far 3320 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      word_writeW_self]
  obtain w12 : word q₈.mem base 3312 = s.gpr .s1 := by
    rw [far 3312 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  obtain w04 : word q₈.mem base 3304 = s.gpr .s0 := by
    rw [far 3304 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3312) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ldAt_ws hw₈ (d := 3320) (by decide) (by decide) fun s₉ u₉ => ?_
  refine ldAt_ws (hw₈.of_kp (Kp.of_upd u₉)) (d := 3328) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  obtain hw₁₀ : WsReg s₁₀ base := ⟨by rw [u₁₀.other .s0 (by decide), u₉.other .s0 (by decide)]; exact hw₈.s0,
    by rw [u₁₀.wr, u₉.wr]; exact hw₈.wr, hfit, hal⟩
  refine ldAt_ws hw₁₀ (d := 3312) (by decide) (by decide) fun s₁₁ u₁₁ => ?_
  obtain hw₁₁ : WsReg s₁₁ base := ⟨by rw [u₁₁.other .s0 (by decide)]; exact hw₁₀.s0,
    by rw [u₁₁.wr]; exact hw₁₀.wr, hfit, hal⟩
  refine ldAt_ws hw₁₁ (d := 3304) (by decide) (by decide) fun s₁₂ u₁₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₁₁ : s₁₁.mem = q₈.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₁₂.gpr, m₁₁, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.mem, u₉.mem, w12]
    by_cases h2 : r = .s4
    · subst h2; rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, w28]
    rw [u₁₂.other _ h0, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ (fun e => by subst e; revert hr; decide),
      KK.gpr r hr h1, g₆ r h0 h2, u₀.other _ (fun e => by subst e; revert hr; decide)]
  · rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, KK.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, w20]
  · have m₁₂ : s₁₂.mem = q₈.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₁₂.mem
    rw [hb, m₁₂]
    refine ⟨fun _ _ => ?_, keepsG_of_unch (O₄.trans UU)⟩
    obtain e : MC.scalar base s.mem = sv base s₆ K := by rw [sv₆ _ (by decide)]; exact cs K (by decide)
    obtain c8 : ∀ i, i < 45 → MC.toPoint.coordAt q₈.mem base (p521.sl i) = sv base q₈ i := fun i hi =>
      ca q₈.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
    obtain x0 : MC.toPoint.coordAt q₈.mem base MC.pAt = sv base q₈ RX := c8 RX (by decide)
    obtain x1 : MC.toPoint.coordAt q₈.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₈ RY := c8 RY (by decide)
    obtain x2 : MC.toPoint.coordAt q₈.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₈ RZ := c8 RZ (by decide)
    have ex : sv base q₈ RX = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RX)) * 2 ^ 55 % W.p := ox₈
    have ey : sv base q₈ RY = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RY)) * 2 ^ 55 % W.p := oy₈
    have ez : sv base q₈ RZ = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RZ)) * 2 ^ 55 % W.p := oz₈
    rw [e]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0, ex]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1, ey]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2, ez]; exact Nat.mod_lt _ hp0
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq, ex, ey, ez, toM_out, toM_out, toM_out]
      exact represents_of_rep R₇

/-! ## The table, for the callers -/

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Point)
open VG.Proof.Ecdh.RISCV64.P521 (TailConsts tailW tailWith_ok coord_sv point_eq sv_unch sl_eq FL)

/-- The table, as the callers of `vg_p521_mul_g` hold it, for the working
space at `base`. -/
structure TabAt (base : Addr) (s : State) : Prop where
  rd : tabRegion s ∈ s.rd
  held : ∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0
  al : (s.syms p521Sym).toNat % 64 = 0
  fit : (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64
  disj : Region.Disjoint (tabRegion s) ⟨base, 8192⟩

/-- The table survives what changes memory only in the working space. -/
theorem TabAt.of_mem {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabAt base s' := by
  obtain hT := tabOk_of_pre h.rd h.held h.al h.fit h.disj
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hm _ ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact hT.far _ (by omega_using [hi, hb])

theorem TabAt.of_unch {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) : TabAt base s' :=
  h.of_mem hsy hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega_using [hx, this]

/-- The table survives what keeps the symbols and changes memory only in
writable regions apart from it. -/
theorem TabAt.of_frame {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hF : Frame s.wr s.mem s'.mem) (hd : ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r) : TabAt base s' := by
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hF _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega_using [hi, hb])]
  omega_using [hi, hb]

theorem combWords_length : p521CombWords.length = 95616 := by
  rw [combWords_eq]
  exact tcombWords_length comb7_len comb7_lenH

/-- A memory holding the table at `0x100000`, for the witnesses of the
contracts with it (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p521CombWords

theorem combSatMem_held : ∀ i < p521CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0 := by
  obtain h := constMem_held 0x100000 p521CombWords (by rw [combWords_length]; decide)
  unfold combSatMem
  exact h

/-- The table, as `abi.withConsts p521CombConsts` gives it, for a working space
among the writable regions. -/
theorem tabAt_of_consts {st : Nat} {s : State} {base : Addr} (h : ConstsOk p521CombConsts st s)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) : TabAt base s := by
  have h' : ConstsOk [(p521Sym, p521CombWords)] st s := h
  obtain hr := ConstsOk.rd1 h'
  obtain hw' := ConstsOk.wr1 h' _ hw
  obtain hf := ConstsOk.fit h' List.mem_cons_self
  rw [combWords_length] at hr hw' hf
  exact ⟨hr, fun i hi => ConstsOk.held1 h' i (by rw [combWords_length]; exact hi),
    ConstsOk.aligned h' List.mem_cons_self, hf, hw'⟩

theorem tab_wr_of_consts {st : Nat} {s : State} (h : ConstsOk p521CombConsts st s) :
    ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r := by
  have h' : ConstsOk [(p521Sym, p521CombWords)] st s := h
  obtain hw' := ConstsOk.wr1 h'
  rw [combWords_length] at hw'
  exact hw'

/-- `tail` with `vg_p521_mul_g`, from `G` in `R`'s first two slots. -/
theorem tailG_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX = W.gx * 2 ^ 576 % W.p)
    (hy : sv base s RY = W.gy * 2 ^ 576 % W.p) (hT : TabAt base s) :
    WP isa (Impl.Ecdh.RISCV64.Cfg.tail p521 mulGP521Name mulGP521) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 576) (sv base s' RX)) (toM W.p (2 ^ 576) (sv base s' RY))
          (toM W.p (2 ^ 576) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 576) (sv base s RX))
            (toM W.p (2 ^ 576) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 576) (sv base s' RX) * toM W.p (2 ^ 576) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 576) (sv base s' ACC) = toM W.p (2 ^ 576) (sv base s' RZ) ^ (W.p - 2) := by
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ sy₁ => ?_
  obtain hc₁ := hc.of_unch U₁ (by decide)
  obtain e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega_using [hi])
      (by omega_using [hi])
  obtain hT₁ : TabAt base s₁ := hT.of_unch sy₁ K₁.rd (by decide) U₁
  obtain eG : MC.point base s₁.mem = Spec.Weierstrass.G W := by
    rw [point_eq hL]
    show Point.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY)) = _
    rw [e₁ RX (by decide), e₁ RY (by decide), hx, hy]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  -- The call, with the table its readable region.
  rw [Cfg.wsCall, eG]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s₁.write .a0 (s₁.gpr wb + BitVec.ofInt 64 0) = s₂
  obtain u₂ : Upd s₁ s₂ .a0 (s₁.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  obtain sy₂ : s₂.syms = s₁.syms := by rw [← hs₂]; rfl
  obtain K₂ : Kp s₁ s₂ := Kp.of_upd u₂
  obtain a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw₁.s0]; simp
  obtain hcov : Covers [⟨base, 8192⟩] s₂.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw₁.wr
  obtain htab : Covers [tabRegion s₂] s₂.rd := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, tabRegion, sy₂]; exact hT₁.rd
  obtain e0 : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  obtain em : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).mem = s₁.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  refine WP.call (mulG_rv hL) (rd := [tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov) hcov
    (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.CombU.mulGP521_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw₁.nowrap, by rw [e0]; exact hw₁.al, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [em]; exact fun i hi => by rw [show (s₂.callEntry.withRegions _ _).syms = s₁.syms from sy₂]; exact hT₁.held i hi
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.al
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.fit
    · rw [e0]
      simp only [tabRegion]
      rw [show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂]
      exact hT₁.disj
  -- `s0` from `s3`.
  refine wp_mv fun s₄ u₄ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₄.rd, r₃, K₂.rd], by rw [u₄.wr, w₃, K₂.wr],
    by rw [u₄.sp, p₃, K₂.sp]⟩, ?_⟩
  · by_cases h : r = .s0
    · subst h; rw [u₄.gpr, G₃ _ (by decide), K₂.gpr _ (by decide), h3₁, hw₁.s0]
    · rw [u₄.other _ h, G₃ _ hr, K₂.gpr _ hr]
  · have := hp
    simp only [mulGRVc, State.withRegions_mem] at this
    rw [e0] at this
    rw [show s₂.callEntry.mem = s₁.mem by rw [State.callEntry_mem, u₂.mem]] at this
    rw [u₄.mem]
    exact this

/-! The constant-time analyses of the calls of the functions on limbs from their arguments, with
the comb's table public, each done once for every check of code that calls it, which keep what is
public of `s0`–`s11`: the functions write none of them. -/
taint_summary uMulSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "mul") Impl.Weierstrass.RISCV64.P521Unsat.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uAddSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "add") Impl.Weierstrass.RISCV64.P521Unsat.addFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uSubSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "sub") Impl.Weierstrass.RISCV64.P521Unsat.subFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uPackSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "pack") Impl.Weierstrass.RISCV64.P521Unsat.packFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uUnpackSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "unpack") Impl.Weierstrass.RISCV64.P521Unsat.unpackFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

/-! The same for the multiplication modulo `p` in Montgomery's form, which the comb's callers
call (the inversion and the affine coordinates). -/
taint_summary pMulSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "mul") Impl.Weierstrass.RISCV64.P521Field.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

/-! The constant-time analysis of the call of `vg_p521_mul_g` from its argument, with the comb's
table public, done once for every check of code that calls it, which keeps what is public of `s2`,
`s3` and `s5`–`s11`: the function writes none of them (`s0`, `s1` and `s4` it restores from
memory). -/
taint_summary mulGSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0])
  (.call mulGP521Name mulGP521)
  keeping (Taint.ofRegs [.s2, .s3, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
  using uMulSymSum uAddSymSum uSubSymSum uPackSymSum uUnpackSymSum

end VG.Proof.Ecdsa.RISCV64.P521.Comb
