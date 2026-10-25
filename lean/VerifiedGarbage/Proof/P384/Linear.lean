module

public import VerifiedGarbage.Impl.P384.Linear
public import VerifiedGarbage.Proof.P384.Ops
import VerifiedGarbage.Proof.Mont.AArch64.RowInit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain

/-!
# P-384's small linear combinations on AArch64

`lin_ok`: `Linear.lin o a b c d` (`Impl/P384/Linear.lean`) stores
`(c [a] + d (p - [b])) mod p` at `o`, for `[a], [b] < p` and `c`, `d` below
`2^16`, changing only the registers `clobX` and `o` (`OpKeepX`). The sum
`V = c A + d (p - B)` is computed exactly (`scaleB_ok`, `addA_ok`); its top
word `T` gives the quotient estimate `T + 1`, whose multiple of
`2^384 - p` the fold adds (`foldPre_ok`), and `p` is added back where the
fold did not carry (`correctPre_ok`), which `reduce_arith` shows is
`V mod p`.
-/

@[expose] public section

-- Powers of two up to `2^448` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.Linear

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.P384.Linear VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.P384.Ops (clobX OpKeepX)
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `ts += hs`, `adds` first, with the carry out. -/
theorem addsIn_ok (s : State) {t h : Reg} {ts hs : List Reg} (hl : ts.length = hs.length)
    (hnd : (t :: ts).Nodup) (hd : ∀ q ∈ h :: hs, q ∉ t :: ts) :
    WP isa (.block (VG.Impl.Mont.AArch64.P384Mul.addsIn true (t :: ts) (h :: hs))) s fun u =>
      regsVal u (t :: ts) + 2 ^ (64 * (ts.length + 1)) * u.c.toNat =
        regsVal s (t :: ts) + regsVal s (h :: hs) ∧ Keeps (t :: ts) s u := by
  rw [VG.Impl.Mont.AArch64.P384Mul.addsIn, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s t t h true (c := false) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
  have hhs : ∀ q ∈ hs, q ∉ ts := fun q hq hm =>
    hd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hm)
  refine WP.mono (P384Mul.adcsIn_ok ts hs s₁ hl (List.nodup_cons.mp hnd).2 hhs)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  have g₁ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
  have gt : regsVal s₁ ts = regsVal s ts := regsVal_congr fun r hr => k₁.gpr r (by
    simp only [List.mem_singleton]; rintro rfl; exact htn hr)
  have gh : regsVal s₁ hs = regsVal s hs := regsVal_congr fun r hr => k₁.gpr r (by
    simp only [List.mem_singleton]; rintro rfl
    exact hd r (List.mem_cons_of_mem _ hr) (List.mem_cons_self ..))
  have ev := Word64.addCarry_value (s.gpr t) (s.gpr h) false
  rw [← v₁, ← c₁] at ev
  rw [gt, gh] at e₂
  simp only [regsVal, g₁, pow64_succ]
  simp only [Nat.mul_assoc, Bool.toNat_false, Nat.add_zero] at ev ⊢
  omega_arith

/-- `x17 = k` and `x16 = 0`, for `k < 2^16`. -/
theorem consts_ok (s : State) {k : Nat} (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x17 (BitVec.ofNat 16 k) 0, .movz .x .x16 0 0]) s fun t =>
      (t.gpr .x17).toNat = k ∧ t.gpr .x16 = 0 ∧ Keeps [.x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x17 = k`, for `k < 2^16`. -/
theorem const_ok (s : State) {k : Nat} (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x17 (BitVec.ofNat 16 k) 0]) s fun t =>
      (t.gpr .x17).toNat = k ∧ Keeps [.x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `q = x16 + 1` into `x16`, and `x3 = q << 32`. -/
theorem foldShift_ok (s : State) (hT : (s.gpr .x16).toNat + 1 < 2 ^ 32) :
    WP isa (.block [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32]) s fun t =>
      (t.gpr .x16).toNat = (s.gpr .x16).toNat + 1 ∧
      (t.gpr .x3).toNat = ((s.gpr .x16).toNat + 1) * 2 ^ 32 ∧ t.c = s.c ∧
      Keeps [.x2, .x3, .x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 16 * 0 < Size.x.bits by decide,
    show 32 < Size.x.bits by decide, ite_true, RegUpd.gpr_write, RegUpd.c_write, reduceCtorEq, ite_false,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  have h1 : (s.gpr .x16 + (1 : BitVec 16).setWidth 64 <<< (16 * 0)).toNat = (s.gpr .x16).toNat + 1 := by
    rw [BitVec.toNat_add]
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth]
    have : (1 : BitVec 16).toNat = 1 := rfl
    omega_arith
  refine ⟨h1, ?_, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The fold's words' arithmetic: `x2 = q - q 2^32` with the borrow `b`, and
`x3 = q 2^32 - b`. -/
theorem fold_arith {q x2 x3 b j : Nat} (hq : q < 2 ^ 32) (hb : b ≤ 1) (h2 : x2 < 2 ^ 64)
    (h3 : x3 < 2 ^ 64) (e2 : x2 + q * 2 ^ 32 = q + 2 ^ 64 * b) (e3 : x3 + b = q * 2 ^ 32 + 2 ^ 64 * j) :
    x2 + 2 ^ 64 * x3 + q * 2 ^ 32 = q + q * 2 ^ 96 := by
  have hj : j = 0 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact h
    · exfalso
      have : 2 ^ 64 * j ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ h
      omega_arith
  subst hj
  omega_arith

/-- The fold's words: `[x3 x2] = q (2^96 - 2^32 + 1)` and `x16 = q`, with
`q = x16 + 1`. -/
theorem foldPre_ok (s : State) (hz : s.gpr .x7 = 0) (hT : (s.gpr .x16).toNat + 1 < 2 ^ 32) :
    WP isa (.block ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32,
        .subs .x .x2 .x16 .x3, .sbc .x .x3 .x3 .x7] : List Instr)) s fun t =>
      (t.gpr .x16).toNat = (s.gpr .x16).toNat + 1 ∧
      (t.gpr .x2).toNat + 2 ^ 64 * (t.gpr .x3).toNat + ((s.gpr .x16).toNat + 1) * 2 ^ 32 =
        ((s.gpr .x16).toNat + 1) + ((s.gpr .x16).toNat + 1) * 2 ^ 96 ∧
      Keeps [.x2, .x3, .x16] s t := by
  rw [show ([.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32,
      .subs .x .x2 .x16 .x3, .sbc .x .x3 .x3 .x7] : List Instr) =
    [.movz .x .x2 1 0, .add .x .x16 .x16 .x2, .lsl .x .x3 .x16 32] ++ [.subs .x .x2 .x16 .x3] ++
      [.sbc .x .x3 .x3 .x7] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (foldShift_ok s hT) fun s₁ ⟨q₁, l₁, _, k₁⟩ => ?_
  refine WP.mono (subc_ok s₁ .x2 .x16 .x3 true rfl) fun s₂ ⟨v₂, c₂, k₂⟩ => ?_
  simp only [↓reduceIte] at v₂ c₂
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  refine WP.mono (P384Mul.sbc0_ok s₂ .x3 z₂) fun s₃ ⟨⟨j, e₃⟩, k₃⟩ => ?_
  have b₂ := sub_borrow (s₁.gpr .x16) (s₁.gpr .x3) true
  rw [← v₂, ← c₂] at b₂
  have h16 : s₃.gpr .x16 = s₁.gpr .x16 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide)]
  have h2 : s₃.gpr .x2 = s₂.gpr .x2 := k₃.gpr _ (by decide)
  have h3 : s₂.gpr .x3 = s₁.gpr .x3 := k₂.gpr _ (by decide)
  rw [h3, l₁] at e₃
  rw [l₁, q₁] at b₂
  refine ⟨by rw [h16, q₁], ?_, (k₁.trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [h2]
  rw [show (!true).toNat = 0 from rfl, Nat.add_zero] at b₂
  exact fold_arith hT (Bool.toNat_le _) (s₂.gpr .x2).isLt (s₃.gpr .x3).isLt b₂ e₃

/-- P-384's prime under the mask `x17`: `[x17 x17 x17 x16 x3 x2] = p` if
the mask is set, else zero. -/
theorem maskWords_ok (s : State) {k : Bool} (hk : s.gpr .x17 = if k then BitVec.allOnes 64 else 0) :
    WP isa (.block [.lsr .x .x2 .x17 32, .logic .eor .x .x3 .x17 .x2, .lsl .x .x16 .x17 1]) s fun t =>
      regsVal t [.x2, .x3, .x16, .x17, .x17, .x17] = (if k then p384 else 0) ∧
      t.c = s.c ∧ Keeps [.x2, .x3, .x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show 32 < Size.x.bits by decide,
    show 1 < Size.x.bits by decide, ite_true, RegUpd.gpr_write, RegUpd.c_write, reduceCtorEq, ite_false,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [regsVal, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, hk]
    cases k <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The mask of the borrow `!c`, and `p` under it. -/
theorem correctPre_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block ([.sbc .x .x17 .x7 .x7, .lsr .x .x2 .x17 32, .logic .eor .x .x3 .x17 .x2,
        .lsl .x .x16 .x17 1] : List Instr)) s fun t =>
      regsVal t [.x2, .x3, .x16, .x17, .x17, .x17] = (if s.c then 0 else p384) ∧
      Keeps [.x2, .x3, .x16, .x17] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (sbcMask_ok s hz) fun s₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (maskWords_ok s₁ m₁) fun t ⟨e, _, k⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k.mono (by sub_regs))⟩
  rw [e]
  cases s.c <;> rfl

/-- One quotient estimate reduces `V = L + 2^384 T` modulo `p`: `L₁` is
`L + (T + 1) (2^384 - p)` less its carry `c₁`, and `L₂` is `L₁ + p` where
`c₁` is clear, modulo `2^384`. -/
theorem reduce_arith {V L T L₁ L₂ c₁ c₂ : Nat} (hV : V = L + 2 ^ 384 * T) (hL : L < 2 ^ 384)
    (hT : T + 1 < 2 ^ 32)
    (hL₁ : L₁ < 2 ^ 384) (hc₁ : c₁ ≤ 1)
    (h₁ : L₁ + 2 ^ 384 * c₁ + (T + 1) * 2 ^ 32 = L + (T + 1) * (2 ^ 128 + 2 ^ 96 + 1))
    (hL₂ : L₂ < 2 ^ 384) (hc₂ : c₂ ≤ 1)
    (h₂ : L₂ + 2 ^ 384 * c₂ = L₁ + (if c₁ = 1 then 0 else p384)) :
    L₂ = V % p384 := by
  have hp : p384 = 2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1 := by decide
  rcases (by omega_arith : c₁ = 0 ∨ c₁ = 1) with rfl | rfl
  · simp only [Nat.zero_ne_one, ↓reduceIte] at h₂
    have e : V = L₂ + T * p384 := by rw [hp] at h₂ ⊢; omega_arith
    have hl : L₂ < p384 := by rw [hp] at h₂ ⊢; omega_arith
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  · simp only [↓reduceIte, Nat.add_zero] at h₂
    have e : V = L₂ + (T + 1) * p384 := by rw [hp]; omega_arith
    have hl : L₂ < p384 := by rw [hp]; omega_arith
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- Three words and three zeros. -/
theorem regsVal_fold {s : State} (hz : s.gpr .x7 = 0) {a b c : Reg} :
    regsVal s [a, b, c, .x7, .x7, .x7] =
      (s.gpr a).toNat + 2 ^ 64 * (s.gpr b).toNat + 2 ^ 128 * (s.gpr c).toNat := by
  simp only [regsVal, hz, show (0 : BitVec 64).toNat = 0 from rfl]
  omega_arith

/-- `[o] = (c [a] + d (p - [b])) mod p`. -/
theorem lin_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA Impl.P384.Ops.M size p384 s.mem base) {o a b c d : Nat} (ho : o + 48 ≤ size)
    (ha : a + 48 ≤ size) (hb : b + 48 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hc : c < 2 ^ 16) (hd : d < 2 ^ 16)
    (hA : wordsVal s.mem base a 6 < p384) (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (lin o a b c d)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 =
        (c * wordsVal s.mem base a 6 + d * (p384 - wordsVal s.mem base b 6)) % p384 := by
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ clobX) →
      ∀ r, r ∉ clobX → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  have hmo : Impl.P384.Ops.M.mo + 48 ≤ size := hM.mo
  have hm : wordsVal s.mem base Impl.P384.Ops.M.mo 6 = p384 := hM.val
  rw [lin, scaleB, List.cons_append, ← List.singleton_append]
  simp only [List.append_assoc]
  -- `x7 = 0`.
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ : Scr s₀ base size := hs.of_keeps k₀ (by decide)
  -- `p - [b]`.
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok qRegs hs₀ (a := Impl.P384.Ops.M.mo) hmo (by decide) ⟨by decide, by decide⟩)
    fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ : Scr s₁ base size := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSubs_ok hs₁ (t := .x8) (ts := [.x9, .x10, .x11, .x12, .x13]) (b := b) hb hb8
    ⟨by decide, by decide⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base size := hs₁.of_keeps k₂ (by decide)
  have hQ : regsVal s₂ qRegs = p384 - wordsVal s.mem base b 6 := by
    have m₁ : s₁.mem = s.mem := by rw [k₁.mem, k₀.mem]
    have r₁ : regsVal s₁ qRegs = p384 := by
      change regsVal s₁ qRegs = wordsVal s₀.mem base Impl.P384.Ops.M.mo 6 at e₁
      rw [e₁, k₀.mem]; exact hm
    change regsVal s₂ qRegs + wordsVal s₁.mem base b 6 = regsVal s₁ qRegs + 2 ^ 384 * _ at e₂
    rw [m₁, r₁] at e₂
    have hl : regsVal s₂ qRegs < 2 ^ 384 := regsVal_lt s₂ qRegs
    have hb := Bool.toNat_le (!s₂.c)
    omega_using [e₂, hl, hb, hB]
  -- `d (p - [b])`.
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₂ hd) fun s₃ ⟨d₃, z₃', k₃⟩ => ?_
  have hs₃ : Scr s₃ base size := hs₂.of_keeps k₃ (by decide)
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), z₀]
  rw [WP.block_append_iff]
  refine WP.mono (rowInit_ok hs₃.ptr z₃ (by decide) (by decide) (ts := rRegs) (bs := qRegs) (x := .x17) rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun t ht => by simp only [rRegs, qRegs, List.length_cons, List.length_nil, List.drop_succ_cons,
      List.drop_zero, List.mem_singleton] at ht; subst ht; exact z₃')) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hQ₃ : regsVal s₃ qRegs = regsVal s₂ qRegs := regsVal_congr fun r hr => k₃.gpr r (by revert r; decide)
  rw [hQ₃, hQ, d₃] at e₄
  have hs₄ : Scr s₄ base size := hs₃.of_keeps k₄ (by decide)
  have z₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by decide), z₃]
  have hm₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem, k₀.mem]
  -- `+ c [a]`.
  rw [addA, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok s₄ hc) fun s₅ ⟨c₅, k₅⟩ => ?_
  have hs₅ : Scr s₅ base size := hs₄.of_keeps k₅ (by decide)
  have z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  have hR₅ : regsVal s₅ rRegs = regsVal s₄ rRegs := regsVal_congr fun r hr => k₅.gpr r (by revert r; decide)
  have hw : rwVal s₅ base (mWords a 0 6) = wordsVal s.mem base a 6 := by
    rw [rwVal_mWords, Nat.mul_zero, Nat.add_zero, k₅.mem, hm₄]
  have hV : regsVal s₅ rRegs + (s₅.gpr .x17).toNat * rwVal s₅ base (mWords a 0 6) =
      d * (p384 - wordsVal s.mem base b 6) + c * wordsVal s.mem base a 6 := by
    rw [hR₅, e₄, c₅, hw]
  have hVlt : d * (p384 - wordsVal s.mem base b 6) + c * wordsVal s.mem base a 6 < 2 ^ 17 * 2 ^ 384 := by
    have h1 := Nat.mul_le_mul_left d (Nat.sub_le p384 (wordsVal s.mem base b 6))
    have h2 := Nat.mul_le_mul_left c (Nat.le_of_lt hA)
    have hp : p384 < 2 ^ 384 := by decide
    have h3 := Nat.mul_le_mul_right p384 (Nat.le_of_lt hd)
    have h4 := Nat.mul_le_mul_right p384 (Nat.le_of_lt hc)
    omega_arith
  have hok : RowOk size .x17 rRegs (mWords a 0 6) := {
    nodup := by decide
    regs := by decide
    ok := by
      simp only [mWords, List.mem_cons, List.not_mem_nil, or_false]
      rintro w (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by omega_arith, by omega_arith⟩
    reads := by
      simp only [mWords, List.mem_cons, List.not_mem_nil, or_false]
      rintro w (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [RWord.reads, Src.reads]
    x2 := by decide
    x3 := by decide }
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs₅.ptr z₅ hok (by decide) (by decide) (by decide)
    (by simp only [mWords, rRegs, List.length_cons, List.length_nil]; omega_arith)
    (by rw [hV]; change _ < 2 ^ 448; omega_arith)) fun s₆ ⟨e₆, k₆⟩ => ?_
  rw [hV] at e₆
  have hs₆ : Scr s₆ base size := hs₅.of_keeps k₆ (by decide)
  have z₆ : s₆.gpr .x7 = 0 := by rw [k₆.gpr _ (by decide), z₅]
  have hm₆ : s₆.mem = s.mem := by rw [k₆.mem, k₅.mem, hm₄]
  -- The fold.
  have hsplit : regsVal s₆ rRegs = regsVal s₆ lowRegs + 2 ^ 384 * (s₆.gpr .x16).toNat := by
    rw [show rRegs = lowRegs ++ [.x16] from rfl, regsVal_append]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rfl
  have hLlt : regsVal s₆ lowRegs < 2 ^ 384 := regsVal_lt s₆ lowRegs
  have hT : (s₆.gpr .x16).toNat + 1 < 2 ^ 32 := by
    have h := hVlt
    rw [← e₆, hsplit] at h
    have : 2 ^ 384 * (s₆.gpr .x16).toNat < 2 ^ 384 * 2 ^ 17 := by omega_arith
    have := Nat.lt_of_mul_lt_mul_left this
    omega_arith
  rw [fold, List.append_assoc, WP.block_append_iff]
  refine WP.mono (foldPre_ok s₆ z₆ hT) fun s₇ ⟨q₇, w₇, k₇⟩ => ?_
  rw [WP.block_append_iff, show lowRegs = .x1 :: [.x4, .x5, .x6, .x14, .x15] from rfl]
  refine WP.mono (addsIn_ok s₇ (t := .x1) (ts := [.x4, .x5, .x6, .x14, .x15]) (h := .x2)
    (hs := [.x3, .x16, .x7, .x7, .x7]) rfl (by decide) (by decide)) fun s₈ ⟨e₈, k₈⟩ => ?_
  have z₇ : s₇.gpr .x7 = 0 := by rw [k₇.gpr _ (by decide), z₆]
  have hL₇ : regsVal s₇ [.x1, .x4, .x5, .x6, .x14, .x15] = regsVal s₆ lowRegs :=
    regsVal_congr fun r hr => k₇.gpr r (by revert r; decide)
  rw [hL₇, regsVal_fold z₇] at e₈
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₈
  -- The correction.
  have z₈ : s₈.gpr .x7 = 0 := by rw [k₈.gpr _ (by decide), z₇]
  rw [correct, List.append_assoc, WP.block_append_iff]
  refine WP.mono (correctPre_ok s₈ z₈) fun s₉ ⟨w₉, k₉⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addsIn_ok s₉ (t := .x1) (ts := [.x4, .x5, .x6, .x14, .x15]) (h := .x2)
    (hs := [.x3, .x16, .x17, .x17, .x17]) rfl (by decide) (by decide)) fun s₁₀ ⟨e₁₀, k₁₀⟩ => ?_
  have hL₉ : regsVal s₉ [.x1, .x4, .x5, .x6, .x14, .x15] = regsVal s₈ [.x1, .x4, .x5, .x6, .x14, .x15] :=
    regsVal_congr fun r hr => k₉.gpr r (by revert r; decide)
  rw [hL₉, w₉] at e₁₀
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁₀
  -- The store.
  have hs₁₀ : Scr s₁₀ base size :=
    ((((hs₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)).of_keeps k₉ (by decide)).of_keeps k₁₀ (by decide))
  refine WP.mono (stores_ok lowRegs hs₁₀ (o := o) ho ho8 (by decide)) fun t ⟨et, kt, Ot⟩ => ?_
  have hm₁₀ : s₁₀.mem = s.mem := by rw [k₁₀.mem, k₉.mem, k₈.mem, k₇.mem, hm₆]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx _ => by rw [Ot x hx, hm₁₀]⟩, ?_⟩
  · rw [kt.gpr r (by simp), kw k₁₀ (by decide) r hr, kw k₉ (by decide) r hr, kw k₈ (by decide) r hr,
      kw k₇ (by decide) r hr, kw k₆ (by decide) r hr, kw k₅ (by decide) r hr, kw k₄ (by decide) r hr,
      kw k₃ (by decide) r hr, kw k₂ (by decide) r hr, kw k₁ (by decide) r hr, kw k₀ (by decide) r hr]
  · rw [kt.rd, k₁₀.rd, k₉.rd, k₈.rd, k₇.rd, k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd, k₀.rd]
  · rw [kt.wr, k₁₀.wr, k₉.wr, k₈.wr, k₇.wr, k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr, k₀.wr]
  · rw [kt.sp, k₁₀.sp, k₉.sp, k₈.sp, k₇.sp, k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₂.sp, k₁.sp, k₀.sp]
  · have et' : wordsVal t.mem base o 6 = regsVal s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15] := et
    rw [et']
    have h0 := regsVal_lt s₈ [.x1, .x4, .x5, .x6, .x14, .x15]
    have h1 := regsVal_lt s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15]
    refine reduce_arith (T := (s₆.gpr .x16).toNat) (c₁ := s₈.c.toNat) (c₂ := s₁₀.c.toNat)
      (L₁ := regsVal s₈ [.x1, .x4, .x5, .x6, .x14, .x15]) (L₂ := regsVal s₁₀ [.x1, .x4, .x5, .x6, .x14, .x15]) (by rw [Nat.add_comm, ← e₆, hsplit]) hLlt hT h0
      (Bool.toNat_le _) (by rw [q₇] at e₈; omega_using [e₈, w₇]) h1 (Bool.toNat_le _) ?_
    rw [e₁₀]
    cases s₈.c <;> rfl

section
variable {m : Nat} [NeZero m] {R : Nat}

theorem toM_mod' (x : Nat) : toM m R (x % m) = toM m R x := by
  unfold toM; rw [ofNat_mod]

theorem toM_scale (c x : Nat) : toM m R (c * x) = Fin.ofNat m c * toM m R x := by
  unfold toM
  rw [ofNat_mul']
  grind

/-- A slot holding `(c a + d (m - b)) mod m` stands for `c A - d B`. -/
theorem toM_lin (a b c d : Nat) (hb : b < m) :
    toM m R ((c * a + d * (m - b)) % m) = Fin.ofNat m c * toM m R a - Fin.ofNat m d * toM m R b := by
  rw [toM_add, toM_scale, toM_scale]
  have h : toM m R (m - b) = -toM m R b := by
    have hh := toM_sub (m := m) (R := R) (A := 0) (B := b) (by omega_arith)
    simp only [Nat.zero_add, toM_mod', toM_zero] at hh
    grind
  rw [h]
  grind

end

/-- `Linear.lin` on the window's slots: `o` comes to stand for `c E_a - d E_b`. -/
theorem linOp_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop}
    (hL : Lay Impl.P384.Ops.M size Sl) (hAl : Aligned Impl.P384.Ops.M Sl) {base : Addr} {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv Impl.P384.Ops.M base size m Sl V E s) {o a b c d : Nat}
    (ho : Sl o) (ha : a ∈ V) (hb : b ∈ V) (hc : c < 2 ^ 16) (hd : d < 2 ^ 16) :
    WP isa (.block (lin o a b c d)) s fun t => OpKeepX base o s t ∧
      Inv Impl.P384.Ops.M base size m Sl (o :: V)
        (Function.update E o (Fin.ofNat m c * E a - Fin.ofNat m d * E b)) t := by
  subst hmp
  have hn := VG.Proof.P384.Ops.M_n
  have hla := hL.le a (hI.sl a ha)
  have hlb := hL.le b (hI.sl b hb)
  have hlo := hL.le o ho
  rw [hn] at hla hlb hlo
  have hA := hI.lt a ha
  have hB := hI.lt b hb
  rw [hn] at hA hB
  refine WP.mono (lin_ok hI.scr hI.mod hlo hla hlb (hAl.sl o ho) (hAl.sl a (hI.sl a ha))
    (hAl.sl b (hI.sl b hb)) hc hd hA hB) fun t ⟨hk, hv⟩ => ⟨hk, VG.Proof.P384.Ops.Inv.updateX hL hI ho hk ?_ ?_⟩
  · rw [hn, hv]; exact Nat.mod_lt _ (by decide)
  · rw [hn, hv, toM_lin _ _ _ _ hB]
    have va := hI.val a ha
    have vb := hI.val b hb
    rw [hn] at va vb
    rw [va, vb]

end VG.Proof.P384.Linear
