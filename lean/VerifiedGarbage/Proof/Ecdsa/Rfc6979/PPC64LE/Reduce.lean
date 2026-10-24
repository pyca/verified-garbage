module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Words32
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
public import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Deterministic ECDSA on PPC64LE: `h = bits2octets(digest)`

The digest's leftmost `4 k` bytes, big-endian in `k` 32-bit words (`Xw`),
less `n` (its words `nWn`), computed as the digest plus the complement of
`n` plus 1, a 32-bit digit at a time in 64-bit registers: the digest's words
go to `V`'s place, and those of the sum (`Dw`, with the carries `cc`) to
`K`'s (`subDigit_ok`). The last carry is 1 exactly when the subtraction does
not borrow; its negation is a mask that selects, word by word, the
difference's word or the digest's, stored big-endian at `h`'s place
(`selDigit_ok`). As the number is below `2^(32 k) < 2n`, this is it modulo
`n` (`mod_mathK`, `reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp M32)

/-! ## The arithmetic, over any words `X` -/

/-- One word of `x + (2³² - 1 - n) + c`. -/
abbrev wsub (x n : BitVec 32) (c : Nat) : Nat := x.toNat + (2 ^ 32 - 1 - n.toNat) + c

/-- The carries of the digest plus the complement of `N` plus 1. -/
def cc (N : Nat) (X : Nat → BitVec 32) : Nat → Nat
  | 0 => 1
  | j + 1 => wsub (X j) (nWn N j) (cc N X j) / 2 ^ 32

/-- The words of the digest plus the complement of `N` plus 1. -/
abbrev Dw (N : Nat) (X : Nat → BitVec 32) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (wsub (X j) (nWn N j) (cc N X j))

theorem cc_le (N : Nat) (X : Nat → BitVec 32) : ∀ j, cc N X j ≤ 1
  | 0 => Nat.le_refl _
  | j + 1 => by
    have := cc_le N X j; have := (X j).isLt; have := (nWn N j).isLt
    simp only [cc, wsub]; omega_arith

theorem chain (N : Nat) (X : Nat → BitVec 32) : ∀ i,
    wsum (Dw N X) i + 2 ^ (32 * i) * cc N X i + wsum (nWn N) i = wsum X i + 2 ^ (32 * i)
  | 0 => by simp [wsum, cc]
  | i + 1 => by
    have ih := chain N X i
    have hc := cc_le N X i
    have hN := (nWn N i).isLt
    have hw : (Dw N X i).toNat + 2 ^ 32 * cc N X (i + 1) =
        wsub (X i) (nWn N i) (cc N X i) := by
      simp only [cc, BitVec.toNat_ofNat]; omega_arith
    simp only [wsub] at hw
    simp only [wsum]
    rw [show 32 * (i + 1) = 32 + 32 * i by omega_arith, Nat.pow_add]
    generalize 2 ^ (32 * i) = P at *
    generalize cc N X (i + 1) = c' at *
    generalize cc N X i = c at *
    generalize (Dw N X i).toNat = D at *
    generalize (X i).toNat = Xv at *
    generalize (nWn N i).toNat = Nw at *
    have e : 2 ^ 32 - 1 - Nw + Nw = 2 ^ 32 - 1 := by omega_arith
    generalize 2 ^ 32 - 1 - Nw = M at *
    grind

/-- `x - N + 2^K` or `x`, by the last carry `c`: `x mod N`. -/
theorem select_math {x d c N K : Nat} (hc : c ≤ 1) (hd : d < 2 ^ K) (hx : x < 2 ^ K) (hN : 2 ^ K < 2 * N)
    (hch : d + 2 ^ K * c + N = x + 2 ^ K) :
    (if c = 1 then d else x) = x % N := by
  rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl
  · have := mod_mathK x N d K true (by simp only [Bool.toNat_true, Nat.mul_one]; omega_arith) hd hx hN
    simp only [Nat.zero_ne_one, ↓reduceIte] at this ⊢
    exact this
  · have := mod_mathK x N d K false (by simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]; omega_arith)
      hd hx hN
    simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    exact this

theorem wsum_ite (p : Prop) [Decidable p] (f g : Nat → BitVec 32) (k : Nat) :
    wsum (fun i => if p then f i else g i) k = if p then wsum f k else wsum g k := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

/-- The difference's words or the digest's, by the last carry: the digest modulo `N`. -/
theorem reduce_math (N k : Nat) (X : Nat → BitVec 32) (hlt : N < 2 ^ (32 * k)) (h2 : 2 ^ (32 * k) < 2 * N) :
    wsum (fun i => if cc N X k = 1 then Dw N X i else X i) k = wsum X k % N := by
  have hch := chain N X k
  rw [wsum_nWn, Nat.mod_eq_of_lt hlt] at hch
  rw [wsum_ite]
  exact select_math (cc_le N X k) (wsum_lt _ k) (wsum_lt _ k) h2 hch


/-! ## The code -/

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The `k` words of the digest at `dg`, least significant first. -/
abbrev Xw (k : Nat) (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 :=
  rev32 (m.readW (dg + BitVec.ofNat 64 (4 * (k - 1 - j))) 32)

theorem rev32_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 4⟩ r) : rev32 (m'.readW a 32) = rev32 (m.readW a 32) :=
  BitVec.eq_of_toNat_eq (by
    rw [show rev32 = byteRev32 from rfl, Proof.Weierstrass.byteRev32_ofBytes, Proof.Weierstrass.byteRev32_ofBytes]
    exact congrArg _ (bytesAt_frame hf hd (by decide)))

theorem and_m32 (v : BitVec 64) : (v &&& M32).toNat = (v.setWidth 32).toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, show M32.toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The words the subtraction leaves, `h`'s and `K`'s, in the frame. -/
abbrev HW (L : Lay dn) : List Region := [⟨L.B + BitVec.ofNat 64 128, 176⟩, ⟨L.B + BitVec.ofNat 64 352, L.e⟩]

/-- After `j` digits of the subtraction, from the memory `M`. -/
structure SubInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ M : Mem) (j : Nat)
    (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  r9 : u.gpr .r9 = L.dg
  r11 : u.gpr .r11 = L.B + BitVec.ofNat 64 96
  r0 : u.gpr .r0 = M32
  r10 : (u.gpr .r10).toNat = cc N (Xw k M L.dg) j
  frame : Frame (HW L) M u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (192 + 4 * i)) 32 = Xw k M L.dg i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (128 + 4 * i)) 32 = Dw N (Xw k M L.dg) i

/-- A word written in the frame, within `HW`. -/
theorem hw_frame {m : Mem} {o : Nat} (ho : 128 ≤ o ∧ o + 4 ≤ 304 ∨ 352 ≤ o ∧ o + 4 ≤ 352 + L.e)
    (hne : L.e ≤ 144) (v : BitVec 32) : Frame (HW L) m (m.writeW (L.B + BitVec.ofNat 64 o) v) := by
  rcases ho with ⟨ho₁, ho₂⟩ | ⟨ho₁, ho₂⟩
  · exact (Frame.refl _ _).writeW (r := ⟨L.B + BitVec.ofNat 64 128, 176⟩) (by simp) _
      (Offset.contains _ ho₁ (by omega) (by omega))
  · exact (Frame.refl _ _).writeW (r := ⟨L.B + BitVec.ofNat 64 352, L.e⟩) (by simp) _
      (Offset.contains _ ho₁ (by omega) (by omega))

/-- A word written in the frame keeps `Ctx`. -/
theorem ctx_word (hL : L.Ok) {u u' : State} (hc : Ctx L g lr m₀ u) (k : Kp [] u u') (hg : u'.gpr = u.gpr)
    {o : Nat} (ho : o + 4 ≤ 312 ∨ 352 ≤ o ∧ o + 4 ≤ 352 + L.e) {v : BitVec 32}
    (hm : u'.mem = u.mem.writeW (L.B + BitVec.ofNat 64 o) v) : Ctx L g lr m₀ u' :=
  hc.keep hL k.rd k.wr k.sp (fun r _ => by rw [hg]) (ws := [⟨L.B + BitVec.ofNat 64 o, 4⟩])
    (by rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by
      simp only [List.mem_singleton]; rintro r rfl
      rcases ho with ho | ⟨ho₁, ho₂⟩
      · exact safe_low L ho
      · exact safe_ext L ho₁ ho₂)

/-- Words apart in the frame. -/
theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 544) (hy : y + 4 ≤ 544) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega) (by omega)

theorem subDigit_ok (hL : L.Ok) {c : Cfg} {k : Nat} (hk : c.len = 4 * k) (hk16 : k ≤ 16) (hdn : 4 * k ≤ dn)
    {M : Mem} {j : Nat} (hj : j < k) {u : State} (h : SubInv c.n k L g lr m₀ M j u) :
    WP isa (.block (c.subDigit j)) u (SubInv c.n k L g lr m₀ M (j + 1)) := by
  have hnB := hL.nB
  have hc := h.ctx
  have ho : c.len - 4 * (j + 1) = 4 * (k - 1 - j) := by omega
  simp only [Cfg.subDigit, Impl.Mont.PPC64LE.movImm, List.cons_append, List.nil_append]
  refine stepLi (by omega) fun u₁ k₁ m₁ v₁ => ?_
  rw [ho] at v₁
  have hrd : ∀ r ∈ HW L, Region.Disjoint ⟨L.dg + BitVec.ofNat 64 (4 * (k - 1 - j)), 4⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hL.dg_safe (safe_low L (by omega))).sub_left (Offset.sub_base _ (by omega))
    · exact (hL.dg_safe (safe_ext L (by omega) (by omega))).sub_left (Offset.sub_base _ (by omega))
  refine stepLwbrx (ea := L.dg + BitVec.ofNat 64 (4 * (k - 1 - j))) (by decide)
    (by rw [k₁.gpr _ (by decide), h.r9, v₁]) (by rw [k₁.rd, k₁.wr]; exact hc.inDg (by omega) (by omega))
    fun u₂ k₂ m₂ v₂ => ?_
  have xv : rev32 (u₂.mem.readW (L.dg + BitVec.ofNat 64 (4 * (k - 1 - j))) 32) = Xw k M L.dg j := by
    rw [m₂, m₁]; exact rev32_frame h.frame hrd
  have hc₂ := hc.kp hL (k₁.mono.trans k₂.mono (rs := [.r8, .r7])) (by rw [m₂, m₁])
  refine stepStw (a := L.B + BitVec.ofNat 64 (192 + 4 * j)) (by decide) (by simp only [fV]; omega)
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h.r11, fr_add,
      show 96 + (fV + 4 * j) = 192 + 4 * j by simp only [fV]; omega])
    (hc₂.inFrW (by omega) (by omega)) fun u₃ k₃ g₃ m₃ => ?_
  have hc₃ := ctx_word hL hc₂ k₃ g₃ (by omega) m₃
  refine stepLis fun u₄ k₄ m₄ v₄ => ?_
  refine stepOri fun u₅ k₅ m₅ v₅ => ?_
  refine stepAnd fun u₆ k₆ m₆ v₆ => ?_
  refine stepAdd fun u₇ k₇ m₇ v₇ => ?_
  refine stepSub fun u₈ k₈ m₈ v₈ => ?_
  refine stepAdd fun u₉ k₉ m₉ v₉ => ?_
  have K₉ : Kp [.r12, .r7] u₃ u₉ :=
    (((((k₄.mono.trans k₅.mono).trans k₆.mono).trans k₇.mono).trans k₈.mono).trans k₉.mono)
  have hm₉ : u₉.mem = u₃.mem := by rw [m₉, m₈, m₇, m₆, m₅, m₄]
  have hc₉ := hc₃.kp hL K₉ hm₉
  have K₂ : Kp [.r8, .r7] u u₂ := k₁.mono.trans k₂.mono
  -- The values.
  have x7 : (u₆.gpr .r7).toNat = (Xw k M L.dg j).toNat := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), g₃, v₂, ← m₂, ← xv,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]
  have r0 : ∀ {v : State}, Kp [.r12, .r7] u₃ v → v.gpr .r0 = M32 := fun K => by
    rw [K.gpr _ (by decide), g₃, K₂.gpr _ (by decide), h.r0]
  have n12 : (u₆.gpr .r12).toNat = (nWn c.n j).toNat := by
    rw [v₆, r0 (k₄.mono.trans k₅.mono), and_m32, v₅, v₄, lis_ori]; rfl
  have hcc := cc_le c.n (Xw k M L.dg) j
  have hX := (Xw k M L.dg j).isLt
  have hN := (nWn c.n j).isLt
  have c10 : (u₈.gpr .r10).toNat = cc c.n (Xw k M L.dg) j := by
    rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
      k₄.gpr _ (by decide), g₃, K₂.gpr _ (by decide), h.r10]
  have e9 : (u₉.gpr .r7).toNat = wsub (Xw k M L.dg j) (nWn c.n j) (cc c.n (Xw k M L.dg) j) := by
    rw [v₉, v₈, v₇, k₇.gpr .r12 (by decide), r0 (k₄.mono.trans (k₅.mono.trans k₆.mono))]
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_add, x7, n12, c10, show M32.toNat = 2 ^ 32 - 1 from rfl]
    simp only [wsub]
    omega
  refine stepStw (a := L.B + BitVec.ofNat 64 (128 + 4 * j)) (by decide) (by simp only [fK]; omega)
    (by rw [K₉.gpr _ (by decide), g₃, K₂.gpr _ (by decide), h.r11, fr_add,
      show 96 + (fK + 4 * j) = 128 + 4 * j by simp only [fK]; omega])
    (hc₉.inFrW (by omega) (by omega)) fun u₁₀ k₁₀ g₁₀ m₁₀ => ?_
  have hc₁₀ := ctx_word hL hc₉ k₁₀ g₁₀ (by omega) m₁₀
  refine stepLsr (by decide) fun u₁₁ k₁₁ m₁₁ v₁₁ => wp_nil ?_
  have K : Kp [.r8, .r7, .r12, .r10] u u₁₁ :=
    ((((K₂.mono.trans k₃.mono).trans K₉.mono).trans k₁₀.mono).trans k₁₁.mono)
  have dv : (u₉.gpr .r7).setWidth 32 = Dw c.n (Xw k M L.dg) j :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth, e9, BitVec.toNat_ofNat])
  have hm : u₁₁.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (192 + 4 * j)) (Xw k M L.dg j)).writeW
      (L.B + BitVec.ofNat 64 (128 + 4 * j)) (Dw c.n (Xw k M L.dg) j) := by
    rw [m₁₁, m₁₀, dv, hm₉, m₃, v₂, lo32_ext, ← m₂, xv, m₂, m₁]
  refine ⟨hc₁₀.kp hL k₁₁ m₁₁, by rw [K.gpr _ (by decide), h.r9], by rw [K.gpr _ (by decide), h.r11],
    by rw [K.gpr _ (by decide), h.r0], ?_, ?_, ?_, ?_⟩
  · rw [v₁₁, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, k₁₀.gpr _ (by decide), e9]; rfl
  · rw [hm]
    exact h.frame.trans ((hw_frame (by omega) hc.ne _).trans (hw_frame (by omega) hc.ne _))
  · intro i hi
    rw [hm, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.x i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · intro i hi
    rw [hm]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.d i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]

/-- The digits before `i`. -/
theorem subs_ok (hL : L.Ok) {c : Cfg} {k : Nat} (hk : c.len = 4 * k) (hk16 : k ≤ 16) (hdn : 4 * k ≤ dn)
    {M : Mem} : ∀ i ≤ k, ∀ u, SubInv c.n k L g lr m₀ M 0 u →
      WP isa (.block ((List.range i).flatMap c.subDigit)) u (SubInv c.n k L g lr m₀ M i)
  | 0, _, u, h => wp_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hL hk hk16 hdn i (by omega) u h) fun u' h' =>
      subDigit_ok hL hk hk16 hdn (by omega) h'

/-- The mask of the last carry. -/
abbrev mask (N k : Nat) (L : Lay dn) (M : Mem) : BitVec 64 :=
  if cc N (Xw k M L.dg) k = 1 then BitVec.allOnes 64 else 0

/-- The word selected. -/
abbrev Sw (N k : Nat) (L : Lay dn) (M : Mem) (i : Nat) : BitVec 32 :=
  if cc N (Xw k M L.dg) k = 1 then Dw N (Xw k M L.dg) i else Xw k M L.dg i

/-- After the mask and `j` words of the selection, from `M`. -/
structure SelInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ M : Mem) (j : Nat)
    (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  r11 : u.gpr .r11 = L.B + BitVec.ofNat 64 96
  r10 : u.gpr .r10 = mask N k L M
  frame : Frame (HW L) M u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (96 + L.ho + 4 * (k - 1 - i))) 32 = rev32 (Sw N k L M i)
  x : ∀ i < k, u.mem.readW (L.B + BitVec.ofNat 64 (192 + 4 * i)) 32 = Xw k M L.dg i
  d : ∀ i < k, u.mem.readW (L.B + BitVec.ofNat 64 (128 + 4 * i)) 32 = Dw N (Xw k M L.dg) i

theorem sel_val (x d : BitVec 32) (p : Prop) [Decidable p] :
    (x.setWidth 64 ^^^ ((d.setWidth 64 ^^^ x.setWidth 64) &&& (if p then BitVec.allOnes 64 else 0))).setWidth 32 =
      if p then d else x := by
  by_cases h : p
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [BitVec.xor_comm (d.setWidth 64), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, lo32_ext]
  · simp only [h, ↓reduceIte]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero, lo32_ext]

theorem selDigit_ok (hL : L.Ok) {c : Cfg} {k : Nat} (hk : c.len = 4 * k) (hk16 : k ≤ 16)
    (hql : c.len = L.q) (hcD : c.H.D = dn) (hq : L.HOk)
    {M : Mem} {j : Nat} (hj : j < k) {u : State} (h : SelInv c.n k L g lr m₀ M j u) :
    WP isa (.block (c.selDigit j)) u (SelInv c.n k L g lr m₀ M (j + 1)) := by
  have hnB := hL.nB
  have hc := h.ctx
  have hne := hc.ne
  have ⟨hq₁, hq₂⟩ := hq
  have hho : c.fHo = L.ho := L.fHo_eq hql hcD
  simp only [Cfg.selDigit]
  refine stepLwz (a := L.B + BitVec.ofNat 64 (192 + 4 * j)) (by decide) (by simp only [fV]; omega)
    (by rw [h.r11, fr_add, show 96 + (fV + 4 * j) = 192 + 4 * j by simp only [fV]; omega])
    (hc.inFr (by omega) (by omega)) fun u₁ k₁ m₁ v₁ => ?_
  refine stepLwz (a := L.B + BitVec.ofNat 64 (128 + 4 * j)) (by decide) (by simp only [fK]; omega)
    (by rw [k₁.gpr _ (by decide), h.r11, fr_add, show 96 + (fK + 4 * j) = 128 + 4 * j by simp only [fK]; omega])
    (by rw [k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega)) fun u₂ k₂ m₂ v₂ => ?_
  refine stepXor fun u₃ k₃ m₃ v₃ => ?_
  refine stepAnd fun u₄ k₄ m₄ v₄ => ?_
  refine stepXor fun u₅ k₅ m₅ v₅ => ?_
  refine stepLi (by rw [hho]; omega) fun u₆ k₆ m₆ v₆ => ?_
  have K₆ : Kp [.r7, .r8, .r12] u u₆ :=
    ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono
  have hm₆ : u₆.mem = u.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  have hc₆ := hc.kp hL K₆ hm₆
  have ea : L.B + BitVec.ofNat 64 96 + BitVec.ofNat 64 (c.fHo + c.len - 4 * (j + 1)) =
      L.B + BitVec.ofNat 64 (96 + L.ho + 4 * (k - 1 - j)) := by
    rw [fr_add, show 96 + (c.fHo + c.len - 4 * (j + 1)) = 96 + L.ho + 4 * (k - 1 - j) by rw [hho]; omega]
  refine stepStwbrx (ea := L.B + BitVec.ofNat 64 (96 + L.ho + 4 * (k - 1 - j))) (by decide)
    (by rw [K₆.gpr _ (by decide), h.r11, v₆, ea])
    (hc₆.inFrW (by omega) (by omega)) fun u₇ k₇ g₇ m₇ => wp_nil ?_
  have val : (u₆.gpr .r7).setWidth 32 = Sw c.n k L M j := by
    have r7₂ : u₂.gpr .r7 = (Xw k M L.dg j).setWidth 64 := by rw [k₂.gpr _ (by decide), v₁, h.x j hj]
    have r8₂ : u₂.gpr .r8 = (Dw c.n (Xw k M L.dg) j).setWidth 64 := by rw [v₂, m₁, h.d j hj]
    have r10₃ : u₃.gpr .r10 = mask c.n k L M := by
      rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), h.r10]
    rw [k₆.gpr _ (by decide), v₅, k₄.gpr .r7 (by decide), v₄, v₃, k₃.gpr .r7 (by decide), r10₃, r7₂, r8₂, Sw, mask]
    exact sel_val _ _ _
  have hm : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (96 + L.ho + 4 * (k - 1 - j))) (rev32 (Sw c.n k L M j)) := by
    rw [m₇, val, hm₆]
  refine ⟨ctx_word hL hc₆ k₇ g₇ (by omega) m₇, by rw [g₇, K₆.gpr _ (by decide), h.r11],
    by rw [g₇, K₆.gpr _ (by decide), h.r10], by rw [hm]; exact h.frame.trans (hw_frame (by omega) hne _),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.h i hij
    · rw [show i = j by omega, Mem.readW_writeW_self32]
  · rw [hm, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.x i hi
  · rw [hm, Mem.readW_writeW_sep (fr_sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h.d i hi

theorem sels_ok (hL : L.Ok) {c : Cfg} {k : Nat} (hk : c.len = 4 * k) (hk16 : k ≤ 16)
    (hql : c.len = L.q) (hcD : c.H.D = dn) (hq : L.HOk) {M : Mem} :
    ∀ i ≤ k, ∀ u, SelInv c.n k L g lr m₀ M 0 u →
      WP isa (.block ((List.range i).flatMap c.selDigit)) u (SelInv c.n k L g lr m₀ M i)
  | 0, _, u, h => wp_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hL hk hk16 hql hcD hq i (by omega) u h) fun u' h' =>
      selDigit_ok hL hk hk16 hql hcD hq (by omega) h'

theorem mask_val {c : BitVec 64} (h : c.toNat ≤ 1) :
    BitVec.ofNat 64 0 - c = if c.toNat = 1 then BitVec.allOnes 64 else 0 := by
  rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with e | e
  · rw [show c = 0 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide
  · rw [show c = 1 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide

/-- `h`: the digest modulo `n`, big-endian in the frame at `h`'s place. -/
theorem reduce_ok (hL : L.Ok) {c : Cfg} {k : Nat} (hk : c.len = 4 * k) (hk16 : k ≤ 16) (hdn : 4 * k ≤ dn)
    (hql : c.len = L.q) (hcD : c.H.D = dn) (hq : L.HOk)
    (hn₁ : c.n < 2 ^ (32 * k)) (hn₂ : 2 ^ (32 * k) < 2 * c.n) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block c.reduce) t fun t' => Ctx L g lr m₀ t' ∧ Frame (HW L) t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + L.ho)) (4 * k)) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg (4 * k)) % c.n := by
  have hnB := hL.nB
  simp only [Cfg.reduce, Impl.Mont.PPC64LE.mask32, List.append_assoc, List.cons_append, List.nil_append,
    show c.len / 4 = k by omega]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (by rw [k₁.rd, k₁.wr]; exact hc.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLi (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepOri fun t₄ k₄ m₄ v₄ => ?_
  refine stepOris fun t₅ k₅ m₅ v₅ => ?_
  refine stepLi (by decide) fun t₆ k₆ m₆ v₆ => ?_
  have K₆ : Kp [.r11, .r9, .r0, .r10] t t₆ :=
    ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono
  have hm₆ : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  rw [WP.block_append_iff]
  refine WP.mono (subs_ok (M := t.mem) hL hk hk16 hdn k (Nat.le_refl _) t₆
    ⟨hc.kp hL K₆ hm₆, by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), v₂, m₁, hc.pDg],
      by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide),
        k₂.gpr _ (by decide), hb],
      by rw [k₆.gpr _ (by decide), v₅, v₄, v₃]; decide, by rw [v₆]; rfl, by rw [hm₆]; exact Frame.refl _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩) fun u hu => ?_
  refine stepLi (by decide) fun u₁ l₁ n₁ w₁ => ?_
  refine stepSub fun u₂ l₂ n₂ w₂ => ?_
  have L₂ : Kp [.r12, .r10] u u₂ := l₁.mono.trans l₂.mono
  have hn₂' : u₂.mem = u.mem := by rw [n₂, n₁]
  have h10 : u₂.gpr .r10 = mask c.n k L t.mem := by
    rw [w₂, w₁, l₁.gpr _ (by decide), mask_val (by rw [hu.r10]; exact cc_le _ _ _), hu.r10]
  refine WP.mono (sels_ok (M := t.mem) hL hk hk16 hql hcD hq k (Nat.le_refl _) u₂
    ⟨hu.ctx.kp hL L₂ hn₂', by rw [L₂.gpr _ (by decide), hu.r11], h10, by rw [hn₂']; exact hu.frame,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => by rw [hn₂']; exact hu.x i hi,
      fun i hi => by rw [hn₂']; exact hu.d i hi⟩) fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  have hX := ofBytes_words t.mem (Xw k t.mem L.dg) L.dg k fun j hj => rfl
  have hH := ofBytes_words t'.mem (Sw c.n k L t.mem) (L.B + BitVec.ofNat 64 (96 + L.ho)) k fun j hj => by
    rw [Offset.add_add, h'.h j hj]
    exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  have hd : Spec.Sha256.bytesAt m₀ L.dg (4 * k) = Spec.Sha256.bytesAt t.mem L.dg (4 * k) := by
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => (hc.dg_byte hL (by have := List.mem_range.mp hi; omega)).symm
  rw [hd]
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * k)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * k)) % _
  rw [hH, hX]
  exact reduce_math _ _ _ hn₁ hn₂

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
