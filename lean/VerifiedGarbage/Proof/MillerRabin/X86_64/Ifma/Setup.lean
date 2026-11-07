module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Mult

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Out
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubExp

/-!
# The IFMA Miller–Rabin round: the area before the vector code

`setup_ok`: from the prepared workspace at `H` (`rdi`) of `W` words (the
candidate `c` in `aN`, `b R mod c` in `aXm`, `R mod c` in `aR1`,
`R = 2^(64 W)`, and `-c⁻¹ mod 2⁶⁴` in the header), the area at `areaBase l H`
(array `aT0` rounded up to 64 bytes) holds `Pre`'s numbers; only the table
arrays change.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma (limb val52)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)
open VG.Impl.Rsa.X86_64.PubIfma (arr)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.Bignum (sMinv)
open VG.Impl.Bignum.Public (aN aXm)
open VG.Impl.RsaKeyGen.X86_64.Candidate (aT0 aR1)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The area's base: array `aT0` of the workspace at `H`, rounded up to a
multiple of 64 (`area`). -/
def areaBase (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (H : Addr) : Addr :=
  (H + BitVec.ofNat 64 (arr l aT0) + 63#64) &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-64))

/-- Rounding down to a multiple of 64. -/
theorem round64 {y : Nat} (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 y &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-64))).toNat = y / 64 * 64 := by
  rw [show BitVec.signExtend 64 (BitVec.ofInt 32 (-64)) = BitVec.ofNat 64 ((2 ^ 58 - 1) <<< 6) by decide]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (by decide : (2 ^ 58 - 1) <<< 6 < 2 ^ 64),
    show y / 64 * 64 = (y >>> 6) <<< 6 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h₁ : 6 ≤ i
  · by_cases h₂ : i - 6 < 58
    · simp [h₁, h₂, Nat.add_sub_cancel' h₁]
    · have : y.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h₁, h₂, Nat.add_sub_cancel' h₁, this]
  · simp [h₁]

/-- The table arrays' bytes. -/
theorem arr_tab : arr l (aT0 + 16) = arr l aT0 + 16 * (8 * (l.W + 2)) := by
  simp only [arr, aT0]; omega

/-- The area lies in the table arrays: from array `aT0`'s offset at most 63
bytes on, `size l` bytes before array `aT0 + 16`'s. -/
theorem areaBase_ofs (hl : PubOk l) {H : Addr} (hn : H.toNat + arr l (aT0 + 16) ≤ 2 ^ 64) :
    arr l aT0 ≤ ofs H (areaBase l H) ∧ ofs H (areaBase l H) + size l ≤ arr l (aT0 + 16) ∧
      areaBase l H = off H (ofs H (areaBase l H)) := by
  have ho := (PubOk.offs hl).1
  have ha := arr_tab (l := l)
  have hx : (H + BitVec.ofNat 64 (arr l aT0) + 63#64).toNat = H.toNat + arr l aT0 + 63 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hb : (areaBase l H).toNat = (H.toNat + arr l aT0 + 63) / 64 * 64 := by
    unfold areaBase
    have e := round64 (H + BitVec.ofNat 64 (arr l aT0) + 63#64).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hx] at e
    exact e
  have hd : ofs H (areaBase l H) = (areaBase l H).toNat - H.toNat := by
    simp only [ofs, BitVec.toNat_sub]; omega_arith
  refine ⟨by omega_arith, by omega_arith, BitVec.eq_of_toNat_eq ?_⟩
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

open VG.Proof.Bignum (word_off wv_off)
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem word_stMem_other limbN se_ofNat)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Rsa.X86_64.CrtIfma (at_)
open VG.Impl.Rsa.X86_64.PubIfma (ld52 base)

/-! ## Changes within the area -/

/-- A change within the area at `off H d` is within the table arrays. -/
theorem frm_area {H B : Addr} {d : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hB : B = off H d) (hd : arr l aT0 ≤ d) (hd' : d + size l ≤ arr l (aT0 + 16))
    (hn : H.toNat + arr l (aT0 + 16) ≤ 2 ^ 64) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ size l) :
    Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m' := by
  subst hB
  have ha := arr_tab (l := l)
  have : 0 < size l := by unfold size; omega
  refine (VG.Proof.Bignum.Frm.rebase h (by omega_arith) fun r hr' => by
    have := hr r hr'; omega_arith).widen fun r hr' => ?_
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  exact ⟨_, List.mem_singleton_self _, by simp only; omega_arith, by simp only; omega_arith⟩

/-- A word of the workspace outside the table arrays. -/
theorem word_tab {H : Addr} {m m' : Mem} (h : Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m') {e : Nat}
    (he : e + 8 ≤ arr l aT0 ∨ arr l (aT0 + 16) ≤ e) (he' : e + 8 ≤ 2 ^ 64) : word m' H e = word m H e :=
  h.word_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := arr_tab (l := l); simp only; omega_arith) he'

/-- An array of the workspace outside the table arrays. -/
theorem wv_tab {H : Addr} {m m' : Mem} (h : Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m') {e k : Nat}
    (he : e + 8 * k ≤ arr l aT0 ∨ arr l (aT0 + 16) ≤ e) (he' : e + 8 * k ≤ 2 ^ 64) : wv m' H e k = wv m H e k :=
  h.wv_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := arr_tab (l := l); simp only; omega_arith) he'

/-- The limbs at `a` through a change elsewhere. -/
theorem limb_frm (hl : PubOk l) {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {a : Nat}
    (hs : ∀ r ∈ rs, a + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a) (ha : a + l.NB < 2 ^ 31) :
    ∀ j < l.L, limb l m' B a j = limb l m B a j := fun j hj => by
  have := VG.Proof.Bignum.X86_64.Ifma.off_ltN hl.amm hj
  show (word m' B (a + l.off j)).toNat = (word m B (a + l.off j)).toNat
  rw [h.word_eq (fun r hr => by have := hs r hr; omega_arith) (by omega_arith)]

/-- A number at `a` through a change elsewhere. -/
theorem num_frm (hl : PubOk l) {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {a v : Nat}
    (hc : Canon l m B a ∧ val52 l m B a = v)
    (hs : ∀ r ∈ rs, a + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ a) (ha : a + l.NB < 2 ^ 31) :
    Canon l m' B a ∧ val52 l m' B a = v :=
  have e := limb_frm hl h hs ha
  ⟨fun j hj => (e j hj) ▸ hc.1 j hj, (lval_congr e).trans hc.2⟩

/-- `Mod` through a change from `NB + 32` on. -/
theorem mod_frm (hl : PubOk l) {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {c k : Nat} (hm : Mod l m B c k)
    (h : Frm B rs m m') (hs : ∀ r ∈ rs, l.NB + 32 ≤ r.1) (hN : l.NB + 32 < 2 ^ 31) : Mod l m' B c k := by
  have e := limb_frm hl h (a := 0) (fun r hr => .inl (by have := hs r hr; omega_arith)) (by omega_arith)
  have hL := (VG.Proof.Bignum.X86_64.Ifma.Pub.PubOk.amm hl).bounds.1
  refine ⟨fun j hj => (e j hj) ▸ hm.lt j hj, (lval_congr e).trans hm.val, fun t ht => ?_, hm.klt,
    by rw [e 0 (by simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.L]; omega_arith)]; exact hm.inv, hm.big⟩
  rw [h.word_eq (fun r hr => by have := hs r hr; simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.oK0]; omega_arith)
    (by simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.oK0]; omega_arith)]
  exact hm.k0 t ht

/-- A number from limbs `limbN v`. -/
theorem num_of (hl : PubOk l) {m : Mem} {B : Addr} {o v : Nat}
    (h : ∀ q < l.L, word m B (o + l.off q) = BitVec.ofNat 64 (limbN v q)) (hv : v < 2 ^ (64 * l.W)) :
    Canon l m B o ∧ val52 l m B o = v :=
  ⟨fun q hq => by
    show (word m B (o + l.off q)).toNat < _
    rw [h q hq]; exact VG.Proof.Bignum.X86_64.Ifma.Pub.limbN_lt64 _ _,
   VG.Proof.Bignum.X86_64.Ifma.Pub.val52_of h (Nat.lt_of_lt_of_le hv
    (VG.Proof.Bignum.X86_64.AmmSym.pow2_le (VG.Proof.Bignum.X86_64.Ifma.conv_boundsN hl.amm).2.1))⟩

theorem one_r {x : Nat × Nat} {p : Nat × Nat → Prop} (h : p x) : ∀ r ∈ [x], p r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact h

theorem two_r {x y : Nat × Nat} {p : Nat × Nat → Prop} (hx : p x) (hy : p y) : ∀ r ∈ [x, y], p r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [hx, hy]

theorem three_r {x y z : Nat × Nat} {p : Nat × Nat → Prop} (hx : p x) (hy : p y) (hz : p z) :
    ∀ r ∈ [x, y, z], p r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hx, hy, hz]

theorem pow_mod_shift {a b e c : Nat} (h : a + b = e) : 2 ^ a * (2 ^ b % c) % c = 2 ^ e % c := by
  rw [Nat.mul_mod_mod, ← Nat.pow_add, h]

/-! ## The first block -/

/-- An array of the workspace (`aN`, `aXm` or `aR1`) into the limbs at `o`. -/
theorem ldA_ok (hl : PubOk l) {s : State} {H B : Addr} {d n j o : Nat} (hB : s.gpr .rbx = B)
    (hdi : s.gpr .rdi = H) (h12 : s.gpr .r12 = mask52) (hBd : B = off H d) (hd : arr l aT0 ≤ d)
    (hd' : d + size l ≤ arr l (aT0 + 16)) (hs : Scr s H (8 * n)) (hsz : arr l 27 ≤ 8 * n)
    (hj : j = aN ∨ j = aXm ∨ j = aR1) (ho : o + l.NB ≤ size l) :
    WP isa (.block (ld52 l j o)) s fun t =>
      (∀ q < l.L, word t.mem B (o + l.off q) = BitVec.ofNat 64 (limbN (wv s.mem H (arr l j) l.W) q)) ∧
      Outside B o l.NB s.mem t.mem ∧ Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem t.mem ∧
      Keep [.rsi, .r11, .rax, .rcx, .rbp] s t ∧ t.mxcsr = s.mxcsr := by
  have ha := arr_tab (l := l)
  have hsize := (PubOk.offs hl).2.1
  have hW := VG.Proof.Bignum.X86_64.Ifma.conv_boundsN hl.amm
  have hn : H.toNat + 8 * n ≤ 2 ^ 64 := hs.nowrap
  have hF : ∀ q < l.L, l.off q + 8 ≤ l.NB := fun q hq => VG.Proof.Bignum.X86_64.Ifma.off_ltN hl.amm hq
  have hJ : (arr l j + 8 * (l.W + 2) ≤ arr l aT0 ∨ arr l (aT0 + 16) ≤ arr l j) ∧
      arr l j + 8 * (l.W + 2) ≤ arr l 27 ∧ arr l j < 2 ^ 31 := by
    rcases hj with rfl | rfl | rfl <;> simp only [arr, aT0, aN, aXm, aR1, VG.Impl.Bignum.hdrBytes] <;> omega
  have h27 : arr l (aT0 + 16) ≤ arr l 27 := by simp only [arr, aT0]; omega
  have hsB : Scr s B (size l) := by
    rw [hBd]; exact hs.sub (by omega_arith) (by unfold size; omega)
  have fa : ∀ m m' : Mem, Outside B o l.NB m m' → Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m' :=
    fun m m' f => frm_area (Frm.of_outside f (List.mem_singleton_self _)) hBd hd hd' (by omega_arith)
      (one_r (p := fun r => r.1 + r.2 ≤ size l) ho)
  refine WP.mono (VG.Proof.Bignum.X86_64.Ifma.Pub.ld52_ok hl hB hdi h12 hJ.2.2
    (fun i hi => by rw [VG.Proof.Bignum.X86_64.AmmSym.off_add]; exact hs.ld (by omega_arith))
    (fun q hq => hsB.st (by have := hF q hq; omega_arith)) (by omega_arith)
    (fun m m' f i hi => by
      rw [word_off, word_off]
      exact word_tab (fa m m' f) (by omega_arith) (by omega_arith)))
    fun t ⟨v, f, k, x⟩ => ⟨fun q hq => by rw [v q hq, wv_off, Nat.add_zero], f, fa _ _ f, k, x⟩

/-- `setup`'s first block: the area's base, the modulus and `k₀`, `b R mod c`
at `T_1`, and `R mod c` at `S` and `T_0`. -/
theorem block_ok (hl : PubOk l) {s : State} {H B : Addr} {d n c : Nat}
    (hdi : s.gpr .rdi = H) (hs : Scr s H (8 * n)) (hsz : arr l 27 ≤ 8 * n)
    (hB : areaBase l H = B) (hBd : B = off H d) (hd : arr l aT0 ≤ d) (hd' : d + size l ≤ arr l (aT0 + 16))
    (hc : wv s.mem H (arr l aN) l.W = c)
    (hinv : ((word s.mem H (arr l aN)).toNat * (word s.mem H (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block (area l ++ ld52 l aN 0 ++
      ([.mov .rax (.mem (hdr sMinv)), .alu .and .rax (.reg .r12)] : List Instr) ++
      (List.range 4).map (fun i => .store (at_ .rbx (l.NB + 8 * i)) .rax) ++ ld52 l aXm (oT l 1) ++
      ld52 l aR1 (oS l) ++ ld52 l aR1 (oT l 0))) s fun t =>
      t.gpr .rbx = B ∧ t.gpr .r12 = mask52 ∧
      Mod l t.mem B c ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) ∧
      (Canon l t.mem B (oT l 1) ∧ val52 l t.mem B (oT l 1) = wv s.mem H (arr l aXm) l.W) ∧
      (Canon l t.mem B (oS l) ∧ val52 l t.mem B (oS l) = wv s.mem H (arr l aR1) l.W) ∧
      (Canon l t.mem B (oT l 0) ∧ val52 l t.mem B (oT l 0) = wv s.mem H (arr l aR1) l.W) ∧
      Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem t.mem ∧
      Keep [.rbx, .r12, .rsi, .r11, .rax, .rcx, .rbp] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, -, -, -, -, -, -, -, -, -, -, -, -⟩ := PubOk.offs hl
  obtain ⟨e1, e2, -⟩ := PubOk.ends hl
  have o6₁ := o6 1
  have e1₀ := e1 0 (by decide)
  have e1₁ := e1 1 (by decide)
  have ha := arr_tab (l := l)
  have hW := VG.Proof.Bignum.X86_64.Ifma.conv_boundsN hl.amm
  have h27 : arr l (aT0 + 16) ≤ arr l 27 := by simp only [arr, aT0]; omega
  have hn : H.toNat + 8 * n ≤ 2 ^ 64 := hs.nowrap
  have hF : ∀ q < l.L, l.off q + 8 ≤ l.NB := fun q hq => VG.Proof.Bignum.X86_64.Ifma.off_ltN hl.amm hq
  have hsB : Scr s B (size l) := by
    rw [hBd]; exact hs.sub (by omega_arith) (by unfold size; omega)
  have hT0 : arr l aT0 < 2 ^ 31 := by simp only [arr, aT0, VG.Impl.Bignum.hdrBytes]; omega
  have hMv : 8 * sMinv + 8 ≤ arr l aT0 := by simp only [arr, aT0, sMinv, VG.Impl.Bignum.hdrBytes]; omega
  have fa : ∀ {m m' : Mem} {o k : Nat}, Outside B o k m m' → o + k ≤ size l →
      Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m' :=
    fun f ho => frm_area (Frm.of_outside f (List.mem_singleton_self _)) hBd hd hd' (by omega_arith)
      (one_r (p := fun r => r.1 + r.2 ≤ size l) ho)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The base and the mask.
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rbx, .r12] (Q := fun t =>
    t.gpr .rbx = B ∧ t.gpr .r12 = mask52 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      unfold area base
      simp only [List.cons_append, List.nil_append]
      xrun [hdi, se_ofNat hT0]
      and_intros
      all_goals first | rfl | (rw [← hB]; rfl)) rfl) fun t₁ ⟨⟨b₁, r12₁, m₁, x₁⟩, k₁⟩ => ?_
  have hdi₁ : t₁.gpr .rdi = H := (k₁.gpr (by decide)).trans hdi
  -- The modulus' limbs.
  rw [WP.block_append_iff]
  refine WP.mono (ldA_ok hl b₁ hdi₁ r12₁ hBd hd hd' (hs.congr k₁.2.2) hsz (.inl rfl) (by omega_arith))
    fun t₂ ⟨v₂, o₂, F₂, k₂, x₂⟩ => ?_
  rw [m₁, hc] at v₂
  rw [m₁] at F₂
  -- `k₀`.
  rw [WP.block_append_iff]
  have hm₂ : word t₂.mem H (8 * sMinv) = word s.mem H (8 * sMinv) :=
    word_tab F₂ (.inl hMv) (by omega_arith)
  have hdi₂ : t₂.gpr .rdi = H := (k₂.gpr (by decide)).trans hdi₁
  have hl₂ : InRegions (t₂.rd ++ t₂.wr) (off H (8 * sMinv)) 8 := by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hs.ld (by omega_arith)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) ∧ t.mem = t₂.mem ∧
      t.mxcsr = t₂.mxcsr) (by
      xrun [State.ea, hdr, hdi₂, VG.Proof.Bignum.X86_64.hdrOff, hl₂, hm₂, (k₂.gpr (by decide)).trans r12₁,
        VG.Proof.Bignum.X86_64.AmmSym.and_mask']
      all_goals rfl) rfl) fun t₃ ⟨⟨a₃, m₃, x₃⟩, k₃⟩ => ?_
  -- `k₀` into its four quadwords.
  rw [WP.block_append_iff]
  have hb₃ : t₃.gpr .rbx = B := by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact b₁
  have hds : (List.range 4).map (fun i => Instr.store (at_ .rbx (l.NB + 8 * i)) .rax) =
      ((List.range 4).map fun i => l.NB + 8 * i).map fun d => .store (at_ .rbx d) .rax := by
    simp only [List.map_map, Function.comp_def]
  rw [hds]
  refine WP.mono (VG.Proof.Bignum.X86_64.Ifma.Pub.stR_ok (b := .rbx) _ t₃ hb₃ a₃ fun d hd => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi
    rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hsB.st (by omega_arith)) fun t₄ h₄ => ?_
  subst h₄
  generalize hM₄ : stMem t₃.mem B (BitVec.ofNat 64 ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52))
    ((List.range 4).map fun i => l.NB + 8 * i) = M₄
  have o₄ : Outside B l.NB 32 t₃.mem M₄ := by
    rw [← hM₄]
    refine stMem_outside _ B _ (by omega_arith) _ fun d hd => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi
    omega_arith
  rw [m₃] at o₄
  have F₄ : Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem M₄ := F₂.trans (fa o₄ (by omega_arith))
  have hN₄ : ∀ q < l.L, word M₄ B (0 + l.off q) = BitVec.ofNat 64 (limbN c q) := fun q hq => by
    have := hF q hq
    rw [← hM₄, word_stMem_other B _ (by omega_arith) _ _ (fun d hd => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd; omega_arith) (fun d hd => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd; rw [List.mem_range] at hi; omega_arith), m₃]
    exact v₂ q hq
  have hk₄ : ∀ i < 4, word M₄ B (l.NB + 8 * i) =
      BitVec.ofNat 64 ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) := fun i hi => by
    rw [← hM₄]
    refine word_stMem B _ _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩) (fun d hd => ?_) (fun d hd => ?_)
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hd
      rw [List.mem_range] at hi'
      by_cases e : i' = i
      · exact .inl (by rw [e])
      · omega_arith
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hd; rw [List.mem_range] at hi'; omega_arith
  have hcW : c < 2 ^ (64 * l.W) := hc ▸ VG.Proof.Bignum.wv_lt _ _ _ _
  have hmod₄ : Mod l M₄ B c ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) :=
    VG.Proof.Bignum.X86_64.Ifma.Pub.mod_of hl hN₄ hcW hk₄ (by
      have := hinv
      rw [← VG.Proof.Bignum.wv_mod64 s.mem H (arr l aN) (n := l.W) (by omega_arith), hc] at this
      exact this)
  have hdi₃ : t₃.gpr .rdi = H := (k₃.gpr (by decide)).trans hdi₂
  have r12₃ : t₃.gpr .r12 = mask52 := by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact r12₁
  have hs₃ : Scr { t₃ with mem := M₄ } H (8 * n) := hs.congr (by
    show t₃.wr = _; rw [k₃.2.2, k₂.2.2, k₁.2.2])
  -- `b R mod c` at `T_1`.
  rw [WP.block_append_iff]
  refine WP.mono (ldA_ok hl (s := { t₃ with mem := M₄ }) hb₃ hdi₃ r12₃ hBd hd hd' hs₃ hsz (.inr (.inl rfl))
    (by omega_arith)) fun t₅ ⟨v₅, o₅, F₅, k₅, x₅⟩ => ?_
  have hdi₅ : t₅.gpr .rdi = H := (k₅.gpr (by decide)).trans hdi₃
  have hb₅ : t₅.gpr .rbx = B := (k₅.gpr (by decide)).trans hb₃
  have r12₅ : t₅.gpr .r12 = mask52 := (k₅.gpr (by decide)).trans r12₃
  -- `R mod c` at `S`.
  rw [WP.block_append_iff]
  refine WP.mono (ldA_ok hl hb₅ hdi₅ r12₅ hBd hd hd' (hs₃.congr k₅.2.2) hsz (.inr (.inr rfl))
    (by omega_arith)) fun t₆ ⟨v₆, o₆, F₆, k₆, x₆⟩ => ?_
  have hdi₆ : t₆.gpr .rdi = H := (k₆.gpr (by decide)).trans hdi₅
  have hb₆ : t₆.gpr .rbx = B := (k₆.gpr (by decide)).trans hb₅
  have r12₆ : t₆.gpr .r12 = mask52 := (k₆.gpr (by decide)).trans r12₅
  -- `R mod c` at `T_0`.
  refine WP.mono (ldA_ok hl hb₆ hdi₆ r12₆ hBd hd hd' ((hs₃.congr k₅.2.2).congr k₆.2.2) hsz (.inr (.inr rfl))
    (by omega_arith)) fun t₇ ⟨v₇, o₇, F₇, k₇, x₇⟩ => ?_
  have hA : arr l aXm + 8 * l.W ≤ arr l 27 ∧ arr l aR1 + 8 * l.W ≤ arr l 27 := by
    simp only [arr, aXm, aR1]; omega
  have hXm : wv M₄ H (arr l aXm) l.W = wv s.mem H (arr l aXm) l.W :=
    wv_tab F₄ (.inl (by simp only [arr, aXm, aT0]; omega)) (by omega_arith)
  have hR₅ : wv t₅.mem H (arr l aR1) l.W = wv s.mem H (arr l aR1) l.W :=
    (wv_tab F₅ (.inr (by simp only [arr, aR1, aT0]; omega)) (by omega_arith)).trans
      (wv_tab F₄ (.inr (by simp only [arr, aR1, aT0]; omega)) (by omega_arith))
  have hR₆ : wv t₆.mem H (arr l aR1) l.W = wv s.mem H (arr l aR1) l.W :=
    (wv_tab F₆ (.inr (by simp only [arr, aR1, aT0]; omega)) (by omega_arith)).trans hR₅
  rw [hXm] at v₅
  rw [hR₅] at v₆
  rw [hR₆] at v₇
  have hN31 : l.NB + 32 < 2 ^ 31 := by omega_arith
  have f₅ := Frm.of_outside o₅ (rs := [(oT l 1, l.NB)]) (List.mem_singleton_self _)
  have f₆ := Frm.of_outside o₆ (rs := [(oS l, l.NB)]) (List.mem_singleton_self _)
  have f₇ := Frm.of_outside o₇ (rs := [(oT l 0, l.NB)]) (List.mem_singleton_self _)
  refine ⟨(k₇.gpr (by decide)).trans hb₆, (k₇.gpr (by decide)).trans r12₆,
    mod_frm hl (mod_frm hl (mod_frm hl hmod₄ f₅ (one_r (p := fun r => l.NB + 32 ≤ r.1) (by omega_arith)) hN31)
      f₆ (one_r (p := fun r => l.NB + 32 ≤ r.1) (by omega_arith)) hN31)
      f₇ (one_r (p := fun r => l.NB + 32 ≤ r.1) (by omega_arith)) hN31,
    num_frm hl f₇ (num_frm hl f₆ (num_of hl v₅ (VG.Proof.Bignum.wv_lt _ _ _ _))
      (one_r (p := fun r => oT l 1 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oT l 1) (.inr (by omega_arith))) (by omega_arith))
      (one_r (p := fun r => oT l 1 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oT l 1) (.inr (by omega_arith))) (by omega_arith),
    num_frm hl f₇ (num_of hl v₆ (VG.Proof.Bignum.wv_lt _ _ _ _))
      (one_r (p := fun r => oS l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oS l) (.inl (by omega_arith))) (by omega_arith),
    num_of hl v₇ (VG.Proof.Bignum.wv_lt _ _ _ _),
    ((F₄.trans F₅).trans F₆).trans F₇, ?_, ?_⟩
  · have k₄ : Keep [] t₃ { t₃ with mem := M₄ } := ⟨fun _ _ => rfl, rfl, rfl⟩
    exact ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).mono (by decide)
  · rw [x₇, x₆, x₅]; show t₃.mxcsr = _; rw [x₃, x₂, x₁]

/-! ## The last block -/

/-- `c − T_0`, `T_0 + c` and `c − T_0 + c` from `T_0 < c`. -/
theorem tail_ok (hl : PubOk l) {s : State} {B : Addr} {c k t0 : Nat} (hB : s.gpr .rbx = B)
    (h12 : s.gpr .r12 = mask52) (hs : Scr s B (size l)) (hm : Mod l s.mem B c k)
    (ht : Canon l s.mem B (oT l 0) ∧ val52 l s.mem B (oT l 0) = t0) (hlt : t0 < c) :
    WP isa (.block (subN l (oM1 l) 0 (oT l 0) ++ addN l (oP1c l) (oT l 0) 0 ++ addN l (oM1c l) (oM1 l) 0)) s
      fun t =>
      (Canon l t.mem B (oM1 l) ∧ val52 l t.mem B (oM1 l) = c - t0) ∧
      (Canon l t.mem B (oP1c l) ∧ val52 l t.mem B (oP1c l) = t0 + c) ∧
      (Canon l t.mem B (oM1c l) ∧ val52 l t.mem B (oM1c l) = c - t0 + c) ∧
      Frm B [(oM1 l, l.NB), (oP1c l, l.NB), (oM1c l, l.NB)] s.mem t.mem ∧
      Keep [.rax, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, -, -, -, o14, -, -, -, -⟩ := PubOk.offs hl
  obtain ⟨-, -, e3⟩ := PubOk.ends hl
  have o6₄ := o6 4
  have hW := VG.Proof.Bignum.X86_64.Ifma.conv_boundsN hl.amm
  have hP : 2 ^ (52 * l.S) ≤ 2 ^ (52 * l.L) :=
    VG.Proof.Bignum.X86_64.AmmSym.pow2_le (Nat.mul_le_mul_left 52 hW.2.2.2.2.2)
  have hP0 := Nat.two_pow_pos (52 * l.L)
  have hbig := hm.big
  have z : Canon l s.mem B 0 ∧ val52 l s.mem B 0 = c := ⟨hm.lt, hm.val⟩
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (subN_ok hl hB h12 hs (o := oM1 l) (a := 0) (b := oT l 0) (by omega_arith) (by omega_arith)
    (by omega_arith) o2 (.inr (by omega_arith)) (.inr (by omega_arith)) z.1 ht.1)
    fun t₁ ⟨M1₁, vM1₁, _, f₁, k₁, x₁⟩ => ?_
  rw [ht.2, z.2] at vM1₁
  simp only [Nat.le_of_lt hlt, ↓reduceIte, Nat.add_zero] at vM1₁
  have F₁ := Frm.of_outside f₁ (rs := [(oM1 l, l.NB)]) (List.mem_singleton_self _)
  have T₁ := num_frm hl F₁ ht (one_r (p := fun r => oT l 0 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oT l 0)
    (.inl (by omega_arith))) (by omega_arith)
  have Z₁ := num_frm hl F₁ z (one_r (p := fun r => 0 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ 0)
    (.inl (by omega_arith))) (by omega_arith)
  refine WP.mono (addN_ok hl ((k₁.gpr (by decide)).trans hB) ((k₁.gpr (by decide)).trans h12) (hs.congr k₁.2.2)
    (o := oP1c l) (a := oT l 0) (b := 0) (by omega_arith) (by omega_arith) (by omega_arith) o2
    (.inr (by omega_arith)) (.inr (by omega_arith)) T₁.1 Z₁.1 (by rw [T₁.2, Z₁.2]; omega_arith))
    fun t₂ ⟨P₂, vP₂, f₂, k₂, x₂⟩ => ?_
  rw [T₁.2, Z₁.2] at vP₂
  have F₂ := Frm.of_outside f₂ (rs := [(oP1c l, l.NB)]) (List.mem_singleton_self _)
  have M₂ := num_frm hl F₂ ⟨M1₁, (by omega_arith : val52 l t₁.mem B (oM1 l) = c - t0)⟩
    (one_r (p := fun r => oM1 l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oM1 l) (.inr (by omega_arith))) (by omega_arith)
  have Z₂ := num_frm hl F₂ Z₁ (one_r (p := fun r => 0 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ 0)
    (.inl (by omega_arith))) (by omega_arith)
  refine WP.mono (addN_ok hl ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hB))
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12)) ((hs.congr k₁.2.2).congr k₂.2.2)
    (o := oM1c l) (a := oM1 l) (b := 0) (by omega_arith) (by omega_arith) (by omega_arith) o2
    (.inr (by omega_arith)) (.inr (by omega_arith)) M₂.1 Z₂.1 (by rw [M₂.2, Z₂.2]; omega_arith))
    fun t₃ ⟨C₃, vC₃, f₃, k₃, x₃⟩ => ?_
  rw [M₂.2, Z₂.2] at vC₃
  have F₃ := Frm.of_outside f₃ (rs := [(oM1c l, l.NB)]) (List.mem_singleton_self _)
  refine ⟨num_frm hl F₃ M₂ (one_r (p := fun r => oM1 l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oM1 l)
      (.inl (by omega_arith))) (by omega_arith),
    num_frm hl F₃ ⟨P₂, vP₂⟩ (one_r (p := fun r => oP1c l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oP1c l)
      (.inl (by omega_arith))) (by omega_arith),
    ⟨C₃, vC₃⟩, ?_, ((k₁.trans k₂).trans k₃).mono (by decide), by rw [x₃, x₂, x₁]⟩
  exact ((F₁.mono (by simp)).trans (F₂.mono (by simp))).trans (F₃.mono (by simp))

/-- `setup`: the area's numbers, from the prepared workspace. -/
theorem setup_ok (hl : PubOk l) {s : State} {H : Addr} {n c bR : Nat}
    (hdi : s.gpr .rdi = H) (hwr : (⟨H, 8 * n⟩ : Region) ∈ s.wr) (hn : H.toNat + 8 * n ≤ 2 ^ 64)
    (hsz : arr l 27 ≤ 8 * n)
    (hc : wv s.mem H (arr l aN) l.W = c) (h3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hinv : ((word s.mem H (arr l aN)).toNat * (word s.mem H (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hr1 : wv s.mem H (arr l aR1) l.W = 2 ^ (64 * l.W) % c)
    (hx : wv s.mem H (arr l aXm) l.W = bR) (hbR : bR < c) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (setup l)) s fun t =>
      t.gpr .rbx = areaBase l H ∧ t.gpr .r12 = mask52 ∧ t.gpr .rdi = H ∧
      Pre l t.mem (areaBase l H) c ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) bR ∧
      Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r11 → r ≠ .r12 → r ≠ .r13 →
        r ≠ .rbp → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  sorry

end VG.Proof.MillerRabin.X86_64.Ifma
