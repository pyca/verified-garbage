module

-- separate module: its proofs (about 2 s, the conversions' stages) are not checked again when `Pass` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Ends
public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# P-256 on x86-64 with AVX512_IFMA: an entry from the words of field elements

`convQ_ok`: the code that makes an entry of the words of a Jacobian point's
`X`, `Y`, `Z`, `Z²` and `Z³` leaves, in `ymm20`–`ymm29`, vectors that stand
for four times `Z²`, `X` and `Y`, eight times `Z` and twice `Z³`, as numbers
(`wv`), and keeps the accumulator. `convG_ok`: the same of an affine point's
`x` and `y`, with a quarter, a half and an eighth for `Z²`, `Z` and `Z³`.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)
open VG.Proof.Bignum.X86_64.Ifma (vi_vreg qv)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg at_)
open VG.Proof.Weierstrass (Unch)

/-- The number whose four words are the lanes of `v`. -/
def wv (E : Env) (v : T) : Int := v.int E 0 + 2 ^ 64 * v.int E 1 + 2 ^ 128 * v.int E 2 + 2 ^ 192 * v.int E 3

/-- The lanes of `v` are words. -/
def Words (E : Env) (v : T) : Prop := ∀ j, j < 4 → 0 ≤ v.int E j ∧ v.int E j < 2 ^ 64

theorem Words.lo {E : Env} {v : T} (h : Words E v) : 0 ≤ wv E v := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [wv]; omega

theorem Words.hi {E : Env} {v : T} (h : Words E v) : wv E v < 2 ^ 256 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [wv]; omega

/-- The limbs of four times a number, from its words in lane `k` of `w0`, …, `w3`. -/
theorem limbs2 {w0 w1 w2 w3 : T} (e0 : ∀ n, shrOf w0 n = .shr w0 n) (e1 : ∀ n, shrOf w1 n = .shr w1 n)
    (e2 : ∀ n, shrOf w2 n = .shr w2 n) (e3 : ∀ n, shrOf w3 n = .shr w3 n) (E : Env) (k : Nat)
    (b0 : 0 ≤ w0.int E k ∧ w0.int E k < 2 ^ 64) (b1 : 0 ≤ w1.int E k ∧ w1.int E k < 2 ^ 64)
    (b2 : 0 ≤ w2.int E k ∧ w2.int E k < 2 ^ 64) (b3 : 0 ≤ w3.int E k ∧ w3.int E k < 2 ^ 64) :
    Carried E k (Id.run (limbs tops w0 w1 w2 w3 2)) ∧ vI E k (Id.run (limbs tops w0 w1 w2 w3 2)) =
      4 * (w0.int E k + 2 ^ 64 * w1.int E k + 2 ^ 128 * w2.int E k + 2 ^ 192 * w3.int E k) := by
  have t : ∀ a n, tops.srl a n = shrOf a n := fun _ _ => rfl
  have u : ∀ a n, tops.sll a n = .shl a n := fun _ _ => rfl
  have v : ∀ a b, tops.add a b = .add a b := fun _ _ => rfl
  simp only [limbs, Id.run, bind, pure, andc_mask, t, u, v, e0, e1, e2, e3, Carried, vI, val5, mask52_int, T.int,
    Nat.reduceSub, Nat.reduceAdd]
  omega

/-- The limbs of twice a number. -/
theorem limbs1 {w0 w1 w2 w3 : T} (e0 : ∀ n, shrOf w0 n = .shr w0 n) (e1 : ∀ n, shrOf w1 n = .shr w1 n)
    (e2 : ∀ n, shrOf w2 n = .shr w2 n) (e3 : ∀ n, shrOf w3 n = .shr w3 n) (E : Env) (k : Nat)
    (b0 : 0 ≤ w0.int E k ∧ w0.int E k < 2 ^ 64) (b1 : 0 ≤ w1.int E k ∧ w1.int E k < 2 ^ 64)
    (b2 : 0 ≤ w2.int E k ∧ w2.int E k < 2 ^ 64) (b3 : 0 ≤ w3.int E k ∧ w3.int E k < 2 ^ 64) :
    Carried E k (Id.run (limbs tops w0 w1 w2 w3 1)) ∧ vI E k (Id.run (limbs tops w0 w1 w2 w3 1)) =
      2 * (w0.int E k + 2 ^ 64 * w1.int E k + 2 ^ 128 * w2.int E k + 2 ^ 192 * w3.int E k) := by
  have t : ∀ a n, tops.srl a n = shrOf a n := fun _ _ => rfl
  have u : ∀ a n, tops.sll a n = .shl a n := fun _ _ => rfl
  have v : ∀ a b, tops.add a b = .add a b := fun _ _ => rfl
  simp only [limbs, Id.run, bind, pure, andc_mask, t, u, v, e0, e1, e2, e3, Carried, vI, val5, mask52_int, T.int,
    Nat.reduceSub, Nat.reduceAdd]
  omega

/-- Word `j` of four numbers, one to a lane, as a term. -/
theorem col_eq (v0 v1 v2 v3 : T) (j : Nat) : Id.run (col tops v0 v1 v2 v3 j) =
    .blend (.blend (.blend (.perm v0 (85 * j)) (.perm v1 (85 * j)) 2) (.perm v2 (85 * j)) 4) (.perm v3 (85 * j)) 8 := by
  have p : ∀ a o, tops.perm a o = .perm a o := fun _ _ => rfl
  simp only [col, Id.run, bind, p, tops_blend _ _ (by decide : 2 < 16), tops_blend _ _ (by decide : 4 < 16),
    tops_blend _ _ (by decide : 8 < 16)]

theorem col_shr (v0 v1 v2 v3 : T) (j n : Nat) :
    shrOf (Id.run (col tops v0 v1 v2 v3 j)) n = .shr (Id.run (col tops v0 v1 v2 v3 j)) n := by
  rw [col_eq]; rfl

/-- Lane `k` of the column of the words `j` is word `j` of the `k`th number. -/
theorem col_int (v0 v1 v2 v3 : T) (E : Env) {j : Nat} (hj : j < 4) :
    (Id.run (col tops v0 v1 v2 v3 j)).int E 0 = v0.int E j ∧ (Id.run (col tops v0 v1 v2 v3 j)).int E 1 = v1.int E j ∧
      (Id.run (col tops v0 v1 v2 v3 j)).int E 2 = v2.int E j ∧ (Id.run (col tops v0 v1 v2 v3 j)).int E 3 = v3.int E j := by
  rw [col_eq]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The vector of `convQ` before its carry, lane by lane: four times `Z²`, `X` and `Y`, eight times `Z`. -/
theorem convQg_val (vx vy vz vzz : T) (E : Env) (hx : Words E vx) (hy : Words E vy) (hz : Words E vz)
    (hzz : Words E vzz) :
    vI E 0 (Id.run (convQg tops vx vy vz vzz)) = 4 * wv E vzz ∧ vI E 1 (Id.run (convQg tops vx vy vz vzz)) = 4 * wv E vx ∧
      vI E 2 (Id.run (convQg tops vx vy vz vzz)) = 8 * wv E vz ∧
      vI E 3 (Id.run (convQg tops vx vy vz vzz)) = 4 * wv E vy := by
  have c0 := col_int vzz vx vz vy E (j := 0) (by decide)
  have c1 := col_int vzz vx vz vy E (j := 1) (by decide)
  have c2 := col_int vzz vx vz vy E (j := 2) (by decide)
  have c3 := col_int vzz vx vz vy E (j := 3) (by decide)
  have L (k : Nat) (b0 : 0 ≤ (Id.run (col tops vzz vx vz vy 0)).int E k ∧ (Id.run (col tops vzz vx vz vy 0)).int E k < 2 ^ 64)
      (b1 : 0 ≤ (Id.run (col tops vzz vx vz vy 1)).int E k ∧ (Id.run (col tops vzz vx vz vy 1)).int E k < 2 ^ 64)
      (b2 : 0 ≤ (Id.run (col tops vzz vx vz vy 2)).int E k ∧ (Id.run (col tops vzz vx vz vy 2)).int E k < 2 ^ 64)
      (b3 : 0 ≤ (Id.run (col tops vzz vx vz vy 3)).int E k ∧ (Id.run (col tops vzz vx vz vy 3)).int E k < 2 ^ 64) :=
    (limbs2 (col_shr vzz vx vz vy 0) (col_shr vzz vx vz vy 1) (col_shr vzz vx vz vy 2) (col_shr vzz vx vz vy 3) E k
      b0 b1 b2 b3).2
  have l0 := L 0 (by rw [c0.1]; exact hzz 0 (by decide)) (by rw [c1.1]; exact hzz 1 (by decide))
    (by rw [c2.1]; exact hzz 2 (by decide)) (by rw [c3.1]; exact hzz 3 (by decide))
  have l1 := L 1 (by rw [c0.2.1]; exact hx 0 (by decide)) (by rw [c1.2.1]; exact hx 1 (by decide))
    (by rw [c2.2.1]; exact hx 2 (by decide)) (by rw [c3.2.1]; exact hx 3 (by decide))
  have l2 := L 2 (by rw [c0.2.2.1]; exact hz 0 (by decide)) (by rw [c1.2.2.1]; exact hz 1 (by decide))
    (by rw [c2.2.2.1]; exact hz 2 (by decide)) (by rw [c3.2.2.1]; exact hz 3 (by decide))
  have l3 := L 3 (by rw [c0.2.2.2]; exact hy 0 (by decide)) (by rw [c1.2.2.2]; exact hy 1 (by decide))
    (by rw [c2.2.2.2]; exact hy 2 (by decide)) (by rw [c3.2.2.2]; exact hy 3 (by decide))
  rw [c0.1, c1.1, c2.1, c3.1] at l0
  rw [c0.2.1, c1.2.1, c2.2.1, c3.2.1] at l1
  rw [c0.2.2.1, c1.2.2.1, c2.2.2.1, c3.2.2.1] at l2
  rw [c0.2.2.2, c1.2.2.2, c2.2.2.2, c3.2.2.2] at l3
  simp only [Id.run] at l0 l1 l2 l3
  refine ⟨?_, ?_, ?_, ?_⟩
  · glue_simp [convQg]
    rw [l0]; simp only [wv]; omega
  · glue_simp [convQg]
    rw [l1]; simp only [wv]; omega
  · glue_simp [convQg]
    rw [l2]; simp only [wv]; omega
  · glue_simp [convQg]
    rw [l3]; simp only [wv]; omega

/-- `convQ`'s second vector: twice `Z³` in its first lane, carried. -/
theorem convQb_val (vzzz : T) (hs : ∀ n, shrOf vzzz n = .shr vzzz n) (E : Env) (h : Words E vzzz) :
    Carried E 0 (Id.run (convQb tops vzzz)) ∧ vI E 0 (Id.run (convQb tops vzzz)) = 2 * wv E vzzz := by
  have p : ∀ a o, tops.perm a o = .perm a o := fun _ _ => rfl
  have := limbs1 (w0 := vzzz) (w1 := .perm vzzz 85) (w2 := .perm vzzz 170) (w3 := .perm vzzz 255) hs (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) E 0 (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))
  simp only [convQb, Id.run, bind, p, wv]
  exact this

/-- What is read through `rcx` and `rdx` is words. -/
theorem words_ld {s₀ : State} {L : List Loc} {bt : BT} (hB : EnvOK s₀ (bndsOf L bt)) (b : Reg) (hb : uBase b = true)
    (d : Nat) : Words (envOf s₀) (.ld b d) := by
  intro j hj
  have := hB.m b d j hj
  simp only [bndsOf, hb, ite_true] at this
  simp only [T.int]
  omega

theorem convQPieces_flat : convQPieces.flatten = convQPieces.getD 0 [] := by decide +kernel

/-- `convQ`'s vector before its carry. -/
abbrev convQG : F5 T := Id.run (convQg tops (.ld .rcx 0) (.ld .rcx 32) (.ld .rcx 64) (.ld .rdx 0))

/-- The entry of the Jacobian point whose words are at `rcx` (`X`, `Y`, `Z`), with those of its `Z²`
and `Z³` at `rdx`: in `ymm20`–`ymm24` four times `Z²`, `X` and `Y` and eight times `Z`, carried, and in
`ymm25`–`ymm29` twice `Z³`; the accumulator is kept. -/
theorem convQ_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) :
    WP isa (.block convQPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs30 (stBT ++ entBT)) ∧
        (∀ xn un z, AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        Car (envOf s) 0 (t5 20) (D (4 * wv (envOf s₀) (.ld .rdx 0))) ∧
        Car (envOf s) 1 (t5 20) (D (4 * wv (envOf s₀) (.ld .rcx 0))) ∧
        Car (envOf s) 2 (t5 20) (D (8 * wv (envOf s₀) (.ld .rcx 64))) ∧
        Car (envOf s) 3 (t5 20) (D (4 * wv (envOf s₀) (.ld .rcx 32))) ∧
        Ent (envOf s) 0 (t5 25) (D (2 * wv (envOf s₀) (.ld .rdx 32))) := by
  have wx := words_ld hB .rcx rfl 0
  have wy := words_ld hB .rcx rfl 32
  have wz := words_ld hB .rcx rfl 64
  have wzz := words_ld hB .rdx rfl 0
  have wzzz := words_ld hB .rdx rfl 32
  obtain ⟨g0, g1, g2, g3⟩ := convQg_val (.ld .rcx 0) (.ld .rcx 32) (.ld .rcx 64) (.ld .rdx 0) (envOf s₀) wx wy wz wzz
  obtain ⟨bc, bv⟩ := convQb_val (.ld .rdx 32) (fun _ => rfl) (envOf s₀) wzzz
  have xl := wx.lo; have xh := wx.hi; have yl := wy.lo; have yh := wy.hi; have zl := wz.lo; have zh := wz.hi
  have zzl := wzz.lo; have zzh := wzz.hi; have zzzl := wzzz.lo; have zzzh := wzzz.hi
  have iv (k : Nat) (hk : k < 4) : ∃ iv, (Id.run (norm tops convQG)).l4.iv stB k = some iv := by
    have hb : ∀ k < 4, (convQIV0.get 4 k).isSome = true := by decide
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hb k hk)
    obtain ⟨iv, e, -⟩ := ivWithin_get convQ_iv0 (n := 24) (t := (Id.run (norm tops convQG)).l4) rfl hk hb
    exact ⟨iv, e⟩
  obtain ⟨i0, hi0⟩ := iv 0 (by decide)
  obtain ⟨i1, hi1⟩ := iv 1 (by decide)
  obtain ⟨i2, hi2⟩ := iv 2 (by decide)
  obtain ⟨i3, hi3⟩ := iv 3 (by decide)
  have c0 : Car (envOf s₀) 0 _ (D (4 * wv (envOf s₀) (.ld .rdx 0))) :=
    Car.norm hB convQG (by decide) hi0 (by rw [g0]; omega) (by rw [g0]; omega) (by rw [g0])
  have c1 : Car (envOf s₀) 1 _ (D (4 * wv (envOf s₀) (.ld .rcx 0))) :=
    Car.norm hB convQG (by decide) hi1 (by rw [g1]; omega) (by rw [g1]; omega) (by rw [g1])
  have c2 : Car (envOf s₀) 2 _ (D (8 * wv (envOf s₀) (.ld .rcx 64))) :=
    Car.norm hB convQG (by decide) hi2 (by rw [g2]; omega) (by rw [g2]; omega) (by rw [g2])
  have c3 : Car (envOf s₀) 3 _ (D (4 * wv (envOf s₀) (.ld .rcx 32))) :=
    Car.norm hB convQG (by decide) hi3 (by rw [g3]; omega) (by rw [g3]; omega) (by rw [g3])
  have cb : Ent (envOf s₀) 0 (Id.run (convQb tops (.ld .rdx 32))) (D (2 * wv (envOf s₀) (.ld .rdx 32))) :=
    ⟨bc, by rw [bv]; omega, by rw [bv]⟩
  rw [convQPieces_flat]
  refine WP.mono (cut_step' convQ_chk0 hc hB convQ_iv0 convQ_ov0
    (rs := [t5 0, t5 5, t5 10, t5 15, Id.run (norm tops convQG), Id.run (convQb tops (.ld .rdx 32))]) rfl rfl
    (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_, ?_⟩
  · intro j k hm
    simp only [convQOv0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · intro xn un z h
    have w : vI (envOf s) 0 (t5 0) = vI (envOf s₀) 0 (t5 0) := hS.val 0 0 (by decide) rfl rfl
    exact ⟨by rw [w]; exact h.ul, by rw [w]; exact h.uh, by rw [w]; exact h.du, hS.car 1 1 (by decide) rfl rfl h.zn,
      hS.car 2 1 (by decide) rfl rfl h.a, hS.car 2 3 (by decide) rfl rfl h.x, hS.raw 3 1 (by decide) rfl rfl h.aa,
      hS.raw 3 3 (by decide) rfl rfl h.xx⟩
  · exact ⟨hS.car 4 0 (by decide) rfl rfl c0, hS.car 4 1 (by decide) rfl rfl c1, hS.car 4 2 (by decide) rfl rfl c2,
      hS.car 4 3 (by decide) rfl rfl c3, hS.car 5 0 (by decide) rfl rfl cb⟩

/-! ### An affine point -/

/-- The vector of `convG` before its constants: four times `x` and `y` in the lanes 1 and 3, carried. -/
theorem convGg_val (vx vy : T) (E : Env) (hx : Words E vx) (hy : Words E vy) :
    (Carried E 1 (Id.run (convGg tops vx vy)) ∧ vI E 1 (Id.run (convGg tops vx vy)) = 4 * wv E vx) ∧
      Carried E 3 (Id.run (convGg tops vx vy)) ∧ vI E 3 (Id.run (convGg tops vx vy)) = 4 * wv E vy := by
  have p : ∀ a o, tops.perm a o = .perm a o := fun _ _ => rfl
  have e : Id.run (convGg tops vx vy) = Id.run (limbs tops (.blend (.perm vx 0) (.perm vy 0) 8)
      (.blend (.perm vx 85) (.perm vy 85) 8) (.blend (.perm vx 170) (.perm vy 170) 8)
      (.blend (.perm vx 255) (.perm vy 255) 8) 2) := by
    simp only [convGg, Id.run, bind, p, tops_blend _ _ (by decide : 8 < 16)]
  rw [e]
  exact ⟨limbs2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) E 1 (hx 0 (by decide)) (hx 1 (by decide))
      (hx 2 (by decide)) (hx 3 (by decide)),
    limbs2 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) E 3 (hy 0 (by decide)) (hy 1 (by decide))
      (hy 2 (by decide)) (hy 3 (by decide))⟩

theorem convGPieces_flat : convGPieces.flatten = convGPieces.getD 0 [] := by decide +kernel

/-- `convG`'s first vector. -/
abbrev convGA : F5 T :=
  Id.run (fblend tops (Id.run (convGg tops (.ld .rdx 0) (.ld .rdx 32))) (Id.run (fconst tops cQuarter 0 cHalf 0)) 5)

/-- The entry of the affine point whose words are at `rdx` (`x`, `y`): in `ymm20`–`ymm24` a quarter,
four times `x`, a half and four times `y`, and in `ymm25`–`ymm29` an eighth; the accumulator is kept. -/
theorem convG_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) :
    WP isa (.block convGPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs30 (stBT ++ entBT)) ∧
        (∀ xn un z, AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        Ent (envOf s) 0 (t5 20) (D (cQuarter : Nat)) ∧
        Ent (envOf s) 1 (t5 20) (D (4 * wv (envOf s₀) (.ld .rdx 0))) ∧
        Ent (envOf s) 2 (t5 20) (D (cHalf : Nat)) ∧
        Ent (envOf s) 3 (t5 20) (D (4 * wv (envOf s₀) (.ld .rdx 32))) ∧
        Ent (envOf s) 0 (t5 25) (D (cEighth : Nat)) := by
  have wx := words_ld hB .rdx rfl 0
  have wy := words_ld hB .rdx rfl 32
  obtain ⟨⟨xc, xv⟩, yc, yv⟩ := convGg_val (.ld .rdx 0) (.ld .rdx 32) (envOf s₀) wx wy
  have xl := wx.lo; have xh := wx.hi; have yl := wy.lo; have yh := wy.hi
  have p0 (a b c d : Nat) : pick4 a b c d 0 = a := rfl
  have p2 (a b c d : Nat) : pick4 a b c d 2 = c := rfl
  have k0 := fconst_car cQuarter 0 cHalf 0 (envOf s₀) (k := 0) (by decide) (by rw [p0]; decide +kernel)
  have k2 := fconst_car cQuarter 0 cHalf 0 (envOf s₀) (k := 2) (by decide) (by rw [p2]; decide +kernel)
  have k8 := fconst_car cEighth 0 0 0 (envOf s₀) (k := 0) (by decide) (by rw [p0]; decide +kernel)
  rw [p0] at k0 k8
  rw [p2] at k2
  have nb : Nb ≤ 2 ^ 259 := by simp only [Nb]; omega
  have a0 : Ent (envOf s₀) 0 convGA (D (cQuarter : Nat)) := Lim.blendR (by decide) (by decide) (k0.mono nb)
  have a1 : Ent (envOf s₀) 1 convGA (D (4 * wv (envOf s₀) (.ld .rdx 0))) :=
    Lim.blendL (by decide) (by decide) ⟨xc, by rw [xv]; omega, by rw [xv]⟩
  have a2 : Ent (envOf s₀) 2 convGA (D (cHalf : Nat)) := Lim.blendR (by decide) (by decide) (k2.mono nb)
  have a3 : Ent (envOf s₀) 3 convGA (D (4 * wv (envOf s₀) (.ld .rdx 32))) :=
    Lim.blendL (by decide) (by decide) ⟨yc, by rw [yv]; omega, by rw [yv]⟩
  have b0 : Ent (envOf s₀) 0 (Id.run (fconst tops cEighth 0 0 0)) (D (cEighth : Nat)) := k8.mono nb
  rw [convGPieces_flat]
  refine WP.mono (cut_step' convG_chk0 hc hB convG_iv0 convG_ov0
    (rs := [t5 0, t5 5, t5 10, t5 15, convGA, Id.run (fconst tops cEighth 0 0 0)]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_, ?_⟩
  · intro xn un z h
    have w : vI (envOf s) 0 (t5 0) = vI (envOf s₀) 0 (t5 0) := hS.val 0 0 (by decide) rfl rfl
    exact ⟨by rw [w]; exact h.ul, by rw [w]; exact h.uh, by rw [w]; exact h.du, hS.car 1 1 (by decide) rfl rfl h.zn,
      hS.car 2 1 (by decide) rfl rfl h.a, hS.car 2 3 (by decide) rfl rfl h.x, hS.raw 3 1 (by decide) rfl rfl h.aa,
      hS.raw 3 3 (by decide) rfl rfl h.xx⟩
  · exact ⟨hS.car 4 0 (by decide) rfl rfl a0, hS.car 4 1 (by decide) rfl rfl a1, hS.car 4 2 (by decide) rfl rfl a2,
      hS.car 4 3 (by decide) rfl rfl a3, hS.car 5 0 (by decide) rfl rfl b0⟩

/-! ### An entry kept as limbs

The entries of `Q`'s table but the first are kept as `convQ` leaves them, in seven vectors of the
working space (`storeEnt`): the five of `ta`, the first four limbs of `tb`'s first lane, and its fifth.
`LEnt` says what the 25 quadwords of an entry at `p` stand for, as `EntOk` does of the registers.
-/

/-- The quadwords at `p`, as what a block reads through a register there. -/
def memEnv (m : Mem) (p : Addr) : Env :=
  ⟨fun _ _ => 0, fun _ d k => ((m.readW (p + BitVec.ofNat 64 (d + 8 * k)) 64).toNat : Int)⟩

/-- The first vector of an entry kept as limbs. -/
def taL : F5 T := ⟨.ld .rcx 0, .ld .rcx 32, .ld .rcx 64, .ld .rcx 96, .ld .rcx 128⟩

/-- The second: its first lane is the four quadwords at 160 and the one at 192. -/
def tbL : F5 T := ⟨.ld .rcx 160, .perm (.ld .rcx 160) 85, .perm (.ld .rcx 160) 170, .perm (.ld .rcx 160) 255, .ld .rcx 192⟩

/-- The entry kept as limbs at `p` stands for `P`'s. -/
def LEnt (m : Mem) (p : Addr) (P : AP (Fin pN)) : Prop := EntOk (memEnv m p) taL tbL P

/-- What a lane stands for goes with its limbs. -/
theorem Lim.limbs {bd : Int} {E E' : Env} {k k' : Nat} {v v' : F5 T} {x : Fin pN} (h : Lim bd E k v x)
    (e : ∀ i, i < 5 → (v'.get i).int E' k' = (v.get i).int E k) : Lim bd E' k' v' x := by
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide)
  simp only [F5.get] at e0 e1 e2 e3 e4
  have ev : vI E' k' v' = vI E k v := by simp only [vI, e0, e1, e2, e3, e4]
  refine ⟨?_, by rw [ev]; exact h.hi, by rw [ev]; exact h.d⟩
  have hc := h.c
  unfold Carried at hc ⊢
  rw [e0, e1, e2, e3, e4]
  exact hc

/-- An entry depends on its 200 bytes only. -/
theorem LEnt.congr {m m' : Mem} {p : Addr} {P : AP (Fin pN)} (h : LEnt m p P)
    (e : ∀ d k, d + 8 * k + 8 ≤ 200 → m'.readW (p + BitVec.ofNat 64 (d + 8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (d + 8 * k)) 64) :
    LEnt m' p P := by
  have q (d k : Nat) (hd : d + 8 * k + 8 ≤ 200) : (T.ld .rcx d).int (memEnv m' p) k = (T.ld .rcx d).int (memEnv m p) k := by
    simp only [T.int, memEnv, e d k hd]
  have ta (k : Nat) (hk : k < 4) (i : Nat) (hi : i < 5) : (taL.get i).int (memEnv m' p) k = (taL.get i).int (memEnv m p) k := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      exact q _ k (by omega)
  have tb (i : Nat) (hi : i < 5) : (tbL.get i).int (memEnv m' p) 0 = (tbL.get i).int (memEnv m p) 0 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact q 160 0 (by decide)
    · exact q 160 1 (by decide)
    · exact q 160 2 (by decide)
    · exact q 160 3 (by decide)
    · exact q 192 0 (by decide)
  exact ⟨h.zz.limbs (ta 0 (by decide)), h.x.limbs (ta 1 (by decide)), h.z.limbs (ta 2 (by decide)),
    h.y.limbs (ta 3 (by decide)), h.zzz.limbs tb⟩

/-- `B`, with the quadwords read through `rcx` and `rdx` that `f` says are limbs. -/
def limB (B : Bnds) (f : Reg → Nat → Nat → Bool) : Bnds where
  vl := B.vl
  vh := B.vh
  ml b d k := if f b d k then 0 else B.ml b d k
  mh b d k := if f b d k then 2 ^ 52 - 1 else B.mh b d k

theorem EnvOK.lim {s : State} {B : Bnds} (h : EnvOK s B) {f : Reg → Nat → Nat → Bool}
    (hf : ∀ b d k, k < 4 → f b d k = true → 0 ≤ (envOf s).m b d k ∧ (envOf s).m b d k < 2 ^ 52) :
    EnvOK s (limB B f) := by
  refine ⟨h.v, fun b d k hk => ?_⟩
  simp only [limB]
  split
  · rename_i hfb
    have := hf b d k hk hfb
    omega
  · exact h.m b d k hk

/-- The accumulator's registers and the entry's first five. -/
def regs25 : List Loc := (List.range 25).map .reg

/-- The bounds of an entry's first vector. -/
def entA : BT := [[carriedB, carriedB, carriedB, carriedB]]

/-- The quadwords of an entry's first five vectors, through `rcx` and `rdx`. -/
def limA (b : Reg) (d _k : Nat) : Bool := (b == .rcx && (d == 0 || d == 32 || d == 64)) || (b == .rdx && (d == 0 || d == 32))

/-- Those of the first lane of its second, through `rdx`. -/
def limT (b : Reg) (d k : Nat) : Bool := b == .rdx && (d == 0 || (d == 32 && k == 0))

/-- What `loadB` starts from: the accumulator, the entry's first vector and the quadwords of its second. -/
def loadBT : List (F5 T) := stT ++ [t5 20, rawGT]

theorem loadA_chk : chkSeg (loadAPieces.getD 0 []) convQT (fun xs => pure xs) regs25 = true := by decide +kernel

theorem loadA_iv : ivWithin (limB stB limA) (segT (fun xs => pure xs) convQT) (stBT ++ entA) = true := by
  decide +kernel

theorem loadA_ov : ovOk (stBT ++ entA) (stBT ++ entA) [] = true := by decide +kernel

theorem loadB_chk : chkSeg (loadBPieces.getD 0 []) loadBT (unpackT tops) regs30 = true := by decide +kernel

theorem loadB_iv :
    ivWithin (limB (bndsOf regs25 (stBT ++ entA)) limT) (segT (unpackT tops) loadBT) (stBT ++ entBT) = true := by
  decide +kernel

theorem loadB_ov : ovOk (stBT ++ entBT) (stBT ++ entBT) [] = true := by decide +kernel

theorem loadAPieces_flat : loadAPieces.flatten = loadAPieces.getD 0 [] := by decide +kernel

theorem loadBPieces_flat : loadBPieces.flatten = loadBPieces.getD 0 [] := by decide +kernel

theorem stBT_app (X : BT) {j k : Nat} {b : Int × Int} (h : stBT.get j k = some b) : (stBT ++ X).get j k = some b := by
  have hj : j < stBT.length := BT.get_lt h
  have e : (stBT ++ X).getD j [] = stBT.getD j [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]
  unfold BT.get at h ⊢
  rw [e]
  exact h

/-- What is known of the accumulator goes with its limbs. -/
theorem AccOk.of_same {iv : BT} {E E' : Env} {xs ys : List (F5 T)} (h : Same iv E' ys E xs)
    (hiv : ∀ {j k b}, stBT.get j k = some b → iv.get j k = some b) {xn un z : Fin pN}
    (ha : AccOk E (xs.getD 0 zero5) (xs.getD 1 zero5) (xs.getD 2 zero5) (xs.getD 3 zero5) xn un z) :
    AccOk E' (ys.getD 0 zero5) (ys.getD 1 zero5) (ys.getD 2 zero5) (ys.getD 3 zero5) xn un z := by
  have e := h.vI (j := 0) (k := 0) (by decide) (hiv (j := 0) (k := 0) rfl)
  exact ⟨by rw [e]; exact ha.ul, by rw [e]; exact ha.uh, by rw [e]; exact ha.du,
    h.car 1 1 (by decide) (hiv (j := 1) (k := 1) rfl) rfl ha.zn, h.car 2 1 (by decide) (hiv (j := 2) (k := 1) rfl) rfl ha.a,
    h.car 2 3 (by decide) (hiv (j := 2) (k := 3) rfl) rfl ha.x, h.raw 3 1 (by decide) (hiv (j := 3) (k := 1) rfl) rfl ha.aa,
    h.raw 3 3 (by decide) (hiv (j := 3) (k := 3) rfl) rfl ha.xx⟩

/-- A quadword read through a register at `x` from `p` is the one at `x + d`. -/
theorem ld_mem (s : State) {b : Reg} (hb : uBase b = true) {p : Addr} {x : Nat}
    (h : s.gpr b = p + BitVec.ofNat 64 x) (d k : Nat) :
    (T.ld b d).int (envOf s) k = (T.ld .rcx (x + d)).int (memEnv s.mem p) k := by
  simp only [T.int, envOf, hb, ite_true, memEnv, h, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]

/-- The entry's first five vectors from its limbs at `rcx`, with `rdx` 96 bytes on: `ymm20`–`ymm24`. -/
theorem loadA_ok {e : State} (hc : Ctx par e) (hB : EnvOK e stB) {p : Addr} {P : AP (Fin pN)}
    (hcx : e.gpr .rcx = p + BitVec.ofNat 64 0) (hdx : e.gpr .rdx = p + BitVec.ofNat 64 96) (hE : LEnt e.mem p P) :
    WP isa (.block loadAPieces.flatten) e fun u =>
      Ctx par u ∧ Kept e u ∧ EnvOK u (bndsOf regs25 (stBT ++ entA)) ∧
        (∀ xn un z, AccOk (envOf e) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf u) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        Ent (envOf u) 0 (t5 20) P.ezz ∧ Ent (envOf u) 1 (t5 20) P.ex ∧ Ent (envOf u) 2 (t5 20) P.ez ∧
        Ent (envOf u) 3 (t5 20) P.ey := by
  have lm (i : Nat) (hi : i < 5) (k : Nat) : (rawQT.get i).int (envOf e) k = (taL.get i).int (memEnv e.mem p) k := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact ld_mem e rfl hcx 0 k
    · exact ld_mem e rfl hcx 32 k
    · exact ld_mem e rfl hcx 64 k
    · exact ld_mem e rfl hdx 0 k
    · exact ld_mem e rfl hdx 32 k
  have car (k : Nat) (hk : k < 4) : Carried (memEnv e.mem p) k taL := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    exacts [hE.zz.c, hE.x.c, hE.z.c, hE.y.c]
  have hB' : EnvOK e (limB stB limA) := by
    refine hB.lim fun b d k hk hf => ?_
    simp only [limA, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
    have g (i : Nat) (hi : i < 5) : 0 ≤ (rawQT.get i).int (envOf e) k ∧ (rawQT.get i).int (envOf e) k < 2 ^ 52 := by
      rw [lm i hi k]; exact (car k hk).get hi
    rcases hf with ⟨rfl, (rfl | rfl) | rfl⟩ | ⟨rfl, rfl | rfl⟩
    exacts [g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide), g 4 (by decide)]
  rw [loadAPieces_flat]
  refine WP.mono (cut_step' loadA_chk hc hB' loadA_iv loadA_ov (rs := stT ++ [rawQT]) rfl rfl (Nat.le_of_eq rfl)
    (fun _ _ hm => nomatch hm)) fun u ⟨hc', hk, hE', hS⟩ => ⟨hc', hk, hE', fun xn un z h => ?_, ?_⟩
  · exact AccOk.of_same hS (stBT_app _) h
  · exact ⟨hS.car 4 0 (by decide) rfl rfl (hE.zz.limbs fun i hi => lm i hi 0),
      hS.car 4 1 (by decide) rfl rfl (hE.x.limbs fun i hi => lm i hi 1),
      hS.car 4 2 (by decide) rfl rfl (hE.z.limbs fun i hi => lm i hi 2),
      hS.car 4 3 (by decide) rfl rfl (hE.y.limbs fun i hi => lm i hi 3)⟩

/-- `loadB`'s second vector, as read. -/
abbrev tbR : F5 T := ⟨.ld .rdx 0, .perm (.ld .rdx 0) 85, .perm (.ld .rdx 0) 170, .perm (.ld .rdx 0) 255, .ld .rdx 32⟩

/-- The entry's second vector from its limbs, with `rdx` at the entry's 160: `ymm25`–`ymm29`. -/
theorem loadB_ok {w : State} (hc : Ctx par w) (hB : EnvOK w (bndsOf regs25 (stBT ++ entA))) {p : Addr}
    {P : AP (Fin pN)} (hdx : w.gpr .rdx = p + BitVec.ofNat 64 160) (hE : LEnt w.mem p P) :
    WP isa (.block loadBPieces.flatten) w fun t =>
      Ctx par t ∧ Kept w t ∧ EnvOK t (bndsOf regs30 (stBT ++ entBT)) ∧
        (∀ xn un z, AccOk (envOf w) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        (∀ k, k < 4 → ∀ x, Ent (envOf w) k (t5 20) x → Ent (envOf t) k (t5 20) x) ∧ Ent (envOf t) 0 (t5 25) P.ezzz := by
  have lm (i : Nat) (hi : i < 5) : (tbR.get i).int (envOf w) 0 = (tbL.get i).int (memEnv w.mem p) 0 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact ld_mem w rfl hdx 0 0
    · exact ld_mem w rfl hdx 0 1
    · exact ld_mem w rfl hdx 0 2
    · exact ld_mem w rfl hdx 0 3
    · exact ld_mem w rfl hdx 32 0
  have hB' : EnvOK w (limB (bndsOf regs25 (stBT ++ entA)) limT) := by
    refine hB.lim fun b d k hk hf => ?_
    simp only [limT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
    have g (i : Nat) (hi : i < 5) : 0 ≤ (tbR.get i).int (envOf w) 0 ∧ (tbR.get i).int (envOf w) 0 < 2 ^ 52 := by
      rw [lm i hi]; exact hE.zzz.c.get hi
    rcases hf with ⟨rfl, rfl | ⟨rfl, rfl⟩⟩
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      exacts [g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide)]
    · exact g 4 (by decide)
  rw [loadBPieces_flat]
  refine WP.mono (cut_step' loadB_chk hc hB' loadB_iv loadB_ov (rs := stT ++ [t5 20, tbR]) rfl rfl (Nat.le_of_eq rfl)
    (fun _ _ hm => nomatch hm)) fun t ⟨hc', hk, hE', hS⟩ => ⟨hc', hk, hE', fun xn un z h => ?_, ?_, ?_⟩
  · exact AccOk.of_same hS (stBT_app _) h
  · intro k hk x hx
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact hS.car 4 0 (by decide) rfl rfl hx
    · exact hS.car 4 1 (by decide) rfl rfl hx
    · exact hS.car 4 2 (by decide) rfl rfl hx
    · exact hS.car 4 3 (by decide) rfl rfl hx
  · exact hS.car 5 0 (by decide) rfl rfl (hE.zzz.limbs lm)

/-- The accumulator's registers zero are within the bounds a block starts from. -/
theorem envOK_zero {t : State} (hz : ∀ r, r < 20 → ∀ k, k < 4 → qv t (vreg r) k = 0) : EnvOK t stB := by
  refine envOK_of fun n l hl k hk b hb => ?_
  have hn : n < 20 ∧ l = .reg n := by
    simp only [regs20, List.getElem?_map, Option.map_eq_some_iff] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hm
    rw [List.length_range] at hlt
    rw [List.getElem_range] at e
    exact ⟨hlt, by rw [e]⟩
  obtain ⟨hn, rfl⟩ := hn
  have e : ints t (.reg n) k = 0 := by
    show (qv t (vreg n) k).toInt = 0
    rw [hz n hn k hk]; rfl
  rw [e]
  have key : ∀ j, j < 4 → ∀ k, k < 4 →
      (match stBT.get j k with | some b => decide (b.1 ≤ 0 ∧ 0 ≤ b.2) | none => true) = true := by decide +kernel
  have := key (n / 5) (by omega) k hk
  rw [hb] at this
  exact of_decide_eq_true this


/-! ### An entry stored -/

/-- The first four limbs of the first lane of `ymm5`–`ymm9`. -/
abbrev packV : T := Id.run (col tops (.reg 5) (.reg 6) (.reg 7) (.reg 8) 0)

/-- `packT0` leaves `packV` in `ymm5`, keeps the other registers and stores nothing. -/
def chkPack : Bool :=
  match VSym.init.run par packT0Pieces.flatten with
  | some σ => σ.st.isEmpty && decide (σ.reg 5 = packV) &&
      (List.range 20).all fun r => r == 5 || decide (σ.reg r = .reg r)
  | none => false

theorem pack_chk : chkPack = true := by decide +kernel

theorem packV_eval (s : State) {k : Nat} (hk : k < 4) : packV.eval s k = qv s (vreg (5 + k)) 0 := by
  rw [packV, col_eq]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The first four limbs of `tb`'s first lane into the lanes of `ymm5`. -/
theorem pack_ok {s : State} (hc : Ctx par s) :
    WP isa (.block packT0Pieces.flatten) s fun t =>
      vm s t = t ∧ t.mem = s.mem ∧ (∀ r, r < 20 → r ≠ 5 → ∀ k, k < 4 → qv t (vreg r) k = qv s (vreg r) k) ∧
        ∀ k, k < 4 → qv t (vreg 5) k = qv s (vreg (5 + k)) 0 := by
  have hchk := pack_chk
  unfold chkPack at hchk
  split at hchk
  case h_2 => cases hchk
  rename_i σ hσ
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.isEmpty_iff] at hchk
  obtain ⟨⟨c0, c5⟩, c4⟩ := hchk
  refine WP.mono (srun_ok hc _ (SRel.init _ s) hσ) fun t h => ⟨h.eq, ?_, fun r hr hn k hk => ?_, fun k hk => ?_⟩
  · rw [h.mem, c0]; rfl
  · have := h.reg (vreg r) k hk
    rw [vi_vreg r (by omega), (c4 r hr).resolve_left hn] at this
    exact this
  · have := h.reg (vreg 5) k hk
    rw [vi_vreg 5 (by decide), c5] at this
    exact this.trans (packV_eval s hk)

/-- Memory after 32-byte stores at offsets of `p`, the first first. -/
def wr32 (m : Mem) (p : Addr) : List (Nat × BitVec 256) → Mem
  | [] => m
  | (e, v) :: l => wr32 (m.writeW (p + BitVec.ofNat 64 e) v) p l

/-- A quadword that the stores are apart from. -/
theorem wr32_off (p : Addr) {o k al : Nat} (hk : k < 4) (ho : o % 32 = al) (ho' : o < 2 ^ 62) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ e ∈ l, e.1 % 32 = al ∧ e.1 < 2 ^ 62 ∧ e.1 ≠ o) →
      (wr32 m p l).readW (p + BitVec.ofNat 64 (o + 8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (o + 8 * k)) 64
  | [], _, _ => rfl
  | (e, v) :: l, m, he => by
    have he0 := he (e, v) List.mem_cons_self
    simp only [wr32]
    rw [wr32_off p hk ho ho' l _ (fun x hx => he x (List.mem_cons_of_mem _ hx))]
    exact readW_writeW_off m p v (d := o + 8 * k) (e := e) (n := 8) (by omega) (by simp only [Nat.reduceDiv]; omega)
      (by simp only [Nat.reduceDiv]; omega)

/-- A quadword of one of the stores, which are at different offsets. -/
theorem wr32_read (p : Addr) {k al : Nat} (hk : k < 4) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ e ∈ l, e.1 % 32 = al ∧ e.1 < 2 ^ 62) →
      l.Pairwise (fun a b => a.1 ≠ b.1) → ∀ o v, (o, v) ∈ l →
      (wr32 m p l).readW (p + BitVec.ofNat 64 (o + 8 * k)) 64 = qword256 v k
  | [], _, _, _, _, _, h => nomatch h
  | (e, t) :: l, m, he, hp, o, v, h => by
    have he0 := he (e, t) List.mem_cons_self
    obtain ⟨hne, hp'⟩ := List.pairwise_cons.mp hp
    simp only [wr32]
    rcases List.mem_cons.mp h with heq | hin
    · cases heq
      rw [wr32_off p hk he0.1 he0.2 l _ (fun x hx => ⟨(he x (List.mem_cons_of_mem _ hx)).1,
        (he x (List.mem_cons_of_mem _ hx)).2, fun h' => hne x hx h'.symm⟩)]
      have r1 := readW_writeW_inside m (p + BitVec.ofNat 64 e) t (k := 8 * k) (n := 8) (by omega) (by decide)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at r1
      rw [r1, qword256, show 64 * k = 8 * (8 * k) by omega]
    · exact wr32_read p hk l _ (fun x hx => he x (List.mem_cons_of_mem _ hx)) hp' o v hin

/-- The stores change nothing outside the bytes they are to. -/
theorem wr32_unch (p : Addr) {lo n : Nat} (hn : lo + n < 2 ^ 62) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ e ∈ l, lo ≤ e.1 ∧ e.1 + 32 ≤ lo + n) →
      Unch p [(lo, n)] m (wr32 m p l)
  | [], _, _ => Unch.refl _ _ _
  | (e, v) :: l, m, he => by
    have he0 := he (e, v) List.mem_cons_self
    intro x hx
    have h1 := hx (lo, n) (List.mem_singleton.2 rfl)
    simp only [wr32]
    rw [wr32_unch p hn l _ (fun y hy => he y (List.mem_cons_of_mem _ hy)) x hx, writeW_byte_off _ _ _ _ ?_]
    simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.reduceDiv]
    have := (x - p).isLt
    simp only [VG.Proof.Mont.ofs] at h1
    omega

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d :=
  VG.Proof.Bignum.X86_64.AmmSym.baseOff_ok (m := at_ b d) rfl s

/-- Vector registers stored through `b`, which is at `o` from `p`. -/
theorem evStores_ok (b : Reg) (p : Addr) (o : Nat) :
    ∀ (l : List (Nat × VReg)) (s : State), s.gpr b = p + BitVec.ofNat 64 o →
      (∀ e ∈ l, InRegions s.wr (p + BitVec.ofNat 64 (o + e.1)) 32) →
      WP isa (.block (l.map fun e => Instr.evStore (at_ b e.1) e.2)) s fun t =>
        t = { s with mem := wr32 s.mem p (l.map fun e => (o + e.1, s.vy e.2)) }
  | [], _, _, _ => WP.block_nil rfl
  | (d, r) :: l, s, hb, hin => by
    have h0 := hin (d, r) List.mem_cons_self
    refine WP.block_cons_iff.2 ⟨{ s with mem := s.mem.writeW (p + BitVec.ofNat 64 (o + d)) (s.vy r) }, ?_, ?_⟩
    · simp only [exec, ea_at, hb, VG.Offset.add_add, State.store256, h0, ite_true]
    · exact evStores_ok b p o l _ hb (fun e he => hin e (List.mem_cons_of_mem _ he))

/-- The entry stored stands for what the registers did. -/
theorem lent_of {s : State} {m : Mem} {p : Addr} {P : AP (Fin pN)} (hE : EntOk (envOf s) (t5 0) (t5 5) P)
    (ha : ∀ i, i < 5 → ∀ k, k < 4 → m.readW (p + BitVec.ofNat 64 (32 * i + 8 * k)) 64 = qv s (vreg i) k)
    (hb : ∀ k, k < 4 → m.readW (p + BitVec.ofNat 64 (160 + 8 * k)) 64 = qv s (vreg (5 + k)) 0)
    (hl : m.readW (p + BitVec.ofNat 64 (192 + 8 * 0)) 64 = qv s (vreg 9) 0) : LEnt m p P := by
  -- a quadword that is a limb is its number
  have nat (x : BitVec 64) (h : 0 ≤ x.toInt) : (x.toNat : Int) = x.toInt := by
    have := x.isLt
    rw [BitVec.toInt_eq_toNat_cond] at h ⊢
    split at h <;> rename_i hx
    · simp only [hx, ite_true]
    · omega
  have ta (k : Nat) (hk : k < 4) (hc : Carried (envOf s) k (t5 0)) (i : Nat) (hi : i < 5) :
      (taL.get i).int (memEnv m p) k = ((t5 0).get i).int (envOf s) k := by
    have e : (taL.get i).int (memEnv m p) k = ((qv s (vreg i) k).toNat : Int) := by
      rw [← ha i hi k hk]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e' : ((t5 0).get i).int (envOf s) k = (qv s (vreg i) k).toInt := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e, e']
    exact nat _ (e' ▸ (hc.get hi).1)
  have tb (i : Nat) (hi : i < 5) : (tbL.get i).int (memEnv m p) 0 = ((t5 5).get i).int (envOf s) 0 := by
    have e' : ((t5 5).get i).int (envOf s) 0 = (qv s (vreg (5 + i)) 0).toInt := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e : (tbL.get i).int (memEnv m p) 0 = ((qv s (vreg (5 + i)) 0).toNat : Int) := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [← hb 0 (by decide)]; rfl
      · rw [← hb 1 (by decide)]; rfl
      · rw [← hb 2 (by decide)]; rfl
      · rw [← hb 3 (by decide)]; rfl
      · rw [← hl]; rfl
    rw [e, e']
    exact nat _ (e' ▸ (hE.zzz.c.get hi).1)
  exact ⟨hE.zz.limbs (ta 0 (by decide) hE.zz.c), hE.x.limbs (ta 1 (by decide) hE.x.c),
    hE.z.limbs (ta 2 (by decide) hE.z.c), hE.y.limbs (ta 3 (by decide) hE.y.c), hE.zzz.limbs tb⟩

end VG.Proof.P256.X86_64.Ifma
