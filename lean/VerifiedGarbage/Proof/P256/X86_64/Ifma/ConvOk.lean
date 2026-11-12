module

-- separate module: its proofs (about 2 s, the conversions' stages) are not checked again when `Pass` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Ends

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

end VG.Proof.P256.X86_64.Ifma
