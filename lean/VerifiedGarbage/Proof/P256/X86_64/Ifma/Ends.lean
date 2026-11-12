module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.AddOk

/-!
# P-256 on x86-64 with AVX512_IFMA: the first point, and out of the vectors

`set_ok`: the code of the first point makes of an entry the accumulator
that stands for `(4 ex, ±4 ey, 2 ez)`. `out_ok`: the code out of the vectors
leaves `[Y, Z, _, X]` of the accumulator's triple `(4 xn, 4 un, 2 z)` in
`ymm0`–`ymm4`, carried, as multiples of `2²⁵⁶` modulo `p` (`out_mont`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

/-! ### The first point -/

/-- The entry's vector, carried. -/
abbrev setN : F5 T := Id.run (norm tops (t5 20))

/-- `±Y'` of the entry. -/
abbrev setU : F5 T :=
  Id.run (fsel tops sgnT.l0 (Id.run (fperm tops setN 3 3 3 3)) (Id.run (fneg tops (Id.run (fperm tops setN 3 3 3 3)))))

theorem setU_v0 (E : Env) {neg : Bool} (hs : SgnOk E sgnT.l0 neg) :
    vI E 0 setU = if neg then 0 - vI E 3 setN else vI E 3 setN := by
  glue_simp [setU, vI_fsel _ hs.b, vI_fneg, hs.s0]
  cases neg <;> simp

/-- After the first stage of the first point: the accumulator but for its squares. -/
structure SetCut (E : Env) (u zn n3 : F5 T) (xn un z : Fin pN) : Prop where
  ul : -20 * pI ≤ vI E 0 u
  uh : vI E 0 u ≤ 3 * pI
  du : D (vI E 0 u) = un
  zn : Car E 1 zn z
  a : Car E 1 n3 (z * z)
  x : Car E 3 n3 xn

/-- The places of the first stage's results, as terms. -/
abbrev sL : List (F5 T) := leaves (setLocs.getD 0 [])

theorem set_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ setB) {p : AP (Fin pN)}
    (hzz : Ent (envOf s₀) 0 (t5 20) (p.ez * p.ez)) (hx : Ent (envOf s₀) 1 (t5 20) p.ex)
    (hz : Ent (envOf s₀) 2 (t5 20) p.ez) (hy : Ent (envOf s₀) 3 (t5 20) p.ey)
    (hs : SgnOk (envOf s₀) sgnT.l0 p.neg) :
    WP isa (.block (setPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (setLocs.getD 0 []) setBT0) ∧
        SetCut (envOf s) (sL.getD 0 zero5) (sL.getD 1 zero5) (sL.getD 2 zero5) p.ex
          (if p.neg then 0 - p.ey else p.ey) p.ez := by
  have iv (k : Nat) (hk : k < 4) : ∃ iv, setN.l4.iv setB k = some iv := by
    have : ∀ k < 4, (setN.l4.iv setB k).isSome = true := by decide +kernel
    exact Option.isSome_iff_exists.1 (this k hk)
  obtain ⟨i0, hi0⟩ := iv 0 (by decide)
  obtain ⟨i1, hi1⟩ := iv 1 (by decide)
  obtain ⟨i2, hi2⟩ := iv 2 (by decide)
  obtain ⟨i3, hi3⟩ := iv 3 (by decide)
  have zzl := hzz.lo; have zzh := hzz.hi; have xl := hx.lo; have xh := hx.hi
  have zl := hz.lo; have zh := hz.hi; have yl := hy.lo; have yh := hy.hi
  have c0 : Car (envOf s₀) 0 setN (p.ez * p.ez) := Car.norm hB _ (by decide) hi0 zzl (by omega) hzz.d
  have c1 : Car (envOf s₀) 1 setN p.ex := Car.norm hB _ (by decide) hi1 xl (by omega) hx.d
  have c2 : Car (envOf s₀) 2 setN p.ez := Car.norm hB _ (by decide) hi2 zl (by omega) hz.d
  have c3 : Car (envOf s₀) 3 setN p.ey := Car.norm hB _ (by decide) hi3 yl (by omega) hy.d
  have vu := setU_v0 (envOf s₀) hs
  have c3l := c3.lo; have c3h := c3.hi
  refine WP.mono (cut_step' set_chk0 hc hB set_iv0 set_ov0
    (rs := [setU, Id.run (fperm tops setN 2 2 2 2), Id.run (fperm tops setN 0 0 1 1)]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [setOv0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Carried.perm 2 2 2 2 c2.c
    · exact Carried.perm 2 2 2 2 c2.c
    · exact Carried.perm 2 2 2 2 c2.c
    · exact Carried.perm 2 2 2 2 c2.c
    · exact Carried.perm 0 0 1 1 c0.c
    · exact Carried.perm 0 0 1 1 c0.c
    · exact Carried.perm 0 0 1 1 c1.c
    · exact Carried.perm 0 0 1 1 c1.c
  · have w : vI (envOf s) 0 (sL.getD 0 zero5) = vI (envOf s₀) 0 setU := hS.val 0 0 (by decide) rfl rfl
    refine ⟨by rw [w, vu]; split <;> rng, by rw [w, vu]; split <;> rng, ?_,
      hS.car 1 1 (by decide) rfl rfl (Lim.perm 2 2 2 2 (by decide) c2),
      hS.car 2 1 (by decide) rfl rfl (Lim.perm 0 0 1 1 (by decide) c0),
      hS.car 2 3 (by decide) rfl rfl (Lim.perm 0 0 1 1 (by decide) c1)⟩
    rw [w, vu]
    split <;> d_ring [c3.d]

theorem set_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (setLocs.getD 0 []) setBT0)) {xn un z : Fin pN}
    (h : SetCut (envOf s₀) (sL.getD 0 zero5) (sL.getD 1 zero5) (sL.getD 2 zero5) xn un z) :
    WP isa (.block (setPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧ AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z := by
  have hchk := set_chk1; have hiv := set_iv1
  have hL := list3 sL zero5 (by decide +kernel)
  simp only [sL] at h hL
  generalize leaves (setLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = u, L.getD 1 zero5 = zn, L.getD 2 zero5 = n3 at h hL
  subst hL
  obtain ⟨ul, uh, du, zn', a, x⟩ := h
  refine WP.mono (cut_step' hchk hc hB hiv set_ov1 (rs := [u, zn, n3, Id.run (sqrCore tops n3)]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  have w : vI (envOf s) 0 (t5 0) = vI (envOf s₀) 0 u := hS.val 0 0 (by decide) rfl rfl
  exact ⟨by rw [w]; exact ul, by rw [w]; exact uh, by rw [w]; exact du, hS.car 1 1 (by decide) rfl rfl zn',
    hS.car 2 1 (by decide) rfl rfl a, hS.car 2 3 (by decide) rfl rfl x, hS.raw 3 1 (by decide) rfl rfl (Raw.sqr a),
    hS.raw 3 3 (by decide) rfl rfl (Raw.sqr x)⟩

theorem setPieces_flat : setPieces.flatten = setPieces.getD 0 [] ++ setPieces.getD 1 [] := by decide +kernel

/-- The first point: the accumulator's vectors stand for the entry's triple, `(4 ex, ±4 ey, 2 ez)`. -/
theorem set_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ setB) {p : AP (Fin pN)}
    (hzz : Ent (envOf s₀) 0 (t5 20) (p.ez * p.ez)) (hx : Ent (envOf s₀) 1 (t5 20) p.ex)
    (hz : Ent (envOf s₀) 2 (t5 20) p.ez) (hy : Ent (envOf s₀) 3 (t5 20) p.ey)
    (hs : SgnOk (envOf s₀) sgnT.l0 p.neg) :
    WP isa (.block setPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧
        AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) p.ex (if p.neg then 0 - p.ey else p.ey) p.ez := by
  rw [setPieces_flat, WP.block_append_iff]
  refine WP.mono (set_s0 hc hB hzz hx hz hy hs) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  exact WP.mono (set_s1 c₁ b₁ h₁) fun s ⟨c, k, b, h⟩ => ⟨c, k₁.trans k, b, h⟩

/-! ### Out of the vectors -/

/-- A lane of a constant below `2²⁵⁶`. -/
theorem fconst_car (c0 c1 c2 c3 : Nat) (E : Env) {k : Nat} (hk : k < 4) (hc : pick4 c0 c1 c2 c3 k < 2 ^ 256) :
    Car E k (Id.run (fconst tops c0 c1 c2 c3)) (D (pick4 c0 c1 c2 c3 k : Nat)) := by
  have e (i : Nat) : (tops.const ⟨limbOf c0 i, limbOf c1 i, limbOf c2 i, limbOf c3 i⟩).int E k =
      (limbOf (pick4 c0 c1 c2 c3 k) i : Nat) := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
  have hv := limbOf_val (pick4 c0 c1 c2 c3 k)
  have ev : vI E k (Id.run (fconst tops c0 c1 c2 c3)) = (pick4 c0 c1 c2 c3 k : Nat) := by
    rw [← hv]
    simp only [vI, fconst, Id.run, bind, pure, e]
  refine ⟨?_, by rw [ev]; simp only [Nb]; omega, by rw [ev]⟩
  simp only [Carried, fconst, Id.run, bind, pure, e]
  simp only [limbOf, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
  omega

/-- `[u, zn, _, Xn]` of the accumulator, with `u` made positive. -/
abbrev outX : F5 T :=
  Id.run (fbias tops (Id.run (fblend tops (Id.run (fblend tops (t5 0) (t5 5) 2)) (t5 10) 8)) 20 0 0 0)

theorem outX_v0 (E : Env) : vI E 0 outX = vI E 0 (t5 0) + 20 * pI := by
  glue_simp [outX]
  omega

theorem outX_v1 (E : Env) : vI E 1 outX = vI E 1 (t5 5) := by
  glue_simp [outX]
  omega

theorem outX_v3 (E : Env) : vI E 3 outX = vI E 3 (t5 10) := by
  glue_simp [outX]
  omega

/-- The places of stage `j`'s results, as terms. -/
abbrev oL (j : Nat) : List (F5 T) := leaves (outLocs.getD j [])

theorem list1 {α : Type} (l : List α) (d : α) (h : l.length = 1) : l = [l.getD 0 d] := by
  match l, h with
  | [_], _ => rfl

/-- A vector's lanes 0, 1 and 3 stand for `a`, `b` and `c`. -/
structure Out3 (bd : Int) (E : Env) (v : F5 T) (a b c : Fin pN) : Prop where
  y : Val bd E 0 v a
  z : Val bd E 1 v b
  x : Val bd E 3 v c

/-- A vector's lanes 0, 1 and 3 are carried and stand for `a`, `b` and `c`. -/
structure Car3 (E : Env) (v : F5 T) (a b c : Fin pN) : Prop where
  y : Car E 0 v a
  z : Car E 1 v b
  x : Car E 3 v c

theorem out_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) :
    WP isa (.block (outPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (outLocs.getD 0 []) outBT0) ∧
        Car3 (envOf s) ((oL 0).getD 0 zero5) un z xn := by
  obtain ⟨ul, uh, du, zn, -, x, -, -⟩ := h
  have iv (k : Nat) (hk : k = 0 ∨ k = 1 ∨ k = 3) : ∃ iv, (Id.run (norm tops outX)).l4.iv stB k = some iv := by
    have : ∀ k < 4, k ≠ 2 → ((Id.run (norm tops outX)).l4.iv stB k).isSome = true := by decide +kernel
    exact Option.isSome_iff_exists.1 (this k (by omega) (by omega))
  obtain ⟨i0, hi0⟩ := iv 0 (by decide)
  obtain ⟨i1, hi1⟩ := iv 1 (by decide)
  obtain ⟨i3, hi3⟩ := iv 3 (by decide)
  have v0 := outX_v0 (envOf s₀); have v1 := outX_v1 (envOf s₀); have v3 := outX_v3 (envOf s₀)
  have zl := zn.lo; have zh := zn.hi; have xl := x.lo; have xh := x.hi
  have c0 : Car (envOf s₀) 0 _ un := Car.norm hB outX (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; d_ring [du])
  have c1 : Car (envOf s₀) 1 _ z := Car.norm hB outX (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; exact zn.d)
  have c3 : Car (envOf s₀) 3 _ xn := Car.norm hB outX (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; exact x.d)
  refine WP.mono (cut_step' out_chk0 hc hB out_iv0 out_ov0 (rs := [Id.run (norm tops outX)]) rfl rfl
    (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [outOv0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 3 (by decide) rfl rfl c3⟩

theorem out_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (outLocs.getD 0 []) outBT0)) {xn un z : Fin pN}
    (h : Car3 (envOf s₀) ((oL 0).getD 0 zero5) un z xn) :
    WP isa (.block (outPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (outLocs.getD 1 []) outBT1) ∧
        Out3 Pb (envOf s) ((oL 1).getD 0 zero5) (un * D (c4R : Nat)) (z * D (c2R : Nat)) (xn * D (c4R : Nat)) := by
  have hchk := out_chk1; have hiv := out_iv1
  have hL := list1 (oL 0) zero5 (by decide +kernel)
  simp only [oL] at h hL
  generalize leaves (outLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = n at h hL
  subst hL
  obtain ⟨y, z', x⟩ := h
  have k0 := fconst_car c4R c2R 0 c4R (envOf s₀) (k := 0) (by decide) (by decide)
  have k1 := fconst_car c4R c2R 0 c4R (envOf s₀) (k := 1) (by decide) (by decide)
  have k3 := fconst_car c4R c2R 0 c4R (envOf s₀) (k := 3) (by decide) (by decide)
  refine WP.mono (cut_step' hchk hc hB hiv out_ov1
    (rs := [Id.run (mulCore tops n (Id.run (fconst tops c4R c2R 0 c4R)))]) rfl rfl (Nat.le_of_eq rfl)
    (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul y k0), hS.raw 0 1 (by decide) rfl rfl (Raw.mul z' k1),
    hS.raw 0 3 (by decide) rfl rfl (Raw.mul x k3)⟩

theorem out_s2 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (outLocs.getD 1 []) outBT1)) {a b c : Fin pN}
    (h : Out3 Pb (envOf s₀) ((oL 1).getD 0 zero5) a b c) :
    WP isa (.block (outPieces.getD 2 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs5 outBT2) ∧ Car3 (envOf s) (t5 0) a b c := by
  have hchk := out_chk2; have hiv := out_iv2
  have hL := list1 (oL 1) zero5 (by decide +kernel)
  simp only [oL] at h hL
  generalize leaves (outLocs.getD 1 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q at h hL
  subst hL
  obtain ⟨y, z, x⟩ := h
  have yl := y.lo; have yh := y.hi; have zl := z.lo; have zh := z.hi; have xl := x.lo; have xh := x.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops q)).l4) rfl 0 (by decide) (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops q)).l4) rfl 1 (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops q)).l4) rfl 3 (by decide) (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ a := Car.norm hB q (by decide) hi0 yl (by rng) y.d
  have c1 : Car (envOf s₀) 1 _ b := Car.norm hB q (by decide) hi1 zl (by rng) z.d
  have c3 : Car (envOf s₀) 3 _ c := Car.norm hB q (by decide) hi3 xl (by rng) x.d
  refine WP.mono (cut_step' hchk hc hB hiv out_ov2 (rs := [Id.run (norm tops q)]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [outOv2, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 3 (by decide) rfl rfl c3⟩

theorem outPieces_flat :
    outPieces.flatten = outPieces.getD 0 [] ++ (outPieces.getD 1 [] ++ outPieces.getD 2 []) := by decide +kernel

/-- Out of the vectors: lanes 0, 1 and 3 of `ymm0`–`ymm4` are carried, and stand for `un`, `z` and
`xn` times `4 · 2²⁵⁶`, `2 · 2²⁵⁶` and `4 · 2²⁵⁶`. -/
theorem out_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) :
    WP isa (.block outPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs5 outBT2) ∧
        Car3 (envOf s) (t5 0) (un * D (c4R : Nat)) (z * D (c2R : Nat)) (xn * D (c4R : Nat)) := by
  rw [outPieces_flat, WP.block_append_iff]
  refine WP.mono (out_s0 hc hB h) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (out_s1 c₁ b₁ h₁) fun s₂ ⟨c₂, k₂, b₂, h₂⟩ => ?_
  exact WP.mono (out_s2 c₂ b₂ h₂) fun s ⟨c, k, b, h⟩ => ⟨c, (k₁.trans k₂).trans k, b, h⟩

/-- A number that stands for `x` times `c · 2²⁵⁶` is `c x` as a multiple of `2²⁵⁶`. -/
theorem out_mont {v : Int} {x : Fin pN} (c : Nat) (h : D v = x * D ((c * 2 ^ 256 % pN : Nat) : Int)) :
    ofI pN v = Fin.ofNat pN c * x * Fin.ofNat pN (2 ^ 256) := by
  have hu := Weierstrass.mul_rinv unitR
  have e : ofI pN ((c * 2 ^ 256 % pN : Nat) : Int) = Fin.ofNat pN c * Fin.ofNat pN (2 ^ 256) := by
    rw [ofI_natCast, Weierstrass.ofNat_mod, Weierstrass.ofNat_mul']
  simp only [D, dec, e] at h
  grind

end VG.Proof.P256.X86_64.Ifma
