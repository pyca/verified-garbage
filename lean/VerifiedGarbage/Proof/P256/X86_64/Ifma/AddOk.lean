module

-- separate module: its proofs (about 5 s, the addition's stages) are not checked again when `Ends` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.DblOk
public import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# P-256 on x86-64 with AVX512_IFMA: the addition

The accumulator's vectors stand for the Jacobian triple `(4 xn, 4 un, 2 z)`
and the entry's for `(ex, ey / 2, ez)` with `ezz = ez²` and `ezzz = ez³`
(`EntOk`), negated where the mask of its sign says so (`SgnOk`); the
addition's code makes of them the accumulator of the sum (`add_ok`,
`add_jac`): seven pieces of code, each a stage of `Impl/…/Ifma/Point.lean`.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

/-- What an addition starts from, as field elements: the accumulator's, the
entry's, and whether the entry is negated. -/
structure AP (F : Type) where
  xn : F
  un : F
  z : F
  ex : F
  ey : F
  ez : F
  ezz : F
  ezzz : F
  neg : Bool

namespace AP
variable {F : Type} [Lean.Grind.CommRing F] (p : AP F)

abbrev U1 : F := p.xn * p.ezz
abbrev H : F := p.z * p.z * p.ex - p.xn * p.ezz
/-- `V`, with the entry's sign. -/
abbrev V : F := if p.neg then 0 - p.z * p.ey else p.z * p.ey
abbrev S1 : F := p.un * p.ezzz
abbrev R : F := p.V * (p.z * p.z) - p.un * p.ezzz
abbrev Z3 : F := 2 * (p.z * p.ez * p.H)
abbrev X3 : F := p.R * p.R - 8 * (p.U1 * (p.H * p.H)) - 4 * (p.H * (p.H * p.H))
abbrev W : F := 4 * (p.U1 * (p.H * p.H)) - p.X3
abbrev Un : F := 2 * (p.R * p.W - 4 * (p.S1 * (p.H * (p.H * p.H))))

end AP

/-- The entry's vectors stand for `p`'s. -/
structure EntOk (E : Env) (ta tb : F5 T) (p : AP (Fin pN)) : Prop where
  zz : Ent E 0 ta p.ezz
  x : Ent E 1 ta p.ex
  z : Ent E 2 ta p.ez
  y : Ent E 3 ta p.ey
  zzz : Ent E 0 tb p.ezzz

/-- The mask of the entry's sign: all ones in lanes 0 and 1 where it is negated, and zero in lanes 2 and 3. -/
structure SgnOk (E : Env) (c : T) (neg : Bool) : Prop where
  b : blendOf c = none
  s0 : c.int E 0 = if neg then -1 else 0
  s1 : c.int E 1 = if neg then -1 else 0
  s2 : c.int E 2 = 0
  s3 : c.int E 3 = 0

/-! ### The numbers of the stages' vectors -/

theorem add2g_snd (q1 u : F5 T) (c : T) : (Id.run (add2g tops q1 u c)).2 = Id.run (fperm tops q1 0 0 0 0) := rfl

theorem add2g_v0 (q1 u : F5 T) (c : T) (E : Env) :
    vI E 0 (Id.run (add2g tops q1 u c)).1 = vI E 0 u + 20 * pI := by
  glue_simp [add2g]
  omega_using []

theorem add2g_v1 (q1 u : F5 T) (c : T) (E : Env) {neg : Bool} (hs : SgnOk E c neg) :
    vI E 1 (Id.run (add2g tops q1 u c)).1 = if neg then 3 * pI - vI E 3 q1 else vI E 3 q1 + 3 * pI := by
  glue_simp [add2g, vI_fsel _ hs.b, vI_fneg, hs.s1]
  cases neg <;> simp <;> omega_using []

theorem add2g_v2 (q1 u : F5 T) (c : T) (E : Env) {neg : Bool} (hs : SgnOk E c neg) :
    vI E 2 (Id.run (add2g tops q1 u c)).1 = vI E 1 q1 - vI E 0 q1 + 3 * pI := by
  glue_simp [add2g, vI_fsel _ hs.b, vI_fneg, hs.s2]
  omega_using []

theorem add2g_v3 (q1 u : F5 T) (c : T) (E : Env) {neg : Bool} (hs : SgnOk E c neg) :
    vI E 3 (Id.run (add2g tops q1 u c)).1 = vI E 2 q1 := by
  glue_simp [add2g, vI_fsel _ hs.b, vI_fneg, hs.s3]
  omega_using []

theorem add3g_fst (al n3 tb : F5 T) : (Id.run (add3g tops al n3 tb)).1 =
    Id.run (fblend tops (Id.run (fblend tops tb n3 2)) (Id.run (fperm tops al 2 2 2 2)) 12) := rfl

theorem add3g_snd (al n3 tb : F5 T) : (Id.run (add3g tops al n3 tb)).2 = Id.run (fperm tops al 2 2 2 2) := rfl

theorem add4g_v0 (q2 pu1 : F5 T) (E : Env) :
    vI E 0 (Id.run (add4g tops q2 pu1)) = vI E 1 q2 - vI E 0 q2 + 2 * pI := by
  glue_simp [add4g]
  omega_using []

theorem add4g_v1 (q2 pu1 : F5 T) (E : Env) : vI E 1 (Id.run (add4g tops q2 pu1)) = 2 * vI E 3 q2 := by
  glue_simp [add4g]
  omega_using []

theorem add4g_v2 (q2 pu1 : F5 T) (E : Env) : vI E 2 (Id.run (add4g tops q2 pu1)) = vI E 2 pu1 := by
  glue_simp [add4g]
  omega_using []

theorem add4g_v3 (q2 pu1 : F5 T) (E : Env) : vI E 3 (Id.run (add4g tops q2 pu1)) = vI E 2 q2 := by
  glue_simp [add4g]
  omega_using []

theorem add5g_fst (be ph : F5 T) : (Id.run (add5g tops be ph)).1 = Id.run (fblend tops be ph 8) := rfl

theorem add5g_snd (be ph : F5 T) :
    (Id.run (add5g tops be ph)).2 = Id.run (fblend tops be (Id.run (fperm tops be 3 3 3 3)) 4) := rfl

theorem add6g_v0 (q : F5 T) (E : Env) :
    vI E 0 (Id.run (add6g tops q)) = 12 * vI E 2 q + 4 * vI E 3 q - vI E 0 q + 2 * pI := by
  glue_simp [add6g]
  omega_using []

theorem add6g_v1 (q : F5 T) (E : Env) : vI E 1 (Id.run (add6g tops q)) = vI E 1 q := by
  glue_simp [add6g]
  omega_using []

theorem add6g_v2 (q : F5 T) (E : Env) : vI E 2 (Id.run (add6g tops q)) = vI E 3 q := by
  glue_simp [add6g]
  omega_using []

theorem add6g_v3 (q : F5 T) (E : Env) :
    vI E 3 (Id.run (add6g tops q)) = vI E 0 q - 8 * vI E 2 q - 4 * vI E 3 q + 13 * pI := by
  glue_simp [add6g]
  omega_using []

theorem add7g_eq (ga be de : F5 T) : Id.run (add7g tops ga be de) =
    Id.run (fblend tops (Id.run (fblend tops ga be 1)) (Id.run (fperm tops de 0 0 0 0)) 4) := rfl

theorem add7u_v0 (q4 : F5 T) (E : Env) : vI E 0 (Id.run (add7u tops q4)) = 2 * (vI E 0 q4 - 4 * vI E 2 q4) := by
  glue_simp [add7u]
  omega_using []

/-! ### What is known between the stages -/

/-- After the first stage: `q1 = [U1, U2, T, V]`. -/
structure AddCut1 (E : Env) (q1 u n3 tb sgn : F5 T) (p : AP (Fin pN)) : Prop where
  u1 : Wide E 0 q1 p.U1
  u2 : Wide E 1 q1 (p.z * p.z * p.ex)
  t : Wide E 2 q1 (p.z * p.ez)
  v : Wide E 3 q1 (p.z * p.ey)
  ul : -20 * pI ≤ vI E 0 u
  uh : vI E 0 u ≤ 3 * pI
  du : D (vI E 0 u) = p.un
  a : Car E 1 n3 (p.z * p.z)
  zzz : Ent E 0 tb p.ezzz
  sg : SgnOk E sgn.l0 p.neg

/-- After the second: `al = [u, ±V, H, T]`, carried. -/
structure AddCut2 (E : Env) (al pu1 n3 tb : F5 T) (p : AP (Fin pN)) : Prop where
  u : Car E 0 al p.un
  v : Car E 1 al p.V
  h : Car E 2 al p.H
  t : Car E 3 al (p.z * p.ez)
  u1 : Wide E 2 pu1 p.U1
  a : Car E 1 n3 (p.z * p.z)
  zzz : Ent E 0 tb p.ezzz

/-- After the third: `q2 = [S1, S2, HH, Zh]`. -/
structure AddCut3 (E : Env) (q2 ph pu1 : F5 T) (p : AP (Fin pN)) : Prop where
  s1 : Wide E 0 q2 p.S1
  s2 : Raw E 1 q2 (p.V * (p.z * p.z))
  hh : Raw E 2 q2 (p.H * p.H)
  zh : Raw E 3 q2 (p.z * p.ez * p.H)
  h : Car E 3 ph p.H
  u1 : Wide E 2 pu1 p.U1

/-- After the fourth: `be = [r, Z3, U1, HH]` and `de = [S1, …]`, carried. -/
structure AddCut4 (E : Env) (be de ph : F5 T) (p : AP (Fin pN)) : Prop where
  r : Car E 0 be p.R
  z3 : Car E 1 be p.Z3
  u1 : Car E 2 be p.U1
  hh : Car E 3 be (p.H * p.H)
  s1 : Car E 0 de p.S1
  h : Car E 3 ph p.H

/-- After the fifth: `q3s = [rr, Z3², U1 HH, HHH]`. -/
structure AddCut5 (E : Env) (q3s be de : F5 T) (p : AP (Fin pN)) : Prop where
  rr : Raw E 0 q3s (p.R * p.R)
  a3 : Raw E 1 q3s (p.Z3 * p.Z3)
  uhh : Raw E 2 q3s (p.U1 * (p.H * p.H))
  hhh : Raw E 3 q3s (p.H * (p.H * p.H))
  r : Car E 0 be p.R
  z3 : Car E 1 be p.Z3
  s1 : Car E 0 de p.S1

/-- After the sixth: `ga = [W, Z3², HHH, X3]`, carried. -/
structure AddCut6 (E : Env) (ga be de : F5 T) (p : AP (Fin pN)) : Prop where
  w : Car E 0 ga p.W
  a3 : Car E 1 ga (p.Z3 * p.Z3)
  hhh : Car E 2 ga (p.H * (p.H * p.H))
  x3 : Car E 3 ga p.X3
  r : Car E 0 be p.R
  z3 : Car E 1 be p.Z3
  s1 : Car E 0 de p.S1

/-- The places of stage `j`'s results, as terms. -/
abbrev aL (j : Nat) : List (F5 T) := leaves (addLocs.getD j [])

/-- `d_ring`, for the addition's field elements. -/
macro "a_ring" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [dec_add, dec_sub, D_lit, D_pI, D_zero, AP.U1, AP.H, AP.V, AP.S1, AP.R, AP.Z3, AP.X3, AP.W, AP.Un,
    $hs,*] <;> grind))

theorem add_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ addB) {p : AP (Fin pN)}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) p.xn p.un p.z)
    (he : EntOk (envOf s₀) (t5 20) (t5 25) p) (hs : SgnOk (envOf s₀) sgnT.l0 p.neg) :
    WP isa (.block (addPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 0 []) addBT0) ∧
        AddCut1 (envOf s) ((aL 0).getD 0 zero5) ((aL 0).getD 1 zero5) ((aL 0).getD 2 zero5) ((aL 0).getD 3 zero5) ((aL 0).getD 4 zero5) p := by
  obtain ⟨ul, uh, du, zn, a, x, -, -⟩ := h
  have a0 : Car (envOf s₀) 0 (Id.run (add1g tops (t5 5) (t5 10))) p.xn :=
    Lim.blendL (by decide) (by decide) (Lim.perm 3 1 1 1 (by decide) x)
  have a1 : Car (envOf s₀) 1 (Id.run (add1g tops (t5 5) (t5 10))) (p.z * p.z) :=
    Lim.blendL (by decide) (by decide) (Lim.perm 3 1 1 1 (by decide) a)
  have a2 : Car (envOf s₀) 2 (Id.run (add1g tops (t5 5) (t5 10))) p.z :=
    Lim.blendR (by decide) (by decide) (Lim.perm 1 1 1 1 (by decide) zn)
  have a3 : Car (envOf s₀) 3 (Id.run (add1g tops (t5 5) (t5 10))) p.z :=
    Lim.blendR (by decide) (by decide) (Lim.perm 1 1 1 1 (by decide) zn)
  refine WP.mono (cut_step' add_chk0 hc hB add_iv0 add_ov0
    (rs := [Id.run (mulCore tops (Id.run (add1g tops (t5 5) (t5 10))) (t5 20)), t5 0, t5 10, t5 25,
      sgnT]) rfl rfl (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil))
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  have w := hS.val 1 0 (by decide) rfl rfl
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Wide.mul a0 he.zz), hS.raw 0 1 (by decide) rfl rfl (Wide.mul a1 he.x),
    hS.raw 0 2 (by decide) rfl rfl (Wide.mul a2 he.z), hS.raw 0 3 (by decide) rfl rfl (Wide.mul a3 he.y),
    by rw [w]; exact ul, by rw [w]; exact uh, by rw [w]; exact du, hS.car 2 1 (by decide) rfl rfl a,
    hS.car 3 0 (by decide) rfl rfl he.zzz,
    ⟨by decide +kernel, (hS.limb 4 0 0 (by decide) rfl (by decide) rfl).trans hs.s0,
      (hS.limb 4 1 0 (by decide) rfl (by decide) rfl).trans hs.s1,
      (hS.limb 4 2 0 (by decide) rfl (by decide) rfl).trans hs.s2,
      (hS.limb 4 3 0 (by decide) rfl (by decide) rfl).trans hs.s3⟩⟩

theorem add_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 0 []) addBT0)) {p : AP (Fin pN)}
    (h : AddCut1 (envOf s₀) ((aL 0).getD 0 zero5) ((aL 0).getD 1 zero5) ((aL 0).getD 2 zero5) ((aL 0).getD 3 zero5) ((aL 0).getD 4 zero5) p) :
    WP isa (.block (addPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 1 []) addBT1) ∧
        AddCut2 (envOf s) ((aL 1).getD 0 zero5) ((aL 1).getD 1 zero5) ((aL 1).getD 2 zero5) ((aL 1).getD 3 zero5) p := by
  have hchk := add_chk1; have hiv := add_iv1
  have hL := list5 (aL 0) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q1, L.getD 1 zero5 = u, L.getD 2 zero5 = n3, L.getD 3 zero5 = tb, L.getD 4 zero5 = sgn at h hL
  subst hL
  obtain ⟨u1, u2, t, v, ul, uh, du, a, zzz, sg⟩ := h
  have v0 := add2g_v0 q1 u sgn.l0 (envOf s₀)
  have v1 := add2g_v1 q1 u sgn.l0 (envOf s₀) sg
  have v2 := add2g_v2 q1 u sgn.l0 (envOf s₀) sg
  have v3 := add2g_v3 q1 u sgn.l0 (envOf s₀) sg
  have u1l := u1.lo; have u1h := u1.hi; have u2l := u2.lo; have u2h := u2.hi
  have tl := t.lo; have th := t.hi; have vl := v.lo; have vh := v.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add2g tops q1 u sgn.l0)).1)).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add2g tops q1 u sgn.l0)).1)).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add2g tops q1 u sgn.l0)).1)).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add2g tops q1 u sgn.l0)).1)).l4) rfl 3 (by decide)
    (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.un := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; a_ring [du])
  have c1 : Car (envOf s₀) 1 _ p.V := Car.norm hB _ (by decide) hi1 (by rw [v1]; split <;> rng)
    (by rw [v1]; split <;> rng) (by rw [v1]; split <;> a_ring [v.d])
  have c2 : Car (envOf s₀) 2 _ p.H := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; a_ring [u1.d, u2.d])
  have c3 : Car (envOf s₀) 3 _ (p.z * p.ez) := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; exact t.d)
  have pu : Wide (envOf s₀) 2 (Id.run (add2g tops q1 u sgn.l0)).2 p.U1 := by
    rw [add2g_snd]; exact Val.perm 0 0 0 0 (by decide) u1
  refine WP.mono (cut_step' hchk hc hB hiv add_ov1
    (rs := [Id.run (norm tops (Id.run (add2g tops q1 u sgn.l0)).1), (Id.run (add2g tops q1 u sgn.l0)).2, n3, tb])
    rfl rfl (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [addOv1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.raw 1 2 (by decide) rfl rfl pu, hS.car 2 1 (by decide) rfl rfl a,
      hS.car 3 0 (by decide) rfl rfl zzz⟩

theorem add_s2 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 1 []) addBT1)) {p : AP (Fin pN)}
    (h : AddCut2 (envOf s₀) ((aL 1).getD 0 zero5) ((aL 1).getD 1 zero5) ((aL 1).getD 2 zero5) ((aL 1).getD 3 zero5) p) :
    WP isa (.block (addPieces.getD 2 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 2 []) addBT2) ∧
        AddCut3 (envOf s) ((aL 2).getD 0 zero5) ((aL 2).getD 1 zero5) ((aL 2).getD 2 zero5) p := by
  have hchk := add_chk2; have hiv := add_iv2
  have hL := list4 (aL 1) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 1 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = al, L.getD 1 zero5 = pu1, L.getD 2 zero5 = n3, L.getD 3 zero5 = tb at h hL
  subst hL
  obtain ⟨u, v, hH, t, u1, a, zzz⟩ := h
  have b0 : Ent (envOf s₀) 0 (Id.run (add3g tops al n3 tb)).1 p.ezzz := by
    rw [add3g_fst]; exact Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) zzz)
  have b1 : Car (envOf s₀) 1 (Id.run (add3g tops al n3 tb)).1 (p.z * p.z) := by
    rw [add3g_fst]; exact Lim.blendL (by decide) (by decide) (Lim.blendR (by decide) (by decide) a)
  have b2 : Car (envOf s₀) 2 (Id.run (add3g tops al n3 tb)).1 p.H := by
    rw [add3g_fst]; exact Lim.blendR (by decide) (by decide) (Lim.perm 2 2 2 2 (by decide) hH)
  have b3 : Car (envOf s₀) 3 (Id.run (add3g tops al n3 tb)).1 p.H := by
    rw [add3g_fst]; exact Lim.blendR (by decide) (by decide) (Lim.perm 2 2 2 2 (by decide) hH)
  have ph : Car (envOf s₀) 3 (Id.run (add3g tops al n3 tb)).2 p.H := by
    rw [add3g_snd]; exact Lim.perm 2 2 2 2 (by decide) hH
  refine WP.mono (cut_step' hchk hc hB hiv add_ov2
    (rs := [Id.run (mulCore tops al (Id.run (add3g tops al n3 tb)).1), (Id.run (add3g tops al n3 tb)).2, pu1])
    rfl rfl (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Wide.mul u b0), hS.raw 0 1 (by decide) rfl rfl (Raw.mul v b1),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul hH b2), hS.raw 0 3 (by decide) rfl rfl (Raw.mul t b3),
    hS.car 1 3 (by decide) rfl rfl ph, hS.raw 2 2 (by decide) rfl rfl u1⟩

theorem add_s3 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 2 []) addBT2)) {p : AP (Fin pN)}
    (h : AddCut3 (envOf s₀) ((aL 2).getD 0 zero5) ((aL 2).getD 1 zero5) ((aL 2).getD 2 zero5) p) :
    WP isa (.block (addPieces.getD 3 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 3 []) addBT3) ∧
        AddCut4 (envOf s) ((aL 3).getD 0 zero5) ((aL 3).getD 1 zero5) ((aL 3).getD 2 zero5) p := by
  have hchk := add_chk3; have hiv := add_iv3
  have hL := list3 (aL 2) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 2 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q2, L.getD 1 zero5 = ph, L.getD 2 zero5 = pu1 at h hL
  subst hL
  obtain ⟨s1, s2, hh, zh, hH, u1⟩ := h
  have v0 := add4g_v0 q2 pu1 (envOf s₀)
  have v1 := add4g_v1 q2 pu1 (envOf s₀)
  have v2 := add4g_v2 q2 pu1 (envOf s₀)
  have v3 := add4g_v3 q2 pu1 (envOf s₀)
  have s1l := s1.lo; have s1h := s1.hi; have s2l := s2.lo; have s2h := s2.hi; have hhl := hh.lo; have hhh := hh.hi
  have zhl := zh.lo; have zhh := zh.hi; have u1l := u1.lo; have u1h := u1.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add4g tops q2 pu1)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add4g tops q2 pu1)))).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add4g tops q2 pu1)))).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add4g tops q2 pu1)))).l4) rfl 3 (by decide)
    (b := _) rfl
  obtain ⟨j0, hj0⟩ := norm_iv1 hiv (t := (Id.run (norm tops q2)).l4) rfl 0 (by decide) (b := _) rfl
  obtain ⟨j1, hj1⟩ := norm_iv1 hiv (t := (Id.run (norm tops q2)).l4) rfl 1 (by decide) (b := _) rfl
  obtain ⟨j2, hj2⟩ := norm_iv1 hiv (t := (Id.run (norm tops q2)).l4) rfl 2 (by decide) (b := _) rfl
  obtain ⟨j3, hj3⟩ := norm_iv1 hiv (t := (Id.run (norm tops q2)).l4) rfl 3 (by decide) (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.R := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; a_ring [s1.d, s2.d])
  have c1 : Car (envOf s₀) 1 _ p.Z3 := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; a_ring [zh.d])
  have c2 : Car (envOf s₀) 2 _ p.U1 := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; exact u1.d)
  have c3 : Car (envOf s₀) 3 _ (p.H * p.H) := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; exact hh.d)
  have d0 : Car (envOf s₀) 0 _ p.S1 := Car.norm hB q2 (by decide) hj0 s1l (by rng) s1.d
  have d1 := Car.norm hB q2 (by decide) hj1 s2l (by rng) rfl
  have d2 := Car.norm hB q2 (by decide) hj2 hhl (by rng) rfl
  have d3 := Car.norm hB q2 (by decide) hj3 zhl (by rng) rfl
  refine WP.mono (cut_step' hchk hc hB hiv add_ov3
    (rs := [Id.run (norm tops (Id.run (add4g tops q2 pu1))), Id.run (norm tops q2), ph])
    rfl rfl (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [addOv3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
    · exact d0.c
    · exact d1.c
    · exact d2.c
    · exact d3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.car 1 0 (by decide) rfl rfl d0, hS.car 2 3 (by decide) rfl rfl hH⟩

theorem add_s4 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 3 []) addBT3)) {p : AP (Fin pN)}
    (h : AddCut4 (envOf s₀) ((aL 3).getD 0 zero5) ((aL 3).getD 1 zero5) ((aL 3).getD 2 zero5) p) :
    WP isa (.block (addPieces.getD 4 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 4 []) addBT4) ∧
        AddCut5 (envOf s) ((aL 4).getD 0 zero5) ((aL 4).getD 1 zero5) ((aL 4).getD 2 zero5) p := by
  have hchk := add_chk4; have hiv := add_iv4
  have hL := list3 (aL 3) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 3 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = be, L.getD 1 zero5 = de, L.getD 2 zero5 = ph at h hL
  subst hL
  obtain ⟨r, z3, u1, hh, s1, hH⟩ := h
  have x0 : Car (envOf s₀) 0 (Id.run (add5g tops be ph)).1 p.R := by
    rw [add5g_fst]; exact Lim.blendL (by decide) (by decide) r
  have x1 : Car (envOf s₀) 1 (Id.run (add5g tops be ph)).1 p.Z3 := by
    rw [add5g_fst]; exact Lim.blendL (by decide) (by decide) z3
  have x2 : Car (envOf s₀) 2 (Id.run (add5g tops be ph)).1 p.U1 := by
    rw [add5g_fst]; exact Lim.blendL (by decide) (by decide) u1
  have x3 : Car (envOf s₀) 3 (Id.run (add5g tops be ph)).1 p.H := by
    rw [add5g_fst]; exact Lim.blendR (by decide) (by decide) hH
  have y0 : Car (envOf s₀) 0 (Id.run (add5g tops be ph)).2 p.R := by
    rw [add5g_snd]; exact Lim.blendL (by decide) (by decide) r
  have y1 : Car (envOf s₀) 1 (Id.run (add5g tops be ph)).2 p.Z3 := by
    rw [add5g_snd]; exact Lim.blendL (by decide) (by decide) z3
  have y2 : Car (envOf s₀) 2 (Id.run (add5g tops be ph)).2 (p.H * p.H) := by
    rw [add5g_snd]; exact Lim.blendR (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) hh)
  have y3 : Car (envOf s₀) 3 (Id.run (add5g tops be ph)).2 (p.H * p.H) := by
    rw [add5g_snd]; exact Lim.blendL (by decide) (by decide) hh
  refine WP.mono (cut_step' hchk hc hB hiv add_ov4
    (rs := [Id.run (mulCore tops (Id.run (add5g tops be ph)).1 (Id.run (add5g tops be ph)).2), be, de])
    rfl rfl (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul x0 y0), hS.raw 0 1 (by decide) rfl rfl (Raw.mul x1 y1),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul x2 y2), hS.raw 0 3 (by decide) rfl rfl (Raw.mul x3 y3),
    hS.car 1 0 (by decide) rfl rfl r, hS.car 1 1 (by decide) rfl rfl z3, hS.car 2 0 (by decide) rfl rfl s1⟩

theorem add_s5 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 4 []) addBT4)) {p : AP (Fin pN)}
    (h : AddCut5 (envOf s₀) ((aL 4).getD 0 zero5) ((aL 4).getD 1 zero5) ((aL 4).getD 2 zero5) p) :
    WP isa (.block (addPieces.getD 5 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (addLocs.getD 5 []) addBT5) ∧
        AddCut6 (envOf s) ((aL 5).getD 0 zero5) ((aL 5).getD 1 zero5) ((aL 5).getD 2 zero5) p := by
  have hchk := add_chk5; have hiv := add_iv5
  have hL := list3 (aL 4) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 4 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q3s, L.getD 1 zero5 = be, L.getD 2 zero5 = de at h hL
  subst hL
  obtain ⟨rr, a3, uhh, hhh, r, z3, s1⟩ := h
  have v0 := add6g_v0 q3s (envOf s₀)
  have v1 := add6g_v1 q3s (envOf s₀)
  have v2 := add6g_v2 q3s (envOf s₀)
  have v3 := add6g_v3 q3s (envOf s₀)
  have rrl := rr.lo; have rrh := rr.hi; have a3l := a3.lo; have a3h := a3.hi; have uhl := uhh.lo; have uhu := uhh.hi
  have hl := hhh.lo; have hu := hhh.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add6g tops q3s)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add6g tops q3s)))).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add6g tops q3s)))).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (add6g tops q3s)))).l4) rfl 3 (by decide)
    (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.W := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; a_ring [rr.d, uhh.d, hhh.d])
  have c1 : Car (envOf s₀) 1 _ (p.Z3 * p.Z3) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; exact a3.d)
  have c2 : Car (envOf s₀) 2 _ (p.H * (p.H * p.H)) := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng)
    (by rw [v2]; rng) (by rw [v2]; exact hhh.d)
  have c3 : Car (envOf s₀) 3 _ p.X3 := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; a_ring [rr.d, uhh.d, hhh.d])
  refine WP.mono (cut_step' hchk hc hB hiv add_ov5
    (rs := [Id.run (norm tops (Id.run (add6g tops q3s))), be, de])
    rfl rfl (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [addOv5, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.car 1 0 (by decide) rfl rfl r, hS.car 1 1 (by decide) rfl rfl z3,
      hS.car 2 0 (by decide) rfl rfl s1⟩

theorem add_s6 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (addLocs.getD 5 []) addBT5)) {p : AP (Fin pN)}
    (h : AddCut6 (envOf s₀) ((aL 5).getD 0 zero5) ((aL 5).getD 1 zero5) ((aL 5).getD 2 zero5) p) :
    WP isa (.block (addPieces.getD 6 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧
        AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) p.X3 p.Un p.Z3 := by
  have hchk := add_chk6; have hiv := add_iv6
  have hL := list3 (aL 5) zero5 (by decide +kernel)
  simp only [aL] at h hL
  generalize leaves (addLocs.getD 5 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = ga, L.getD 1 zero5 = be, L.getD 2 zero5 = de at h hL
  subst hL
  obtain ⟨w, a3, hhh, x3, r, z3, s1⟩ := h
  have x0 : Car (envOf s₀) 0 (Id.run (add7g tops ga be de)) p.R := by
    rw [add7g_eq]; exact Lim.blendL (by decide) (by decide) (Lim.blendR (by decide) (by decide) r)
  have x1 : Car (envOf s₀) 1 (Id.run (add7g tops ga be de)) (p.Z3 * p.Z3) := by
    rw [add7g_eq]; exact Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) a3)
  have x2 : Car (envOf s₀) 2 (Id.run (add7g tops ga be de)) p.S1 := by
    rw [add7g_eq]; exact Lim.blendR (by decide) (by decide) (Lim.perm 0 0 0 0 (by decide) s1)
  have x3' : Car (envOf s₀) 3 (Id.run (add7g tops ga be de)) p.X3 := by
    rw [add7g_eq]; exact Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) x3)
  have q0 := Raw.mul x0 w; have q1 := Raw.mul x1 a3; have q2 := Raw.mul x2 hhh; have q3 := Raw.mul x3' x3
  have vu := add7u_v0 (Id.run (mulCore tops (Id.run (add7g tops ga be de)) ga)) (envOf s₀)
  have q0l := q0.lo; have q0h := q0.hi; have q2l := q2.lo; have q2h := q2.hi
  refine WP.mono (cut_step' hchk hc hB hiv add_ov6
    (rs := [Id.run (add7u tops (Id.run (mulCore tops (Id.run (add7g tops ga be de)) ga))), be, ga,
      Id.run (mulCore tops (Id.run (add7g tops ga be de)) ga)])
    rfl rfl (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  have e : vI (envOf s) 0 (t5 0) =
      vI (envOf s₀) 0 (Id.run (add7u tops (Id.run (mulCore tops (Id.run (add7g tops ga be de)) ga)))) :=
    hS.val 0 0 (by decide) rfl rfl
  exact ⟨by rw [e, vu]; rng, by rw [e, vu]; rng, by rw [e, vu]; a_ring [q0.d, q2.d],
    hS.car 1 1 (by decide) rfl rfl z3, hS.car 2 1 (by decide) rfl rfl a3, hS.car 2 3 (by decide) rfl rfl x3,
    hS.raw 3 1 (by decide) rfl rfl q1, hS.raw 3 3 (by decide) rfl rfl q3⟩

theorem addPieces_flat : addPieces.flatten = addPieces.getD 0 [] ++ (addPieces.getD 1 [] ++ (addPieces.getD 2 [] ++
    (addPieces.getD 3 [] ++ (addPieces.getD 4 [] ++ (addPieces.getD 5 [] ++ addPieces.getD 6 []))))) := by
  decide +kernel

/-- The addition: the accumulator's vectors stand for the sum's triple. -/
theorem add_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ addB) {p : AP (Fin pN)}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) p.xn p.un p.z)
    (he : EntOk (envOf s₀) (t5 20) (t5 25) p) (hs : SgnOk (envOf s₀) sgnT.l0 p.neg) :
    WP isa (.block addPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧ AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) p.X3 p.Un p.Z3 := by
  rw [addPieces_flat, WP.block_append_iff]
  refine WP.mono (add_s0 hc hB h he hs) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_s1 c₁ b₁ h₁) fun s₂ ⟨c₂, k₂, b₂, h₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_s2 c₂ b₂ h₂) fun s₃ ⟨c₃, k₃, b₃, h₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_s3 c₃ b₃ h₃) fun s₄ ⟨c₄, k₄, b₄, h₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_s4 c₄ b₄ h₄) fun s₅ ⟨c₅, k₅, b₅, h₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_s5 c₅ b₅ h₅) fun s₆ ⟨c₆, k₆, b₆, h₆⟩ => ?_
  exact WP.mono (add_s6 c₆ b₆ h₆) fun s ⟨c, k, b, h⟩ =>
    ⟨c, (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k, b, h⟩

/-- The sum's triple is the textbook's, `(X3, Y3, Z3)`, as `(X3 / 2², Y3 / 2³, Z3 / 2)`: for an entry
that stands for `(ex, y, ez)`, with `ey = 2 y` and its powers of `ez`. -/
theorem add_jac {F : Type} [Lean.Grind.CommRing F] (p : AP F) (y : F) (hy : p.ey = 2 * y) (hzz : p.ezz = p.ez * p.ez)
    (hzzz : p.ezzz = p.ez * p.ez * p.ez) :
    Weierstrass.jacAddF (4 * p.xn) (4 * p.un) (2 * p.z) p.ex (if p.neg then 0 - y else y) p.ez =
      (4 * (4 * p.X3), 8 * (4 * p.Un), 2 * (2 * p.Z3)) := by
  simp only [Weierstrass.jacAddF, Prod.mk.injEq, AP.U1, AP.H, AP.V, AP.S1, AP.R, AP.Z3, AP.X3, AP.W, AP.Un, hy, hzz,
    hzzz]
  cases p.neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> refine ⟨?_, ?_, ?_⟩ <;> grind

end VG.Proof.P256.X86_64.Ifma
