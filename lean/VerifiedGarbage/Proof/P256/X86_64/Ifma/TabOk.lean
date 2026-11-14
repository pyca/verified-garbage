module

-- separate module: its proofs (the stages of the table's blocks) are not checked again when `Pass` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.ConvOk
public import VerifiedGarbage.Proof.Weierstrass.JacCoZ

/-!
# P-256 on x86-64 with AVX512_IFMA: the table of `Q`'s odd multiples

Between the blocks that make the table, `2 Q` and the entry made last are a
pair of Jacobian triples with one `Z`: `(x₁, y₁, z)` and `(x₂, y₂, z)`, in
`r` (not carried: `Chn`) and `c`. `zaddu_ok`: the block of the next entry
leaves the entry of their sum (`zadduF`, as `EntOk` wants it) and the pair
with the sum's `Z`. `dblu_ok`: the first pair, `2 Q` and `Q`, from `Q`'s
entry, which is made of the words of its coordinates (`tabG_ok`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- A lane of the points between the table's blocks: not carried, in `[70 p, 85 p)`. -/
structure Chn (E : Env) (k : Nat) (v : F5 T) (x : Fin pN) : Prop where
  lo : 70 * pI ≤ vI E k v
  hi : vI E k v < 85 * pI
  d : D (vI E k v) = x

theorem Same.chn {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) (j k : Nat) {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) {v : F5 T} (hv : xs.getD j zero5 = v) {x : Fin pN}
    (hc : Chn E k v x) : Chn E' k (ys.getD j zero5) x := by
  have e := h.val j k hk hb hv
  exact ⟨by rw [e]; exact hc.lo, by rw [e]; exact hc.hi, by rw [e]; exact hc.d⟩

/-- Two points with one `Z`: `(x1, y1, z)` and `(x2, y2, z)`. -/
structure ZP (F : Type) where
  x1 : F
  y1 : F
  x2 : F
  y2 : F
  z : F

namespace ZP
variable {F : Type} [Lean.Grind.CommRing F] (p : ZP F)

abbrev dx : F := p.x1 - p.x2
abbrev dy : F := p.y1 - p.y2
abbrev C : F := p.dx * p.dx
abbrev Dd : F := p.dy * p.dy
abbrev z3 : F := p.z * p.dx
abbrev W1 : F := p.x1 * p.C
abbrev W2 : F := p.x2 * p.C
abbrev x3 : F := p.Dd - p.W1 - p.W2
abbrev A1 : F := p.y1 * (p.W1 - p.W2)
abbrev Ev : F := p.dy * (p.W1 - p.x3)
abbrev zz3 : F := p.z3 * p.z3
abbrev zzz3 : F := p.z3 * p.zz3

end ZP

/-- `d_ring`, for the table's field elements. -/
macro "z_ring" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [dec_add, dec_sub, D_lit, D_pI, D_zero, ZP.dx, ZP.dy, ZP.C, ZP.Dd, ZP.z3, ZP.W1, ZP.W2, ZP.x3,
    ZP.A1, ZP.Ev, ZP.zz3, ZP.zzz3, $hs,*] <;> grind))

/-- The points between the blocks: `r = [x1, y1, y2, _]` and `c = [_, _, z, x2]`. -/
structure ChainOk (E : Env) (r c : F5 T) (p : ZP (Fin pN)) : Prop where
  x1 : Chn E 0 r p.x1
  y1 : Chn E 1 r p.y1
  y2 : Chn E 2 r p.y2
  z : Ent E 2 c p.z
  x2 : Car E 3 c p.x2

/-- An entry of the table: `ta = [z², x, z, y']` and `tb = [z³, …]`. -/
structure TEnt (E : Env) (ta tb : F5 T) (x y' z : Fin pN) : Prop where
  ezz : Ent E 0 ta (z * z)
  ex : Ent E 1 ta x
  ez : Ent E 2 ta z
  ey : Ent E 3 ta y'
  ezzz : Ent E 0 tb (z * (z * z))

/-! ### The numbers of the stages' vectors -/

theorem zaddu1g_v0 (r c : F5 T) (E : Env) :
    vI E 0 (Id.run (zaddu1g tops r c)) = vI E 0 r - vI E 3 c + 80 * pI := by
  glue_simp [zaddu1g]
  omega_using []

theorem zaddu1g_v1 (r c : F5 T) (E : Env) :
    vI E 1 (Id.run (zaddu1g tops r c)) = vI E 1 r - vI E 2 r + 80 * pI := by
  glue_simp [zaddu1g]
  omega_using []

theorem zaddu1g_v2 (r c : F5 T) (E : Env) : vI E 2 (Id.run (zaddu1g tops r c)) = vI E 2 c + 80 * pI := by
  glue_simp [zaddu1g]
  omega_using []

theorem zaddu1g_v3 (r c : F5 T) (E : Env) : vI E 3 (Id.run (zaddu1g tops r c)) = vI E 0 r + 96 * pI := by
  glue_simp [zaddu1g]
  omega_using []

/-- `[C, D, z₃, y₁]`, before the carry. -/
abbrev zn1g (q1 r : F5 T) : F5 T := Id.run (fblend tops q1 (Id.run (fperm tops r 1 1 1 1)) 8)

theorem zn1g_v (q1 r : F5 T) (E : Env) : vI E 0 (zn1g q1 r) = vI E 0 q1 ∧ vI E 1 (zn1g q1 r) = vI E 1 q1 ∧
    vI E 2 (zn1g q1 r) = vI E 2 q1 ∧ vI E 3 (zn1g q1 r) = vI E 1 r := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> glue_simp [zn1g]

theorem zaddu5g_v0 (q2 n1 : F5 T) (E : Env) :
    vI E 0 (Id.run (zaddu5g tops q2 n1)) = vI E 0 q2 - vI E 1 q2 + 80 * pI := by
  glue_simp [zaddu5g]
  omega_using []

theorem zaddu5g_v1 (q2 n1 : F5 T) (E : Env) :
    vI E 1 (Id.run (zaddu5g tops q2 n1)) = vI E 1 q2 + 2 * vI E 0 q2 - vI E 1 n1 + 80 * pI := by
  glue_simp [zaddu5g]
  omega_using []

theorem zaddu5g_v2 (q2 n1 : F5 T) (E : Env) : vI E 2 (Id.run (zaddu5g tops q2 n1)) = vI E 2 q2 + 80 * pI := by
  glue_simp [zaddu5g]
  omega_using []

theorem zaddu5g_v3 (q2 n1 : F5 T) (E : Env) :
    vI E 3 (Id.run (zaddu5g tops q2 n1)) = vI E 1 n1 - vI E 3 q2 - vI E 1 q2 + 96 * pI := by
  glue_simp [zaddu5g]
  omega_using []

/-- `A` in every lane. -/
abbrev zpa (q3 : F5 T) : F5 T := Id.run (fperm tops q3 0 0 0 0)

theorem zaddu7v_v0 (q3 : F5 T) (E : Env) :
    vI E 0 (Id.run (zaddu7v tops q3 (zpa q3))) = vI E 2 q3 + 80 * pI := by
  glue_simp [zaddu7v, zpa]
  omega_using []

theorem zaddu7v_v3 (q3 : F5 T) (E : Env) :
    vI E 3 (Id.run (zaddu7v tops q3 (zpa q3))) = 2 * (vI E 1 q3 - vI E 0 q3) + 96 * pI := by
  glue_simp [zaddu7v, zpa]
  omega_using []

theorem zaddu7r_v0 (q3 q2 : F5 T) (E : Env) :
    vI E 0 (Id.run (zaddu7r tops q3 q2 (zpa q3))) = vI E 0 q2 + 80 * pI := by
  glue_simp [zaddu7r, zpa]
  omega_using []

theorem zaddu7r_v1 (q3 q2 : F5 T) (E : Env) :
    vI E 1 (Id.run (zaddu7r tops q3 q2 (zpa q3))) = vI E 0 q3 + 80 * pI := by
  glue_simp [zaddu7r, zpa]
  omega_using []

theorem zaddu7r_v2 (q3 q2 : F5 T) (E : Env) :
    vI E 2 (Id.run (zaddu7r tops q3 q2 (zpa q3))) = vI E 1 q3 - vI E 0 q3 + 80 * pI := by
  glue_simp [zaddu7r, zpa]
  omega_using []

/-! ### The stages of the next entry -/

/-- After the first stage: `o1 = [dx, dy, z, x1]`, carried. -/
structure ZCut1 (E : Env) (o1 r c : F5 T) (p : ZP (Fin pN)) : Prop where
  dx : Car E 0 o1 p.dx
  dy : Car E 1 o1 p.dy
  z : Car E 2 o1 p.z
  x1 : Car E 3 o1 p.x1
  y1 : Chn E 1 r p.y1
  x2 : Car E 3 c p.x2

/-- After the second: `q1 = [C, D, z3, _]`. -/
structure ZCut2 (E : Env) (q1 o1 r c : F5 T) (p : ZP (Fin pN)) : Prop where
  cc : Raw E 0 q1 p.C
  dd : Raw E 1 q1 p.Dd
  z3 : Raw E 2 q1 p.z3
  dy : Car E 1 o1 p.dy
  x1 : Car E 3 o1 p.x1
  y1 : Chn E 1 r p.y1
  x2 : Car E 3 c p.x2

/-- After the third: `n1 = [C, D, z3, y1]`, carried. -/
structure ZCut3 (E : Env) (n1 o1 c : F5 T) (p : ZP (Fin pN)) : Prop where
  cc : Car E 0 n1 p.C
  dd : Car E 1 n1 p.Dd
  z3 : Car E 2 n1 p.z3
  y1 : Car E 3 n1 p.y1
  dy : Car E 1 o1 p.dy
  x1 : Car E 3 o1 p.x1
  x2 : Car E 3 c p.x2

/-- After the fourth: `q2 = [W1, W2, zz3, W1]`. -/
structure ZCut4 (E : Env) (q2 n1 o1 : F5 T) (p : ZP (Fin pN)) : Prop where
  w1 : Raw E 0 q2 p.W1
  w2 : Raw E 1 q2 p.W2
  zz3 : Raw E 2 q2 p.zz3
  w1' : Raw E 3 q2 p.W1
  dd : Car E 1 n1 p.Dd
  z3 : Car E 2 n1 p.z3
  y1 : Car E 3 n1 p.y1
  dy : Car E 1 o1 p.dy

/-- After the fifth: `n2 = [W1 - W2, W1 - x3, zz3, x3]`, carried. -/
structure ZCut5 (E : Env) (n2 q2 n1 o1 : F5 T) (p : ZP (Fin pN)) : Prop where
  dw : Car E 0 n2 (p.W1 - p.W2)
  e : Car E 1 n2 (p.W1 - p.x3)
  zz3 : Car E 2 n2 p.zz3
  x3 : Car E 3 n2 p.x3
  w1 : Raw E 0 q2 p.W1
  z3 : Car E 2 n1 p.z3
  y1 : Car E 3 n1 p.y1
  dy : Car E 1 o1 p.dy

/-- After the sixth: `q3 = [A, E, zzz3, _]`. -/
structure ZCut6 (E : Env) (q3 n2 q2 n1 : F5 T) (p : ZP (Fin pN)) : Prop where
  a1 : Raw E 0 q3 p.A1
  ev : Raw E 1 q3 p.Ev
  zzz3 : Raw E 2 q3 p.zzz3
  zz3 : Car E 2 n2 p.zz3
  x3 : Car E 3 n2 p.x3
  w1 : Raw E 0 q2 p.W1
  z3 : Car E 2 n1 p.z3

/-- The places of stage `j`'s results, as terms. -/
abbrev zL (j : Nat) : List (F5 T) := leaves (zadduLocs.getD j [])

theorem zaddu_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf regs20 tabBT)) {p : ZP (Fin pN)}
    (h : ChainOk (envOf s₀) (t5 10) (t5 15) p) :
    WP isa (.block (zadduPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 0 []) zadduBT0) ∧
        ZCut1 (envOf s) ((zL 0).getD 0 zero5) ((zL 0).getD 1 zero5) ((zL 0).getD 2 zero5) p := by
  obtain ⟨x1, y1, y2, z, x2⟩ := h
  have v0 := zaddu1g_v0 (t5 10) (t5 15) (envOf s₀)
  have v1 := zaddu1g_v1 (t5 10) (t5 15) (envOf s₀)
  have v2 := zaddu1g_v2 (t5 10) (t5 15) (envOf s₀)
  have v3 := zaddu1g_v3 (t5 10) (t5 15) (envOf s₀)
  have x1l := x1.lo; have x1h := x1.hi; have y1l := y1.lo; have y1h := y1.hi; have y2l := y2.lo; have y2h := y2.hi
  have zl := z.lo; have zh := z.hi; have x2l := x2.lo; have x2h := x2.hi
  obtain ⟨i0, hi0⟩ := norm_iv zaddu_iv0 (t := (Id.run (norm tops (Id.run (zaddu1g tops (t5 10) (t5 15))))).l4) rfl 0
    (by decide) (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv zaddu_iv0 (t := (Id.run (norm tops (Id.run (zaddu1g tops (t5 10) (t5 15))))).l4) rfl 1
    (by decide) (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv zaddu_iv0 (t := (Id.run (norm tops (Id.run (zaddu1g tops (t5 10) (t5 15))))).l4) rfl 2
    (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv zaddu_iv0 (t := (Id.run (norm tops (Id.run (zaddu1g tops (t5 10) (t5 15))))).l4) rfl 3
    (by decide) (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.dx := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; z_ring [x1.d, x2.d])
  have c1 : Car (envOf s₀) 1 _ p.dy := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; z_ring [y1.d, y2.d])
  have c2 : Car (envOf s₀) 2 _ p.z := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; z_ring [z.d])
  have c3 : Car (envOf s₀) 3 _ p.x1 := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; z_ring [x1.d])
  refine WP.mono (cut_step' zaddu_chk0 hc hB zaddu_iv0 zaddu_ov0
    (rs := [Id.run (norm tops (Id.run (zaddu1g tops (t5 10) (t5 15)))), t5 10, t5 15]) rfl rfl (by decide) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [zadduOv0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.chn 1 1 (by decide) rfl rfl y1, hS.car 2 3 (by decide) rfl rfl x2⟩

theorem zaddu_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 0 []) zadduBT0))
    {p : ZP (Fin pN)} (h : ZCut1 (envOf s₀) ((zL 0).getD 0 zero5) ((zL 0).getD 1 zero5) ((zL 0).getD 2 zero5) p) :
    WP isa (.block (zadduPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 1 []) zadduBT1) ∧
        ZCut2 (envOf s) ((zL 1).getD 0 zero5) ((zL 1).getD 1 zero5) ((zL 1).getD 2 zero5) ((zL 1).getD 3 zero5) p := by
  have hchk := zaddu_chk1; have hiv := zaddu_iv1
  have hL := list3 (zL 0) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = o1, L.getD 1 zero5 = r, L.getD 2 zero5 = c at h hL
  subst hL
  obtain ⟨dx, dy, z, x1, y1, x2⟩ := h
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov1
    (rs := [Id.run (mulCore tops o1 (Id.run (fperm tops o1 0 1 0 3))), o1, r, c]) rfl rfl (Nat.le_of_eq rfl)
    (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul dx (Lim.perm 0 1 0 3 (by decide) dx)),
    hS.raw 0 1 (by decide) rfl rfl (Raw.mul dy (Lim.perm 0 1 0 3 (by decide) dy)),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul z (Lim.perm 0 1 0 3 (by decide) dx)),
    hS.car 1 1 (by decide) rfl rfl dy, hS.car 1 3 (by decide) rfl rfl x1, hS.chn 2 1 (by decide) rfl rfl y1,
    hS.car 3 3 (by decide) rfl rfl x2⟩

theorem zaddu_s2 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 1 []) zadduBT1))
    {p : ZP (Fin pN)}
    (h : ZCut2 (envOf s₀) ((zL 1).getD 0 zero5) ((zL 1).getD 1 zero5) ((zL 1).getD 2 zero5) ((zL 1).getD 3 zero5) p) :
    WP isa (.block (zadduPieces.getD 2 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 2 []) zadduBT2) ∧
        ZCut3 (envOf s) ((zL 2).getD 0 zero5) ((zL 2).getD 1 zero5) ((zL 2).getD 2 zero5) p := by
  have hchk := zaddu_chk2; have hiv := zaddu_iv2
  have hL := list4 (zL 1) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 1 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q1, L.getD 1 zero5 = o1, L.getD 2 zero5 = r, L.getD 3 zero5 = c at h hL
  subst hL
  obtain ⟨cc, dd, z3, dy, x1, y1, x2⟩ := h
  obtain ⟨v0, v1, v2, v3⟩ := zn1g_v q1 r (envOf s₀)
  have ccl := cc.lo; have cch := cc.hi; have ddl := dd.lo; have ddh := dd.hi; have z3l := z3.lo; have z3h := z3.hi
  have y1l := y1.lo; have y1h := y1.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (zn1g q1 r))).l4) rfl 0 (by decide) (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (zn1g q1 r))).l4) rfl 1 (by decide) (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (zn1g q1 r))).l4) rfl 2 (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (zn1g q1 r))).l4) rfl 3 (by decide) (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.C := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; exact cc.d)
  have c1 : Car (envOf s₀) 1 _ p.Dd := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; exact dd.d)
  have c2 : Car (envOf s₀) 2 _ p.z3 := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; exact z3.d)
  have c3 : Car (envOf s₀) 3 _ p.y1 := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; exact y1.d)
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov2 (rs := [Id.run (norm tops (zn1g q1 r)), o1, c]) rfl rfl
    (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [zadduOv2, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.car 1 1 (by decide) rfl rfl dy, hS.car 1 3 (by decide) rfl rfl x1,
      hS.car 2 3 (by decide) rfl rfl x2⟩

/-- `[x1, x2, z3, x1]`. -/
abbrev za2 (o1 c n1 : F5 T) : F5 T :=
  Id.run (fblend tops (Id.run (fblend tops (Id.run (fperm tops o1 3 3 3 3)) (Id.run (fperm tops c 3 3 3 3)) 2)) n1 4)

theorem zaddu_s3 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 2 []) zadduBT2))
    {p : ZP (Fin pN)} (h : ZCut3 (envOf s₀) ((zL 2).getD 0 zero5) ((zL 2).getD 1 zero5) ((zL 2).getD 2 zero5) p) :
    WP isa (.block (zadduPieces.getD 3 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 3 []) zadduBT3) ∧
        ZCut4 (envOf s) ((zL 3).getD 0 zero5) ((zL 3).getD 1 zero5) ((zL 3).getD 2 zero5) p := by
  have hchk := zaddu_chk3; have hiv := zaddu_iv3
  have hL := list3 (zL 2) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 2 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = n1, L.getD 1 zero5 = o1, L.getD 2 zero5 = c at h hL
  subst hL
  obtain ⟨cc, dd, z3, y1, dy, x1, x2⟩ := h
  have a0 : Car (envOf s₀) 0 (za2 o1 c n1) p.x1 :=
    Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) x1))
  have a1 : Car (envOf s₀) 1 (za2 o1 c n1) p.x2 :=
    Lim.blendL (by decide) (by decide) (Lim.blendR (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) x2))
  have a2 : Car (envOf s₀) 2 (za2 o1 c n1) p.z3 := Lim.blendR (by decide) (by decide) z3
  have a3 : Car (envOf s₀) 3 (za2 o1 c n1) p.x1 :=
    Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) x1))
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov3
    (rs := [Id.run (mulCore tops (za2 o1 c n1) (Id.run (fperm tops n1 0 0 2 0))), n1, o1]) rfl rfl (Nat.le_of_eq rfl)
    (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul a0 (Lim.perm 0 0 2 0 (by decide) cc)),
    hS.raw 0 1 (by decide) rfl rfl (Raw.mul a1 (Lim.perm 0 0 2 0 (by decide) cc)),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul a2 (Lim.perm 0 0 2 0 (by decide) z3)),
    hS.raw 0 3 (by decide) rfl rfl (Raw.mul a3 (Lim.perm 0 0 2 0 (by decide) cc)),
    hS.car 1 1 (by decide) rfl rfl dd, hS.car 1 2 (by decide) rfl rfl z3, hS.car 1 3 (by decide) rfl rfl y1,
    hS.car 2 1 (by decide) rfl rfl dy⟩

theorem zaddu_s4 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 3 []) zadduBT3))
    {p : ZP (Fin pN)} (h : ZCut4 (envOf s₀) ((zL 3).getD 0 zero5) ((zL 3).getD 1 zero5) ((zL 3).getD 2 zero5) p) :
    WP isa (.block (zadduPieces.getD 4 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 4 []) zadduBT4) ∧
        ZCut5 (envOf s) ((zL 4).getD 0 zero5) ((zL 4).getD 1 zero5) ((zL 4).getD 2 zero5) ((zL 4).getD 3 zero5) p := by
  have hchk := zaddu_chk4; have hiv := zaddu_iv4
  have hL := list3 (zL 3) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 3 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q2, L.getD 1 zero5 = n1, L.getD 2 zero5 = o1 at h hL
  subst hL
  obtain ⟨w1, w2, zz3, w1', dd, z3, y1, dy⟩ := h
  have v0 := zaddu5g_v0 q2 n1 (envOf s₀)
  have v1 := zaddu5g_v1 q2 n1 (envOf s₀)
  have v2 := zaddu5g_v2 q2 n1 (envOf s₀)
  have v3 := zaddu5g_v3 q2 n1 (envOf s₀)
  have w1l := w1.lo; have w1h := w1.hi; have w2l := w2.lo; have w2h := w2.hi; have zl := zz3.lo; have zh := zz3.hi
  have w3l := w1'.lo; have w3h := w1'.hi; have ddl := dd.lo; have ddh := dd.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (zaddu5g tops q2 n1)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (zaddu5g tops q2 n1)))).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (zaddu5g tops q2 n1)))).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (zaddu5g tops q2 n1)))).l4) rfl 3 (by decide)
    (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ (p.W1 - p.W2) := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; z_ring [w1.d, w2.d])
  have c1 : Car (envOf s₀) 1 _ (p.W1 - p.x3) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; z_ring [w1.d, w2.d, dd.d])
  have c2 : Car (envOf s₀) 2 _ p.zz3 := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; z_ring [zz3.d])
  have c3 : Car (envOf s₀) 3 _ p.x3 := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; z_ring [w1'.d, w2.d, dd.d])
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov4
    (rs := [Id.run (norm tops (Id.run (zaddu5g tops q2 n1))), q2, n1, o1]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [zadduOv4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.raw 1 0 (by decide) rfl rfl w1, hS.car 2 2 (by decide) rfl rfl z3,
      hS.car 2 3 (by decide) rfl rfl y1, hS.car 3 1 (by decide) rfl rfl dy⟩

/-- `[y1, dy, z3, y1]`. -/
abbrev za3 (n1 o1 : F5 T) : F5 T :=
  Id.run (fblend tops (Id.run (fblend tops (Id.run (fperm tops n1 3 3 3 3)) o1 2)) n1 4)

theorem zaddu_s5 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 4 []) zadduBT4))
    {p : ZP (Fin pN)}
    (h : ZCut5 (envOf s₀) ((zL 4).getD 0 zero5) ((zL 4).getD 1 zero5) ((zL 4).getD 2 zero5) ((zL 4).getD 3 zero5) p) :
    WP isa (.block (zadduPieces.getD 5 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (zadduLocs.getD 5 []) zadduBT5) ∧
        ZCut6 (envOf s) ((zL 5).getD 0 zero5) ((zL 5).getD 1 zero5) ((zL 5).getD 2 zero5) ((zL 5).getD 3 zero5) p := by
  have hchk := zaddu_chk5; have hiv := zaddu_iv5
  have hL := list4 (zL 4) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 4 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = n2, L.getD 1 zero5 = q2, L.getD 2 zero5 = n1, L.getD 3 zero5 = o1 at h hL
  subst hL
  obtain ⟨dw, e, zz3, x3, w1, z3, y1, dy⟩ := h
  have a0 : Car (envOf s₀) 0 (za3 n1 o1) p.y1 :=
    Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) y1))
  have a1 : Car (envOf s₀) 1 (za3 n1 o1) p.dy := Lim.blendL (by decide) (by decide) (Lim.blendR (by decide) (by decide) dy)
  have a2 : Car (envOf s₀) 2 (za3 n1 o1) p.z3 := Lim.blendR (by decide) (by decide) z3
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov5 (rs := [Id.run (mulCore tops (za3 n1 o1) n2), n2, q2, n1]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul a0 dw), hS.raw 0 1 (by decide) rfl rfl (Raw.mul a1 e),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul a2 zz3), hS.car 1 2 (by decide) rfl rfl zz3,
    hS.car 1 3 (by decide) rfl rfl x3, hS.raw 2 0 (by decide) rfl rfl w1, hS.car 3 2 (by decide) rfl rfl z3⟩

/-- The sum's entry and the points after it. -/
structure ZOut (E : Env) (ta tb r c : F5 T) (p : ZP (Fin pN)) : Prop where
  ent : TEnt E ta tb p.x3 (2 * (p.Ev - p.A1)) p.z3
  x1 : Chn E 0 r p.W1
  y1 : Chn E 1 r p.A1
  y2 : Chn E 2 r (p.Ev - p.A1)
  z : Car E 2 c p.z3
  x2 : Car E 3 c p.x3

/-- The entry's second vector, carried. -/
abbrev znv (q3 : F5 T) : F5 T := Id.run (norm tops (Id.run (zaddu7v tops q3 (zpa q3))))

/-- The entry's first vector. -/
abbrev zta (q3 n2 n1 : F5 T) : F5 T :=
  Id.run (fblend tops (Id.run (fblend tops (Id.run (fperm tops n2 2 3 2 3)) n1 4)) (znv q3) 8)

theorem zaddu_s6 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (zadduLocs.getD 5 []) zadduBT5))
    {p : ZP (Fin pN)}
    (h : ZCut6 (envOf s₀) ((zL 5).getD 0 zero5) ((zL 5).getD 1 zero5) ((zL 5).getD 2 zero5) ((zL 5).getD 3 zero5) p) :
    WP isa (.block (zadduPieces.getD 6 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs20 tabBT) ∧ ZOut (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) p := by
  have hchk := zaddu_chk6; have hiv := zaddu_iv6
  have hL := list4 (zL 5) zero5 (by decide +kernel)
  simp only [zL] at h hL
  generalize leaves (zadduLocs.getD 5 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q3, L.getD 1 zero5 = n2, L.getD 2 zero5 = q2, L.getD 3 zero5 = n1 at h hL
  subst hL
  obtain ⟨a1, ev, zzz3, zz3, x3, w1, z3⟩ := h
  have nb : Nb ≤ 2 ^ 259 := by simp only [Nb]; omega_using []
  have v0 := zaddu7v_v0 q3 (envOf s₀)
  have v3 := zaddu7v_v3 q3 (envOf s₀)
  have r0 := zaddu7r_v0 q3 q2 (envOf s₀)
  have r1 := zaddu7r_v1 q3 q2 (envOf s₀)
  have r2 := zaddu7r_v2 q3 q2 (envOf s₀)
  have a1l := a1.lo; have a1h := a1.hi; have evl := ev.lo; have evh := ev.hi; have zl := zzz3.lo; have zh := zzz3.hi
  have w1l := w1.lo; have w1h := w1.hi
  obtain ⟨i0, hi0⟩ := norm_iv1 hiv (t := (znv q3).l4) rfl 0 (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv1 hiv (t := (znv q3).l4) rfl 3 (by decide) (b := _) rfl
  have c0 : Car (envOf s₀) 0 (znv q3) p.zzz3 := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; z_ring [zzz3.d])
  have c3 : Car (envOf s₀) 3 (znv q3) (2 * (p.Ev - p.A1)) :=
    Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng) (by rw [v3]; z_ring [ev.d, a1.d])
  have t0 : Car (envOf s₀) 0 (zta q3 n2 n1) p.zz3 :=
    Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) (Lim.perm 2 3 2 3 (by decide) zz3))
  have t1 : Car (envOf s₀) 1 (zta q3 n2 n1) p.x3 :=
    Lim.blendL (by decide) (by decide) (Lim.blendL (by decide) (by decide) (Lim.perm 2 3 2 3 (by decide) x3))
  have t2 : Car (envOf s₀) 2 (zta q3 n2 n1) p.z3 :=
    Lim.blendL (by decide) (by decide) (Lim.blendR (by decide) (by decide) z3)
  have t3 : Car (envOf s₀) 3 (zta q3 n2 n1) (2 * (p.Ev - p.A1)) := Lim.blendR (by decide) (by decide) c3
  have cz : Car (envOf s₀) 2 (Id.run (fblend tops n1 n2 8)) p.z3 := Lim.blendL (by decide) (by decide) z3
  have cx : Car (envOf s₀) 3 (Id.run (fblend tops n1 n2 8)) p.x3 := Lim.blendR (by decide) (by decide) x3
  have k0 : Chn (envOf s₀) 0 (Id.run (zaddu7r tops q3 q2 (zpa q3))) p.W1 :=
    ⟨by rw [r0]; rng, by rw [r0]; rng, by rw [r0]; z_ring [w1.d]⟩
  have k1 : Chn (envOf s₀) 1 (Id.run (zaddu7r tops q3 q2 (zpa q3))) p.A1 :=
    ⟨by rw [r1]; rng, by rw [r1]; rng, by rw [r1]; z_ring [a1.d]⟩
  have k2 : Chn (envOf s₀) 2 (Id.run (zaddu7r tops q3 q2 (zpa q3))) (p.Ev - p.A1) :=
    ⟨by rw [r2]; rng, by rw [r2]; rng, by rw [r2]; z_ring [ev.d, a1.d]⟩
  refine WP.mono (cut_step' hchk hc hB hiv zaddu_ov6
    (rs := [zta q3 n2 n1, znv q3, Id.run (zaddu7r tops q3 q2 (zpa q3)), Id.run (fblend tops n1 n2 8)]) rfl rfl
    (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [zadduOv6, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact t3.c
    · exact c0.c
  · exact ⟨⟨(hS.car 0 0 (by decide) rfl rfl t0).mono nb, (hS.car 0 1 (by decide) rfl rfl t1).mono nb,
        (hS.car 0 2 (by decide) rfl rfl t2).mono nb, (hS.car 0 3 (by decide) rfl rfl t3).mono nb,
        (hS.car 1 0 (by decide) rfl rfl c0).mono nb⟩,
      hS.chn 2 0 (by decide) rfl rfl k0, hS.chn 2 1 (by decide) rfl rfl k1, hS.chn 2 2 (by decide) rfl rfl k2,
      hS.car 3 2 (by decide) rfl rfl cz, hS.car 3 3 (by decide) rfl rfl cx⟩

theorem zadduPieces_flat : zadduPieces.flatten = zadduPieces.getD 0 [] ++ (zadduPieces.getD 1 [] ++
    (zadduPieces.getD 2 [] ++ (zadduPieces.getD 3 [] ++ (zadduPieces.getD 4 [] ++ (zadduPieces.getD 5 [] ++
    zadduPieces.getD 6 []))))) := by
  decide +kernel

/-- The next entry: from `2 Q` and the entry before with one `Z`, their sum's entry, and the two with
the sum's `Z`. -/
theorem zaddu_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf regs20 tabBT)) {p : ZP (Fin pN)}
    (h : ChainOk (envOf s₀) (t5 10) (t5 15) p) :
    WP isa (.block zadduPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs20 tabBT) ∧ ZOut (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) p := by
  rw [zadduPieces_flat, WP.block_append_iff]
  refine WP.mono (zaddu_s0 hc hB h) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zaddu_s1 c₁ b₁ h₁) fun s₂ ⟨c₂, k₂, b₂, h₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zaddu_s2 c₂ b₂ h₂) fun s₃ ⟨c₃, k₃, b₃, h₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zaddu_s3 c₃ b₃ h₃) fun s₄ ⟨c₄, k₄, b₄, h₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zaddu_s4 c₄ b₄ h₄) fun s₅ ⟨c₅, k₅, b₅, h₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zaddu_s5 c₅ b₅ h₅) fun s₆ ⟨c₆, k₆, b₆, h₆⟩ => ?_
  exact WP.mono (zaddu_s6 c₆ b₆ h₆) fun s ⟨c, k, b, h⟩ =>
    ⟨c, (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k, b, h⟩

/-- The block's field elements are `zadduF`'s. -/
theorem zp_zadduF {F : Type} [Lean.Grind.CommRing F] (p : ZP F) :
    Weierstrass.zadduF p.x1 p.y1 p.x2 p.y2 p.z = ((p.x3, p.Ev - p.A1, p.z3), (p.W1, p.A1)) := by
  simp only [Weierstrass.zadduF, ZP.dx, ZP.dy, ZP.C, ZP.Dd, ZP.z3, ZP.W1, ZP.W2, ZP.x3, ZP.A1, ZP.Ev]

/-- The points after an entry's block are those the next one starts from. -/
theorem ZOut.chain {E : Env} {ta tb r c : F5 T} {p : ZP (Fin pN)} (h : ZOut E ta tb r c p) :
    ChainOk E r c ⟨p.W1, p.A1, p.x3, p.Ev - p.A1, p.z3⟩ :=
  ⟨h.x1, h.y1, h.y2, h.z.mono (by simp only [Nb]; omega_using []), h.x2⟩

/-! ### `2 Q` and `Q` with one `Z` -/

/-- The bound of the square of an entry's lane. -/
abbrev Sq : Int := pI + 2 ^ 258

/-- The square of an entry's lane. -/
theorem Val.sqrE {E : Env} {k : Nat} {a : F5 T} {x : Fin pN} (h : Ent E k a x) :
    Val Sq E k (Id.run (sqrCore tops a)) (x * x) := by
  obtain ⟨M, h0, h1, h2⟩ := sqrCore_val a E k h.c
  have a0 := h.c.nonneg
  have hA := h.hi
  have hp : vI E k a * vI E k a ≤ 2 ^ 259 * 2 ^ 259 :=
    Int.mul_le_mul (Int.le_of_lt hA) (Int.le_of_lt hA) a0 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · have := Int.mul_nonneg a0 a0
    simp only [pI] at h2
    omega_using [h0, h2, this]
  · simp only [pI, Sq] at h2 hp ⊢
    omega_using [h1, h2, hp]
  · have e : D (vI E k (Id.run (sqrCore tops a))) = D (vI E k a) * D (vI E k a) := by
      rw [← pN_eq] at h2
      exact dec_mont unitR h2
    rw [e, h.d]

/-- `Q`'s entry: `x`, `y` (twice the triple's) and `zz`, the square of its `Z`, a half. -/
structure DP (F : Type) where
  x : F
  y : F
  zz : F

namespace DP
variable {F : Type} [Lean.Grind.CommRing F] (p : DP F)

abbrev XX : F := p.x * p.x
abbrev YY : F := p.y * p.y
abbrev ZZ : F := p.zz * p.zz
abbrev M : F := 6 * (p.XX - p.ZZ)
abbrev S : F := p.x * p.YY
abbrev YY2 : F := p.YY * p.YY
abbrev MM : F := p.M * p.M
abbrev w : F := 12 * p.S - p.MM
abbrev XT : F := p.MM - 8 * p.S
abbrev YT : F := p.M * p.w - 4 * p.YY2
/-- `2 Q` and `Q` with one `Z`. -/
abbrev out : ZP F := ⟨p.XT, p.YT, 4 * p.S, 4 * p.YY2, p.y⟩

end DP

/-- `d_ring`, for the doubling's field elements. -/
macro "u_ring" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [dec_add, dec_sub, D_lit, D_pI, D_zero, DP.XX, DP.YY, DP.ZZ, DP.M, DP.S, DP.YY2, DP.MM, DP.w,
    DP.XT, DP.YT, $hs,*] <;> grind))

theorem dblu2g_v0 (sq ta : F5 T) (E : Env) : vI E 0 (Id.run (dblu2g tops sq ta)) = vI E 1 ta + 80 * pI := by
  glue_simp [dblu2g]
  omega_using []

theorem dblu2g_v1 (sq ta : F5 T) (E : Env) : vI E 1 (Id.run (dblu2g tops sq ta)) = vI E 3 sq + 80 * pI := by
  glue_simp [dblu2g]
  omega_using []

theorem dblu2g_v2 (sq ta : F5 T) (E : Env) :
    vI E 2 (Id.run (dblu2g tops sq ta)) = 6 * (vI E 1 sq - vI E 0 sq) + 80 * pI := by
  glue_simp [dblu2g]
  omega_using []

theorem dblu2g_v3 (sq ta : F5 T) (E : Env) : vI E 3 (Id.run (dblu2g tops sq ta)) = vI E 3 sq + 96 * pI := by
  glue_simp [dblu2g]
  omega_using []

theorem dblu4g_v0 (q2 : F5 T) (E : Env) :
    vI E 0 (Id.run (dblu4g tops q2)) = 12 * vI E 0 q2 - vI E 2 q2 + 80 * pI := by
  glue_simp [dblu4g]
  omega_using []

theorem dblu4g_v1 (q2 : F5 T) (E : Env) : vI E 1 (Id.run (dblu4g tops q2)) = 4 * vI E 0 q2 + 80 * pI := by
  glue_simp [dblu4g]
  omega_using []

theorem dblu5r_v0 (q3 q2 : F5 T) (E : Env) :
    vI E 0 (Id.run (dblu5r tops q3 q2)) = vI E 2 q2 - 8 * vI E 0 q2 + 80 * pI := by
  glue_simp [dblu5r]
  omega_using []

theorem dblu5r_v1 (q3 q2 : F5 T) (E : Env) :
    vI E 1 (Id.run (dblu5r tops q3 q2)) = vI E 0 q3 - 4 * vI E 1 q2 + 80 * pI := by
  glue_simp [dblu5r]
  omega_using []

theorem dblu5r_v2 (q3 q2 : F5 T) (E : Env) : vI E 2 (Id.run (dblu5r tops q3 q2)) = 4 * vI E 1 q2 + 80 * pI := by
  glue_simp [dblu5r]
  omega_using []

/-- After the first stage: `sq = [zz², XX, _, YY]`. -/
structure UCut1 (E : Env) (sq ta : F5 T) (p : DP (Fin pN)) : Prop where
  zz : Val Sq E 0 sq p.ZZ
  xx : Val Sq E 1 sq p.XX
  yy : Val Sq E 3 sq p.YY
  x : Ent E 1 ta p.x
  y : Ent E 3 ta p.y

/-- After the second: `n1 = [x, YY, M, YY]`, carried. -/
structure UCut2 (E : Env) (n1 ta : F5 T) (p : DP (Fin pN)) : Prop where
  x : Car E 0 n1 p.x
  yy : Car E 1 n1 p.YY
  m : Car E 2 n1 p.M
  y : Ent E 3 ta p.y

/-- After the third: `q2 = [S, YY², M², _]`. -/
structure UCut3 (E : Env) (q2 n1 ta : F5 T) (p : DP (Fin pN)) : Prop where
  s : Raw E 0 q2 p.S
  yy2 : Raw E 1 q2 p.YY2
  mm : Raw E 2 q2 p.MM
  m : Car E 2 n1 p.M
  y : Ent E 3 ta p.y

/-- After the fourth: `n2 = [12 S - M², 4 S, _, _]`, carried. -/
structure UCut4 (E : Env) (n2 q2 n1 ta : F5 T) (p : DP (Fin pN)) : Prop where
  w : Car E 0 n2 p.w
  s4 : Car E 1 n2 (4 * p.S)
  s : Raw E 0 q2 p.S
  yy2 : Raw E 1 q2 p.YY2
  mm : Raw E 2 q2 p.MM
  m : Car E 2 n1 p.M
  y : Ent E 3 ta p.y

/-- The places of stage `j`'s results, as terms. -/
abbrev uL (j : Nat) : List (F5 T) := leaves (dbluLocs.getD j [])

theorem dblu_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf regs10 entBT)) {p : DP (Fin pN)}
    (hzz : Ent (envOf s₀) 0 (t5 0) p.zz) (hx : Ent (envOf s₀) 1 (t5 0) p.x) (hy : Ent (envOf s₀) 3 (t5 0) p.y) :
    WP isa (.block (dbluPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dbluLocs.getD 0 []) dbluBT0) ∧
        UCut1 (envOf s) ((uL 0).getD 0 zero5) ((uL 0).getD 1 zero5) p := by
  refine WP.mono (cut_step' dblu_chk0 hc hB dblu_iv0 dblu_ov0 (rs := [Id.run (sqrCore tops (t5 0)), t5 0, t5 5])
    rfl rfl (by decide) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Val.sqrE hzz), hS.raw 0 1 (by decide) rfl rfl (Val.sqrE hx),
    hS.raw 0 3 (by decide) rfl rfl (Val.sqrE hy), hS.car 1 1 (by decide) rfl rfl hx,
    hS.car 1 3 (by decide) rfl rfl hy⟩

theorem dblu_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dbluLocs.getD 0 []) dbluBT0))
    {p : DP (Fin pN)} (h : UCut1 (envOf s₀) ((uL 0).getD 0 zero5) ((uL 0).getD 1 zero5) p) :
    WP isa (.block (dbluPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dbluLocs.getD 1 []) dbluBT1) ∧
        UCut2 (envOf s) ((uL 1).getD 0 zero5) ((uL 1).getD 1 zero5) p := by
  have hchk := dblu_chk1; have hiv := dblu_iv1
  have hL := list3 (uL 0) zero5 (by decide +kernel)
  simp only [uL] at h hL
  generalize leaves (dbluLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = sq, L.getD 1 zero5 = ta, L.getD 2 zero5 = tb at h hL
  subst hL
  obtain ⟨zz, xx, yy, x, y⟩ := h
  have v0 := dblu2g_v0 sq ta (envOf s₀)
  have v1 := dblu2g_v1 sq ta (envOf s₀)
  have v2 := dblu2g_v2 sq ta (envOf s₀)
  have v3 := dblu2g_v3 sq ta (envOf s₀)
  have zzl := zz.lo; have zzh := zz.hi; have xxl := xx.lo; have xxh := xx.hi; have yyl := yy.lo; have yyh := yy.hi
  have xl := x.lo; have xh := x.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu2g tops sq ta)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu2g tops sq ta)))).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu2g tops sq ta)))).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu2g tops sq ta)))).l4) rfl 3 (by decide)
    (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.x := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; u_ring [x.d])
  have c1 : Car (envOf s₀) 1 _ p.YY := Car.norm hB _ (by decide) hi1 (by rw [v1]; simp only [Sq] at *; rng)
    (by rw [v1]; simp only [Sq] at *; rng) (by rw [v1]; u_ring [yy.d])
  have c2 : Car (envOf s₀) 2 _ p.M := Car.norm hB _ (by decide) hi2 (by rw [v2]; simp only [Sq] at *; rng)
    (by rw [v2]; simp only [Sq] at *; rng) (by rw [v2]; u_ring [xx.d, zz.d])
  have c3 : Car (envOf s₀) 3 _ p.YY := Car.norm hB _ (by decide) hi3 (by rw [v3]; simp only [Sq] at *; rng)
    (by rw [v3]; simp only [Sq] at *; rng) (by rw [v3]; u_ring [yy.d])
  refine WP.mono (cut_step' hchk hc hB hiv dblu_ov1 (rs := [Id.run (norm tops (Id.run (dblu2g tops sq ta))), ta, tb])
    rfl rfl (Nat.le_of_eq rfl) ?_) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [dbluOv1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 1 3 (by decide) rfl rfl y⟩

theorem dblu_s2 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dbluLocs.getD 1 []) dbluBT1))
    {p : DP (Fin pN)} (h : UCut2 (envOf s₀) ((uL 1).getD 0 zero5) ((uL 1).getD 1 zero5) p) :
    WP isa (.block (dbluPieces.getD 2 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dbluLocs.getD 2 []) dbluBT2) ∧
        UCut3 (envOf s) ((uL 2).getD 0 zero5) ((uL 2).getD 1 zero5) ((uL 2).getD 2 zero5) p := by
  have hchk := dblu_chk2; have hiv := dblu_iv2
  have hL := list3 (uL 1) zero5 (by decide +kernel)
  simp only [uL] at h hL
  generalize leaves (dbluLocs.getD 1 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = n1, L.getD 1 zero5 = ta, L.getD 2 zero5 = tb at h hL
  subst hL
  obtain ⟨x, yy, m, y⟩ := h
  refine WP.mono (cut_step' hchk hc hB hiv dblu_ov2
    (rs := [Id.run (mulCore tops n1 (Id.run (fperm tops n1 1 1 2 1))), n1, ta, tb]) rfl rfl (Nat.le_of_eq rfl)
    (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.mul x (Lim.perm 1 1 2 1 (by decide) yy)),
    hS.raw 0 1 (by decide) rfl rfl (Raw.mul yy (Lim.perm 1 1 2 1 (by decide) yy)),
    hS.raw 0 2 (by decide) rfl rfl (Raw.mul m (Lim.perm 1 1 2 1 (by decide) m)),
    hS.car 1 2 (by decide) rfl rfl m, hS.car 2 3 (by decide) rfl rfl y⟩

theorem dblu_s3 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dbluLocs.getD 2 []) dbluBT2))
    {p : DP (Fin pN)}
    (h : UCut3 (envOf s₀) ((uL 2).getD 0 zero5) ((uL 2).getD 1 zero5) ((uL 2).getD 2 zero5) p) :
    WP isa (.block (dbluPieces.getD 3 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dbluLocs.getD 3 []) dbluBT3) ∧
        UCut4 (envOf s) ((uL 3).getD 0 zero5) ((uL 3).getD 1 zero5) ((uL 3).getD 2 zero5) ((uL 3).getD 3 zero5) p := by
  have hchk := dblu_chk3; have hiv := dblu_iv3
  have hL := list4 (uL 2) zero5 (by decide +kernel)
  simp only [uL] at h hL
  generalize leaves (dbluLocs.getD 2 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q2, L.getD 1 zero5 = n1, L.getD 2 zero5 = ta, L.getD 3 zero5 = tb at h hL
  subst hL
  obtain ⟨s', yy2, mm, m, y⟩ := h
  have v0 := dblu4g_v0 q2 (envOf s₀)
  have v1 := dblu4g_v1 q2 (envOf s₀)
  have sl := s'.lo; have sh := s'.hi; have ml := mm.lo; have mh := mm.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu4g tops q2)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dblu4g tops q2)))).l4) rfl 1 (by decide)
    (b := _) rfl
  have c0 : Car (envOf s₀) 0 _ p.w := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; u_ring [s'.d, mm.d])
  have c1 : Car (envOf s₀) 1 _ (4 * p.S) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; u_ring [s'.d])
  refine WP.mono (cut_step' hchk hc hB hiv dblu_ov3
    (rs := [Id.run (norm tops (Id.run (dblu4g tops q2))), q2, n1, ta, tb]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [dbluOv3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.raw 1 0 (by decide) rfl rfl s',
      hS.raw 1 1 (by decide) rfl rfl yy2, hS.raw 1 2 (by decide) rfl rfl mm, hS.car 2 2 (by decide) rfl rfl m,
      hS.car 3 3 (by decide) rfl rfl y⟩

/-- `M (4 S - X₃)` in the first lane. -/
abbrev uq3 (n1 n2 : F5 T) : F5 T := Id.run (mulCore tops (Id.run (fperm tops n1 2 2 2 2)) n2)

theorem dblu_s4 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dbluLocs.getD 3 []) dbluBT3))
    {p : DP (Fin pN)}
    (h : UCut4 (envOf s₀) ((uL 3).getD 0 zero5) ((uL 3).getD 1 zero5) ((uL 3).getD 2 zero5) ((uL 3).getD 3 zero5) p) :
    WP isa (.block (dbluPieces.getD 4 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs20 tabBT) ∧ ChainOk (envOf s) (t5 10) (t5 15) p.out := by
  have hchk := dblu_chk4; have hiv := dblu_iv4
  have hL := list5 (uL 3) zero5 (by decide +kernel)
  simp only [uL] at h hL
  generalize leaves (dbluLocs.getD 3 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = n2, L.getD 1 zero5 = q2, L.getD 2 zero5 = n1, L.getD 3 zero5 = ta,
    L.getD 4 zero5 = tb at h hL
  subst hL
  obtain ⟨w, s4, s', yy2, mm, m, y⟩ := h
  have q0 : Raw (envOf s₀) 0 (uq3 n1 n2) (p.M * p.w) := Raw.mul (Lim.perm 2 2 2 2 (by decide) m) w
  have r0 := dblu5r_v0 (uq3 n1 n2) q2 (envOf s₀)
  have r1 := dblu5r_v1 (uq3 n1 n2) q2 (envOf s₀)
  have r2 := dblu5r_v2 (uq3 n1 n2) q2 (envOf s₀)
  have sl := s'.lo; have sh := s'.hi; have ml := mm.lo; have mh := mm.hi; have yl := yy2.lo; have yh := yy2.hi
  have ql := q0.lo; have qh := q0.hi
  have k0 : Chn (envOf s₀) 0 (Id.run (dblu5r tops (uq3 n1 n2) q2)) p.XT :=
    ⟨by rw [r0]; rng, by rw [r0]; rng, by rw [r0]; u_ring [mm.d, s'.d]⟩
  have k1 : Chn (envOf s₀) 1 (Id.run (dblu5r tops (uq3 n1 n2) q2)) p.YT :=
    ⟨by rw [r1]; rng, by rw [r1]; rng, by rw [r1]; u_ring [q0.d, yy2.d]⟩
  have k2 : Chn (envOf s₀) 2 (Id.run (dblu5r tops (uq3 n1 n2) q2)) (4 * p.YY2) :=
    ⟨by rw [r2]; rng, by rw [r2]; rng, by rw [r2]; u_ring [yy2.d]⟩
  have cz : Ent (envOf s₀) 2 (Id.run (fblend tops (Id.run (fperm tops ta 3 3 3 3)) (Id.run (fperm tops n2 1 1 1 1)) 8))
      p.y := Lim.blendL (by decide) (by decide) (Lim.perm 3 3 3 3 (by decide) y)
  have cx : Car (envOf s₀) 3 (Id.run (fblend tops (Id.run (fperm tops ta 3 3 3 3)) (Id.run (fperm tops n2 1 1 1 1)) 8))
      (4 * p.S) := Lim.blendR (by decide) (by decide) (Lim.perm 1 1 1 1 (by decide) s4)
  refine WP.mono (cut_step' hchk hc hB hiv dblu_ov4
    (rs := [ta, tb, Id.run (dblu5r tops (uq3 n1 n2) q2),
      Id.run (fblend tops (Id.run (fperm tops ta 3 3 3 3)) (Id.run (fperm tops n2 1 1 1 1)) 8)]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.chn 2 0 (by decide) rfl rfl k0, hS.chn 2 1 (by decide) rfl rfl k1, hS.chn 2 2 (by decide) rfl rfl k2,
    hS.car 3 2 (by decide) rfl rfl cz, hS.car 3 3 (by decide) rfl rfl cx⟩

theorem dbluPieces_flat : dbluPieces.flatten = dbluPieces.getD 0 [] ++ (dbluPieces.getD 1 [] ++
    (dbluPieces.getD 2 [] ++ (dbluPieces.getD 3 [] ++ dbluPieces.getD 4 []))) := by
  decide +kernel

/-- `2 Q` and `Q` with one `Z`, from `Q`'s entry in `ymm0`–`ymm4`. -/
theorem dblu_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf regs10 entBT)) {p : DP (Fin pN)}
    (hzz : Ent (envOf s₀) 0 (t5 0) p.zz) (hx : Ent (envOf s₀) 1 (t5 0) p.x) (hy : Ent (envOf s₀) 3 (t5 0) p.y) :
    WP isa (.block dbluPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs20 tabBT) ∧ ChainOk (envOf s) (t5 10) (t5 15) p.out := by
  rw [dbluPieces_flat, WP.block_append_iff]
  refine WP.mono (dblu_s0 hc hB hzz hx hy) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblu_s1 c₁ b₁ h₁) fun s₂ ⟨c₂, k₂, b₂, h₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblu_s2 c₂ b₂ h₂) fun s₃ ⟨c₃, k₃, b₃, h₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblu_s3 c₃ b₃ h₃) fun s₄ ⟨c₄, k₄, b₄, h₄⟩ => ?_
  exact WP.mono (dblu_s4 c₄ b₄ h₄) fun s ⟨c, k, b, h⟩ => ⟨c, (((k₁.trans k₂).trans k₃).trans k₄).trans k, b, h⟩

/-! ### `Q`'s entry -/

theorem tabGPieces_flat : tabGPieces.flatten = tabGPieces.getD 0 [] := by decide +kernel

/-- `tabG`'s first vector. -/
abbrev tabGA : F5 T :=
  Id.run (fblend tops (Id.run (convGg tops (.ld .rcx 0) (.ld .rdx 0))) (Id.run (fconst tops cQuarter 0 cHalf 0)) 5)

/-- The entry of the affine point whose words are at `rcx` (`x`) and at `rdx` (`y`): in `ymm0`–`ymm4`
a quarter, four times `x`, a half and four times `y`, and in `ymm5`–`ymm9` an eighth. -/
theorem tabG_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) :
    WP isa (.block tabGPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf regs10 entBT) ∧
        Ent (envOf s) 0 (t5 0) (D (cQuarter : Nat)) ∧
        Ent (envOf s) 1 (t5 0) (D (4 * wv (envOf s₀) (.ld .rcx 0))) ∧
        Ent (envOf s) 2 (t5 0) (D (cHalf : Nat)) ∧
        Ent (envOf s) 3 (t5 0) (D (4 * wv (envOf s₀) (.ld .rdx 0))) ∧
        Ent (envOf s) 0 (t5 5) (D (cEighth : Nat)) := by
  have wx := words_ld hB .rcx rfl 0
  have wy := words_ld hB .rdx rfl 0
  obtain ⟨⟨xc, xv⟩, yc, yv⟩ := convGg_val (.ld .rcx 0) (.ld .rdx 0) (envOf s₀) wx wy
  have xl := wx.lo; have xh := wx.hi; have yl := wy.lo; have yh := wy.hi
  have p0 (a b c d : Nat) : pick4 a b c d 0 = a := rfl
  have p2 (a b c d : Nat) : pick4 a b c d 2 = c := rfl
  have k0 := fconst_car cQuarter 0 cHalf 0 (envOf s₀) (k := 0) (by decide) (by rw [p0]; decide +kernel)
  have k2 := fconst_car cQuarter 0 cHalf 0 (envOf s₀) (k := 2) (by decide) (by rw [p2]; decide +kernel)
  have k8 := fconst_car cEighth 0 0 0 (envOf s₀) (k := 0) (by decide) (by rw [p0]; decide +kernel)
  rw [p0] at k0 k8
  rw [p2] at k2
  have nb : Nb ≤ 2 ^ 259 := by simp only [Nb]; omega_using []
  have a0 : Ent (envOf s₀) 0 tabGA (D (cQuarter : Nat)) := Lim.blendR (by decide) (by decide) (k0.mono nb)
  have a1 : Ent (envOf s₀) 1 tabGA (D (4 * wv (envOf s₀) (.ld .rcx 0))) :=
    Lim.blendL (by decide) (by decide) ⟨xc, by rw [xv]; omega_using [xh], by rw [xv]⟩
  have a2 : Ent (envOf s₀) 2 tabGA (D (cHalf : Nat)) := Lim.blendR (by decide) (by decide) (k2.mono nb)
  have a3 : Ent (envOf s₀) 3 tabGA (D (4 * wv (envOf s₀) (.ld .rdx 0))) :=
    Lim.blendL (by decide) (by decide) ⟨yc, by rw [yv]; omega_using [yh], by rw [yv]⟩
  have b0 : Ent (envOf s₀) 0 (Id.run (fconst tops cEighth 0 0 0)) (D (cEighth : Nat)) := k8.mono nb
  rw [tabGPieces_flat]
  refine WP.mono (cut_step' tabG_chk0 hc hB tabG_iv0 tabG_ov0
    (rs := [tabGA, Id.run (fconst tops cEighth 0 0 0)]) rfl rfl (Nat.le_of_eq rfl)
    (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.car 0 0 (by decide) rfl rfl a0, hS.car 0 1 (by decide) rfl rfl a1, hS.car 0 2 (by decide) rfl rfl a2,
    hS.car 0 3 (by decide) rfl rfl a3, hS.car 1 0 (by decide) rfl rfl b0⟩

end VG.Proof.P256.X86_64.Ifma
