module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw

import VerifiedGarbage.Proof.Rsa.Arm.InverseCT
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the GCD and the products

`gcd_vp`: after the halvings, `gcd(u, x / 2^k)` by `inverse` (`1` where
`u = 1`), for an odd `u`. `product_vp`: `[a] := [y] [x]` modulo `2^(32 W)` by
the `32 w` bits of the narrow `[y]`, whose step is any `g` with the
product's formula (Appendix C.2's model calls it `prodStep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Inv (Gk nk)
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

section
variable {P : RP}

/-! ## The GCD -/

/-- `gcd(u, x / 2^k)`, as the code computes it. -/
abbrev gV (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  if (ts P f σ (32 * P.w)).1 = 1 then 1 else Nat.gcd (ts P f σ (32 * P.w)).2.1 (ts P f σ (32 * P.w)).1

def AG (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n) aG (gV P f σ)
def AWG (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX3 (ts P f σ (32 * P.w)).2.2
def VG' (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sOkDE (b2n (okDEv P σ))

abbrev LG : List Nat := [aG, aN, aZN, aOneN]

/-- After the GCD. -/
abbrev GS (P : RP) (E : State → Prop) (f : Nat × Nat × Nat → Nat × Nat × Nat) : State → State → Prop :=
  Dk P E (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] P.w nArr

theorem invArrs_eq : invArrs = [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14] := rfl

theorem gcd_vp [InvLaw] {f : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop}
    (hodd : ∀ σ, E σ → (ts P f σ (32 * P.w)).1 % 2 = 1) :
    VP (fun σ s => E σ ∧ TI P f σ (32 * P.w) s) gcd (GS P E f) := by
  simp only [gcd, seqs]
  -- `[0] := x / 2^k`.
  let AC := fun σ => upd (AT P f σ (32 * P.w)) aGx (AT P f σ (32 * P.w) aX2)
  refine VP.seq (G := Dk P E AC (aGx :: LT) (fun σ => AWT P f σ (32 * P.w)) LWT (fun σ => VT P σ (32 * P.w)) LST
    P.w nArr) (VP.dctx gcdCopy_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
      WP.mono (h.copy_w hw (o := aGx) (a := aX2) (by decide) (by decide) (by decide) (by decide))
        fun t ⟨ht, hwt, _, _⟩ => ⟨e, ht, hwt⟩) ?_
  -- `inverse`: `[1] = gcd(x / 2^k, u)` where `u > 1`.
  let GI := fun σ s => Dk P E (fun σ => AT P f σ (32 * P.w)) [aU, aN, aZN, aOneN] (fun σ => AWT P f σ (32 * P.w))
    LWT (fun σ => VT P σ (32 * P.w)) LST P.w nArr σ s ∧
    (1 < (ts P f σ (32 * P.w)).1 → num s.mem P.B P.w aG1 =
      Nat.gcd (ts P f σ (32 * P.w)).2.1 (ts P f σ (32 * P.w)).1)
  refine VP.seq (G := GI) (VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨inverse_ct s t tr1 tr2 u v trivial trivial
      ⟨by rw [h.1.2.2.r7, h.2.2.2.r7], by rw [h.1.2.2.r8, h.2.2.2.r8], by rw [h.1.2.2.r9, h.2.2.2.r9]⟩ e1 e2,
      trivial⟩) fun σ s ⟨e, h, hw⟩ => ?_) ?_
  · have sz := h.sizes
    have g : Gk s P.B P.Z P.w P.w nArr := ⟨hw.nowrap, hw.writable, hw.fits, hw.wpos, le_refl _, hw.wle, hw.r7,
      hw.r8, hw.r9⟩
    refine WP.mono (InvLaw.inverseK_ok g (by decide) (by decide)) fun t ⟨gt, k, r, v⟩ => ⟨⟨e, ?_, ?_⟩, ?_⟩
    · have fitI : ∀ j ∈ invArrs, arr P.w j + S P.w ≤ P.Z := fun j hj => fitZ_w sz (by
        rw [invArrs_eq] at hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      refine h.core k fitI (by decide) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (fun j hj => ?_)
        (by decide) (h.arrsW_w k (by rw [invArrs_eq]; decide) (by decide)) h.liveW_lt
        (h.sl_keep k (by decide)) h.ls_ok
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;>
        (rw [k.num (by rw [invArrs_eq]; decide) (by decide) (fit_w sz (by decide))]
         rw [h.arrs _ (by decide)]
         simp only [AC]; rd_ev)
    · exact hw.of (gt.r7.trans hw.r7.symm) (gt.r8.trans hw.r8.symm) (gt.r9.trans hw.r9.symm) r.wr
    · intro hu
      have o := hodd σ e
      have v0 : nk s.mem P.B P.w 0 P.w = (ts P f σ (32 * P.w)).2.1 := by
        have := h.arrs aGx (by decide); simp only [AC, upd_self] at this
        change num s.mem P.B P.w aGx = _; rw [this]
        simp only [AT]; rd_ev
      have vM : nk s.mem P.B P.w aM P.w = (ts P f σ (32 * P.w)).1 := by
        have := h.arrs aU (by decide); change num s.mem P.B P.w aU = _; rw [this]; simp only [AC, AT]; rd_ev
      rw [vM, v0] at v
      change nk t.mem P.B P.w 1 P.w = _
      rw [(v o hu).1, Nat.gcd_comm]
  -- `u = 1`, and the GCD into `aG`.
  refine VP.dctx gcdPost_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, hg⟩ => ?_
  have h1 := h.addLive (j := aG1) (by decide)
  simp only [gcdPost]
  refine WP.seq (WP.mono (h1.eqS_w hw (d := sU1) (a := aU) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s1 ⟨h2, hw2, _⟩ => ?_)
  refine WP.mono (h2.sel_w hw2 (o := aG) (a := aG1) (b := aOneN) (sl := sU1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rd_up; split <;> omega) (by decide)) fun t ⟨ht, hwt, _⟩ => ⟨e, ?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ⟨hj, by simp only [AWG, AWT]⟩) (fun d hd => ?_)
  · simp only [LG, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [upd_self]; rd_up
      simp only [AT, AG, gV]; rd_ev
      by_cases u1 : (ts P f σ (32 * P.w)).1 = 1
      · simp [u1]
      · have o := hodd σ e
        simp only [u1, ↓reduceIte]
        exact hg (by omega)
    all_goals refine ⟨by decide, ?_⟩; simp only [AG, AT]; rd_ev
  · simp only [List.mem_singleton] at hd; subst hd
    exact ⟨by decide, by simp only [VG', VT]; rd_ev⟩

/-! ## Products -/

theorem upd_upd (A : Nat → Nat) (j v v' : Nat) : upd (upd A j v) j v' = upd A j v' := by
  funext i; by_cases e : i = j
  · subst e; rw [upd_self, upd_self]
  · rw [upd_ne _ _ e, upd_ne _ _ e, upd_ne _ _ e]

theorem upd_comm (A : Nat → Nat) {i j : Nat} (v v' : Nat) (h : i ≠ j) :
    upd (upd A i v) j v' = upd (upd A j v') i v := by
  funext k; by_cases e : k = i
  · subst e; rw [upd_ne _ _ h, upd_self, upd_self]
  · by_cases e' : k = j
    · subst e'; rw [upd_self, upd_ne _ _ e, upd_self]
    · rw [upd_ne _ _ e', upd_ne _ _ e, upd_ne _ _ e, upd_ne _ _ e']

/-- The step of the products. -/
abbrev ProdF (P : RP) (g : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ y x a, g (y, x, a) = (y / 2, 2 * x % 2 ^ (32 * P.W), (a + if y % 2 = 0 then 0 else x) % 2 ^ (32 * P.W))

/-- What a product needs of its arrays: the multiplier `y` (narrow), the multiplicand `x`, the
product `a`, the temporaries `t` and `t2` and zero `z` (wide), and the other arrays and header words. -/
structure PCfg (y x a t t2 z : Nat) (L LW LS : List Nat) : Prop where
  hy : y ∈ L
  hx : x ∈ LW
  hz : z ∈ LW
  ha22 : a < 22
  ht22 : t < 22
  ht222 : t2 < 22
  htLW : t ∉ LW
  ht2LW : t2 ∉ LW
  haLW : a ∉ LW
  htz : t ≠ z
  htx : t ≠ x
  ht2a : t2 ≠ a
  ht2t : t2 ≠ t
  ht2z : t2 ≠ z
  hta : t ≠ a
  hax : a ≠ x
  haz : a ≠ z
  hzx : z ≠ x
  hL : ∀ j ∈ L, j / 2 ≠ t ∧ j / 2 ≠ t2 ∧ j / 2 ≠ a ∧ j / 2 ≠ x
  hyW : y / 2 ≠ x ∧ y / 2 ≠ a ∧ y / 2 ≠ t ∧ y / 2 ≠ t2 ∧ ∀ i ∈ LW, y / 2 ≠ i
  hsK : sK ∉ LS
  hsY : sY ∉ LS

theorem productStep_ok {y x a t t2 z : Nat} {L LW LS : List Nat} (c : PCfg y x a t t2 z L LW LS)
    {σ s : State} {A AW V : Nat → Nat}
    (h : KS P σ A L AW (a :: LW) V (sK :: LS) s) (hv : Ws s P.B P.Z P.w nArr) (z0 : AW z = 0)
    (k1 : 1 ≤ V sK) (k2 : V sK < 2 ^ 32) :
    WP isa (productStep y x a t t2 z) s fun u =>
      KS P σ (upd A y (A y / 2)) L
        (upd (upd AW x (2 * AW x % 2 ^ (32 * P.W))) a ((AW a + if A y % 2 = 0 then 0 else AW x) % 2 ^ (32 * P.W)))
        (a :: LW) (upd V sK (V sK - 1)) (sK :: LS) u ∧
      Ws u P.B P.Z P.w nArr ∧ u.z = decide (V sK - 1 = 0) := by
  have sz := h.sizes
  have hxa : x ∈ a :: LW := List.mem_cons_of_mem _ c.hx
  have hza : z ∈ a :: LW := List.mem_cons_of_mem _ c.hz
  have tW : ∀ i ∈ a :: LW, i ≠ t := by
    intro i hi; rcases List.mem_cons.mp hi with rfl | hi
    · exact Ne.symm c.hta
    · exact fun e => c.htLW (e ▸ hi)
  have t2W : ∀ i ∈ a :: LW, i ≠ t2 := by
    intro i hi; rcases List.mem_cons.mp hi with rfl | hi
    · exact Ne.symm c.ht2a
    · exact fun e => c.ht2LW (e ▸ hi)
  simp only [productStep, seqs]
  refine WP.seq ?_
  refine h.bitOf_w hv (j := y) (sl := sY) c.hy (by decide) fun s1 h1 hv1 _ => ?_
  refine h1.toW hv1 fun s2 h2 hv2 _ => WP.block_nil ?_
  refine WP.seq (WP.mono (h2.sel_W hv2 (o := t) (a := z) (b := x) (sl := sY) c.ht22 hza hxa c.htz c.htx
    (List.mem_cons_self ..) (by rw [upd_self]; omega) fun j hj => (c.hL j hj).1)
    fun s3 ⟨h3, hv3, _⟩ => ?_)
  rw [upd_self] at h3
  have z1 : upd AW t (if A y % 2 = 0 then AW z else AW x) z = 0 := by rw [upd_ne _ _ (Ne.symm c.htz), z0]
  refine WP.seq (WP.mono (h3.add_W hv3 (o := t) (a := a) (b := t) (t := t2) (z := z) c.ht22 c.ht222
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (List.mem_cons_self ..) (List.mem_cons_of_mem _ hza) z1
    c.ht2a c.ht2t c.ht2z c.hta (Ne.symm c.ht2t) fun j hj => ⟨(c.hL j hj).1, (c.hL j hj).2.1⟩)
    fun s4 ⟨h4, hv4⟩ => ?_)
  refine WP.seq (WP.mono (h4.copy_W hv4 (o := a) (a := t) c.ha22 (List.mem_cons_self ..) (Ne.symm c.hta)
    fun j hj => (c.hL j hj).2.2.1) fun s5 ⟨h5, hv5, _⟩ => ?_)
  refine WP.seq (h5.clr11 hv5 fun s6 h6 hv6 z6 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h6.shl_W hv6 (j := x) (by simp [hxa]) (by omega) fun j hj => (c.hL j hj).2.2.2)
    fun s7 ⟨h7, hv7, _, _⟩ => ?_)
  rw [z6] at h7
  refine WP.seq (h7.toN hv7 fun s8 h8 hv8 _ => ?_)
  refine h8.clr11 hv8 fun s9 h9 hv9 z9 => WP.block_nil ?_
  refine WP.seq (WP.mono (h9.half_w hv9 (j := y) c.hy z9 fun i hi => ?_)
    fun s10 ⟨h10, hv10, _⟩ => ?_)
  · obtain ⟨y1, y2, y3, y4, y5⟩ := c.hyW
    simp only [List.mem_cons] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | hi
    · exact y1
    · exact y2
    · exact y3
    · exact y4
    · exact y3
    · rcases hi with rfl | hi
      · exact y2
      · exact y5 i hi
  refine WP.mono (h10.cntNext hv10 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (by rw [upd_ne _ _ (by decide)]; exact k1) (by rw [upd_ne _ _ (by decide)]; exact k2))
    fun u ⟨hu, hvu, zu⟩ => ⟨?_, hvu, by rw [zu, upd_ne _ _ (by decide)]⟩
  rw [upd_ne _ _ (show sK ≠ sY by decide)] at hu
  have hax := c.hax
  refine hu.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun j hj => ⟨List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)))), ?_⟩)
    (fun d hd => ?_)
  · simp only [upd]
  · have jt := tW j hj; have jt2 := t2W j hj
    simp only [upd]
    by_cases ex : j = x
    · subst ex; simp [Ne.symm hax, jt, jt2]
    · by_cases ea : j = a
      · subst ea; simp [ex, jt, z0]
      · simp [ex, ea, jt, jt2]
  · rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨List.mem_cons_self .., by rw [upd_self, upd_self]⟩
    · have dK : d ≠ sK := fun e => c.hsK (e ▸ hd)
      have dY : d ≠ sY := fun e => c.hsY (e ▸ hd)
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)), by
        rw [upd_ne _ _ dK, upd_ne _ _ dK, upd_ne _ _ dY]⟩

/-- `(y, x, a)` after `k` steps of a product. -/
abbrev pr (g : Nat × Nat × Nat → Nat × Nat × Nat) (y x : Nat) (k : Nat) : Nat × Nat × Nat := g^[k] (y, x, 0)

/-- After `k` steps of the product of `y` and `x` into `a`. -/
def PI (P : RP) (g : Nat × Nat × Nat → Nat × Nat × Nat) (y x a : Nat) (A : State → Nat → Nat) (L : List Nat)
    (AW : State → Nat → Nat) (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (k : Nat) (σ s : State) :
    Prop :=
  KS P σ (upd (A σ) y (pr g (A σ y) (AW σ x) k).1) L
    (upd (upd (AW σ) x (pr g (A σ y) (AW σ x) k).2.1) a (pr g (A σ y) (AW σ x) k).2.2) (a :: LW)
    (upd (V σ) sK (32 * P.w - k)) (sK :: LS) s ∧ Ws s P.B P.Z P.w nArr

theorem product_vp {y x a t t2 z : Nat} {L LW LS : List Nat} (c : PCfg y x a t t2 z L LW LS)
    {g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {E : State → Prop}
    {A AW V : State → Nat → Nat} (z0 : ∀ σ, E σ → AW σ z = 0)
    (cert0 : DCert (productPre a z)) (cert : DCert (productStep y x a t t2 z)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (product y x a t t2 z)
      (fun σ s => E σ ∧ PI P g y x a A L AW LW V LS (32 * P.w) σ s) := by
  have hxa := c.hax
  have hza := c.haz
  refine VP.seq (G := fun σ s => E σ ∧ PI P g y x a A L AW LW V LS 0 σ s) (VP.dctx cert0 (fun _ _ h => h.2.2)
    fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · have sz := h.sizes
    simp only [productPre, seqs]
    refine WP.seq (h.toW hv fun s1 h1 hv1 _ => WP.block_nil ?_)
    refine WP.seq (WP.mono (h1.copy_W hv1 (o := a) (a := z) c.ha22 c.hz c.haz fun j hj => (c.hL j hj).2.2.1)
      fun s2 ⟨h2, hv2, _⟩ => ?_)
    refine h2.toN hv2 fun s3 h3 hv3 _ => ?_
    refine h3.cntInit hv3 (e := 5) (by decide) (by have := sz.wle; omega) fun u hu hvu => WP.block_nil ⟨e, ?_, hvu⟩
    rw [z0 σ e] at hu
    refine hu.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, ?_⟩)
    · simp only [pr, Function.iterate_zero, id]; rw [upd_noop rfl]
    · simp only [pr, Function.iterate_zero, id]
      by_cases ea : j = a
      · subst ea; rw [upd_self, upd_self]
      · rw [upd_ne _ _ ea, upd_ne _ _ ea, upd_noop rfl]
    · simp only [Nat.sub_zero]
  refine VP.of_imp (p := 0 < 32 * P.w) (fun σ s ⟨_, h, _⟩ => by show 0 < 32 * (2 * P.w6 + 2); omega)
    fun pos => ?_
  refine VP.count (E := E) (I := PI P g y x a A L AW LW V LS) pos fun k hk => VP.dctx cert (fun _ _ h => h.2.2)
    fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have wl := sz.wle
  have z0' : upd (upd (AW σ) x (pr g (A σ y) (AW σ x) k).2.1) a (pr g (A σ y) (AW σ x) k).2.2 z = 0 := by
    rw [upd_ne _ _ (Ne.symm c.haz), upd_ne _ _ c.hzx, z0 σ e]
  refine WP.mono (productStep_ok c h hv z0' (by rw [upd_self]; omega) (by rw [upd_self]; omega))
    fun u ⟨hu, hvu, zu⟩ => ⟨⟨e, ?_, hvu⟩, by rw [zu, upd_self, Nat.sub_sub]⟩
  have hs : pr g (A σ y) (AW σ x) (k + 1) = g (pr g (A σ y) (AW σ x) k) := by
    simp only [pr]; rw [Function.iterate_succ_apply']
  generalize pr g (A σ y) (AW σ x) k = q at hs hu
  obtain ⟨qy, qx, qa⟩ := q
  rw [hg] at hs
  rw [hs]
  refine hu.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, ?_⟩)
  · simp only [upd]; split <;> simp
  · simp only [upd]
    by_cases ea : j = a
    · subst ea; simp [Ne.symm hxa]
    · by_cases ex : j = x
      · subst ex; simp [ea]
      · simp [ea, ex]
  · simp only [upd]; split
    · simp only [ite_true]; omega
    · rfl

end

end VG.Proof.Rsa.Arm.RecoverDet
