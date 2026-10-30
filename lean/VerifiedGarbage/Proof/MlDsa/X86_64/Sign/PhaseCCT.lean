module

import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseC
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsD
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on x86-64: the commitment leaks only the pointers

Each piece of the commitment leaks only its pointers, given that its inputs
are reduced (and the coefficients of `HighBits(w[i])` bounded): `maskR_trL`,
`rowW_trL`, `w1R_trL`; so two runs agree on what the commitment leaks
(`commit_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- A piece that keeps `I`, from runs in the layout that satisfy it. -/
theorem stepSelf {c : Prog isa} {I : State → Prop}
    (h : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c fun _ _ => True)
    (w : ∀ x, Lay D (sgR p) (sgW p) x → I x → WP isa c x fun x' => (∃ W, PostB D x x' W) ∧ I x') :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c
      fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y :=
  VG.Proof.MlKem.X86_64.RelCT.postDep h (F := fun x x' => (∃ W, PostB D x x' W) ∧ I x')
    (fun x y h => ⟨w x h.1.lx h.2.1, w y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (sgB_bases p) hx hy, jx, jy⟩

theorem lrel_rbx {x y : State} (h : LRel D (sgR p) (sgW p) x y) : ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact h.regs (.rbx, scrLen p) (by simp [sgR, sgW])

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r : Nat}
    (hr : r < 2 ^ 31) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : pa s (sc (oMS + 65)) = pa s (sc (oMS + 64)) + 1 := (pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have c0 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 64))) 1 := by
    have := contains_offset' (base := pa s (sc (oMS + 64))) (off := 0) (len := 1) (n := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact contains_offset' (off := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMS + 64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (setKap_ok (oMS + 64) r hr s (L.iR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (postB_of_keep (D := D) k (by decide)
    (W := [⟨pa s (sc (oMS + 64)), 2⟩]) ?_).1⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

theorem maskR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {r : Nat} (hc : mChk p r = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  have hcc := copyChk_spec cc
  unfold maskR
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (block_tr rfl fun x y h => lrel_rbx h.1) (fun x L _ => WP.mono (setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (seqL (J := fun s => Reduced s.mem (pa s (yP p r)))
      (RelCT.mono (maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩)
      (seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
        (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
          fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
          (fun _ _ h => h) fun _ _ h => h)
        (fun x L hy => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
        (ipAt_tr (t := ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `y` and `ŷ`, four at a time -/

theorem ms4_trL {D : Nat} {p : Params} {g k : Nat} (hc : ms4Chk p g k = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (cpM4 g k) fun _ _ => True := by
  simp only [ms4Chk, Bool.and_eq_true] at hc
  have cc := hc.1.1.1.1.1.1.1.1
  have hcc := copyChk_spec cc
  unfold cpM4
  exact RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L _ => WP.mono (copy_okB L cc) fun _ ⟨hP', _⟩ => ⟨⟨_, hP'⟩, trivial⟩)
    (block_tr rfl fun x y h => lrel_rbx h.1))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem yhR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t ry r : Nat} (hc : yhChk p ry r = true)
    (hr : r < ry) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICy p D σ t ry r x) ∧ ∃ σ, ICy p D σ t ry r y)
      (yhR P p r) fun _ _ => True := by
  simp only [yhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨cc, _⟩, ci⟩, _⟩ := hc
  have hcc := copyChk_spec cc
  unfold yhR
  exact seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
    (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L ⟨_, I⟩ => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.y r hr).1⟩)
    (ipAt_tr (t := ntt) hP.ntt ci)

theorem mask4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat} (hc : m4Chk p g = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * g) s) (mask4 P p g)
      (RS p D E fun σ s => ICm p D σ t (4 * (g + 1)) s) := by
  obtain ⟨hcp, cm, c2, hyh, hγ⟩ := m4Chk_spec hc
  unfold mask4
  refine RelCT.seq (R := RS p D E fun σ s => SD p D σ t g 4 s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICy p D σ t (4 * g + 4) (4 * g) s) ?_ ?_)
  · refine RelCT.mono (seqR_tr (R := fun k => RS p D E fun σ s => SD p D σ t g k s) 4 0 fun k _ hk =>
      liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => ms4_ok (hcp k (by omega)) h) (ms4_trL (hcp k (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => m4call_ok hP hγ cm c2 h) (mask4Call_tr hP hγ cm)
  · exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICy p D σ t (4 * g + 4) r s) 4 (4 * g)
      fun r h1 hr => liftL (T := fun s => ∃ σ, ICy p D σ t (4 * g + 4) r s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => yhR_ok hP (hyh r h1 hr) (by omega) h) (yhR_trL hP (hyh r h1 hr) (by omega)))
      (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h.l, h.y, h.yh⟩

/-! ## The last three polynomials of `y`, four at a time -/

theorem tailR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t r : Nat} (hc : tChk p r = true)
    (h1 : 4 * (p.ℓ / 4) ≤ r) (h2 : r < 4 * (p.ℓ / 4) + 3) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICT p D σ t r x) ∧ ∃ σ, ICT p D σ t r y)
      (tailR P p r) fun _ _ => True := by
  simp only [tChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, _⟩, _⟩, cc⟩, _⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩ := hc
  have hc0 := copyChk_spec c0
  have hcc := copyChk_spec cc
  unfold tailR yhR
  exact seqL (J := fun s => Reduced s.mem (pa s (yP p r)))
    (RelCT.mono (copy_tr hc0.2.2.2.1 hc0.2.2.2.2.1 hc0.2.2.2.2.2.1 hc0.2.2.2.2.2.2.1 hc0.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L ⟨_, I⟩ => WP.mono (copy_okB L c0) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, by
      rw [hP'.pa (pS_bases _)]
      have := I.tmp (r - 4 * (p.ℓ / 4)) (by omega) (by omega)
      exact reduced_congr₂ (bytes_of_bytesAt hb) this.1⟩)
    (seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
      (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
        fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
        (fun _ _ h => h) fun _ _ h => h)
      (fun x L hy => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
      (ipAt_tr (t := ntt) hP.ntt ci))

theorem maskTail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hl : p.ℓ % 4 = 3)
    (hc : tailChk p = true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) (maskTail P p)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  have hc' := hc
  simp only [tailChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨hcp, cm⟩, c2⟩, ht⟩, hγ⟩ := hc'
  have htr : ∀ r, 4 * (p.ℓ / 4) ≤ r → r < 4 * (p.ℓ / 4) + 3 → tChk p r = true := fun r h1 h2 => by
    have := ht (r - 4 * (p.ℓ / 4)) (by omega)
    rwa [show 4 * (p.ℓ / 4) + (r - 4 * (p.ℓ / 4)) = r by omega] at this
  unfold maskTail
  refine RelCT.seq (R := RS p D E fun σ s => SD p D σ t (p.ℓ / 4) 4 s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICT p D σ t (4 * (p.ℓ / 4)) s) ?_ ?_)
  · refine RelCT.mono (seqR_tr (R := fun k => RS p D E fun σ s => SD p D σ t (p.ℓ / 4) k s) 4 0 fun k _ hk =>
      liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => ms4_ok (hcp k (by omega)) h) (ms4_trL (hcp k (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => maskTailCall_ok hP hc h) (mask4Call_tr hP hγ cm)
  · exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICT p D σ t r s) 3 (4 * (p.ℓ / 4))
      fun r h1 hr => liftL (T := fun s => ∃ σ, ICT p D σ t r s) (fun σ s h => ⟨h.m.l.st, σ, h⟩)
        (fun _ _ _ h => tailR_ok hP (htr r h1 hr) h1 hr h) (tailR_trL hP (htr r h1 hr) h1 hr))
      (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h => by
        rw [show 4 * (p.ℓ / 4) + 3 = p.ℓ by omega] at h; exact h.m

theorem maskRest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : restChk p = true)
    (hm : ∀ r < p.ℓ, mChk p r = true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) (maskRest P p)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  unfold maskRest
  unfold restChk at hc
  cases e : p.ℓ % 4 == 3
  · rw [Bool.cond_false]
    exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICm p D σ t r s) (p.ℓ % 4) (4 * (p.ℓ / 4))
      fun r _ hr =>
      liftT (fun _ _ h => h.l.st) (fun _ _ _ h => maskR_ok hP (hm r (by omega)) h) (maskR_trL hP (hm r (by omega))))
      (fun x y h => h) fun x y h => by rwa [Nat.div_add_mod] at h
  · rw [Bool.cond_true]
    rw [e, Bool.cond_true] at hc
    exact maskTail_tr hP (beq_iff_eq.mp e) hc

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICw p D σ t i x) ∧ ∃ σ, ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [wChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨cd, _⟩, hl⟩ := hc
  unfold rowW
  exact RelCT.mono (dotAt_tr (hP.dotInv p.ℓ hl) cd) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
    ⟨R, ⟨fun j hj => by rw [famP_aP]; exact (rowA hi I₁ hj).1, fun j hj => by rw [famP_yhP]; exact (I₁.yh j hj).1⟩,
      ⟨fun j hj => by rw [famP_aP]; exact (rowA hi I₂ hj).1, fun j hj => by rw [famP_yhP]; exact (I₂.yh j hj).1⟩⟩)
    fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICh p D σ t i x) ∧ ∃ σ, ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : ICh p D σ t p.k s) :
    WP isa (shakeAt [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (shake_ok (sgB_bases p) hP.hD hs h.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (commit P p) (RS p D E fun σ s => IC p D σ t s) := by
  have hc' := hc
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hm4, hm⟩, hrest⟩, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commit
  refine RelCT.seq (R := RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICw p D σ t 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t p.k s) ?_ ?_)))
  · refine RelCT.mono (seqR_tr (R := fun g => RS p D E fun σ s => ICm p D σ t (4 * g) s) (p.ℓ / 4) 0 fun g _ hg =>
      mask4_tr hP (hm4 g (by omega)))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact RelCT.mono (maskRest_tr hP hrest hm) (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
      ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICw p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => rowW_ok hP (hw i (by omega)) (by omega) h) (rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [w1Enc]; rfl⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICh p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => w1R_ok hP (hh i (by omega)) (by omega) h) (w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => ctShake_ok hP hc h)
      (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.X86_64.Sign
