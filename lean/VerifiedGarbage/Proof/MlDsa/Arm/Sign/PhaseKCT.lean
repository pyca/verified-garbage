module

import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.CopyTr
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr

/-!
# ML-DSA signing on ARMv7: the checks leak only the pointers and whether they passed

Each check leaks only its pointers, given that its inputs are reduced
(`zR_trL`, `r0R_trL`, `hR_trL`); the branch on their result leaks whether the
iteration passed, which two runs agree on when they agree on what the
iteration leaks (`checks_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
include hP

theorem normAt_post {s : State} (L : Lay D (sgR p) (sgW p) s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : normChk (sgB p) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] := by
  refine WP.seq (WP.mono (normCall_ok hP L hB hc hr) fun s1 ⟨hP1, _, _⟩ => ?_)
  refine WP.mono (and11_ok s1) fun s2 ⟨_, k2⟩ => ?_
  exact PostB.trans hP1 (postB11 (D := D) k2 ([] : List Region)).1 (fun r h => h) fun _ h => absurd h List.not_mem_nil

theorem normAt_trL {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk (sgB p) f = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (normAt P f B)
      fun _ _ => True :=
  seqL (J := fun _ => True) (normCall_tr hP (B := B) hc)
    (fun x L hr => WP.mono (normCall_ok hP L hB hc hr) fun _ h => ⟨⟨_, h.1⟩, trivial⟩)
    (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)

/-! ## `z` -/

theorem zR_trL {t r : Nat} (hc : zChk p r = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IZ p D σ t r x) ∧ ∃ σ, IZ p D σ t r y) (zR P p r)
      fun _ _ => True := by
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩, hr⟩ := hc
  unfold zR
  refine seqL (J := fun s => (∃ σ, IZb p D σ t r s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
    (seqL (J := fun s => (∃ σ, IZb p D σ t r s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s (yP p r))) ?_ ?_ (normAt_trL hP hB cn)))
  · exact RelCT.mono (mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s1 r hr).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s1 r hr).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.s1 r hr).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (addAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.y 0 (by omega)).1, r₁⟩, ⟨(I₂.y 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (addAt_ok hP L ca (I.y 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩

/-! ## `r₀` -/

theorem r0R_trL {t i : Nat} (hc : rChk p i = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IR p D σ t i x) ∧ ∃ σ, IR p D σ t i y) (r0R P p i)
      fun _ _ => True := by
  simp only [rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  unfold r0R
  refine seqL (J := fun s => (∃ σ, IRb p D σ t i s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
    (seqL (J := fun s => (∃ σ, IRb p D σ t i s) ∧ Reduced s.mem (pa s t1P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s (wP p i))) ?_ ?_
        (seqL (J := fun s => Reduced s.mem (pa s t2P)) ?_ ?_ (normAt_trL hP hB cn))))
  · exact RelCT.mono (mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s2 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s2 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.s2 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (subAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.w 0 (by omega)).1, r₁⟩, ⟨(I₂.w 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (subAt_ok hP L ca (I.w 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · exact lowBitsAt_tr hP hγ cl
  · intro x L r1
    exact WP.mono (lowBitsAt_ok hP L hγ cl r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases 2)]; exact hq.1⟩

/-! ## `ct₀` and `h` -/

theorem hR_trL {t i : Nat} (hc : hChk2 p i = true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, IH p D σ t i x) ∧ ∃ σ, IH p D σ t i y) (hR P p i)
      fun _ _ => True := by
  simp only [hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, _⟩, g6⟩, _⟩, _⟩,
    _⟩, _⟩, o1⟩, o2⟩, o3⟩, o4⟩, _⟩, _⟩, t3⟩, t4⟩, u5⟩, _⟩, _⟩, _⟩, hγ'⟩, hγ⟩, hi⟩, _⟩ := hc
  have hcc := copyChk_spec cc
  have f6 : keepB (sgB p) [(t4P, 1024)] (wP p i) 1024 = true := by
    simp only [hfam, Bool.and_eq_true] at g6
    exact famChk_one (b := wBase p) g6.1.1.2 (show i < i + 1 by omega)
  let J : State → Prop := fun s => (∃ σ, IHb p D σ t i i s) ∧ Reduced s.mem (pa s t3P)
  unfold hR
  refine seqL (J := J) ?_ ?_ (seqL (J := J) ?_ ?_ (seqL (J := J) ?_ ?_
    (seqL (J := fun s => J s ∧ Reduced s.mem (pa s t4P)) ?_ ?_
      (seqL (J := fun s => Reduced s.mem (pa s t4P) ∧ Reduced s.mem (pa s (wP p i))) ?_ ?_
        (seqL (J := fun s => Reduced s.mem (pa s t4P) ∧ Reduced s.mem (pa s (wP p i))) ?_ ?_
          (seqL (J := fun _ => True) ?_ ?_ ?_))))))
  · exact RelCT.mono (mulAt_tr hP cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.t0 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.t0 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (mulAt_ok hP L cm I.1.b.c.1 (I.1.b.l.k.d.t0 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' g1 o1⟩, by rw [hP'.pa (pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (ipAt_tr (t := nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (ipAt_ok (t := nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g2 o2⟩, by rw [hP'.pa (pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (normAt_trL hP hγ' cn) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (normAt_post hP L hγ' cn r1) fun x' hP' => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g3 o3⟩, L.keepRed hP' t3 r1⟩
  · exact RelCT.mono (copy_tr hcc.2.2.2.2.1 hcc.2.2.2.2.2
      fun x y h => ⟨lrel_r7 h.1 _ (List.mem_singleton_self _), lrel_r7 h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r3⟩
    exact WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, ⟨⟨σ, I.step hP' g4 o4⟩, L.keepRed hP' t4 r3⟩,
      by rw [hP'.pa (pS_bases 4)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.w' 0 (by omega)).1⟩
  · exact RelCT.mono (addAt_tr hP ca) (fun x y ⟨R, ⟨⟨⟨_, I₁⟩, r₁⟩, _⟩, ⟨⟨⟨_, I₂⟩, r₂⟩, _⟩⟩ =>
      ⟨R, ⟨(I₁.w' 0 (by omega)).1, r₁⟩, ⟨(I₂.w' 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨⟨σ, I⟩, r3⟩, r4⟩
    exact WP.mono (addAt_ok hP L ca (I.w' 0 (by omega)).1 r3) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, L.keepRed hP' u5 r4, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩
  · exact RelCT.mono (subAt_tr hP cs) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (subAt_ok hP L cs r4 rw) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases 4)]; exact hq.1, L.keepRed hP' f6 rw⟩
  · exact RelCT.mono (hintCall_tr hP hγ ch) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩)
      fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (hintCall_ok hP L hγ ch r4 rw) fun x' ⟨hP', _, _⟩ => ⟨⟨_, hP'⟩, trivial⟩
  · exact block_tr rfl fun x y h => lrel_r7 h.1

/-! ## The checks -/

omit hP in
theorem ifOk_r7 {E I : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {C : State → Prop} {x y : State}
    (h : ∃ x₀ y₀, RS p D E I x₀ y₀ ∧ (PPostB D x₀ x [] ∧ CS x₀ x ∧ x.mem = x₀.mem) ∧
      (PPostB D y₀ y [] ∧ CS y₀ y ∧ y.mem = y₀.mem) ∧ C x₀) :
    ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := by
  obtain ⟨x₀, y₀, R, ⟨hx, _⟩, ⟨hy, _⟩, _⟩ := h
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [hx.bs _ (by decide), hy.bs _ (by decide)]
  exact lrel_r7 (R.lrel hI) _ (List.mem_singleton_self _)

omit hP in
/-- `ifOkElse` on runs related by `RS`, whose `r11` agree: each branch from
the states its entry gives (`hIt`, `hIe`). -/
theorem ifOkElse_RS {E I It Ie Q : State → State → Prop} {t e : Prog isa}
    (hq : ∀ σ₁ σ₂ x y, (signK p D).pre σ₁ → (signK p D).pre σ₂ → (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → (x.gpr .r11) = (y.gpr .r11))
    (hIt : ∀ σ x x₁, I σ x → PPostB D x x₁ [] → CS x x₁ → x₁.mem = x.mem →
      (x.gpr .r11) ≠ 0 → It σ x₁)
    (hIe : ∀ σ x x₁, I σ x → PPostB D x x₁ [] → CS x x₁ → x₁.mem = x.mem →
      (x.gpr .r11) = 0 → Ie σ x₁)
    (ht : RelCT isa (RS p D E It) t Q) (he : RelCT isa (RS p D E Ie) e Q) :
    RelCT isa (RS p D E I) (ifOkElse t e) Q := by
  refine ifOkElse_tr (D := D) (fun x y ⟨σ₁, σ₂, p₁, p₂, hpub, hE, i₁, i₂⟩ => hq σ₁ σ₂ x y p₁ p₂ hpub hE i₁ i₂)
    (RelCT.mono ht (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, hpub, hE, i₁, i₂⟩, ⟨hx, cx, mx⟩, ⟨hy, cy, my⟩, hne⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hpub, hE, hIt _ _ _ i₁ hx cx mx hne,
        hIt _ _ _ i₂ hy cy my (by rw [← hq σ₁ σ₂ x₀ y₀ p₁ p₂ hpub hE i₁ i₂]; exact hne)⟩) fun _ _ h => h)
    (RelCT.mono he (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, hpub, hE, i₁, i₂⟩, ⟨hx, cx, mx⟩, ⟨hy, cy, my⟩, he⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hpub, hE, hIe _ _ _ i₁ hx cx mx he,
        hIe _ _ _ i₂ hy cy my (by rw [← hq σ₁ σ₂ x₀ y₀ p₁ p₂ hpub hE i₁ i₂]; exact he)⟩) fun _ _ h => h)

omit hP in
/-- `seqOk` on runs related by `RS`, whose `r11` agree after each piece:
both stop after the same piece. -/
theorem seqOk_RS {f : Nat → Prog isa} {E : State → State → Prop} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a < k → k ≤ a + n → ∀ σ₁ σ₂ x y, (signK p D).pre σ₁ → (signK p D).pre σ₂ →
        (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ → I k σ₁ x → I k σ₂ y →
        (x.gpr .r11) = (y.gpr .r11)) →
      (∀ k, a < k → k ≤ a + n → ∀ σ x x₁, I k σ x → PPostB D x x₁ [] →
        CS x x₁ → x₁.mem = x.mem → I k σ x₁) →
      (∀ k, a ≤ k → k < a + n → RelCT isa (RS p D E (I k)) (f k) (RS p D E (I (k + 1)))) →
      RelCT isa (RS p D E (I a)) (seqOk f a n) (RS p D E fun σ s => ∃ k, a ≤ k ∧ k ≤ a + n ∧ I k σ s ∧
        (k = a + n ∨ (s.gpr .r11) = 0))
  | 0, a, _, _, _ => RelCT.mono nil_tr (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨a, Nat.le_refl _, by omega, i₁, .inl rfl⟩,
        ⟨a, Nat.le_refl _, by omega, i₂, .inl rfl⟩⟩
  | n + 1, a, hq, hst, h => by
    rw [seqOk]
    refine RelCT.seq (h a (Nat.le_refl _) (by omega)) ?_
    refine ifOkElse_RS (It := I (a + 1)) (Ie := fun σ s => I (a + 1) σ s ∧ (s.gpr .r11) = 0)
      (hq (a + 1) (by omega) (by omega)) (fun σ x x₁ i hP hcs hm _ => hst _ (by omega) (by omega) _ _ _ i hP hcs hm)
      (fun σ x x₁ i hP hcs hm he => ⟨hst _ (by omega) (by omega) _ _ _ i hP hcs hm, by rw [hcs _ (by decide) (by decide)]; exact he⟩)
      (RelCT.mono (seqOk_RS n (a + 1) (fun k hk hk' => hq k (by omega) (by omega))
          (fun k hk hk' => hst k (by omega) (by omega)) fun k hk hk' => h k (by omega) (by omega))
        (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨k₁, a₁, b₁, c₁, d₁⟩, ⟨k₂, a₂, b₂, c₂, d₂⟩⟩ =>
          ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨k₁, by omega, by omega, c₁, d₁.imp (fun _ => by omega) id⟩,
            ⟨k₂, by omega, by omega, c₂, d₂.imp (fun _ => by omega) id⟩⟩)
      (RelCT.mono nil_tr (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨a + 1, by omega, by omega, i₁, .inr z₁⟩, ⟨a + 1, by omega, by omega, i₂, .inr z₂⟩⟩)

theorem checksR0_tr (hc : ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome → ChecksAgree p t σ₁ σ₂) :
    RelCT isa (RS p D E fun σ s => IR p D σ t 0 s) (checksR0 P p) (RS p D E fun σ s => KO p D σ t s) := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have hc2' := ksChk_branches hc
  simp only [ksChk2, Bool.and_eq_true] at hc2'
  obtain ⟨⟨⟨_, _⟩, d3⟩, d4⟩ := hc2'
  unfold checksR0
  refine RelCT.seq (seqOk_RS (I := fun i σ s => IR p D σ t i s) p.k 0
    (fun i hi hi' σ₁ σ₂ x y _ _ _ he i₁ i₂ => by
      rw [i₁.2, i₂.2, bit_congr ((hE σ₁ σ₂ he i₁.1.b.some i₂.1.b.some).2.1 i (by omega))])
    (fun i hi hi' σ x x₁ h hP hcs _ => IR.stable hc (by omega) (by omega) h hP hcs)
    fun i _ hi => liftL (T := fun s => ∃ σ, IR p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => r0R_ok hP (hr i (by omega)) h) (r0R_trL hP (hr i (by omega)))) ?_
  refine ifOkElse_RS (It := fun σ s => IH p D σ t 0 s) (Ie := fun σ s => KO p D σ t s)
    (fun σ₁ σ₂ x y _ _ _ he ⟨i₁, _, hi₁, I₁, hd₁⟩ ⟨i₂, _, hi₂, I₂, hd₂⟩ => by
      rw [Nat.zero_add] at hi₁ hd₁ hi₂ hd₂
      rw [IR.done hi₁ I₁ hd₁, IR.done hi₂ I₂ hd₂,
        bit_congr ((hE σ₁ σ₂ he I₁.1.b.some I₂.1.b.some).2.1 p.k (Nat.le_refl _))])
    (fun σ x x₁ ⟨i, _, hi, I, hd⟩ hP hcs _ hne => by
      rw [Nat.zero_add] at hi hd
      have hik : i = p.k := hd.resolve_right hne
      subst hik
      exact IR.ih (⟨I.1.step hP d3 d4, by rw [hcs _ (by decide) (by decide), I.2]⟩ : IR p D σ t p.k x₁))
    (fun σ x x₁ ⟨i, _, hi, I, hd⟩ hP hcs _ he => by
      rw [Nat.zero_add] at hi hd
      exact kFail_ko hc I.1.b (IR.done hi I hd) (fun hp => ⟨hp.1, hp.2.1⟩) hP hcs he) ?_ nil_tr
  refine RelCT.seq (R := RS p D E fun σ s => IH p D σ t p.k s) (RelCT.mono (seqR_tr (R := fun i => RS p D E
    fun σ s => IH p D σ t i s) p.k 0 fun i _ hi => liftL (T := fun s => ∃ σ, IH p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => hR_ok hP (hh i (by omega)) h) (hR_trL hP (hh i (by omega))))
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  exact liftT (fun _ _ h => h.1.b.l.st) (fun _ _ _ h => onesOk_ok hc h) (block_tr rfl fun x y h => lrel_r7 h)

theorem checks_tr (hc : ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome → ChecksAgree p t σ₁ σ₂) :
    RelCT isa (RS p D E fun σ s => KA p D σ t s) (checks P p)
      (RS p D E fun σ s => EP p D σ t s ∨ EF p D σ t s) := by
  refine ksChk_spec hc fun c1 _ _ _ _ _ _ hz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have hc2' := ksChk_branches hc
  simp only [ksChk2, Bool.and_eq_true] at hc2'
  obtain ⟨⟨⟨d1, d2⟩, _⟩, _⟩ := hc2'
  unfold checks
  refine RelCT.seq (R := RS p D E fun σ s => KN p D σ t s)
    (liftL (T := fun s => Reduced s.mem (pa s cP)) (fun σ s h => ⟨h.c.l.st, h.cc.1⟩)
      (fun _ _ _ h => cntt_ok hP hc h) (ipAt_tr (t := ntt) hP.ntt c1)) ?_
  refine RelCT.seq (R := RS p D E fun σ s => IZ p D σ t 0 s)
    (liftT (fun _ _ h => h.b.l.st) (fun _ _ _ h => kInit_ok hc h) (block_tr rfl fun x y h => lrel_r7 h)) ?_
  refine RelCT.seq (seqOk_RS (I := fun r σ s => IZ p D σ t r s) p.ℓ 0
    (fun r hr hr' σ₁ σ₂ x y _ _ _ he i₁ i₂ => by
      rw [i₁.2, i₂.2, bit_congr ((hE σ₁ σ₂ he i₁.1.b.some i₂.1.b.some).1 r (by omega))])
    (fun r hr hr' σ x x₁ h hP hcs _ => IZ.stable hc (by omega) (by omega) h hP hcs)
    fun r _ hr => liftL (T := fun s => ∃ σ, IZ p D σ t r s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => zR_ok hP (hz r (by omega)) h) (zR_trL hP (hz r (by omega)))) ?_
  refine RelCT.seq (R := RS p D E fun σ s => KO p D σ t s)
    (ifOkElse_RS (It := fun σ s => IR p D σ t 0 s) (Ie := fun σ s => KO p D σ t s)
      (fun σ₁ σ₂ x y _ _ _ he ⟨k₁, _, hk₁, I₁, hd₁⟩ ⟨k₂, _, hk₂, I₂, hd₂⟩ => by
        rw [Nat.zero_add] at hk₁ hd₁ hk₂ hd₂
        rw [IZ.done hk₁ I₁ hd₁, IZ.done hk₂ I₂ hd₂,
          bit_congr ((hE σ₁ σ₂ he I₁.1.b.some I₂.1.b.some).1 p.ℓ (Nat.le_refl _))])
      (fun σ x x₁ ⟨k, _, hk, I, hd⟩ hP hcs _ hne => by
        rw [Nat.zero_add] at hk hd
        have hkl : k = p.ℓ := hd.resolve_right hne
        subst hkl
        exact IZ.ir (⟨I.1.step hP d1 d2, by rw [hcs _ (by decide) (by decide), I.2]⟩ : IZ p D σ t p.ℓ x₁))
      (fun σ x x₁ ⟨k, _, hk, I, hd⟩ hP hcs _ he => by
        rw [Nat.zero_add] at hk hd
        exact kFail_ko hc I.1.b (IZ.done hk I hd) (fun hp => hp.1) hP hcs he)
      (checksR0_tr hP hc hE) nil_tr) ?_
  refine liftR (fun _ _ _ h => kBranch_ok hc h) (ifOkElse_tr (D := D) (fun x y h => ?_)
    (block_tr rfl fun x y h => ifOk_r7 (I := fun σ s => KO p D σ t s) (fun _ _ h => h.b.l.st) h)
    (block_tr rfl fun x y h => ifOk_r7 (I := fun σ s => KO p D σ t s) (fun _ _ h => h.b.l.st) h))
  obtain ⟨σ₁, σ₂, _, _, _, he, k₁, k₂⟩ := h
  rw [k₁.r11, k₂.r11, bit_congr (hE σ₁ σ₂ he k₁.b.some k₂.b.some).2.2]

end

end VG.Proof.MlDsa.Arm.Sign
