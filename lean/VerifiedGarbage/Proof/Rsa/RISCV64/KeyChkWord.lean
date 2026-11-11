module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyWordDiv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on RISC-V: division by words

`Stg.divWA_ok`: `divWA a d`, `[aVR] := [a] mod [d]` by words
(`Proof/Rsa/RISCV64/KeyWordDiv.lean`), exact for `2^(64 (v - 1)) ≤ [d] <
2^(64 v)`, `v = w / 2`: `aVR` zeroed, `[d]` copied to `aVD`, its top word made
not zero (`fixTop_ok`), and `divW_ok`. -/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)

/-- The arrays the checks start from. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The arrays after `start`. -/
abbrev aStart (v : Vals) : Nat → Nat := upd (vals v) aOne 1

/-- The arrays the checks of `d` use. -/
abbrev aFin (v : Vals) : Nat → Nat := upd (upd (vals v) aM1 (2 * (v.p / 2))) aM2 (2 * (v.q / 2))
abbrev liveFin : List Nat := [aZ, aN, aD, aDP, aDQ, aM1, aM2]

/-- `divWA a d`: `[aVR] := [a] mod [d]` by words, exact for `2^(64 (v - 1)) ≤
[d] < 2^(64 v)`; `aVR` then tracked, `aVD` and `aVT` written. -/
theorem Stg.divWA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live) (hz : aZ ∈ live) (hA0 : A aZ = 0)
    (hfree : ∀ j ∈ live, j ∉ [aVR, aVD, aVT]) (hw : 8 ≤ g.w) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (divWA a d)) s fun t => ∃ X,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → X = A a % A d) ∧
      Stg g s0 (upd A aVR X) (aVR :: live) c t := by
  have aR : a ≠ aVR := fun e => hfree a ha (by simp [e])
  have aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  have aT : a ≠ aVT := fun e => hfree a ha (by simp [e])
  have dR : d ≠ aVR := fun e => hfree d hd (by simp [e])
  have dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  have zR : aZ ≠ aVR := by decide
  have hS : S g.w = 8 * (g.w + 2) := rfl
  have hwl := h.ws.wle
  unfold divWA
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVR) (a := aZ) (by decide) hz (Ne.symm zR)) fun t1 h1 => ?_
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  have nR : num t2.mem g.B g.w aVR = 0 := by rw [h2.arrs.get (by simp), upd_ne _ _ (by decide), upd_self, hA0]
  have nD : num t2.mem g.B g.w aVD = A d := by rw [h2.arrs.get (by simp), upd_self, upd_ne _ _ dR]
  rw [kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (fixTop_ok h2.ws (m := aVD) (by decide) (by decide) (by omega))
    fun t3 ⟨w3, f3, v3, p3, _, _, k3, o3⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.RISCV64.WordDiv.divW a aVR aVD aVT] = VG.Impl.Rsa.RISCV64.WordDiv.divW a aVR aVD aVT
    from rfl]
  have fitR := h.ws.fit64 (j := aVR) (by decide)
  have r0 : wordsVal t3.mem g.B (arr g.w aVR) (g.w / 2) = 0 := by
    rw [f3.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := g.w) (j := aVD) (k := aVR) (by decide); omega)
      (by simp) (by omega)]
    exact wordsVal_zero_part (d := arr g.w aVR) (a := 0) (c := g.w / 2) nR (by omega) |>.symm ▸ by simp
  refine WP.mono (divW_ok w3 (a := a) (r := aVR) (m := aVD) (t := aVT) (by decide) (h.live_lt a ha) (by decide)
    (by decide) (by decide) (Ne.symm aR) (by decide) (by decide) (by decide) aT (by omega) hw2 r0 p3)
    fun t ⟨w4, f4, k4, x4, top4, hi4⟩ => ?_
  -- `[a]` in `t3`, and `[aVR]`'s `w` words.
  have na : num t3.mem g.B g.w a = A a := by
    rw [f3.num (by simp; exact aD.symm) (by simp) (h.ws.fit64 (h.live_lt a ha)), h2.arrs.get (by simp [ha]),
      upd_ne _ _ aD, upd_ne _ _ aR]
  generalize hM : wordsVal t3.mem g.B (arr g.w aVD) (g.w / 2) = M at x4
  rw [na] at x4
  have hR : num t.mem g.B g.w aVR = A a % M := by
    have e1 := wordsVal_append t.mem g.B (arr g.w aVR) (g.w / 2) (g.w - g.w / 2)
    have e2 := wordsVal_append t.mem g.B (arr g.w aVR + 8 * (g.w / 2)) 1 (g.w - g.w / 2 - 1)
    rw [show g.w / 2 + (g.w - g.w / 2) = g.w by omega] at e1
    rw [show 1 + (g.w - g.w / 2 - 1) = g.w - g.w / 2 by omega, show arr g.w aVR + 8 * (g.w / 2) + 8 * 1 =
      arr g.w aVR + 8 * (g.w / 2 + 1) by omega, show g.w - g.w / 2 - 1 = g.w - 1 - g.w / 2 by omega, hi4] at e2
    have z2 : wordsVal t3.mem g.B (arr g.w aVR + 8 * (g.w / 2 + 1)) (g.w - 1 - g.w / 2) = 0 := by
      rw [f3.words (fun k hk => by simp at hk; subst hk; have := arr_disj (w := g.w) (j := aVD) (k := aVR) (by decide); omega)
        (by simp) (by omega)]
      exact wordsVal_zero_part nR (by omega)
    have w1 : wordsVal t.mem g.B (arr g.w aVR + 8 * (g.w / 2)) 1 = 0 := by
      simp only [wordsVal, top4]; rfl
    rw [z2, w1, Nat.mul_zero, Nat.add_zero] at e2
    show wordsVal t.mem g.B (arr g.w aVR) g.w = _
    rw [e1, e2, Nat.mul_zero, Nat.add_zero, x4]
  have F : Keys.Frame g.B g.w [aVD, aVR, aVT] [] t2.mem t.mem :=
    (f3.mono (js' := [aVD, aVR, aVT]) (by simp) (by simp)).trans (f4.mono (js' := [aVD, aVR, aVT]) (by simp) (by simp))
  refine ⟨A a % M, fun hlo hhi => ?_, ?_⟩
  · -- The divisor is `[d]`, whose top word is not zero.
    have mv : wordsVal t2.mem g.B (arr g.w aVD) (g.w / 2) = A d := words_low (by omega) nD hhi
    have tp := top_pos (m := t2.mem) (B := g.B) (d := arr g.w aVD) (v := g.w / 2) (by omega) (by rw [mv]; exact hlo)
    rw [← hM, v3, mv, ite_eq_right (by omega), Nat.add_zero]
  · refine h2.next w4 F (by decide) (by simp) (k3.trans k4) (by decide) ?_ ?_ ?_ (h2.mask_keep F (by simp))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [upd_self]; exact hR
      have hn := hfree j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rw [upd_ne _ _ hn.1, F.num
        (by simp; exact ⟨Ne.symm hn.2.1, Ne.symm hn.1, Ne.symm hn.2.2⟩) (by simp) (h.ws.fit64 (h.live_lt j hj)),
        h2.arrs.get (by simp [hj]), upd_ne _ _ hn.2.1, upd_ne _ _ hn.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · decide
      · exact h.live_lt j hj
    · have fitD := h.ws.fit64 (j := aVD) (by decide)
      rw [f4.word (by omega) (by decide) (by simp) fitD, o3.word (by omega) (by omega), h2.vdTop]

/-- Arrays the word path's helpers write: none of them is tracked. -/
abbrev Free (live : List Nat) : Prop := ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT, aW]

/-- `mulQ y x ++ eqA aVQ b`: the mask and'ed with `[y] [x] mod 2^(64 w) = [b]`. -/
theorem Stg.mulEq_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x b : Nat} (hy : y ∈ live) (hx : x ∈ live) (hb : b ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hf : Free live) :
    WP isa (seqs (mulQ y x ++ eqA aVQ b)) s
      (Stg g s0 A live (c && decide (A y * A x % 2 ^ (64 * g.w) = A b))) := by
  have yQ : y ≠ aVQ := fun e => hf y hy (by simp [e])
  have xQ : x ≠ aVQ := fun e => hf x hx (by simp [e])
  have bQ : b ≠ aVQ := fun e => hf b hb (by simp [e])
  unfold mulQ
  rw [List.cons_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h.copy_ok (o := aVQ) (a := aZ) (by decide) hz (by decide)) fun t1 h1 => ?_
  rw [List.cons_append, List.nil_append, kc_seqs_cons (by simp [eqA])]
  refine WP.mono (h1.mulLow_ok (o := aVQ) (y := y) (x := x) (by simp) (by simp [hy]) (by simp [hx]) (Ne.symm yQ)
    (Ne.symm xQ) (by decide) (by rw [upd_self, hA0])) fun t2 h2 => ?_
  refine WP.mono (h2.eqA_ok (a := aVQ) (b := b) (by simp) (by simp [hb])) fun t h3 => ?_
  simp only [upd_self, upd_ne _ _ bQ, upd_ne _ _ yQ, upd_ne _ _ xQ] at h3
  refine (h3.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
  have jQ : j ≠ aVQ := fun e => hf j hj (by simp [e])
  rw [upd_ne _ _ jQ, upd_ne _ _ jQ]

/-- `divWA a d ++ eqA aVR b`: the mask and'ed with `Y = [b]`, `Y` `[a] mod [d]`
for `2^(64 (v - 1)) ≤ [d] < 2^(64 v)`. -/
theorem Stg.divEq_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d b : Nat} (ha : a ∈ live) (hd : d ∈ live) (hb : b ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (hf : ∀ j ∈ live, j ∉ [aVR, aVD, aVT]) (hw : 8 ≤ g.w) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (divWA a d ++ eqA aVR b)) s fun t => ∃ Y,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → Y = A a % A d) ∧
      Stg g s0 A live (c && decide (Y = A b)) t := by
  have bR : b ≠ aVR := fun e => hf b hb (by simp [e])
  rw [kc_seqs_append (by simp [divWA]) (by simp [eqA])]
  refine WP.mono (h.divWA_ok ha hd hz hA0 hf hw hw2) fun t1 ⟨Y, hY, h1⟩ => ?_
  refine WP.mono (h1.eqA_ok (a := aVR) (b := b) (by simp) (by simp [hb])) fun t h2 => ⟨Y, hY, ?_⟩
  rw [upd_self, upd_ne _ _ bR] at h2
  refine (h2.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
  have jR : j ≠ aVR := fun e => hf j hj (by simp [e])
  rw [upd_ne _ _ jR]

/-- `mulModOne y x d`: the mask and'ed with `X = 1`, `X` `([y] [x] mod
2^(64 w)) mod [d]` for `2^(64 (v - 1)) ≤ [d] < 2^(64 v)`. -/
theorem Stg.mulModOne_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {y x d : Nat} (hy : y ∈ live) (hx : x ∈ live) (hd : d ∈ live) (hz : aZ ∈ live)
    (hA0 : A aZ = 0) (ho : aOne ∈ live) (hA1 : A aOne = 1) (hf : Free live) (hw : 8 ≤ g.w) (hw2 : g.w % 2 = 0) :
    WP isa (seqs (mulModOne y x d)) s fun t => ∃ X,
      (2 ^ (64 * (g.w / 2 - 1)) ≤ A d → A d < 2 ^ (64 * (g.w / 2)) → X = A y * A x % 2 ^ (64 * g.w) % A d) ∧
      Stg g s0 A live (c && decide (X = 1)) t := by
  have yQ : y ≠ aVQ := fun e => hf y hy (by simp [e])
  have xQ : x ≠ aVQ := fun e => hf x hx (by simp [e])
  have dQ : d ≠ aVQ := fun e => hf d hd (by simp [e])
  unfold mulModOne mulQ
  simp only [List.cons_append, List.nil_append]
  rw [kc_seqs_cons (by simp [divWA])]
  refine WP.mono (h.copy_ok (o := aVQ) (a := aZ) (by decide) hz (by decide)) fun t1 h1 => ?_
  rw [kc_seqs_cons (by simp [divWA])]
  refine WP.mono (h1.mulLow_ok (o := aVQ) (y := y) (x := x) (by simp) (by simp [hy]) (by simp [hx]) (Ne.symm yQ)
    (Ne.symm xQ) (by decide) (by rw [upd_self, hA0])) fun t2 h2 => ?_
  have hf2 : ∀ j ∈ aVQ :: live, j ∉ [aVR, aVD, aVT] := fun j hj => by
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    · have := hf j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩
  refine WP.mono (h2.divEq_ok (a := aVQ) (d := d) (b := aOne) (by simp) (by simp [hd]) (by simp [ho]) (by simp [hz])
    (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hA0]) hf2 hw hw2) fun t ⟨X, hX, h3⟩ => ⟨X, ?_, ?_⟩
  · intro hlo hhi
    simp only [upd_self, upd_ne _ _ dQ, upd_ne _ _ yQ, upd_ne _ _ xQ] at hX
    exact hX hlo hhi
  · simp only [upd_ne _ _ (by decide : aOne ≠ aVQ), hA1] at h3
    refine (h3.sub (live' := live) (fun j hj => by simp [hj])).congr' fun j hj => ?_
    have jQ : j ≠ aVQ := fun e => hf j hj (by simp [e])
    rw [upd_ne _ _ jQ, upd_ne _ _ jQ]


/-- The mask of the checks by words: `p` odd, `p q mod 2^(64 w) = n`, `qInv < p`,
`(q qInv mod 2^(64 w)) mod p = 1` (`Xq`), `dP < p - 1`, `(e dP mod 2^(64 w)) mod
(p - 1) = 1` (`X₁`), and the same for `q` (`X₂`). -/
def crtBitsW (n p q dP dQ qI L Xq X₁ X₂ : Nat) : Bool :=
  decide (p % 2 = 1) && decide (L = n) && decide (qI < p) && decide (Xq = 1) &&
    decide (dP < 2 * (p / 2)) && decide (X₁ = 1) && decide (dQ < 2 * (q / 2)) && decide (X₂ = 1)

/-- `2^(64 (v - 1)) ≤ x < 2^(64 v)`, for `v = w / 2`: what the division by
words needs of its divisor to be exact. -/
abbrev InW (w x : Nat) : Prop := 2 ^ (64 * (w / 2 - 1)) ≤ x ∧ x < 2 ^ (64 * (w / 2))

/-- The checks of `vg_rsa_check_crt_key`, by words. -/
theorem crtChecksW_ok {g : Geo} {s0 s : State} {v : Vals}
    (h : Stg g s0 (aStart v) live0 (decide (v.p % 2 = 1)) s) (hw : 8 ≤ g.w) (hw2 : g.w % 2 = 0) :
    WP isa (seqs crtChecksW) s fun t => ∃ Xq X₁ X₂ : Nat,
      (InW g.w v.p → Xq = v.q * v.qI % 2 ^ (64 * g.w) % v.p) ∧
      (InW g.w (2 * (v.p / 2)) → X₁ = v.e * v.dP % 2 ^ (64 * g.w) % (2 * (v.p / 2))) ∧
      (InW g.w (2 * (v.q / 2)) → X₂ = v.e * v.dQ % 2 ^ (64 * g.w) % (2 * (v.q / 2))) ∧
      Stg g s0 (aFin v) liveFin
        (crtBitsW v.n v.p v.q v.dP v.dQ v.qI (v.p * v.q % 2 ^ (64 * g.w)) Xq X₁ X₂) t := by
  unfold crtChecksW
  simp only [List.append_assoc]
  have f0 : Free live0 := by decide
  rw [← List.append_assoc (mulQ aP aQ), kc_seqs_append (by simp [mulQ]) (by simp [ltA])]
  refine WP.mono (h.mulEq_ok (y := aP) (x := aQ) (b := aN) (by decide) (by decide) (by decide) (by decide) rfl f0)
    fun t1 h1 => ?_
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h1.ltA_ok (a := aQI) (b := aP) (by decide) (by decide) (by decide)) fun t2 h2 => ?_
  rw [kc_seqs_append (by simp [mulModOne, mulQ]) (by simp)]
  refine WP.mono (h2.mulModOne_ok (y := aQ) (x := aQI) (d := aP) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) rfl f0 hw hw2) fun t3 ⟨Xq, hXq, h3⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h3.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t4 h4 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h4.clrLow_ok (j := aM1) (by decide) (by decide)) fun t5 h5 => ?_
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (h5.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t6 h6 => ?_
  rw [kc_seqs_cons (by simp [ltA])]
  refine WP.mono (h6.clrLow_ok (j := aM2) (by decide) (by decide)) fun t7 h7 => ?_
  have f7 : Free (aM2 :: aM1 :: live0) := by decide
  -- `dP`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h7.ltA_ok (a := aDP) (b := aM1) (by decide) (by decide) (by decide)) fun t8 h8 => ?_
  rw [kc_seqs_append (by simp [mulModOne, mulQ]) (by simp [ltA])]
  refine WP.mono (h8.mulModOne_ok (y := aE) (x := aDP) (d := aM1) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) rfl f7 hw hw2) fun t9 ⟨X₁, hX₁, h9⟩ => ?_
  -- `dQ`.
  rw [kc_seqs_append (by simp [ltA]) (by simp [mulModOne, mulQ])]
  refine WP.mono (h9.ltA_ok (a := aDQ) (b := aM2) (by decide) (by decide) (by decide)) fun t10 h10 => ?_
  refine WP.mono (h10.mulModOne_ok (y := aE) (x := aDQ) (d := aM2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) rfl f7 hw hw2) fun t h11 => ?_
  obtain ⟨X₂, hX₂, h11⟩ := h11
  refine ⟨Xq, X₁, X₂, fun hi => hXq hi.1 hi.2, fun hi => hX₁ hi.1 hi.2, fun hi => hX₂ hi.1 hi.2,
    (h11.sub (live' := liveFin) (by decide)).congr' fun j hj => ?_⟩
  simp only [liveFin, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The checks of `d`, by words. -/
theorem dChecksW_ok {g : Geo} {s0 s : State} {v : Vals} {c : Bool} (h : Stg g s0 (aFin v) liveFin c s)
    (hw : 8 ≤ g.w) (hw2 : g.w % 2 = 0) :
    WP isa (seqs dChecksW) s fun t => ∃ Y₁ Y₂,
      (InW g.w (2 * (v.p / 2)) → Y₁ = v.d % (2 * (v.p / 2))) ∧ (InW g.w (2 * (v.q / 2)) → Y₂ = v.d % (2 * (v.q / 2))) ∧
      ∃ A live, Stg g s0 A live (c && decide (v.d < v.n) && decide (Y₁ = v.dP) && decide (Y₂ = v.dQ)) t := by
  unfold dChecksW
  simp only [List.append_assoc]
  have ff : ∀ j ∈ liveFin, j ∉ [aVR, aVD, aVT] := by decide
  rw [kc_seqs_append (by simp [ltA]) (by simp [divWA])]
  refine WP.mono (h.ltA_ok (a := aD) (b := aN) (by decide) (by decide) (by decide)) fun t1 h1 => ?_
  rw [← List.append_assoc, kc_seqs_append (by simp [divWA]) (by simp [divWA])]
  refine WP.mono (h1.divEq_ok (a := aD) (d := aM1) (b := aDP) (by decide) (by decide) (by decide) (by decide) rfl ff
    hw hw2) fun t2 ⟨Y₁, hY₁, h2⟩ => ?_
  refine WP.mono (h2.divEq_ok (a := aD) (d := aM2) (b := aDQ) (by decide) (by decide) (by decide) (by decide) rfl ff
    hw hw2) fun t ⟨Y₂, hY₂, h3⟩ => ⟨Y₁, Y₂, fun hi => hY₁ hi.1 hi.2, fun hi => hY₂ hi.1 hi.2, _, _, h3⟩


theorem bv_or0 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx : x.toNat ||| y.toNat = 0 := by rw [← BitVec.toNat_or, h]; rfl
    rw [Nat.or_eq_zero_iff] at hx
    exact ⟨BitVec.eq_of_toNat_eq hx.1, BitVec.eq_of_toNat_eq hx.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem bv_and7 (x : BitVec 64) : (x &&& 7#64 = 0) ↔ x.toNat % 8 = 0 := by
  constructor
  · intro h
    have : (x &&& 7#64).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; exact h

theorem bv_xor0 (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h; have := congrArg (· ^^^ y) h; simpa [BitVec.xor_assoc] using this
  · rintro rfl; simp

theorem bv_lt_ite0 (x y : BitVec 64) : (if x < y then (1 : BitVec 64) else 0) = 0 ↔ ¬ x < y := by
  by_cases h : x < y <;> simp [h]

theorem kc_exec_li32 {s : State} {d : Reg} : exec (.li d 32) s = some (s.write d 32#64) := by
  rw [exec_li (by decide)]; rfl

/-- `shape`: `t0 = 0` exactly for `p_len` (`s5`) a multiple of 8 and at least
32, equal to `q_len` (`s6`) and to `4 w` (`s9`). -/
theorem shape_ok {s : State} {pl ql w : Nat} (h5 : s.gpr .s5 = BitVec.ofNat 64 pl)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 ql) (h9 : s.gpr .s9 = BitVec.ofNat 64 w) (hpl : pl < 2 ^ 32)
    (hql : ql < 2 ^ 32) (hw : w ≤ 1024) :
    WP isa (.block shape) s fun t =>
      ((t.gpr .t0 = 0 ↔ (pl % 8 = 0 ∧ 4 * w = pl ∧ pl = ql ∧ 32 ≤ pl)) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hP : ∀ x : Nat, x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega
  unfold shape
  brun [h5, h6, h9, kc_exec_li32]
  simp only [bv_or0, bv_xor0, bv_lt_ite0]
  have l2 : BitVec.ofNat 64 w <<< 2 = BitVec.ofNat 64 (4 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hP w (by omega), BitVec.toNat_ofNat]; omega
  simp only [l2, bv_and7, hP pl hpl, BitVec.lt_def, show (32#64).toNat = 32 from rfl, Nat.not_lt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · have := congrArg BitVec.toNat h2; rw [hP _ (by omega), hP pl hpl] at this; exact this
    · have := congrArg BitVec.toNat h3; rw [hP pl hpl, hP ql hql] at this; exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, by rw [h2]⟩, by rw [h3]⟩, h4⟩


end VG.Proof.Rsa.RISCV64.KeyCheck
