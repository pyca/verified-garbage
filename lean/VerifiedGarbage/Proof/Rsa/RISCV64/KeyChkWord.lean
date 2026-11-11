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

/-- The first `v` of `w` words, for a number below `2^(64 v)`. -/
theorem words_low {m : Mem} {B : Addr} {d w v X : Nat} (hv : v ≤ w) (h : wordsVal m B d w = X)
    (hX : X < 2 ^ (64 * v)) : wordsVal m B d v = X := by
  have e := wordsVal_append m B d v (w - v)
  rw [show v + (w - v) = w by omega, h] at e
  have l := wordsVal_lt m B d v
  rcases Nat.eq_zero_or_pos (wordsVal m B (d + 8 * v) (w - v)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * v)) z
    omega

/-- The top word of a number of `v` words at least `2^(64 (v - 1))` is not zero. -/
theorem top_pos {m : Mem} {B : Addr} {d v : Nat} (hv : 1 ≤ v) (h : 2 ^ (64 * (v - 1)) ≤ wordsVal m B d v) :
    0 < (word m B (d + 8 * (v - 1))).toNat := by
  have e := wordsVal_succ_top m B d (v - 1)
  rw [show v - 1 + 1 = v by omega] at e
  have l := wordsVal_lt m B d (v - 1)
  rcases Nat.eq_zero_or_pos (word m B (d + 8 * (v - 1))).toNat with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; omega
  · exact z

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

end VG.Proof.Rsa.RISCV64.KeyCheck
