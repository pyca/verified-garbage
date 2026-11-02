module

public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValPhase
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on RISC-V: `d` divided by `p - 1` and by `q - 1`

`clrLowW_ok`: `clrLow` as `clrLow_ok`, writing only the array's low word;
`dParts_ok`: the remainders of `d` by `p` and `q` with their low bits cleared
(`Dd`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy clrLow ptr)
open VG.Impl.Rsa.RISCV64.Div (div)
open VG.Impl.Rsa.RISCV64.CrtValues (dParts nArr aP aQ aD aDQ aDD aDT aDR2 aDR3 sMask)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- `clrLow j`: the low bit of `[j]` cleared, and only its low word written. -/
theorem clrLowW_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048) :
    WP isa (.block (clrLow j)) s fun t => Ws t B Z w N ∧ Keys.Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = num s.mem B w j / 2 * 2 ∧ Keep opRegs s t ∧
      Outside B (arr w j) 8 s.mem t.mem := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  refine ptr_ok h (r := .t0) (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hk : WP isa (.block [.load .d .t5 .t0 0, .logicImm .and .t5 .t5 (-2), .store .d .t5 .t0 0])
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.mem = s.mem.writeW (off B (arr w j)) (word s.mem B (arr w j) &&& BitVec.ofInt 64 (-2))) ∧
          Keep [.t5] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.scr.st (d := arr w j) (n := 8) (by omega_arith), h.scr.al8 (d := arr w j) (by omega_arith) (arr_al _ _),
      h.scr.ld (d := arr w j) (n := 8) (by omega_arith)]
  refine WP.mono hk fun u ⟨mu, ku⟩ => ?_
  have kt : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have lw := low_write (m := s.mem) (B := B) h.wpos (h.fit64 hj) (word s.mem B (arr w j) &&& BitVec.ofInt 64 (-2))
  rw [← mu] at lw
  refine ⟨h.of_keep kt, lw.1, ?_, kt, by rw [mu]; exact writeW_outside _ _ _ (by omega_arith)⟩
  rw [lw.2, clr_toNat]
  have e := wordsVal_mod64 s.mem B (d := arr w j) (k := w) h.wpos
  change num s.mem B w j % 2 ^ 64 = _ at e
  rw [← e]
  have := Nat.div_add_mod (num s.mem B w j) (2 ^ 64)
  omega_arith

/-- After the divisions of `d`. -/
structure Dd (s0 : State) (X₁ X₂ V : Nat) (M : Mem) (t : State) : Prop where
  cb : CB s0 M t
  ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr
  mask : slot t.mem (bOf s0) sMask = if maskOf (Pv s0) (Qv s0) X₁ X₂ V then 1 else 0
  r2 : 0 < 2 * (Pv s0 / 2) → num t.mem (bOf s0) (wOf s0) aDR2 = Dv s0 % (2 * (Pv s0 / 2))
  r3 : 0 < 2 * (Qv s0 / 2) → num t.mem (bOf s0) (wOf s0) aDR3 = Dv s0 % (2 * (Qv s0 / 2))

/-- One division of `d` by `[a]` with its low bit cleared, into `[r]`. -/
theorem dDiv_ok {s0 s : State} (h : PreC s0) {M : Mem} (c : CB s0 M s) (ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr)
    {a r : Nat} (ha : a = aP ∨ a = aQ) (hr : r = aDR2 ∨ r = aDR3)
    (hd : num s.mem (bOf s0) (wOf s0) aD = Dv s0)
    (hz : word s.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0) :
    WP isa (seqs [copy aDQ aD, copy aDD a, .block (clrLow aDD), div aDQ r aDD aDT]) s fun t =>
      CB s0 M t ∧ Ws t (bOf s0) (zOf s0) (wOf s0) nArr ∧
      Keys.Frame (bOf s0) (wOf s0) [aDQ, aDD, r, aDT] [] s.mem t.mem ∧
      word t.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 ∧
      (0 < num s.mem (bOf s0) (wOf s0) a / 2 * 2 →
        num t.mem (bOf s0) (wOf s0) r = Dv s0 % (num s.mem (bOf s0) (wOf s0) a / 2 * 2)) := by
  have ⟨w1, w2⟩ := h.w_bounds
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => ws.fit64 hj
  have ha' : a < nArr ∧ a ≠ aDQ ∧ a ≠ aDD ∧ a ≠ aDT := by rcases ha with rfl | rfl <;> decide
  have hr' : r < nArr ∧ r ≠ aDQ ∧ r ≠ aDD ∧ r ≠ aDT ∧ r ≠ aD := by rcases hr with rfl | rfl <;> decide
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws (o := aDQ) (a := aD) (by cvx) (by cvx) (by decide) (by cvx))
    fun t1 ⟨ws1, f1, v1, k1, _⟩ => ?_
  have c1 := c.step h f1 (by cvx) (by simp) k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws1 (o := aDD) (a := a) (by cvx) ha'.1 (by decide) (Ne.symm ha'.2.2.1))
    fun t2 ⟨ws2, f2, v2, k2, o2⟩ => ?_
  have c2 := c1.step h f2 (by cvx) (by simp) k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLowW_ok ws2 (j := aDD) (by cvx) (by decide)) fun t3 ⟨ws3, f3, v3, k3, o3⟩ => ?_
  have c3 := c2.step h f3 (by cvx) (by simp) k3
  have hS : S (wOf s0) = 8 * (wOf s0 + 2) := rfl
  have fD := fit aDD (by cvx)
  have z3 : word t3.mem (bOf s0) (arr (wOf s0) aDD + 8 * wOf s0) = 0 := by
    rw [o3.word (.inr (by omega_arith)) (by omega_arith), o2.word (.inr (by omega_arith)) (by omega_arith),
      f1.word (i := wOf s0) (by omega_arith) (by cvx) (by simp) fD]
    exact hz
  have a1 : num t1.mem (bOf s0) (wOf s0) a = num s.mem (bOf s0) (wOf s0) a :=
    f1.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm ha'.2.1) (by simp) (fit _ ha'.1)
  rw [v2, a1] at v3
  have q3 : num t3.mem (bOf s0) (wOf s0) aDQ = Dv s0 := by
    rw [f3.num (j := aDQ) (by cvx) (by simp) (fit _ (by cvx)), f2.num (j := aDQ) (by cvx) (by simp) (fit _ (by cvx)),
      v1, hd]
  refine WP.mono (div_ok ws3 (q := aDQ) (r := r) (d := aDD) (t := aDT) (by cvx) hr'.1 (by cvx) (by cvx) (by decide)
    (Ne.symm hr'.2.1) (by cvx) (by cvx) hr'.2.2.1 hr'.2.2.2.1 (by cvx) z3) fun t ⟨ws4, f4, k4, _, v4⟩ => ?_
  have c4 := c3.step h f4 (by simp [hr'.1]; cvx) (by simp) k4
  refine ⟨c4, ws4, ?_, ?_, fun hp => ?_⟩
  · refine (f1.mono (by simp) (by simp)).trans ((f2.mono (by simp) (by simp)).trans
      ((f3.mono (by simp) (by simp)).trans (f4.mono (by simp) (by simp))))
  · have hjD : ∀ k ∈ [aDQ, r, aDT], k ≠ aDD := by
      simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨by decide, hr'.2.2.1, by decide⟩
    rw [f4.word (i := wOf s0) (by omega_arith) hjD (by simp) fD]
    exact z3
  · have := (v4 (by rw [v3]; exact hp)).2.2.1
    rw [this, q3, v3]

theorem dParts_eq : dParts = seqs ([copy aDQ aD, copy aDD aP, .block (clrLow aDD), div aDQ aDR2 aDD aDT] ++
    [copy aDQ aD, copy aDD aQ, .block (clrLow aDD), div aDQ aDR3 aDD aDT]) := rfl

theorem dParts_ok {s0 s : State} (h : PreC s0) {X₁ X₂ V X : Nat} (iv : Iv s0 X₁ X₂ V X s) :
    WP isa dParts s (Dd s0 X₁ X₂ V s.mem) := by
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => iv.ws.fit64 hj
  rw [dParts_eq, wp_seqs_append (by simp) (by simp)]
  refine WP.mono (dDiv_ok h iv.cb iv.ws (a := aP) (r := aDR2) (.inl rfl) (.inl rfl) iv.d iv.ddz)
    fun t1 ⟨c1, w1, f1, z1, v1⟩ => ?_
  have d1 : num t1.mem (bOf s0) (wOf s0) aD = Dv s0 := by rw [f1.num (j := aD) (by decide) (by simp) (fit _ (by decide)), iv.d]
  have q1 : num t1.mem (bOf s0) (wOf s0) aQ = Qv s0 := by rw [f1.num (j := aQ) (by decide) (by simp) (fit _ (by decide)), iv.q]
  refine WP.mono (dDiv_ok h c1 w1 (a := aQ) (r := aDR3) (.inr rfl) (.inr rfl) d1 z1)
    fun t ⟨c2, w2, f2, _, v2⟩ => ⟨c2, w2, ?_, fun hp => ?_, fun hq => ?_⟩
  · rw [f2.slot (by decide) (by simp), f1.slot (by decide) (by simp)]; exact iv.mask
  · rw [f2.num (j := aDR2) (by decide) (by simp) (fit _ (by decide)), v1 (by rw [iv.p]; omega_arith), iv.p,
      Nat.mul_comm]
  · rw [v2 (by rw [q1]; omega_arith), q1, Nat.mul_comm]

end VG.Proof.Rsa.RISCV64.CrtValues
