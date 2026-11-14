module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
import VerifiedGarbage.Proof.P256.PPC64LE.Comb
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombJ
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.Window
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lays
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulFn
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate

/-!
# ECDSA verification over P-256 on PPC64LE, by the comb and windows: `[u]G + [v]Q`

`combPts_ok`: `pointsP256` computes `[u]G + [v]Q` as `PtsOk` states,
from the comb's table in memory at the address its symbol names: `u`'s bits,
`b` in Montgomery's form at `EM`, `[u]G` by the comb (`combJ_ok`), `U = [u]G`
and `R = O` (`save_ok`), `v`'s bits, `[v]Q` by the windows (`Window.mul_ok`),
and `R = U + R` (`sum_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.P256

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsP256_eq : pointsP256 =
    .seq (bits (p256.sl U) (bitsAt p256.n 0) (8 * p256.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst p256.n (p256.sl EM) (p256.mont p256.C.b)))
      (.seq mulGeneratorP256 (.seq (.block (Cfg.save p256)) (.seq (bits (p256.sl V) (bitsAt p256.n 0) (8 * p256.n))
        (.seq (Window.Cfg.mul p256 PX PY EM) (Cfg.sum p256)))))) := rfl

/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.P256.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T p256CombWords) (sym : s₀.syms p256Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * p256CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk p256 s₀ pointsP256 := by
  intro s hM syms P hP hQ rest Q h
  have hc := p256_ok
  have hn := hM.ws.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * p256.n)
  have hmont : ∀ x, p256.mont x < p256.C.p := fun x => Nat.mod_lt _ (by decide)
  rw [pointsP256_eq]
  refine WP.seq ?_
  -- `u`'s bits.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (tbl_bits_ok hc hM.ws (i := U) (j := 0) (by decide)
    (by decide)) fun s₁ h => h) fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have K₁ := hM.toKeep.step (by decide) (k₁.rk (rs' := bitsClob)) (hU := O₁.unch)
    (hW := fixedOk_tbl (by decide) 0) (hWs := by decide)
  -- `b R mod p` at `EM`.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (setSl_ok hc K₁.ws (o := EM) (x := p256.mont p256.C.b)
    (by decide) (Nat.lt_trans (hmont _) hc.p_lt)) fun s₂ h => h) fun s₂ ⟨e₂, k₂, O₂⟩ sy₂ => ?_)
  have K₂ := K₁.step (by decide) (k₂.rk (rs' := [.r11])) (hU := O₂.unch)
    (hW := fixedOk_slW (l := [EM]) (by decide)) (hWs := by decide)
  -- `[u]G` by the comb.
  have ht₂ : TableMem s₂ T p256CombWords :=
    ht.unch (by rw [K₂.rk.rd, K₂.rk.wr]) K₂.whole (by decide) hd
  have ht' : TableMem s₂ T (TComb.tableWords p256Comb Spec.P256.curve VG.Impl.P256.p256Comb7) := by
    rw [Proof.P256.PPC64LE.comb_words_eq]; exact ht₂
  have hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords p256Comb Spec.P256.curve VG.Impl.P256.p256Comb7).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.P256.PPC64LE.comb_words_eq]; exact hd
  have bu : ∀ i < 64 * p256.n, s₂.mem (off (s₀.gpr .r6) (bitsAt p256.n 0 + i)) =
      if (sv p256 (s₀.gpr .r6) s U).testBit i then 1 else 0 := fun i hi => by
    rw [tbl_unch O₂.unch (by decide) (j := 0) (by decide) hi (tbl_apart_slW (c := p256) (l := [EM]) (by decide) (by decide) 0 i)]
    exact b₁ i hi
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (TCombJ.combJ_ok p256Comb (Proof.P256.PPC64LE.comb_jconfig hC) hC
    hc.onG K₂.ws ht' (by rw [sy₂, sy₁, syms, sym]) hd' (k := sv p256 (s₀.gpr .r6) s U)
    (Nat.lt_trans hM.u_lt hc.n_enc) K₂.fixed.zero (fun i hi => bu i (by
      have : i < 8 * Spec.P256.curve.len := hi
      exact Nat.lt_of_lt_of_le this (by decide))) K₂.fixed.ap K₂.fixed.b3p) fun s₃ h => h)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ sy₃ => ?_)
  have K₃ := K₂.step (by decide) k₃ (hU := U₃.cover Proof.P256.PPC64LE.comb_writes_cover)
    (hW := (fixedOk_ladWp (by decide) (by decide) GX GY).append (fixedOk_genX (by decide)))
    (hWs := VG.Proof.Ecdh.PPC64LE.le_append (ladWp_le (by decide) (by decide) GX GY) (genX_le (by decide)))
  -- A slot apart from what a step writes keeps its number.
  have sl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' → ∀ {i : Nat}, i < 45 →
      (∀ w ∈ W, p256.sl i + 8 * p256.n ≤ w.1 ∨ w.1 + w.2 ≤ p256.sl i) →
      wordsVal m' (s₀.gpr .r6) (p256.sl i) p256.n = wordsVal m (s₀.gpr .r6) (p256.sl i) p256.n :=
    fun {_ _ _} U {_} hi hW => sv_unch (c := p256) U (by decide) hn hi hW
  -- `U = [u]G`, `R = O`.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (save_ok hc K₃.ws) fun s₄ h => h)
    fun s₄ ⟨k₄, U₄, ux₄, uy₄, uz₄, rx₄, ry₄, rz₄⟩ sy₄ => ?_)
  have K₄ := K₃.step (by decide) (k₄.rk (rs' := [.r4, .r11])) (hU := U₄) (hW := fixedOk_slW (by decide))
    (hWs := by decide)
  -- `v`'s bits.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (tbl_bits_ok hc K₄.ws (i := V) (j := 0) (by decide)
    (by decide)) fun s₅ h => h) fun s₅ ⟨b₅, k₅, O₅⟩ sy₅ => ?_)
  have K₅ := K₄.step (by decide) (k₅.rk (rs' := bitsClob)) (hU := O₅.unch)
    (hW := fixedOk_tbl (by decide) 0) (hWs := by decide)
  -- What the windows read.
  have v₄ : sv p256 (s₀.gpr .r6) s₄ V = sv p256 (s₀.gpr .r6) s V :=
    (sl U₄ (by decide) (by decide)).trans ((sl U₃ (by decide) (by decide)).trans
      ((sl O₂.unch (by decide) (by decide)).trans (sl O₁.unch (by decide) (by decide))))
  have keep5 : ∀ {i : Nat}, i < 45 → i ∈ [PX, PY] →
      sv p256 (s₀.gpr .r6) s₅ i = sv p256 (s₀.gpr .r6) s i := fun {i} hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact (sl O₅.unch hi (by decide)).trans ((sl U₄ hi (by decide)).trans ((sl U₃ hi (by decide)).trans
        ((sl O₂.unch hi (by decide)).trans (sl O₁.unch hi (by decide)))))
  have F₅ := K₅.fixed
  have bp₅ : wordsVal s₅.mem (s₀.gpr .r6) (p256.sl EM) 4 = Spec.P256.curve.b * 2 ^ 256 % Spec.P256.curve.p :=
    (sl O₅.unch (by decide) (by decide)).trans ((sl U₄ (by decide) (by decide)).trans
      ((sl U₃ (by decide) (by decide)).trans e₂))
  have gQ : Window.PtOk (s₀.gpr .r6) s₅ Window.gPt P :=
    Window.PtOk.of_eq ⟨hQ, hM.px_lt, hM.py_lt, lt_of_eq_of_lt hM.fixed.onep (Nat.mod_lt _ (by decide))⟩
      (keep5 (by decide) (by simp)) (keep5 (by decide) (by simp))
      (F₅.onep.trans hM.fixed.onep.symm)
  have bv : Window.Bits (s₀.gpr .r6) s₅ (sv p256 (s₀.gpr .r6) s V) := fun t ht => by
    rw [← v₄]; exact b₅ t ht
  -- `[v]Q` by the windows.
  refine WP.seq (WP.mono (Window.mul_ok hC ⟨K₅.ws, ⟨F₅.ap, bp₅, F₅.zero, F₅.onep⟩, gQ, hP, bv,
    Nat.lt_trans hM.v_lt (by decide)⟩) fun s₆ ⟨k₆, U₆, R₆⟩ => ?_)
  have K₆ := K₅.step (by decide) k₆ (hU := U₆) (hW := fun w hw => by
      simp only [Window.mulW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact Or.inr (by decide)) (hWs := by decide)
  -- `U`, `[u]G`, through the save and the windows.
  have uS : ∀ {i j : Nat}, i ∈ [UX, UY, UZ] → sv p256 (s₀.gpr .r6) s₄ i = sv p256 (s₀.gpr .r6) s₃ j →
      sv p256 (s₀.gpr .r6) s₆ i = sv p256 (s₀.gpr .r6) s₃ j := fun {i _} hi e => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sl U₆ (by decide) (by decide)).trans ((sl O₅.unch (by decide) (by decide)).trans e)
  have ux := uS (by simp) ux₄
  have uy := uS (by simp) uy₄
  have uz := uS (by simp) uz₄
  have F₆ := K₆.fixed
  -- The sum.
  refine WP.mono (sum_ok hc K₆ (fun i hi => ?_)) fun s₇ ⟨K₇, U₇, _, _, rz₇, t₇⟩ => h s₇ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₆.ap (hmont _)
    · exact lt_of_eq_of_lt F₆.b3p (hmont _)
    · rw [ux]; exact L₃ _ (List.mem_cons_self ..)
    · rw [uy]; exact L₃ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [uz]; exact L₃ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact R₆.x
    · exact R₆.y
    · exact R₆.z
  -- What `Pts` keeps from `s`.
  have tb : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' →
      (∀ w ∈ W, w.1 + w.2 ≤ 4352 ∨ 4608 ≤ w.1) → ∀ t < 64 * p256.n,
      m' (off (s₀.gpr .r6) (bitsAt p256.n 1 + t)) = m (off (s₀.gpr .r6) (bitsAt p256.n 1 + t)) :=
    fun {_ _ _} U hW t ht => tbl_unch U (by decide) (j := 1) (by decide) ht (fun w hw => by
      have := hW w hw; have : t < 256 := ht; show 4352 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ 4352 + t; omega_arith)
  have fl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' →
      (∀ w ∈ W, p256.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ p256.sl FLAG) →
      word m' (s₀.gpr .r6) (p256.sl FLAG) = word m (s₀.gpr .r6) (p256.sl FLAG) :=
    fun {_ _ _} U hW => U.word hW (by decide)
  have ha : tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl AP) = Fin.ofNat p256.C.p p256.C.a := by
    show toM _ _ (wordsVal _ _ (p256.sl AP) p256.n) = _; rw [F₆.ap]; exact toM_cmont hc _
  have hb : tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl B3P) = Fin.ofNat p256.C.p (3 * p256.C.b) := by
    show toM _ _ (wordsVal _ _ (p256.sl B3P) p256.n) = _; rw [F₆.b3p]; exact toM_cmont hc _
  have tU : ∀ {i j : Nat}, sv p256 (s₀.gpr .r6) s₆ i = sv p256 (s₀.gpr .r6) s₃ j →
      tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl i) = tmv p256.C p256.n (s₀.gpr .r6) s₃ (p256.sl j) :=
    fun e => by show toM _ _ (sv p256 _ _ _) = toM _ _ (sv p256 _ _ _); rw [e]
  have hU1 : Rep p256.C (tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl UX))
      (tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl UY)) (tmv p256.C p256.n (s₀.gpr .r6) s₆ (p256.sl UZ))
      (mul (sv p256 (s₀.gpr .r6) s U) (G p256.C)) := by
    rw [tU ux, tU uy, tU uz]; exact R₃
  have rm₇ : sv p256 (s₀.gpr .r6) s₇ RM' = sv p256 (s₀.gpr .r6) s RM' :=
    (sl U₇ (by decide) (by decide)).trans ((sl U₆ (by decide) (by decide)).trans
      ((sl O₅.unch (by decide) (by decide)).trans ((sl U₄ (by decide) (by decide)).trans
      ((sl U₃ (by decide) (by decide)).trans ((sl O₂.unch (by decide) (by decide)).trans
      (sl O₁.unch (by decide) (by decide)))))))
  refine ⟨K₇, fun t ht => ?_, ?_, by rw [rm₇]; exact hM.rm_lt, by rw [rm₇]; exact hM.rm, rz₇,
    Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hP _) hU1 R₆.rep (by have e := t₇; rw [ha, hb] at e; exact e.symm)⟩
  · rw [tb U₇ (by decide) t ht, tb U₆ (by decide) t ht, tb O₅.unch (by decide) t ht, tb U₄ (by decide) t ht,
      tb U₃ (by decide) t ht, tb O₂.unch (by decide) t ht, tb O₁.unch (by decide) t ht]
    exact hM.t₁ t ht
  · simp only [flagW]
    rw [fl U₇ (by decide), fl U₆ (by decide), fl O₅.unch (by decide), fl U₄ (by decide), fl U₃ (by decide),
      fl O₂.unch (by decide), fl O₁.unch (by decide)]
    exact hM.flag

end VG.Proof.Ecdsa.Verify.PPC64LE.P256
