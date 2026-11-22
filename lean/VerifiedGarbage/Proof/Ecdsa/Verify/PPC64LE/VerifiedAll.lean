module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.CombAll
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.VerifiedAll
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ECDSA verification on PPC64LE by a comb and windows: for every curve

What `<Curve>/Verified.lean` needs of a curve whose `[u]G` is by a comb's
table and whose `[v]Q` is by windows, once for every configuration:

* `CombWin.pts`, the program of `[u]G + [v]Q`, and `CombWin.pts_ok`: it is
  as `PtsOk` states, for a generator that leaves `GeneratorPost` from the
  table of `u`'s bits (the comb, with its table), and a multiplication on
  the windows' ranges that leaves `R` reduced and representing `[v]Q`
  (`Proof/Ecdsa/PPC64LE/WindowAll.lean`): `u`'s bits, `b R mod p` at `EM`,
  `[u]G`, `U = R` and `R = O` (`save_ok`), `v`'s bits, `[v]Q`, and the sum
  (`sum_ok`), with the slots, the flag and the table of `p - 2` that `Pts`
  keeps apart from what each step writes;
* `CombWin.kit_mul`: the windows of a kit (`WAll.Kit.mulP`), called as the
  function ECDH calls too (`Cfg.winCall`), are such a
  multiplication, and `CombWin.kit_pts_ok` is `pts_ok` with them;
* `CombWin.verify_ok`: `verifyWith` with points that read a table runs and
  leaves `VPost`, from `VPre` without the table's region and `ConstsOk`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.CombWin

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

variable {c : Cfg}

/-- `[u]G + [v]Q`: `u`'s bits, `b R mod p` at `EM`, `[u]G` by `gen`, `U = R`
and `R = O`, `v`'s bits, `[v]Q` by `mulP`, and the sum. -/
def pts (c : Cfg) (gen mulP : Prog isa) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.seq
    (.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl EM) (c.mont c.C.b)))
    (.seq gen (.seq (.block (Cfg.save c)) (.seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n))
      (.seq mulP (Cfg.sum c))))))

theorem fixedOk_mulW (h7 : c.n < 10) (E : Nat) : FixedOk c (Proof.Ecdh.PPC64LE.Win.mulWS c E) := fun w hw => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [sl_eq c 12]
  rcases hw with rfl | rfl | rfl | rfl <;> exact Or.inr (by simp only [sl_eq, nslots]; omega_using [h7])

/-- The table of `p - 2` is apart from what the windows write. -/
theorem tbl_apart_mulW (h7 : c.n < 10) (E : Nat) {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ Proof.Ecdh.PPC64LE.Win.mulWS c E, bitsAt c.n 1 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 1 + t := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [bitsAt_eq]
  rcases hw with rfl | rfl | rfl | rfl <;> simp only [sl_eq, nslots] <;> omega_using [ht, h7]

/-- `[u]G + [v]Q`, into `R`, by a generator from the table of `u`'s bits and
a multiplication on the windows' ranges. -/
theorem pts_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {E : Nat}
    (hWs : ∀ w ∈ Proof.Ecdh.PPC64LE.Win.mulWS c E, w.1 + w.2 ≤ size) {gen mulP : Prog isa} {s₀ : State}
    (hgen : ∀ {s : State} {k : Nat}, Keep c s₀ (s₀.gpr .r6) s → s.syms = s₀.syms → k < 2 ^ (8 * c.C.len) →
      (∀ i < 64 * c.n, s.mem (off (s₀.gpr .r6) (bitsAt c.n 0 + i)) = if k.testBit i then 1 else 0) →
      WP isa gen s (GeneratorPost c (s₀.gpr .r6) k (G c.C) s))
    (hmul : ∀ {s : State} {k : Nat} {P : Point c.C}, Keep c s₀ (s₀.gpr .r6) s →
      sv c (s₀.gpr .r6) s EM = c.mont c.C.b → WAll.PtOk c (s₀.gpr .r6) s (WAll.gPt c) P →
      onCurve c.C P = true → WAll.Bits c (s₀.gpr .r6) s k → k < c.C.n →
      WP isa mulP s fun s' => Rk powClob s s' ∧ Unch (s₀.gpr .r6) (Proof.Ecdh.PPC64LE.Win.mulWS c E) s.mem s'.mem ∧
        WAll.PtOk c (s₀.gpr .r6) s' (Window.Cfg.rPt c) (mul k P)) :
    PtsOk c s₀ (pts c gen mulP) := by
  intro s hM syms P hP hQ rest Q h
  have h7 := hc.n10
  have hn := hM.ws.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hp0 : 0 < c.C.p := by omega_using [hp3]
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ hp0
  obtain tblLe : ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], w.1 + w.2 ≤ size := fun w hw => by
    rw [List.mem_singleton.mp hw]; exact bitsAt_le c h7 (by decide)
  obtain apL : ∀ {i : Nat}, i < 45 → i ∉ ACC :: PT :: ladIx → ∀ w ∈ Point.ladWp (ladderAt c GX GY) ++ genX c,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl =>
    apart_append (apart_ladWp h3 h7 hi (nmem_of hl (by decide))) (apart_genX h7 hi (nmem_of hl (by decide)))
  rw [pts]
  refine WP.seq ?_
  -- `u`'s bits.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (tbl_bits_ok hc hM.ws (i := U) (j := 0) (by decide)
    (by decide)) fun s₁ h => h) fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  obtain K₁ := hM.toKeep.step h7 (k₁.rk (rs' := bitsClob)) (hU := O₁.unch)
    (hW := fixedOk_tbl h7 0) (hWs := tblLe)
  -- `b R mod p` at `EM`.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (setSl_ok hc K₁.ws (o := EM) (x := c.mont c.C.b)
    (by decide) (Nat.lt_trans (hmont _) hc.p_lt)) fun s₂ h => h) fun s₂ ⟨e₂, k₂, O₂⟩ sy₂ => ?_)
  obtain K₂ := K₁.step h7 (k₂.rk (rs' := [.r11])) (hU := O₂.unch)
    (hW := fixedOk_slW (l := [EM]) (by decide)) (hWs := slW_le h7 (l := [EM]) (by decide))
  -- `[u]G` by the generator.
  obtain bu : ∀ i < 64 * c.n, s₂.mem (off (s₀.gpr .r6) (bitsAt c.n 0 + i)) =
      if (sv c (s₀.gpr .r6) s U).testBit i then 1 else 0 := fun i hi => by
    rw [tbl_unch O₂.unch h7 (j := 0) (by decide) hi (tbl_apart_slW (c := c) (l := [EM]) h7 (by decide) 0 i)]
    exact b₁ i hi
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (hgen K₂ (by rw [sy₂, sy₁, syms])
    (Nat.lt_trans hM.u_lt hc.n_enc) bu) fun s₃ h => h) fun s₃ ⟨k₃, U₃, L₃, R₃⟩ sy₃ => ?_)
  obtain K₃ := K₂.step h7 k₃ (hU := U₃)
    (hW := (fixedOk_ladWp h3 h7 GX GY).append (fixedOk_genX h7))
    (hWs := VG.Proof.Ecdh.PPC64LE.le_append (ladWp_le h3 h7 GX GY) (genX_le h7))
  -- A slot apart from what a step writes keeps its number.
  obtain sl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' → ∀ {i : Nat}, i < 45 →
      (∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) →
      wordsVal m' (s₀.gpr .r6) (c.sl i) c.n = wordsVal m (s₀.gpr .r6) (c.sl i) c.n :=
    fun {_ _ _} U {_} hi hW => sv_unch (c := c) U h7 hn hi hW
  -- `U = [u]G`, `R = O`.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (save_ok hc K₃.ws) fun s₄ h => h)
    fun s₄ ⟨k₄, U₄, ux₄, uy₄, uz₄, rx₄, ry₄, rz₄⟩ sy₄ => ?_)
  obtain K₄ := K₃.step h7 (k₄.rk (rs' := [.r4, .r11])) (hU := U₄) (hW := fixedOk_slW (by decide))
    (hWs := slW_le h7 (by decide))
  -- `v`'s bits.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (tbl_bits_ok hc K₄.ws (i := V) (j := 0) (by decide)
    (by decide)) fun s₅ h => h) fun s₅ ⟨b₅, k₅, O₅⟩ sy₅ => ?_)
  obtain K₅ := K₄.step h7 (k₅.rk (rs' := bitsClob)) (hU := O₅.unch)
    (hW := fixedOk_tbl h7 0) (hWs := tblLe)
  -- What the windows read.
  obtain v₄ : sv c (s₀.gpr .r6) s₄ V = sv c (s₀.gpr .r6) s V :=
    (sl U₄ (by decide) (apart_slW (by decide))).trans ((sl U₃ (by decide) (apL (by decide) (by decide))).trans
      ((sl O₂.unch (by decide) (apart_slW (l := [EM]) (by decide))).trans
      (sl O₁.unch (by decide) (apart_tbl h7 (by decide) 0))))
  obtain keep5 : ∀ {i : Nat}, i ∈ [PX, PY] →
      sv c (s₀.gpr .r6) s₅ i = sv c (s₀.gpr .r6) s i := fun {i} hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact (sl O₅.unch (by decide) (apart_tbl h7 (by decide) 0)).trans
        ((sl U₄ (by decide) (apart_slW (by decide))).trans
        ((sl U₃ (by decide) (apL (by decide) (by decide))).trans
        ((sl O₂.unch (by decide) (apart_slW (l := [EM]) (by decide))).trans
        (sl O₁.unch (by decide) (apart_tbl h7 (by decide) 0)))))
  have F₅ := K₅.fixed
  obtain bp₅ : sv c (s₀.gpr .r6) s₅ EM = c.mont c.C.b :=
    (sl O₅.unch (by decide) (apart_tbl h7 (by decide) 0)).trans
      ((sl U₄ (by decide) (apart_slW (by decide))).trans
      ((sl U₃ (by decide) (apL (by decide) (by decide))).trans e₂))
  obtain gQ : WAll.PtOk c (s₀.gpr .r6) s₅ (WAll.gPt c) P :=
    WAll.PtOk.of_eq ⟨hQ, hM.px_lt, hM.py_lt, lt_of_eq_of_lt hM.fixed.onep (Nat.mod_lt _ hp0)⟩
      (keep5 (by simp)) (keep5 (by simp)) (F₅.onep.trans hM.fixed.onep.symm)
  obtain bv : WAll.Bits c (s₀.gpr .r6) s₅ (sv c (s₀.gpr .r6) s V) := fun t ht => by
    rw [← v₄]; exact b₅ t ht
  -- `[v]Q` by the windows.
  refine WP.seq (WP.mono (hmul K₅ bp₅ gQ hP bv hM.v_lt) fun s₆ ⟨k₆, U₆, R₆⟩ => ?_)
  obtain K₆ := K₅.step h7 k₆ (hU := U₆) (hW := fixedOk_mulW h7 E) (hWs := hWs)
  obtain apM : ∀ {i : Nat}, i < 45 → i ∉ ACC :: PT :: ladIx → ∀ w ∈ Proof.Ecdh.PPC64LE.Win.mulWS c E,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl => Proof.Ecdh.PPC64LE.Win.apart_mulW h7 E hi hl
  -- `U`, `[u]G`, through the save and the windows.
  obtain uS : ∀ {i j : Nat}, i ∈ [UX, UY, UZ] → sv c (s₀.gpr .r6) s₄ i = sv c (s₀.gpr .r6) s₃ j →
      sv c (s₀.gpr .r6) s₆ i = sv c (s₀.gpr .r6) s₃ j := fun {i _} hi e => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sl U₆ (by decide) (apM (by decide) (by decide))).trans
        ((sl O₅.unch (by decide) (apart_tbl h7 (by decide) 0)).trans e)
  obtain ux := uS (by simp) ux₄
  obtain uy := uS (by simp) uy₄
  obtain uz := uS (by simp) uz₄
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
  obtain hFl := sl_le c h7 (i := FLAG) (by decide)
  obtain h0 := hc.n0
  obtain fl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' →
      (∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) →
      word m' (s₀.gpr .r6) (c.sl FLAG) = word m (s₀.gpr .r6) (c.sl FLAG) := fun U ap =>
    U.word (fun w hw => (ap w hw).imp (fun h => by omega_using [h, h0]) id) (by omega_using [hFl, hn, h0])
  obtain ha : tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal _ _ (c.sl AP) c.n) = _; rw [F₆.ap]; exact toM_cmont hc _
  obtain hb : tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal _ _ (c.sl B3P) c.n) = _; rw [F₆.b3p]; exact toM_cmont hc _
  obtain tU : ∀ {i j : Nat}, sv c (s₀.gpr .r6) s₆ i = sv c (s₀.gpr .r6) s₃ j →
      tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl i) = tmv c.C c.n (s₀.gpr .r6) s₃ (c.sl j) :=
    fun e => by show toM _ _ (sv c _ _ _) = toM _ _ (sv c _ _ _); rw [e]
  obtain hU1 : Rep c.C (tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl UX))
      (tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl UY)) (tmv c.C c.n (s₀.gpr .r6) s₆ (c.sl UZ))
      (mul (sv c (s₀.gpr .r6) s U) (G c.C)) := by
    rw [tU ux, tU uy, tU uz]; exact R₃
  obtain rm₇ : sv c (s₀.gpr .r6) s₇ RM' = sv c (s₀.gpr .r6) s RM' :=
    (sl U₇ (by decide) (apart_append (apart_slW (by decide)) (apart_own h7 (by decide)))).trans
      ((sl U₆ (by decide) (apM (by decide) (by decide))).trans
      ((sl O₅.unch (by decide) (apart_tbl h7 (by decide) 0)).trans
      ((sl U₄ (by decide) (apart_slW (by decide))).trans
      ((sl U₃ (by decide) (apL (by decide) (by decide))).trans
      ((sl O₂.unch (by decide) (apart_slW (l := [EM]) (by decide))).trans
      (sl O₁.unch (by decide) (apart_tbl h7 (by decide) 0)))))))
  refine ⟨K₇, fun t ht => ?_, ?_, by rw [rm₇]; exact hM.rm_lt, by rw [rm₇]; exact hM.rm, rz₇,
    Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hP _) hU1 R₆.rep
      (by have e := t₇; rw [ha, hb] at e; exact e.symm)⟩
  · rw [tbl_unch U₇ h7 (j := 1) (by decide) ht
        (apart_append (tbl_apart_slW h7 (by decide) 1 t) (tbl_apart_own h7 1 t)),
      tbl_unch U₆ h7 (j := 1) (by decide) ht (tbl_apart_mulW h7 E ht),
      tbl_unch O₅.unch h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch U₄ h7 (j := 1) (by decide) ht (tbl_apart_slW h7 (by decide) 1 t),
      tbl_unch U₃ h7 (j := 1) (by decide) ht
        (apart_append (tbl_apart_ladWp h3 h7 _ _ _ _) (tbl_apart_genX h7 (by decide) ht)),
      tbl_unch O₂.unch h7 (j := 1) (by decide) ht (tbl_apart_slW (c := c) (l := [EM]) h7 (by decide) 1 t),
      tbl_unch O₁.unch h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht)]
    exact hM.t₁ t ht
  · simp only [flagW]
    rw [fl U₇ (apart_append (apart_slW (by decide)) (apart_own h7 (by decide))),
      fl U₆ (apM (by decide) (by decide)), fl O₅.unch (apart_tbl h7 (by decide) 0),
      fl U₄ (apart_slW (by decide)), fl U₃ (apL (by decide) (by decide)),
      fl O₂.unch (apart_slW (l := [EM]) (by decide)), fl O₁.unch (apart_tbl h7 (by decide) 0)]
    exact hM.flag

/-- The windows of a kit, as `pts_ok` takes the multiplication: for `b` at
`EM` or `3 b` at the signature's slot, as the kit's arithmetic reads it, and
a scalar below `n` of no more bits than the windows'. -/
theorem kit_mul (K : WAll.Kit c) (hb : (K.bs = EM ∧ K.bK = c.C.b) ∨ (K.bs = B3P ∧ K.bK = 3 * c.C.b))
    (hnw : 8 * c.C.len ≤ K.wb * K.nw) (hC : Law c.C) {s₀ s : State} {k : Nat} {P : Point c.C}
    (S : Keep c s₀ (s₀.gpr .r6) s) (hbm : sv c (s₀.gpr .r6) s EM = c.mont c.C.b)
    (g : WAll.PtOk c (s₀.gpr .r6) s (WAll.gPt c) P) (hP : onCurve c.C P = true)
    (bits : WAll.Bits c (s₀.gpr .r6) s k) (hk : k < c.C.n) :
    WP isa (c.winCall K.mulP) s fun s' => Rk powClob s s' ∧ Unch (s₀.gpr .r6) (Proof.Ecdh.PPC64LE.Win.mulWS c K.E) s.mem s'.mem ∧
      WAll.PtOk c (s₀.gpr .r6) s' (Window.Cfg.rPt c) (mul k P) := by
  have F := S.fixed
  have hkc : WAll.KC c K.bs K.bK (s₀.gpr .r6) s := by
    refine ⟨F.ap, ?_, F.zero, F.onep⟩
    rcases hb with ⟨e, e'⟩ | ⟨e, e'⟩
    · rw [e, e']; exact hbm
    · rw [e, e']; exact F.b3p
  exact Proof.Ecdh.PPC64LE.Win.mulCall_ok K hC ⟨S.ws, hkc, g, hP, bits,
    Nat.lt_of_lt_of_le (Nat.lt_trans hk K.ok.n_enc) (Nat.pow_le_pow_right (by decide) hnw)⟩

/-- `[u]G + [v]Q`, into `R`, by a generator from the table of `u`'s bits and
a kit's windows. -/
theorem kit_pts_ok (K : WAll.Kit c) (h3 : 3 ≤ c.n)
    (hb : (K.bs = EM ∧ K.bK = c.C.b) ∨ (K.bs = B3P ∧ K.bK = 3 * c.C.b)) (hnw : 8 * c.C.len ≤ K.wb * K.nw)
    (hC : Law c.C) {gen : Prog isa} {s₀ : State}
    (hgen : ∀ {s : State} {k : Nat}, Keep c s₀ (s₀.gpr .r6) s → s.syms = s₀.syms → k < 2 ^ (8 * c.C.len) →
      (∀ i < 64 * c.n, s.mem (off (s₀.gpr .r6) (bitsAt c.n 0 + i)) = if k.testBit i then 1 else 0) →
      WP isa gen s (GeneratorPost c (s₀.gpr .r6) k (G c.C) s)) :
    PtsOk c s₀ (pts c gen (c.winCall K.mulP)) :=
  pts_ok K.ok h3 hC (Proof.Ecdh.PPC64LE.Win.mulW_le K) hgen (kit_mul K hb hnw hC)

/-- The verification with points that read a table. -/
theorem verify_ok (hc : CfgOk c) (hL : Law c.C) {tsym : String} {words : List (BitVec 64)} {points : Prog isa}
    (hpts : ∀ {s₀ : State} {T : Addr}, TableMem s₀ T words → s₀.syms tsym = T →
      Region.Disjoint ⟨T, 8 * words.length⟩ ⟨s₀.gpr .r6, 8192⟩ → PtsOk c s₀ points)
    {s : State} (hp : VPre c (stripConsts [(tsym, words)] s)) (hk : ConstsOk [(tsym, words)] 0 s) :
    ∃ t s', Exec isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c points) s t s' ∧ abiPreserved s s' ∧
      VPost c s s' := by
  obtain hpre : VPre c s (constRegs [(tsym, words)] s) := by
    refine ⟨?_, hp.wr, hp.pk_sc, hp.dg_sc, hp.sig_sc, hp.pk_fit, hp.dg_fit, hp.sig_fit, hp.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - [(tsym, words)].length) s.rd, hk.1]
    have e := hp.rd
    simp only [List.append_nil] at e
    exact congrArg (fun rs => rs ++ constRegs [(tsym, words)] s) e
  obtain hd : Region.Disjoint ⟨s.syms tsym, 8 * words.length⟩ ⟨s.gpr .r6, 8192⟩ :=
    hk.disjoint_wr (List.mem_singleton_self _) (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := verifyWith_ok hc hL hpre (hpts (Proof.Ecdsa.PPC64LE.Tab.tableMem hk) rfl hd)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

end VG.Proof.Ecdsa.Verify.PPC64LE.CombWin
