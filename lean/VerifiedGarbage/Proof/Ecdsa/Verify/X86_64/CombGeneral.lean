module

-- separate module: generic over the curve, for every curve whose `a` is not `-3` (brainpoolP384r1's and brainpoolP512r1's verification next), and not imported by the other curves' verification proofs
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.CombGeneral
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Points
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombGeneral
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFinal
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-!
# ECDSA verification on x86-64 with a comb for any `a`

`Cfg.verifyG d` (`Impl/Ecdsa/Verify/X86_64/CombGeneral.lean`) is `Cfg.verify`
with `[u]G` by the signature's comb for any `a` (`Cfg.gMulG d`), so its proof
is `verify_ok`'s (`Proof/Ecdsa/Verify/X86_64/Main.lean`) with the points'
(`pointsG_ok`), which is `pointsL_ok`'s (`Proof/Ecdsa/Verify/X86_64/Points.lean`)
with `[u]G` by `gMulG_ok'` (`Proof/Ecdsa/X86_64/CombGeneral.lean`) from the
tables of `d`, which the configuration declares as its `gtab`
(`tbl_of_held_mem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

/-- `[u]G + [v]Q`, into `R`, `[u]G` by the comb of `d` (`gMulG_ok'`): `pointsL_ok`'s proof. -/
theorem pointsG_ok (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) (hcd : c.gtab = some d) {s₀ : State} {base : Addr}
    {g : Reg → BitVec 64} {s : State} (hM : Mid c s₀ base g s) (htb : TblsHeld c s₀ s₀.wr)
    (hsc : (⟨base, size⟩ : Region) ∈ s₀.wr)
    (hrdT : ∀ r ∈ Abi.constRegions (fun n => s₀.syms n) c.combConsts, r ∈ s₀.rd)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base g (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.pointsG c d).inline rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_apart_bits c hi (.inr (.inl (by decide))) _ (by omega_arith)
  unfold Impl.Ecdsa.Verify.X86_64.Cfg.pointsG
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega_arith) (sl_le c h7 (i := U) (by decide))
    (bitsAt_le c h7 (j := 0) (by decide)) (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  have hTb : TblMem s₁ (s₁.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s₁.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
    rw [sy₁, hM.syms]
    refine tbl_of_held_mem (gtab_mem_consts hcd) htb hsc (fun r hr => by rw [k₁.rd, hM.rd]; exact hrdT r hr) ?_
    have hb0 := bitsAt_le c h7 (j := 0) (by decide)
    exact Unch.cover (hM.unch.trans U₁) fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.mem_singleton_self _, Nat.zero_le _, by dsimp only; omega_arith⟩
  refine WP.seq (WP.mono (gMulG_ok' hc hC hd hW hs₁ F₁ (k := sv c base s U) (wordsVal_lt _ _ _ _)
    (fun t ht => b₁ t ht) hTb.1 hTb.2)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs K₂ (rdi_not_powClob _)
  have F₂ := F₁.unch h7 hn fixedOk_gW U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₂ : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM], i ∈ ptsW := by
    decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_gW hi (fun h => hl (sub₂ _ h))))).trans (v₁ hi)
  -- `[v]P`.
  have tv₃ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _)
      rw [W₃ hi hl]
  refine mulV_ok hc hC hs₃ F₃ hP (by rw [W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [tv₃ (by decide) (by decide), tv₃ (by decide) (by decide), tv₃ (by decide) (by decide)]; exact hrep)
    rx₃ ry₃ rz₃ (by rw [W₃ (by decide) (by decide)]; exact Nat.lt_of_lt_of_le hM.v_lt hc.n_bits)
    fun s₅ V₅ => ?_
  rw [show sv c base s₃ V = sv c base s V from W₃ (by decide) (by decide)] at V₅
  have hs₅ := V₅.scr
  have F₅ := F₃.unch h7 hn fixedOk_vW V₅.unch
  have v₅ : ∀ {i}, i < 45 → i ∉ vI → sv c base s₅ i = sv c base s₃ i := fun hi hl =>
    sv_unch V₅.unch h7 hn hi (apart_vW hi hl)
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact v₅ (by decide) (by decide)
  refine WP.mono (sum_ok hc hs₅ V₅.mod (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rx₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact V₅.lt _ (List.mem_cons_self ..)
    · exact V₅.lt _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact V₅.lt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have v₆ : ∀ {i}, i < 45 → i ∉ ptsW → i ∉ vI → sv c base s₆ i = sv c base s i := fun hi hl hl' =>
    (sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))).trans ((v₅ hi hl').trans (W₃ hi hl))
  have UW : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c)) s.mem s₆.mem := by
    have sl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slW c l,
        ∃ w' ∈ [(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c), w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
      fun hl w hw => ⟨w, List.mem_append_right _ (List.mem_append_left _
        (List.map_subset _ (fun i hi => hl i hi) hw)), Nat.le_refl _, Nat.le_refl _⟩
    have tb0 : ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)],
        ∃ w' ∈ [(bitsAt c.n 0, 64 * c.n + 8)] ++ (slW c ptsW ++ vW c), w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
      fun w hw => by
        rw [List.mem_singleton.mp hw]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Nat.le_refl _, by dsimp only; omega_arith⟩
    refine Unch.cover (U₁.trans (U₂.trans (U₃.trans (V₅.unch.trans U₆)))) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw | hw | hw
    · exact tb0 w hw
    · exact sl sub₂ w hw
    · rw [List.mem_singleton.mp hw]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), by dsimp only; omega_arith,
        by dsimp only; omega_arith⟩
    · exact sl sub₃ w hw
    · exact ⟨w, List.mem_append_right _ (List.mem_append_right _ hw), Nat.le_refl _, Nat.le_refl _⟩
    · exact sl sub₆ w hw
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), W₃ (by decide) (by decide)]
  have ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  have hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  refine ⟨hs₆, by rw [wr₆, V₅.keep.wr, k₃.wr, K₂.wr, k₁.wr, hM.wr],
    by rw [rd₆, V₅.keep.rd, k₃.rd, K₂.rd, k₁.rd, hM.rd], F₆,
    by rw [v₆ (i := K) (by decide) (by decide) (by decide), hM.k], fun h9 t ht => ?_, ?_,
    by rw [v₆ (by decide) (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₆ (by decide) (by decide) (by decide)]; exact hM.rm, rx₆, rz₆,
    ⟨_, _, _, _, _, _, q₂, V₅.q, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]⟩, ?_⟩
  · rw [tbl_unch UW h7 hn (j := 1) (by decide) ht (apart_append (fun w hw => by
      rw [List.mem_singleton.mp hw]; simp only [bitsAt_eq]; exact Or.inr (by omega_arith))
      (apart_append (fun w hw => by
        rcases List.mem_cons.mp hw with he | hw
        · rw [he]; simp only [bitsAt_eq, sl_eq c 62]
          have := hc.n0
          omega_arith
        · exact tbl_apart_slW (l := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
            TX, TY, TZ, PT, TMP, UX, UY, UZ, EM]) (by decide) 1 t ht (by omega_arith) (by decide) w hw)
        (tbl₁_apart_vW h9 ht)))]
    exact hM.t₁ h9 t ht
  · rw [UW.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)]
    · exact hM.flag
    · rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
        have := sl_below_bits c (i := FLAG) (by decide) 0 0
        exact Or.inl (by dsimp only; omega_arith)
      · rcases List.mem_append.mp hw with hw | hw
        · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
            (fun h => Or.inl (by omega_arith)) (fun h => Or.inr h)
        · exact (apart_vW (c := c) (i := FLAG) (by decide) (by decide)) w hw |>.elim
            (fun h => Or.inl (by omega_arith)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | hw | hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
    · rw [List.mem_singleton.mp hw]; have := bitsAt_le_pad c h7 (j := 0) (by decide); dsimp only; omega_arith
    · exact slW_le84 h7 (by decide) w hw
    · exact vW_le h7 w hw

/-- `verifyG d` inlined, as `verify_inline`. -/
theorem verifyG_inline (c : Cfg) (d : CombData) : (Impl.Ecdsa.Verify.X86_64.Cfg.verifyG c d).inline =
    .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
      (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.check c).inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline
      (.seq c.nPow.inline (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline
      (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.pointsG c d).inline
        (Impl.Ecdsa.Verify.X86_64.Cfg.tail c).inline)))))))) := by
  show Code.seq _ (Code.seq _ (Code.seq _ (Code.seq _ (Code.seq (Impl.Ecdh.X86_64.Cfg.check c).inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline (Code.seq c.nPow.inline
    (Code.seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline _))))))) = _
  rfl

/-- `verifyG d` returns whether the specification's verification holds, and
restores the callee-saved registers: `verify_ok`'s proof, with `pointsG_ok`. -/
theorem verifyG_ok (hc : BaseCfgOk c) (hC : Law c.C) {d : CombData} (hd : CombOk c d)
    (hW : CombOkW c.C d.w (c.combJ d.w) d.tbl d.start) (hcd : c.gtab = some d) {s₀ : State}
    (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.verifyG c d).inline s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [verifyG_inline]
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  obtain ⟨-, -, h1⟩ := consts_tmv hc F₂
  -- The point the second ladder multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .rdi) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine pointsG_ok hc hC hd hW hcd hM hp.tbls (by rw [hp.wr]; simp) (fun r hr => by rw [hp.rd]; simp [hr]) hPc hQ
    fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved, xo, hxo, hx, rax⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr), ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1 q2 hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .rdi)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .rcx) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .rcx) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, rax]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .rcx) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86_64
