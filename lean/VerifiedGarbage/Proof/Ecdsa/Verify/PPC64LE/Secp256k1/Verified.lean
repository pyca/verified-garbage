module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Hash
meta import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Contract
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Window
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lays
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulFn
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate

/-!
# ECDSA verification over secp256k1 on PPC64LE: `Verified`

`vg_ecdsa_secp256k1_verify` with `[u]G` by the comb, from its table, a
constant (`abi.withConsts secp256k1CombConsts`), and `[v]Q` by the windows for any
`a`, as P-256's (`Proof/Ecdsa/Verify/PPC64LE/P256Comb.lean`, `Verified.lean`):
`combPts_ok`, `pointsSecp256k1` as `PtsOk` states; `verify_ppc`, from
`verifyWith_ok`; `verify_ct`: the time depends only on the pointers and the
table's address (`taint_decide` with `vectorTaintSym` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.Secp256k1

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.Verify.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdsa.Verify.PPC64LE Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Proof.Weierstrass.PPC64LE.TComb (TableMem)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V UX UY UZ RM')

theorem pointsSecp256k1_eq : pointsSecp256k1 =
    .seq (bits (secp256k1.sl U) (bitsAt secp256k1.n 0) (8 * secp256k1.n)) (.seq
      (.block (VG.Impl.Mont.PPC64LE.setConst secp256k1.n (secp256k1.sl EM) (secp256k1.mont secp256k1.C.b)))
      (.seq mulGeneratorSecp256k1 (.seq (.block (Cfg.save secp256k1)) (.seq (bits (secp256k1.sl V) (bitsAt secp256k1.n 0) (8 * secp256k1.n))
        (.seq (WindowA.Cfg.mul secp256k1 PX PY B3P) (Cfg.sum secp256k1)))))) := rfl

/-- `[u]G + [v]Q` by the comb and windows, with the comb's table at `T`. -/
theorem combPts_ok (hC : Law Spec.Secp256k1.curve) {s₀ : State} {T : Addr}
    (ht : TableMem s₀ T secp256k1CombWords) (sym : s₀.syms secp256k1Comb.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * secp256k1CombWords.length⟩ ⟨s₀.gpr .r6, 8192⟩) :
    PtsOk secp256k1 s₀ pointsSecp256k1 := by
  intro s hM syms P hP hQ rest Q h
  have hc := secp256k1_ok
  have hn := hM.ws.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * secp256k1.n)
  have hmont : ∀ x, secp256k1.mont x < secp256k1.C.p := fun x => Nat.mod_lt _ (by decide)
  rw [pointsSecp256k1_eq]
  refine WP.seq ?_
  -- `u`'s bits.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (tbl_bits_ok hc hM.ws (i := U) (j := 0) (by decide)
    (by decide)) fun s₁ h => h) fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have K₁ := hM.toKeep.step (by decide) (k₁.rk (rs' := bitsClob)) (hU := O₁.unch)
    (hW := fixedOk_tbl (by decide) 0) (hWs := by decide)
  -- `b R mod p` at `EM`.
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (setSl_ok hc K₁.ws (o := EM) (x := secp256k1.mont secp256k1.C.b)
    (by decide) (Nat.lt_trans (hmont _) hc.p_lt)) fun s₂ h => h) fun s₂ ⟨_, k₂, O₂⟩ sy₂ => ?_)
  have K₂ := K₁.step (by decide) (k₂.rk (rs' := [.r11])) (hU := O₂.unch)
    (hW := fixedOk_slW (l := [EM]) (by decide)) (hWs := by decide)
  -- `[u]G` by the comb.
  have ht₂ : TableMem s₂ T secp256k1CombWords :=
    ht.unch (by rw [K₂.rk.rd, K₂.rk.wr]) K₂.whole (by decide) hd
  have ht' : TableMem s₂ T (TComb.tableWords secp256k1Comb Spec.Secp256k1.curve VG.Impl.Secp256k1.secp256k1Comb7) := by
    rw [Proof.Secp256k1.PPC64LE.comb_words_eq]; exact ht₂
  have hd' : Region.Disjoint ⟨T, 8 * (TComb.tableWords secp256k1Comb Spec.Secp256k1.curve VG.Impl.Secp256k1.secp256k1Comb7).length⟩
      ⟨s₀.gpr .r6, 8192⟩ := by
    rw [Proof.Secp256k1.PPC64LE.comb_words_eq]; exact hd
  have bu : ∀ i < 64 * secp256k1.n, s₂.mem (off (s₀.gpr .r6) (bitsAt secp256k1.n 0 + i)) =
      if (sv secp256k1 (s₀.gpr .r6) s U).testBit i then 1 else 0 := fun i hi => by
    rw [tbl_unch O₂.unch (by decide) (j := 0) (by decide) hi (tbl_apart_slW (c := secp256k1) (l := [EM]) (by decide) (by decide) 0 i)]
    exact b₁ i hi
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.mono (TComb.comb_ok secp256k1Comb (Proof.Secp256k1.PPC64LE.comb_config hC) hC
    hc.onG K₂.ws ht' (by rw [sy₂, sy₁, syms, sym]) hd' (k := sv secp256k1 (s₀.gpr .r6) s U)
    (Nat.lt_trans hM.u_lt hc.n_enc) K₂.fixed.zero (fun i hi => bu i (by
      have : i < 8 * Spec.Secp256k1.curve.len := hi
      exact Nat.lt_of_lt_of_le this (by decide))) K₂.fixed.ap K₂.fixed.b3p) fun s₃ h => h)
    fun s₃ ⟨k₃, U₃, L₃, R₃⟩ sy₃ => ?_)
  have K₃ := K₂.step (by decide) k₃ (hU := U₃.cover Proof.Secp256k1.PPC64LE.comb_writes_cover)
    (hW := (fixedOk_ladWp (by decide) (by decide) GX GY).append (fixedOk_genX (by decide)))
    (hWs := VG.Proof.Ecdh.PPC64LE.le_append (ladWp_le (by decide) (by decide) GX GY) (genX_le (by decide)))
  -- A slot apart from what a step writes keeps its number.
  have sl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' → ∀ {i : Nat}, i < 45 →
      (∀ w ∈ W, secp256k1.sl i + 8 * secp256k1.n ≤ w.1 ∨ w.1 + w.2 ≤ secp256k1.sl i) →
      wordsVal m' (s₀.gpr .r6) (secp256k1.sl i) secp256k1.n = wordsVal m (s₀.gpr .r6) (secp256k1.sl i) secp256k1.n :=
    fun {_ _ _} U {_} hi hW => sv_unch (c := secp256k1) U (by decide) hn hi hW
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
  have v₄ : sv secp256k1 (s₀.gpr .r6) s₄ V = sv secp256k1 (s₀.gpr .r6) s V :=
    (sl U₄ (by decide) (by decide)).trans ((sl U₃ (by decide) (by decide)).trans
      ((sl O₂.unch (by decide) (by decide)).trans (sl O₁.unch (by decide) (by decide))))
  have keep5 : ∀ {i : Nat}, i < 45 → i ∈ [PX, PY] →
      sv secp256k1 (s₀.gpr .r6) s₅ i = sv secp256k1 (s₀.gpr .r6) s i := fun {i} hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact (sl O₅.unch hi (by decide)).trans ((sl U₄ hi (by decide)).trans ((sl U₃ hi (by decide)).trans
        ((sl O₂.unch hi (by decide)).trans (sl O₁.unch hi (by decide)))))
  have F₅ := K₅.fixed
  have gQ : Window.Secp256k1.PtOk (s₀.gpr .r6) s₅ Window.Secp256k1.gPt P :=
    Window.Secp256k1.PtOk.of_eq ⟨hQ, hM.px_lt, hM.py_lt, lt_of_eq_of_lt hM.fixed.onep (Nat.mod_lt _ (by decide))⟩
      (keep5 (by decide) (by simp)) (keep5 (by decide) (by simp))
      (F₅.onep.trans hM.fixed.onep.symm)
  have bv : Window.Bits (s₀.gpr .r6) s₅ (sv secp256k1 (s₀.gpr .r6) s V) := fun t ht => by
    rw [← v₄]; exact b₅ t ht
  -- `[v]Q` by the windows.
  refine WP.seq (WP.mono (Window.Secp256k1.mul_ok hC ⟨K₅.ws, ⟨F₅.ap, F₅.b3p, F₅.zero, F₅.onep⟩, gQ, hP, bv,
    Nat.lt_trans hM.v_lt (by decide)⟩) fun s₆ ⟨k₆, U₆, R₆⟩ => ?_)
  have K₆ := K₅.step (by decide) k₆ (hU := U₆) (hW := fun w hw => by
      simp only [Window.Secp256k1.mulW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact Or.inr (by decide)) (hWs := by decide)
  -- `U`, `[u]G`, through the save and the windows.
  have uS : ∀ {i j : Nat}, i ∈ [UX, UY, UZ] → sv secp256k1 (s₀.gpr .r6) s₄ i = sv secp256k1 (s₀.gpr .r6) s₃ j →
      sv secp256k1 (s₀.gpr .r6) s₆ i = sv secp256k1 (s₀.gpr .r6) s₃ j := fun {i _} hi e => by
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
      (∀ w ∈ W, w.1 + w.2 ≤ 4352 ∨ 4608 ≤ w.1) → ∀ t < 64 * secp256k1.n,
      m' (off (s₀.gpr .r6) (bitsAt secp256k1.n 1 + t)) = m (off (s₀.gpr .r6) (bitsAt secp256k1.n 1 + t)) :=
    fun {_ _ _} U hW t ht => tbl_unch U (by decide) (j := 1) (by decide) ht (fun w hw => by
      have := hW w hw; have : t < 256 := ht; show 4352 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ 4352 + t; omega)
  have fl : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch (s₀.gpr .r6) W m m' →
      (∀ w ∈ W, secp256k1.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ secp256k1.sl FLAG) →
      word m' (s₀.gpr .r6) (secp256k1.sl FLAG) = word m (s₀.gpr .r6) (secp256k1.sl FLAG) :=
    fun {_ _ _} U hW => U.word hW (by decide)
  have ha : tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl AP) = Fin.ofNat secp256k1.C.p secp256k1.C.a := by
    show toM _ _ (wordsVal _ _ (secp256k1.sl AP) secp256k1.n) = _; rw [F₆.ap]; exact toM_cmont hc _
  have hb : tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl B3P) = Fin.ofNat secp256k1.C.p (3 * secp256k1.C.b) := by
    show toM _ _ (wordsVal _ _ (secp256k1.sl B3P) secp256k1.n) = _; rw [F₆.b3p]; exact toM_cmont hc _
  have tU : ∀ {i j : Nat}, sv secp256k1 (s₀.gpr .r6) s₆ i = sv secp256k1 (s₀.gpr .r6) s₃ j →
      tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl i) = tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₃ (secp256k1.sl j) :=
    fun e => by show toM _ _ (sv secp256k1 _ _ _) = toM _ _ (sv secp256k1 _ _ _); rw [e]
  have hU1 : Rep secp256k1.C (tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl UX))
      (tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl UY)) (tmv secp256k1.C secp256k1.n (s₀.gpr .r6) s₆ (secp256k1.sl UZ))
      (mul (sv secp256k1 (s₀.gpr .r6) s U) (G secp256k1.C)) := by
    rw [tU ux, tU uy, tU uz]; exact R₃
  have rm₇ : sv secp256k1 (s₀.gpr .r6) s₇ RM' = sv secp256k1 (s₀.gpr .r6) s RM' :=
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


theorem pre_of {s : State} (h : verifyPPC.pre s) : VPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x8000, 8192⟩]

/-- `verifyPPC` states `verifyContract`'s facts by name. -/
theorem verifyPPC_implies : verifyPPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst PPC64LE.abi) :=
  { pre := by
      sig_implies_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    post := by
      intro s s' _ h
      sig_post [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
      simp only [verifyPPC, vf, Spec.Secp256k1.curve] at h
      revert h
      split <;> rename_i hv <;> simp only [hv, ite_true, ite_false, Bool.false_eq_true] <;>
        exact fun h => by rw [h]; rfl
    pub := by
      sig_implies_pub [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
    sat := by
      sig_implies_sat [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract,
        Proof.Ecdsa.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, verifyPPC, vf,
        PPC64LE.abi, PPC64LE.argRegs]
        [satState] using satState }

/-- The verification's contract with the comb's table, as the proof states it. -/
def vPC : Contract isa where
  pre s := verifyPPC.pre (stripConsts secp256k1CombConsts s) ∧ ConstsOk secp256k1CombConsts 0 s
  post := verifyPPC.post
  pub s₁ s₂ := verifyPPC.pub s₁ s₂ ∧ s₁.syms secp256k1Comb.tsym = s₂.syms secp256k1Comb.tsym

theorem verify_ppc (hL : Weierstrass.Law Spec.Secp256k1.curve) (s : State) (hs : vPC.pre s) :
    ∃ t s', Exec isa verifySecp256k1 s t s' ∧ abiPreserved s s' ∧ vPC.post s s' := by
  obtain ⟨hp, hk⟩ := hs
  have p := pre_of hp
  have hpre : VPre secp256k1 s (constRegs secp256k1CombConsts s) := by
    refine ⟨?_, p.wr, p.pk_sc, p.dg_sc, p.sig_sc, p.pk_fit, p.dg_fit, p.sig_fit, p.sc_fit⟩
    rw [← List.take_append_drop (s.rd.length - secp256k1CombConsts.length) s.rd, hk.1]
    have e := p.rd
    simp only [List.append_nil] at e
    exact congrArg (fun rs => rs ++ constRegs secp256k1CombConsts s) e
  have member : (secp256k1Comb.tsym, secp256k1CombWords) ∈ secp256k1CombConsts := List.mem_singleton_self _
  have ht : VG.Proof.Weierstrass.PPC64LE.TComb.TableMem s (s.syms secp256k1Comb.tsym) secp256k1CombWords :=
    ⟨hk.fit member, ⟨_, List.mem_append_left _ (hk.mem_rd member), Region.contains_self _ _⟩,
      fun i hi => hk.readW member hi⟩
  have hd : Region.Disjoint ⟨s.syms secp256k1Comb.tsym, 8 * secp256k1CombWords.length⟩ ⟨s.gpr .r6, 8192⟩ :=
    hk.disjoint_wr member (by rw [hpre.wr]; simp)
  obtain ⟨t, s', he, K, hpost⟩ := verifyWith_ok secp256k1_ok hL hpre (combPts_ok hL ht rfl hd)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, hpost⟩

theorem verify_ct : ConstantTime isa vPC.pre vPC.pub verifySecp256k1 :=
  VG.Taint.constantTime (A := vectorTaintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5, h6⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact sy⟩)
    (by taint_decide)

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def vSatMem : Mem := constMem 0x100000 secp256k1CombWords

theorem vSatMem_held : ∀ i < secp256k1CombWords.length,
    vSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = secp256k1CombWords.getD i 0 := by
  unfold vSatMem
  exact constMem_held _ _ (by rw [Proof.Secp256k1.PPC64LE.comb_words_length]; omega)

/-- A state satisfying the precondition with the table. -/
def vSatC : State :=
  { satState with mem := vSatMem, rd := satState.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem combConsts_eq : secp256k1CombConsts = [(secp256k1Comb.tsym, secp256k1CombWords)] := rfl

theorem vSat : (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (abi.withConsts secp256k1CombConsts)).pre vSatC := by
  have hl := Proof.Secp256k1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, secp256k1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : vSatC = s
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Secp256k1.curve,
    Spec.Ecdsa.scratchWords, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x8000, 8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem vPC_implies :
    vPC.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (abi.withConsts secp256k1CombConsts)) :=
  { pre := fun _ hs => ⟨verifyPPC_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (verifyPPC_implies.post (stripConsts secp256k1CombConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨verifyPPC_implies.pub (stripConsts secp256k1CombConsts s₁)
        (stripConsts secp256k1CombConsts s₂) (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨vSatC, vSat⟩ }

theorem verify_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified PPC64LE.target verifySecp256k1
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (PPC64LE.abi.withConsts secp256k1CombConsts)) :=
  Verified.of_correct (verify_ppc hL) verify_ct vPC_implies

/-- A state satisfying `verifyHashContract`'s precondition with the table, with an empty hash. -/
def hSatC : State :=
  let h := Hash.hashSatState 32
  { h with mem := vSatMem, rd := h.rd ++ [⟨0x100000, 151552⟩], syms := fun _ => 0x100000 }

theorem verifyHash_sat :
    ∃ s, (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (PPC64LE.abi.withConsts secp256k1CombConsts) 112).pre s := by
  refine ⟨hSatC, ?_⟩
  have hl := Proof.Secp256k1.PPC64LE.comb_words_length
  have held := vSatMem_held
  rw [combConsts_eq]
  obtain ⟨W, eW⟩ : ∃ W, secp256k1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : hSatC = s
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.Secp256k1.inst,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_,
    Region.disjoint_of_sep (by decide), by decide, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x8000, 8192⟩] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_p256_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified PPC64LE.target
      (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false verifySecp256k1)
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (PPC64LE.abi.withConsts secp256k1CombConsts) 112) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.secp256k1_len (by decide)
    (verify_verified hL) (by taint_decide) verifyHash_sat

end VG.Proof.Ecdsa.Verify.PPC64LE.Secp256k1
