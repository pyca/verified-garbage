module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-!
# Timing of verification with `[v]Q` by the public NAF

Two runs with the same public inputs (`JacPublic`: the pointers, the table,
the key, the digest and the signature) leak the same trace
(`pubNafVerify_public_ct`): around the public comb and the public NAF, taint
tracking checks the code with the pointers public; the comb reads the digits
of the public `u` (`publicComb_ct`), and the recoding and the multiplication
the public `v` and `Q` (`pubNafMul_relCT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- One run's state before the recoding of `v`. -/
structure NafWinState (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g, Fixed c base g s.mem
  px : sv c base s PX < c.C.p
  py : sv c base s PY < c.C.p
  rep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) P
  scalar : sv c base s V = k

/-- Two runs multiplying the same point by the same scalar. -/
structure NafWinPublic (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  left : NafWinState c base P k s
  right : NafWinState c base P k t
  sp : s.sp = t.sp
  px : tmv c.C c.n base s (c.sl PX) = tmv c.C c.n base t (c.sl PX)
  py : tmv c.C c.n base s (c.sl PY) = tmv c.C c.n base t (c.sl PY)

theorem NafWinPublic.fields {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (h : NafWinPublic c base P k s t) :
    ∀ x ∈ winRo (winQ c), tmv c.C c.n base s x = tmv c.C c.n base t x := by
  obtain ⟨_, fs⟩ := h.left.fixed
  obtain ⟨_, ft⟩ := h.right.fixed
  intro x hx
  simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · change toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = toM _ _ (wordsVal t.mem base (c.sl AP) c.n)
    rw [fs.ap, ft.ap]
  · change toM _ _ (wordsVal s.mem base (c.sl BM) c.n) = toM _ _ (wordsVal t.mem base (c.sl BM) c.n)
    rw [fs.bm, ft.bm]
  · change toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n) = toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)
    rw [fs.zero, ft.zero]
  · exact h.px
  · exact h.py
  · change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)
    rw [fs.onep, ft.onep]

/-- The recoding of `v` and `[v]Q` use only the public `v` and `Q`. -/
theorem pubNafMul_relCT (hc : CfgOk c) (hn4 : c.n ≠ 4) (hn6 : c.n ≤ 6) (hC : Law c.C)
    (hO : PrimeOrder c.C) (hn17 : 17 ≤ c.C.n)
    (hprep : PubNaf.PrepChecks (winQ c) (c.sl V)) (hwin : PubNaf.WindowChecks (winQ c))
    {base : Addr} {dd : Option (Prog isa)} (hD : PubNaf.NafDblOk (winQ c) c.C base size dd)
    (hT : PubNaf.NafDblCT dd) {P : Point c.C} {k : Nat} (hP : onCurve c.C P = true) :
    RelCT isa (NafWinPublic c base P k)
      (.seq (PubNaf.prep (winQ c) (c.sl V)) (PubNaf.window (winQ c) dd))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  have h7 := hc.n10
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega_arith)
  have hBs := winBits_le c hc.n0
  have hTs := sl_le' c h7 (i := WT) (by decide)
  have hb4 := (winAQ hc).bits4
  intro s t ts tt s' t' hp es et
  obtain ⟨_, fs⟩ := hp.left.fixed
  obtain ⟨_, ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
  cases et with | seq pt wt =>
  have he := (PubNaf.prep_relCT (winQ c) (PubNaf.regs_ok c.n hc.n0 hn6) (base := base)
    (sl_le c h7 (i := V) (by decide)) (sl_mod8 c _) (by omega_arith)
    (by show c.sl WB + (64 * c.n + 1) ≤ size; omega_arith) hprep _ _ _ _ _ _
    ⟨hp.left.scr, hp.right.scr, hp.sp, hp.left.scalar.trans hp.right.scalar.symm⟩ ps pt).1
  obtain ⟨_, _, xs, ss, ms, Fs, vs, sps, -, -, -, -, zs⟩ :=
    pubNafPrep_ok hc hn6 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
  obtain ⟨_, rfl⟩ := Exec.det ps xs
  obtain ⟨_, _, xt, st, mt, Ft, vt, spt, -, -, -, -, -⟩ :=
    pubNafPrep_ok hc hn6 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
  obtain ⟨_, rfl⟩ := Exec.det pt xt
  rw [hp.left.scalar] at Fs
  rw [hp.right.scalar] at Ft
  have Is : Inv (winQ c).M base size c.C.p (· ∈ winSlots (winQ c)) (winRo (winQ c))
      (tmv c.C c.n base _) _ := ⟨ss, ms, winRo_slots _, Fs.ro_lt, fun _ _ => rfl⟩
  have It : Inv (winQ c).M base size c.C.p (· ∈ winSlots (winQ c)) (winRo (winQ c))
      (tmv c.C c.n base _) _ := ⟨st, mt, winRo_slots _, Ft.ro_lt, fun _ _ => rfl⟩
  have pair : FieldPair (winQ c).M base size c.C.p (· ∈ winSlots (winQ c)) (winRo (winQ c)) _ _ _ :=
    ⟨Is, It.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
      sps.trans (hp.sp.trans spt.symm)⟩
  have hk : k < 2 ^ (64 * c.n) := by
    rw [← hp.left.scalar]; exact wordsVal_lt _ _ _ _
  obtain ⟨hw, post⟩ := PubNaf.window_relCT (nafLayQ hc hn4 hn6) (unitMod_pow_two hc.p_odd (64 * c.n))
    hC hc.am3 hc.p_lt (hmont 1) (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl)
    hwin hO hn17 hP hk zs hD hT _ _ _ _ _ _ ⟨pair, ⟨ss, ms, Fs⟩, ⟨st, mt, Ft⟩⟩ ws wt
  exact ⟨by rw [he, hw], post⟩

/-- What the comb and `save` leave for the recoding of `v`. -/
structure SavePost (c : Cfg) (base : Addr) (g : Reg → BitVec 64) (a b : State) : Prop where
  scr : Scr b base size
  fixed : Fixed c base g b.mem
  px_lt : sv c base b PX < c.C.p
  py_lt : sv c base b PY < c.C.p
  px : tmv c.C c.n base b (c.sl PX) = tmv c.C c.n base a (c.sl PX)
  py : tmv c.C c.n base b (c.sl PY) = tmv c.C c.n base a (c.sl PY)
  onep : tmv c.C c.n base b (c.sl ONEP) = tmv c.C c.n base a (c.sl ONEP)
  v : sv c base b V = sv c base a V
  sp : b.sp = a.sp

/-- The public comb and saving `[u]G` leave the public point and `v` as they were. -/
theorem combSave_ok (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    {s₀ a : State} {g : Reg → BitVec 64} (hM : Mid c s₀ (s₀.gpr .x3) g a)
    (hr : CombReady c s₀ a) :
    WP isa (.seq (TCombCfg.comb c.combCfg true) (.block (VG.Impl.Ecdsa.Verify.AArch64.Cfg.save c))) a
      (SavePost c (s₀.gpr .x3) g a) := by
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have WC := tcomb_ok (publicLookup := true) (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC
    hc.am3 hc.onG (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt hr.1 hr.2.1 hr.2.2 (pa := none)
    trivial trivial trivial
  refine WP.seq (WP.mono WC fun b ⟨kb, ub, _, _, _⟩ => ?_)
  have fb := hM.fixed.unch h7 hn fixedOk_tcombW ub
  have sb := hM.scr.of_keepRegs kb (x0_not_tcombClob hc.n10)
  rw [tcombW_eq] at ub
  refine WP.mono (save_ok hc sb) fun d ⟨sd, kd, ud, _, _, _, _, _, _⟩ => ?_
  have fd := fb.unch h7 hn (fixedOk_slW (by decide)) ud
  have subb : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP], i ∈ ptsW := by
    decide
  have subd : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have eqv : ∀ {i}, i < 45 → i ∉ ptsW → sv c (s₀.gpr .x3) d i = sv c (s₀.gpr .x3) a i := fun hi hl =>
    (sv_unch ud h7 hn hi (apart_slW (fun h => hl (subd _ h)))).trans
      (sv_unch ub h7 hn hi (apart_append (apart_slW (fun h => hl (subb _ h))) (apart_zw hi)))
  have eqf : ∀ {i}, i < 45 → i ∉ ptsW →
      tmv c.C c.n (s₀.gpr .x3) d (c.sl i) = tmv c.C c.n (s₀.gpr .x3) a (c.sl i) := by
    intro i hi hl
    change toM _ _ (sv c _ d i) = toM _ _ (sv c _ a i)
    rw [eqv hi hl]
  exact ⟨sd, fd, by rw [eqv (by decide) (by decide)]; exact hM.px_lt,
    by rw [eqv (by decide) (by decide)]; exact hM.py_lt,
    eqf (by decide) (by decide), eqf (by decide) (by decide), eqf (by decide) (by decide),
    eqv (by decide) (by decide), kd.sp.trans kb.sp⟩

/-- The recoding of `v` and `[v]Q`. -/
def pubNafVariable (c : Cfg) (dd : Option (Prog isa)) : Prog isa :=
  .seq (PubNaf.prep (winQ c) (c.sl V)) (PubNaf.window (winQ c) dd)

/-- The sum and the comparison. -/
def pubNafTail (c : Cfg) : Prog isa :=
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.sum c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

/-- Cut the public comb and the public NAF out of the verifier's trace. -/
theorem pubNafVerify_cut {dd : Option (Prog isa)} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.pubNafVerify c dd) s t s') :
    ∃ a b d e tp tc ts tw tf, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa (TCombCfg.comb c.combCfg true) a tc b ∧
      Exec isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c)) b ts d ∧
      Exec isa (pubNafVariable c dd) d tw e ∧ Exec isa (pubNafTail c) e tf s' ∧
      t = tp ++ tc ++ ts ++ tw ++ tf := by
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ep tail => cases ep with
                    | seq bits h => cases h with
                      | seq comb h => cases h with
                        | seq save h => cases h with
                          | seq prep h => cases h with
                            | seq win sum =>
                              have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                              have pre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4
                                (.seq e5 (.seq e6 (.seq e7 (.seq bits (nil _)))))))))
                              exact ⟨_, _, _, _, _, _, _, _, _, pre, comb, save, .seq prep win,
                                .seq sum tail, by simp only [List.append_nil, List.append_assoc]⟩

/-- The pieces whose timing taint tracking checks. -/
structure PubNafVerifyChecks (c : Cfg) : Prop where
  before : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) (verifyPrefix c)
  comb : PublicChecks c.combCfg
  save : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c))
  prep : PubNaf.PrepChecks (winQ c) (c.sl V)
  window : PubNaf.WindowChecks (winQ c)
  tail : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (pubNafTail c)

/-- The comb's lookups depend on the public `u`, and the NAF's branches and
lookups on the public `v` and key: the verifier leaks nothing more than the
contract's public inputs. -/
theorem pubNafVerify_public_ct (hc : CfgOk c) (hn4 : c.n ≠ 4) (hn6 : c.n ≤ 6) (hC : Law c.C)
    (hO : PrimeOrder c.C) (hn17 : 17 ≤ c.C.n)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) (checks : PubNafVerifyChecks c)
    {dd : Option (Prog isa)} (hD : ∀ base, PubNaf.NafDblOk (winQ c) c.C base size dd)
    (hDT : PubNaf.NafDblCT dd) :
    ConstantTime isa (VPre c) (JacPublic c) (Impl.Ecdsa.Verify.AArch64.Cfg.pubNafVerify c dd) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁, b₁, d₁, f₁, tp₁, tc₁, ts₁, tw₁, tf₁, ep₁, ec₁, es₁, ew₁, ef₁, et₁⟩ := pubNafVerify_cut e₁
  obtain ⟨a₂, b₂, d₂, f₂, tp₂, tc₂, ts₂, tw₂, tf₂, ep₂, ec₂, es₂, ew₂, ef₂, et₂⟩ := pubNafVerify_cut e₂
  have ht := checks.before _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_, _, wp₁, r₁, g₁, m₁⟩ := jacPrefix_ok hc pre₁
  obtain ⟨_, _, wp₂, r₂, g₂, m₂⟩ := jacPrefix_ok hc pre₂
  obtain ⟨_, rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_, rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3 = s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp = a₂.sp := (Exec.rdwr ep₁).2.2.trans (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have second : Scr a₂ (s₁.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p a₂.mem (s₁.gpr .x3) ∧
      TCombFixed c.combCfg c.C (s₁.gpr .x3) size a₂ (publicU c s₁) (s₁.syms c.tsym) c.combWords := by
    rw [base, pub.u, pub.table]; exact r₂
  -- The comb.
  have hh := publicComb_ct (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG
    (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt checks.comb _ _ _ _ _ _
    ⟨r₁.1, second.1, sp, r₁.2.1, second.2.1, r₁.2.2, second.2.2⟩ ec₁ ec₂
  have wpComb := fun {s₀ a : State} (h : CombReady c s₀ a) =>
    tcomb_ok (publicLookup := true) (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG
      (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt h.1 h.2.1 h.2.2 (pa := none) trivial trivial trivial
  obtain ⟨_, _, wc₁, keep₁, _⟩ := wpComb r₁
  obtain ⟨_, _, wc₂, keep₂, _⟩ := wpComb r₂
  have db₁ := Exec.det ec₁ wc₁
  have db₂ := Exec.det ec₂ wc₂
  -- `save`.
  have hsTrace := checks.save _ _ _ _ _ _ trivial trivial
    ⟨by rw [db₁.2, db₂.2]; exact keep₁.sp.trans (sp.trans keep₂.sp.symm), fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      rw [db₁.2, db₂.2, keep₁.gpr _ (x0_not_tcombClob hc.n10), keep₂.gpr _ (x0_not_tcombClob hc.n10),
        r₁.1.x0, r₂.1.x0, base]⟩ es₁ es₂
  obtain ⟨_, _, wSave₁, sv₁⟩ := combSave_ok hc hC hT m₁ r₁
  obtain ⟨_, _, wSave₂, sv₂⟩ := combSave_ok hc hC hT m₂ r₂
  obtain ⟨_, rfl⟩ := Exec.det (.seq ec₁ es₁) wSave₁
  obtain ⟨_, rfl⟩ := Exec.det (.seq ec₂ es₂) wSave₂
  -- `[v]Q`.
  have ms₂ : Mid c s₂ (s₁.gpr .x3) g₂ a₂ := by rw [base]; exact m₂
  have vs₂ : SavePost c (s₁.gpr .x3) g₂ a₂ d₂ := by rw [base]; exact sv₂
  let P := peerPt c (s₁.mem (s₁.gpr .x0) = 4) (keyX c s₁) (keyY c s₁)
  have hp : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have peer := mid_peer_public pub m₁ ms₂
  have wins : NafWinPublic c (s₁.gpr .x3) P (publicV c s₁) d₁ d₂ := by
    refine ⟨⟨sv₁.scr, ⟨g₁, sv₁.fixed⟩, sv₁.px_lt, sv₁.py_lt, ?_, ?_⟩,
      ⟨vs₂.scr, ⟨g₂, vs₂.fixed⟩, vs₂.px_lt, vs₂.py_lt, ?_, ?_⟩,
      sv₁.sp.trans (sp.trans vs₂.sp.symm),
      sv₁.px.trans (peer.1.trans vs₂.px.symm), sv₁.py.trans (peer.2.trans vs₂.py.symm)⟩
    · rw [sv₁.px, sv₁.py, sv₁.onep]; exact m₁.peer_rep hc hC
    · exact sv₁.v.trans (mid_publicV m₁)
    · rw [vs₂.px, vs₂.py, vs₂.onep]
      change Rep _ _ _ _ (peerPt c _ _ _)
      rw [pub.peerPoint]; exact ms₂.peer_rep hc hC
    · exact vs₂.v.trans ((mid_publicV ms₂).trans pub.v.symm)
  obtain ⟨hwTrace, tailpub⟩ := pubNafMul_relCT hc hn4 hn6 hC hO hn17 checks.prep checks.window (hD _) hDT hp
    _ _ _ _ _ _ wins ew₁ ew₂
  have hfTrace := checks.tail _ _ _ _ _ _ trivial trivial tailpub ef₁ ef₂
  rw [et₁, et₂, ht, hh.1, hsTrace, hwTrace, hfTrace]

end VG.Proof.Ecdsa.Verify.AArch64
