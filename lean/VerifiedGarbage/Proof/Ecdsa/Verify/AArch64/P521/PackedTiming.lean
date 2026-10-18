module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Timing of verification with `[v]Q` by the public NAF

Two runs with the same public inputs (`JacPublic`: the pointers, the table,
the key, the digest and the signature) leak the same trace
(`packedNafVerify_public_ct`): around the public comb and the public NAF, taint
tracking checks the code with the pointers public; the comb reads the digits
of the public `u` (`publicComb_ct`), and the recoding and the multiplication
the public `v` and `Q` (`packedNafMul_relCT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- The recoding of `v` and `[v]Q` use only the public `v` and `Q`. -/
theorem packedNafMul_relCT (hc : CfgOk c) (hn9 : c.n = 9) (hC : Law c.C)
    (hO : PrimeOrder c.C) (hn17 : 17 ≤ c.C.n)
    (hprep : PubNaf.PrepChecks (packedQ c) (c.sl V)) (hwin : PubNaf.WindowChecks (packedQ c))
    {base : Addr} {P : Point c.C} {k : Nat} (hP : onCurve c.C P = true) :
    RelCT isa (NafWinPublic c base P k)
      (.seq (PubNaf.prep (packedQ c) (c.sl V)) (PubNaf.window (packedQ c)))
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
  have he := (PubNaf.prep_relCT (packedQ c) (PubNaf.regs_ok9 c.n hc.n0 (by omega)) (base := base)
    (sl_le c h7 (i := V) (by decide)) (sl_mod8 c _) (by change c.sl WB < 4096; change c.sl WB + 3 < 4096 at hb4; omega)
    (by change c.sl WB + (64 * c.n + 1) ≤ size; rw [sl_eq c WB (by decide),hn9]; decide) hprep _ _ _ _ _ _
    ⟨hp.left.scr, hp.right.scr, hp.sp, hp.left.scalar.trans hp.right.scalar.symm⟩ ps pt).1
  obtain ⟨_, _, xs, ss, ms, Fs, vs, sps, -, -, -, -, zs⟩ :=
    packedPrep_ok hc hn9 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
  obtain ⟨_, rfl⟩ := Exec.det ps xs
  obtain ⟨_, _, xt, st, mt, Ft, vt, spt, -, -, -, -, -⟩ :=
    packedPrep_ok hc hn9 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
  obtain ⟨_, rfl⟩ := Exec.det pt xt
  rw [hp.left.scalar] at Fs
  rw [hp.right.scalar] at Ft
  have Is : Inv (packedQ c).M base size c.C.p (· ∈ winSlots (packedQ c)) (winRo (packedQ c))
      (tmv c.C c.n base _) _ := ⟨ss, ms, winRo_slots _, Fs.ro_lt, fun _ _ => rfl⟩
  have It : Inv (packedQ c).M base size c.C.p (· ∈ winSlots (packedQ c)) (winRo (packedQ c))
      (tmv c.C c.n base _) _ := ⟨st, mt, winRo_slots _, Ft.ro_lt, fun _ _ => rfl⟩
  have pair : FieldPair (packedQ c).M base size c.C.p (· ∈ winSlots (packedQ c)) (winRo (packedQ c)) _ _ _ :=
    ⟨Is, It.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
      sps.trans (hp.sp.trans spt.symm)⟩
  have hk : k < 2 ^ (64 * c.n) := by
    rw [← hp.left.scalar]; exact wordsVal_lt _ _ _ _
  obtain ⟨hw, post⟩ := PubNaf.window_relCT (packedNafLay hc hn9) (unitMod_pow_two hc.p_odd (64 * c.n))
    hC hc.am3 hc.p_lt (hmont 1) (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl)
    hwin hO hn17 hP hk zs _ _ _ _ _ _ ⟨pair, ⟨ss, ms, Fs⟩, ⟨st, mt, Ft⟩⟩ ws wt
  exact ⟨by rw [he, hw], post⟩

/-- The recoding of `v` and `[v]Q`. -/
def packedNafVariable (c : Cfg) : Prog isa :=
  .seq (PubNaf.prep (packedQ c) (c.sl V)) (PubNaf.window (packedQ c))

/-- The sum and the comparison. -/
def pubNafTail (c : Cfg) : Prog isa :=
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.sum c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

/-- Cut the public comb and the public NAF out of the verifier's trace. -/
theorem packedNafVerify_cut {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.packedNafVerify c) s t s') :
    ∃ a b d e tp tc ts tw tf, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa (TCombCfg.comb c.combCfg true) a tc b ∧
      Exec isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c)) b ts d ∧
      Exec isa (packedNafVariable c) d tw e ∧ Exec isa (pubNafTail c) e tf s' ∧
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
structure PackedNafVerifyChecks (c : Cfg) : Prop where
  before : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) (verifyPrefix c)
  comb : PublicChecks c.combCfg
  save : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c))
  prep : PubNaf.PrepChecks (packedQ c) (c.sl V)
  window : PubNaf.WindowChecks (packedQ c)
  tail : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (pubNafTail c)

/-- The comb's lookups depend on the public `u`, and the NAF's branches and
lookups on the public `v` and key: the verifier leaks nothing more than the
contract's public inputs. -/
theorem packedNafVerify_public_ct (hc : CfgOk c) (hn9 : c.n = 9) (hC : Law c.C)
    (hO : PrimeOrder c.C) (hn17 : 17 ≤ c.C.n)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) (checks : PackedNafVerifyChecks c) :
    ConstantTime isa (VPre c) (JacPublic c) (Impl.Ecdsa.Verify.AArch64.Cfg.packedNafVerify c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁, b₁, d₁, f₁, tp₁, tc₁, ts₁, tw₁, tf₁, ep₁, ec₁, es₁, ew₁, ef₁, et₁⟩ := packedNafVerify_cut e₁
  obtain ⟨a₂, b₂, d₂, f₂, tp₂, tc₂, ts₂, tw₂, tf₂, ep₂, ec₂, es₂, ew₂, ef₂, et₂⟩ := packedNafVerify_cut e₂
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
  obtain ⟨hwTrace, tailpub⟩ := packedNafMul_relCT hc hn9 hC hO hn17 checks.prep checks.window hp
    _ _ _ _ _ _ wins ew₁ ew₂
  have hfTrace := checks.tail _ _ _ _ _ _ trivial trivial tailpub ef₁ ef₂
  rw [et₁, et₂, ht, hh.1, hsTrace, hwTrace, hfTrace]

end VG.Proof.Ecdsa.Verify.AArch64.P521
