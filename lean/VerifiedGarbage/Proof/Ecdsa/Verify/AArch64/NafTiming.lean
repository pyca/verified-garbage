import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacSave
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPeer

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
variable {c : Cfg}

def nafVariable (c : Cfg) : Prog isa :=
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep c)
    (Naf.window (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg c))

def nafTail (c : Cfg) : Prog isa :=
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.sum c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

/-- Cut both public multiplication loops out of the complete verifier trace. -/
theorem nafVerify_cut {c : Cfg} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.nafVerify c) s t s') :
    ∃ a b d e tp tc ts tw tf, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa (Jacobian.jacComb c.combCfg) a tc b ∧
      Exec isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c)) b ts d ∧
      Exec isa (nafVariable c) d tw e ∧ Exec isa (nafTail c) e tf s' ∧
      t=tp++tc++ts++tw++tf := by
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
                              exact ⟨_,_,_,_,_,_,_,_,_,pre,comb,save,.seq prep win,.seq sum tail,
                                by simp only [List.append_nil,List.append_assoc]⟩

/-- Fixed instruction fragments and the proved public-point loop checks. -/
structure NafVerifyChecks (c : Cfg) : Prop where
  before : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (verifyPrefix c)
  comb : JacCombChecks c.combCfg
  combFinish : FieldCT (Jacobian.jacCombFinish c.combCfg)
  save : FieldCT (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c))
  prep : NafPrepChecks (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg c) (c.sl V)
  window : NafWindowChecks (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg c)
  tail : FieldCT (nafTail c)

/-- Both exceptional-point branches and selected table addresses depend only
on the signature, digest and public key bytes in the original public contract. -/
theorem nafVerify_public_ct (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start) (checks : NafVerifyChecks c) :
    ConstantTime isa (VPre c) (JacPublic c) (Impl.Ecdsa.Verify.AArch64.Cfg.nafVerify c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,d₁,f₁,tp₁,tc₁,ts₁,tw₁,tf₁,ep₁,ec₁,es₁,ew₁,ef₁,et₁⟩ := nafVerify_cut e₁
  obtain ⟨a₂,b₂,d₂,f₂,tp₂,tc₂,ts₂,tw₂,tf₂,ep₂,ec₂,es₂,ew₂,ef₂,et₂⟩ := nafVerify_cut e₂
  have ht := checks.before _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_,_,wp₁,r₁,g₁,m₁⟩ := jacPrefix_ok hc pre₁
  obtain ⟨_,_,wp₂,r₂,g₂,m₂⟩ := jacPrefix_ok hc pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp=a₂.sp := (Exec.rdwr ep₁).2.2.trans
    (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have second : Scr a₂ (s₁.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p a₂.mem (s₁.gpr .x3) ∧
      TCombFixed c.combCfg c.C (s₁.gpr .x3) size a₂ (publicU c s₁) (s₁.syms c.tsym) c.combWords := by
    rw [base,pub.u,pub.table]; exact r₂
  have hpR := unitMod_pow_two hc.p_odd (64*c.n)
  have hmont : c.mont 1<c.C.p := Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hsum := jacComb_sum_ok (base:=s₁.gpr .x3) (tcombLay hc) (combA c) hC hc.am3 hpR hn4 hmont
  obtain ⟨hcTrace,ec,shared⟩ := jacComb_relCT (tcombLay hc) (combA c) hC hc.onG
    (tcombVals hc hC hT) hc.p_lt hpR hn4 checks.comb hsum checks.combFinish
    _ _ _ _ _ _ ⟨r₁.1,second.1,sp,r₁.2.1,second.2.1,r₁.2.2,second.2.2⟩ ec₁ ec₂
  have hsTrace := checks.save _ _ _ _ _ _ trivial trivial shared.public es₁ es₂
  obtain ⟨_,_,wSave₁,sv₁⟩ := jacSave_ok hc hn4 hC hT m₁ r₁
  obtain ⟨_,_,wSave₂,sv₂⟩ := jacSave_ok hc hn4 hC hT m₂ r₂
  obtain ⟨_,rfl⟩ := Exec.det (.seq ec₁ es₁) wSave₁
  obtain ⟨_,rfl⟩ := Exec.det (.seq ec₂ es₂) wSave₂
  have ms₂ : Mid c s₂ (s₁.gpr .x3) g₂ a₂ := by rw [base]; exact m₂
  have vs₂ : JacSavePost c (s₁.gpr .x3) g₂ a₂ d₂ := by rw [base]; exact sv₂
  let P := peerPt c (s₁.mem (s₁.gpr .x0)=4) (keyX c s₁) (keyY c s₁)
  have hp : onCurve c.C P=true := peerPt_onCurve hc _ _ _
  have peer := mid_peer_public pub m₁ ms₂
  have wins : JacWinPublic c (s₁.gpr .x3) P (publicV c s₁) d₁ d₂ := by
    refine ⟨⟨sv₁.scr,⟨g₁,sv₁.fixed⟩,sv₁.px_lt,sv₁.py_lt,?_,?_⟩,
      ⟨vs₂.scr,⟨g₂,vs₂.fixed⟩,vs₂.px_lt,vs₂.py_lt,?_,?_⟩,
      sv₁.sp.trans (sp.trans vs₂.sp.symm),
      sv₁.px.trans (peer.1.trans vs₂.px.symm),sv₁.py.trans (peer.2.trans vs₂.py.symm)⟩
    · rw [sv₁.px,sv₁.py,sv₁.onep]; exact m₁.peer_rep hc hC
    · exact sv₁.v.trans (mid_publicV m₁)
    · rw [vs₂.px,vs₂.py,vs₂.onep]
      change Rep _ _ _ _ (peerPt c _ _ _)
      rw [pub.peerPoint]; exact ms₂.peer_rep hc hC
    · exact vs₂.v.trans ((mid_publicV ms₂).trans pub.v.symm)
  obtain ⟨hwTrace,tailpub⟩ := nafWinMul_relCT hc hn4 hC checks.window hp (nafWinPrep_relCT hc hn4 checks.prep)
    _ _ _ _ _ _ wins ew₁ ew₂
  have hfTrace := checks.tail _ _ _ _ _ _ trivial trivial tailpub ef₁ ef₂
  rw [et₁,et₂,ht,hcTrace,hsTrace,hwTrace,hfTrace]

end VG.Proof.Ecdsa.Verify.AArch64
