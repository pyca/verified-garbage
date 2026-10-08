import VerifiedGarbage.Proof.P256.EcdhJac.Lit
import VerifiedGarbage.Proof.P256.EcdhJac.Prefix
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64

theorem keepsV : Impl.P256.EcdhJac.exchange.allInstrs AArch64.keepsV = true := by lit_decide

theorem middle_callsKeep : CallsKeep finish := by lit_decide

theorem middle_keepsUntouched : KeepsUntouched finish := by lit_decide

abbrev Public := AArch64.Taint.Agree (Taint.ofRegs [.x0,.x20])
abbrev Ready (s t : State) : Prop := MulInput p256 s ∧ MulInput p256 t ∧ Public s t

theorem before_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) before :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem multiply_ct : ConstantTime isa (fun _ => True) Public multiply :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem finish_ct : ConstantTime isa (fun _ => True) Public finish :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem before_relCT (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds) :
    RelCT isa (fun s t => ecdhAArch64.pre s ∧ ecdhAArch64.pre t ∧ ecdhAArch64.pub s t)
      before Ready := by
  intro s t ts tt s' t' ⟨ps,pt,h0,h1,h2,h3,hsp⟩ es et
  obtain ⟨_,_,es',hs,xs,os⟩ := Frontend.beforeMul_ok (p256_ok hI) hL (pre_of ps)
  obtain ⟨_,_,et',ht,xt,ot⟩ := Frontend.beforeMul_ok (p256_ok hI) hL (pre_of pt)
  obtain ⟨_,rfl⟩ := es.det es'
  obtain ⟨_,rfl⟩ := et.det et'
  have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t := by
    refine ⟨hsp,?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  refine ⟨before_ct _ _ _ _ _ _ trivial trivial pub es et,hs,ht,
    (Exec.sp es).trans (hsp.trans (Exec.sp et).symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact xs.trans (h3.trans xt.symm)
  · exact os.trans (h0.trans ot.symm)

/-- Recover the public output pointer after its round trip through private scratch. -/
theorem multiply_relCT (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) : RelCT isa Ready multiply Public := by
  intro s t ts tt s' t' ⟨⟨bs,gs,ps,hss,fs,hps,lxs,lys,reps⟩,
    ⟨bt,gt,pt,hst,ft,hpt,lxt,lyt,rept⟩,hp⟩ es et
  have ws := hm hss fs hps lxs lys reps (rest:=.block [])
    (R:=fun u => MulPost p256 bs gs ps (sv p256 bs s K) s u) (fun _ h => WP.block_nil h)
  have wt := hm hst ft hpt lxt lyt rept (rest:=.block [])
    (R:=fun u => MulPost p256 bt gt pt (sv p256 bt t K) t u) (fun _ h => WP.block_nil h)
  obtain ⟨_,_,xs,hs⟩ := WP.assoc' ws
  obtain ⟨_,_,xt,ht⟩ := WP.assoc' wt
  have esn : Exec isa (.seq multiply (.block [])) s (ts++[]) s' := .seq es (.block rfl)
  have etn : Exec isa (.seq multiply (.block [])) t (tt++[]) t' := .seq et (.block rfl)
  obtain ⟨_,rfl⟩ := esn.det xs
  obtain ⟨_,rfl⟩ := etn.det xt
  refine ⟨multiply_ct _ _ _ _ _ _ trivial trivial hp es et,
    (Exec.sp es).trans (hp.1.trans (Exec.sp et).symm),?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.scr.x0.trans (hss.x0.symm.trans ((hp.2 _ (by simp [Taint.mem_ofRegs])).trans
      (hst.x0.trans ht.scr.x0.symm)))
  · exact hs.x20.trans ((hp.2 _ (by simp [Taint.mem_ofRegs])).trans ht.x20.symm)

private theorem regroup {s t : State} {tr}
    (h : Exec isa Impl.P256.EcdhJac.exchange s tr t) :
    Exec isa (.seq before (.seq multiply finish)) s tr t := by
  cases h with
  | seq a h => cases h with
    | seq b h => cases h with
      | seq c h => cases h with
        | seq d h => cases h with
          | seq p h => cases h with
            | seq w h => cases h with
              | seq i f =>
                simpa only [before, multiply, mq, finish, Impl.P256.EcdhJac.Frontend.before,
                  Impl.P256.EcdhJac.c, List.append_assoc] using
                  (Exec.seq (Exec.seq a (Exec.seq b (Exec.seq c d)))
                    (Exec.seq (Exec.seq (Exec.seq p w) i) f))

theorem constantTime (hL : Weierstrass.Law Spec.P256.curve)
    (hI : Weierstrass.AArch64.InvSounds) (hm : MulWithInverseOk p256 mq Impl.P256.EcdhInverse.inverse) :
    ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub Impl.P256.EcdhJac.exchange := by
  have hf : RelCT isa Public finish (fun _ _ => True) := by
    intro s t ts tt s' t' hp es et
    exact ⟨finish_ct _ _ _ _ _ _ trivial trivial hp es et,trivial⟩
  have h := RelCT.constantTime ((before_relCT hL hI).seq ((multiply_relCT hm).seq hf))
  intro s t ts tt s' t' ps pt hp es et
  exact h _ _ _ _ _ _ ps pt hp (regroup es) (regroup et)

end VG.Proof.P256.EcdhJac
