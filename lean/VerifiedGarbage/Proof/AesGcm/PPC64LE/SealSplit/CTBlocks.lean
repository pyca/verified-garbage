module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Whole
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFusedCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Whole
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFusedCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: promote the public outgoing scratch word through the proved argument setup.
/-! # Constant time of the split whole-block call -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
open VG VG.PPC64LE


def SI (c st w sp : Addr) (R : Nat) (A D N S : BitVec 64) (count : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29=c ∧ V .r30=st ∧ V .r31=w ∧ V .r28=BitVec.ofNat 64 R ∧
    V .r22=A ∧ V .r27=D ∧ V .r23=N ∧ Env V sp s ∧ DataW c st w s D N.toNat ∧ Call.Layout V sp S count s


theorem si_bi {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64} {s : State}
    (hs : SI c st w sp R A D N S count s) : SealFusedCT.BI c st w sp R A D N s := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata,_⟩ := hs
  exact ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩


def publicRegs : List Reg := SealFusedCT.bodyPublic++[.r7,.r8]


theorem si_agree {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64} {s t : State}
    (hs : SI c st w sp R A D N S count s) (ht : SI c st w sp R A D N S count t) :
    s.sp=t.sp ∧ ∀ r ∈ publicRegs, s.gpr r=t.gpr r := by
  have hb := SealFusedCT.bi_agree (si_bi hs) (si_bi ht)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hl⟩ := hs
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hl'⟩ := ht
  refine ⟨hb.1,fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hb.2 r hr
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.source.trans hl'.source.symm
    · exact hl.countReg.trans hl'.countReg.symm


def ArgsI (c st w sp : Addr) (R : Nat) (A D N S : BitVec 64) (count : Nat) (t : State) : Prop :=
  ∃ s, SI c st w sp R A D N S count s ∧ t=Call.argsState s


theorem call_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (ArgsI c st w sp R A D N S count)
      (.call "vg_aes_gcm_encrypt_blocks_split" Impl.AesGcm.PPC64LE.SplitBlocks.encrypt) := by
  refine RelCT.callEx SplitBlocks.encrypt_correct SplitBlocks.encrypt_ct fun a b ⟨⟨s,hs,ea⟩,⟨t,ht,eb⟩⟩ => ?_
  subst a b
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata,lay⟩ := hs
  obtain ⟨V',hc',hst',hw',hR',ha',hd',hn',he',hdata',lay'⟩ := ht
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  have hdt : DataW (V' .r29) (V' .r30) (V' .r31) t (V' .r27) (V' .r23).toNat := by
    rw [hc',hst',hw',hd',hn']; exact hdata'
  have cs := Call.args_config (L.v hc hst hw) he hds lay hR hv
  have ct := Call.args_config (L.v hc' hst' hw') he' hdt lay' hR' hv
  refine ⟨Call.reads (Call.argsState s),Call.writes (Call.argsState s),
    Call.reads (Call.argsState t),Call.writes (Call.argsState t),cs.pre,ct.pre,?_,
    cs.reads,cs.writes,ct.reads,ct.writes⟩
  sig_pub [Spec.Gcm.encryptBlocksSplitContract,Spec.Gcm.encryptBlocksSplitSig,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
  simp only [he.r29,he'.r29,he.r30,he'.r30,he.r31,he'.r31,he.r28,he'.r28,
    he.fr .r27 (by decide),he'.fr .r27 (by decide),he.fr .r23 (by decide),he'.fr .r23 (by decide),
    hc,hc',hst,hst',hw,hw',hR,hR',hd,hd',hn,hn',he.sp,he'.sp,lay.source,lay'.source,lay.countReg,lay'.countReg]
  have slot : ∀ m : Mem, (m.writeW (sp+96) (w+448)).readW (sp+96#64) 64=w+448 :=
    fun m => Mem.readW_writeW_self64 m _ _
  simp only [slot,true_and]


theorem args_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs publicRegs)
    (.block Impl.AesGcm.PPC64LE.SealSplit.blockArgs) h).isSome=true := ⟨_,by taint_decide⟩


theorem whole_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (SI c st w sp R A D N S count) Impl.AesGcm.PPC64LE.SealSplit.whole := by
  obtain ⟨_,hc⟩ := args_taint
  refine CT.seq (J := ArgsI c st w sp R A D N S count)
    (CT.taint publicRegs (fun _ _ => si_agree) hc) ?_ (call_ct L hv)
  intro s hs
  have hs₀ := hs
  obtain ⟨_,_,_,_,_,_,_,_,he,_,lay⟩ := hs
  exact WP.mono (Call.args_ok s (by rw [he.sp]; exact lay.slotWrite)) fun t ht => ⟨s,hs₀,ht⟩

end VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
