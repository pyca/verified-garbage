module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne

-- separate module: isolate the taint checks from the functional seal composition proofs.
/-! # Constant time of the fused POWER8 AES-GCM seal body -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealFusedCT
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.SealFused

def BI (c st w sp : Addr) (R : Nat) (A D N : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29=c ∧ V .r30=st ∧ V .r31=w ∧ V .r28=BitVec.ofNat 64 R ∧
    V .r22=A ∧ V .r27=D ∧ V .r23=N ∧ Env V sp s ∧ DataW c st w s D N.toNat

def bodyPublic : List Reg := [.r22,.r23,.r27,.r28,.r29,.r30,.r31]

theorem bi_agree {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s t : State}
    (hs : BI c st w sp R A D N s) (ht : BI c st w sp R A D N t) :
    s.sp=t.sp ∧ ∀ r ∈ bodyPublic, s.gpr r=t.gpr r := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,_⟩ := hs
  obtain ⟨V',hc',hst',hw',hR',ha',hd',hn',he',_⟩ := ht
  refine ⟨he.sp.trans he'.sp.symm,?_⟩
  intro r hr
  simp only [bodyPublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [he.fr .r22 (by decide),he'.fr .r22 (by decide),ha,ha']
  · rw [he.fr .r23 (by decide),he'.fr .r23 (by decide),hn,hn']
  · rw [he.fr .r27 (by decide),he'.fr .r27 (by decide),hd,hd']
  · rw [he.r28,he'.r28,hR,hR']
  · rw [he.r29,he'.r29,hc,hc']
  · rw [he.r30,he'.r30,hst,hst']
  · rw [he.r31,he'.r31,hw,hw']

def ArgsI (c st w sp : Addr) (R : Nat) (A D N : BitVec 64) (t : State) : Prop :=
  ∃ s, BI c st w sp R A D N s ∧ t=argsState s

theorem block_call_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R : Nat} {A D N : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (ArgsI c st w sp R A D N)
      (.call "vg_aes_gcm_encrypt_blocks" Impl.AesGcm.PPC64LE.Blocks.encrypt) := by
  refine RelCT.callEx Blocks.encrypt_correct Blocks.encrypt_ct fun a b ⟨⟨s,hs,ea⟩,⟨t,ht,eb⟩⟩ => ?_
  subst a b
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩ := hs
  obtain ⟨V',hc',hst',hw',hR',ha',hd',hn',he',hdata'⟩ := ht
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  have hdt : DataW (V' .r29) (V' .r30) (V' .r31) t (V' .r27) (V' .r23).toNat := by
    rw [hc',hst',hw',hd',hn']; exact hdata'
  have hcs := args_call (L.v hc hst hw) he hds hR hv
  have hct := args_call (L.v hc' hst' hw') he' hdt hR' hv
  refine ⟨blockReads (argsState s),blockWrites (argsState s),
    blockReads (argsState t),blockWrites (argsState t),hcs.pre,hct.pre,?_,
    hcs.reads,hcs.writes,hct.reads,hct.writes⟩
  sig_eval [Spec.Gcm.encryptBlocksContract,Spec.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs]
  simp only [he.r29,he'.r29,he.r30,he'.r30,he.r31,he'.r31,he.r28,he'.r28,
    he.fr .r27 (by decide),he'.fr .r27 (by decide),he.fr .r23 (by decide),he'.fr .r23 (by decide),
    hc,hc',hst,hst',hw,hw',hR,hR',hd,hd',hn,hn',he.sp,he'.sp]
  trivial

theorem blockArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs bodyPublic)
    (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs) h).isSome=true := ⟨_,by taint_decide⟩

theorem whole_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R : Nat} {A D N : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (BI c st w sp R A D N)
      (.seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
        (.call "vg_aes_gcm_encrypt_blocks" Impl.AesGcm.PPC64LE.Blocks.encrypt)) := by
  obtain ⟨_,hc⟩ := blockArgs_taint
  exact CT.seq (J := ArgsI c st w sp R A D N) (CT.taint bodyPublic (fun _ _ => bi_agree) hc)
    (fun s hs => WP.mono (args_ok s) fun t ht => ⟨s,hs,ht⟩) (block_call_ct L hv)

theorem whole_bi [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s : State}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) (hs : BI c st w sp R A D N s) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
      (.call "vg_aes_gcm_encrypt_blocks" Impl.AesGcm.PPC64LE.Blocks.encrypt)) s
      (BI c st w sp R A D N) := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩ := hs
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  refine WP.mono (WP.with_rdwr (SealFused.whole_ok (L.v hc hst hw) he hds hR hv)) fun t ⟨ho,rd,wr,_⟩ => ?_
  exact ⟨V,hc,hst,hw,hR,ha,hd,hn,ho.env,hdata.of_eq rd wr⟩

def GI (c st w sp : Addr) (R : Nat) (A D N : BitVec 64) (s : State) : Prop :=
  BI c st w sp R A D N s ∧ s.gpr .r24=D+BitVec.ofNat 64 (16*(N.toNat/16)) ∧
    s.gpr .r25=BitVec.ofNat 64 (N.toNat%16) ∧ s.gpr .r26=0

theorem tailSetup_gi {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s : State}
    (hs : BI c st w sp R A D N s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) s (GI c st w sp R A D N) := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩ := hs
  refine WP.mono (tailSetup_ok he) fun t ⟨h24,h25,h26,hg,hk⟩ => ?_
  have het := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine ⟨⟨V,hc,hst,hw,hR,ha,hd,hn,het,hdata.of_eq hk.rd hk.wr⟩,?_,?_,h26⟩
  · rw [hd,hn] at h24; exact h24
  · rw [hn] at h25; exact h25

theorem tailSetup_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs bodyPublic)
    (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) h).isSome=true := ⟨_,by taint_decide⟩

private theorem gi_crm {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s : State}
    (hv : R=10 ∨ R=12 ∨ R=14) (hs : GI c st w sp R A D N s) :
    CrM c st w sp R (D+BitVec.ofNat 64 (16*(N.toNat/16))) (N.toNat%16) 0 0 s := by
  obtain ⟨⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩,h24,h25,_⟩ := hs
  have hds := data_suffix hdata (j := 16*(N.toNat/16)) (by omega)
  rw [show N.toNat-16*(N.toNat/16)=N.toNat%16 by omega] at hds
  refine ⟨V,0,16*(N.toNat/16),s.mem,hc,hst,hw,by omega,he,by omega,?_,?_,hR,hv,?_,?_,?_,?_,.inr (by omega),Frame.refl _ _⟩
  · simpa only [BitVec.add_zero] using h24
  · simpa only [Nat.sub_zero] using h25
  · rw [hc,hst,hw]; exact hds
  · intro hh; simpa only [Nat.add_zero] using hh
  · intro _; simp only [Spec.Aes.bytesAt,List.range_zero,List.map_nil,Proof.Gcm.xorKs_nil]
  · rfl

theorem tail_ct {c st w sp : Addr} {R : Nat} {A D N : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (BI c st w sp R A D N)
      (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail) := by
  obtain ⟨_,hc⟩ := tailSetup_taint
  exact CT.seq (J := GI c st w sp R A D N) (CT.taint bodyPublic (fun _ _ => bi_agree) hc)
    (fun _ => tailSetup_gi) ((cryptTail_ct L).mono fun _ => gi_crm hv)

theorem tail_gi {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s : State}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) (hs : BI c st w sp R A D N s) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail) s
      (GI c st w sp R A D N) := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩ := hs
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  refine WP.mono (WP.with_rdwr (SealFused.tail_ok (icb := 0) (L.v hc hst hw) he hds hR hv))
    fun t ⟨⟨ho,h24,h25,h26⟩,rd,wr,_⟩ => ?_
  refine ⟨⟨V,hc,hst,hw,hR,ha,hd,hn,ho.env,hdata.of_eq rd wr⟩,?_,?_,h26⟩
  · rw [hd,hn] at h24; exact h24
  · rw [hn] at h25; exact h25

private theorem gi_abs {c st w sp : Addr} {R : Nat} {A D N : BitVec 64} {s : State}
    (hs : GI c st w sp R A D N s) :
    AbsI c st w sp 16 (D+BitVec.ofNat 64 (16*(N.toNat/16))) (N.toNat%16) 0 s := by
  obtain ⟨⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩,h24,h25,h26⟩ := hs
  have hds := data_suffix hdata (j := 16*(N.toNat/16)) (by omega)
  rw [show N.toNat-16*(N.toNat/16)=N.toNat%16 by omega] at hds
  refine ⟨V,Spec.Gcm.blockAt s.mem (V .r29+BitVec.ofNat 64 240),[],hc,hst,hw,rfl,
    he,h24,h25,h26,?_,rfl⟩
  rw [hst,hw]; exact hds.ok

theorem absorb_fin_ct [VG.Proof.Gcm.PPC64LE.GhashLaw]
    {c st w sp : Addr} {R : Nat} {A D N : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (GI c st w sp R A D N) (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0)) := by
  refine CT.seq (J := FTI c st w sp R A N)
    ((absorb_ct L (.inr rfl) (q := 0) (by decide)).mono fun _ => gi_abs)
    (fun s ⟨⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩,h24,h25,h26⟩ => ?_)
    (finTag_ct L (.inl rfl) hv)
  have hds := data_suffix hdata (j := 16*(N.toNat/16)) (by omega)
  rw [show N.toNat-16*(N.toNat/16)=N.toNat%16 by omega] at hds
  have ai : AbsIn V sp 16 (Spec.Gcm.blockAt s.mem (V .r29+BitVec.ofNat 64 240)) []
      (D+BitVec.ofNat 64 (16*(N.toNat/16))) (N.toNat%16) s :=
    ⟨he,h24,h25,h26,by rw [hst,hw]; exact hds.ok,rfl⟩
  exact WP.mono (absorb_ok (L.v hc hst hw) (.inr rfl) ai) fun _ ab =>
    ⟨V,hc,hst,hw,hR,ha,hn,ab.env⟩

theorem fastBody_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R : Nat} {A D N : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (BI c st w sp R A D N) Impl.AesGcm.PPC64LE.SealFused.fastBody :=
  CT.seq (whole_ct L hv) (fun _ => whole_bi L hv)
    (CT.seq (tail_ct L hv) (fun _ => tail_gi L hv) (absorb_fin_ct L hv))

theorem one_bi {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D N : BitVec 64}
    {s : State} (hs : OneI c W sp R Np n Ad A D N s) :
    BI c (W+BitVec.ofNat 64 16) W sp R A D N s := by
  obtain ⟨V,hc,hst,hw,hR,_,_,ha,hd,hn,he,_,_,hdata⟩ := hs
  exact ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata⟩

theorem smallBody_ct [VG.Proof.Gcm.PPC64LE.GhashLaw]
    {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D N : BitVec 64}
    (L : Lay c (W+BitVec.ofNat 64 16) W) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (OneI c W sp R Np n Ad A D N)
      (.seq Impl.AesGcm.PPC64LE.oneCrypt (Impl.AesGcm.PPC64LE.oneTag 0)) := by
  refine CT.seq (J := OneI c W sp R Np n Ad A D N) (oneCrypt_ct L hv)
    (fun s hs => ?_) (oneTag_ct L (.inl rfl) hv)
  have hs₀ := hs
  obtain ⟨V,hc,hst,hw,hR,_,_,ha,hd,hn,he,_,_,hdata⟩ := hs
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  exact WP.mono (WP.with_rdwr (oneCrypt_ok (L.v hc hst hw) he hR hv hds rfl)) fun t ⟨ho,rd,wr,_⟩ =>
    hs₀.keep (fun r hr => (he.fr r hr).symm) ho.env rd wr

theorem selector_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs bodyPublic)
    (.block [.lsr .d .r12 .r23 9]) h).isSome=true := ⟨_,by taint_decide⟩

theorem body_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D N : BitVec 64}
    (L : Lay c (W+BitVec.ofNat 64 16) W) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (OneI c W sp R Np n Ad A D N) Impl.AesGcm.PPC64LE.SealFused.body := by
  obtain ⟨_,hc⟩ := selector_taint
  refine CT.seq (J := fun s => OneI c W sp R Np n Ad A D N s ∧
    s.gpr .r12=BitVec.ofNat 64 (N.toNat/512))
    (CT.taint bodyPublic (fun _ _ hs ht => bi_agree (one_bi hs) (one_bi ht)) hc)
    (fun s hs => ?_) ?_
  · have hs₀ := hs
    obtain ⟨V,hc,hst,hw,hR,_,_,ha,hd,hn,he,_,_,hdata⟩ := hs
    have h23 := he.fr .r23 (by decide)
    rw [hn] at h23
    have hshift : N >>> 9=BitVec.ofNat 64 (N.toNat/512) := by
      calc
        _ = BitVec.ofNat 64 N.toNat >>> 9 := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
        _ = _ := shr9 N.isLt
    have hp : WP isa (.block [.lsr .d .r12 .r23 9]) s fun t =>
        t.gpr .r12=BitVec.ofNat 64 (N.toNat/512) ∧
        (∀ r, r≠.r12 → t.gpr r=s.gpr r) ∧ Keeps s t := by
      crun [h23,hshift]
      exact ⟨fun r h => by simp [h],⟨rfl,rfl,rfl,rfl,rfl⟩⟩
    refine WP.mono hp fun t ⟨h12,hg,hk⟩ => ?_
    have het := he.keep (fun r hr => hg r (by revert r; decide)) hk.sp hk.rd hk.wr
    exact ⟨hs₀.keep (fun r hr => (he.fr r hr).symm) het hk.rd hk.wr,h12⟩
  · exact CT.ite (decide (N.toNat/512=0))
      (fun _ hs => eval_zero hs.2 (by have := N.isLt; omega))
      (fun _ => (smallBody_ct L hv).mono fun _ hs => hs.1)
      (fun _ => (fastBody_ct L hv).mono fun _ hs => one_bi hs.1)

end VG.Proof.AesGcm.PPC64LE.SealFusedCT
