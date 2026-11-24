module

-- separate module: the backend registrations share this end-to-end functional proof, checked independently of the trace proof.

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneAuthStage
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneFrame
import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneReturn
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Spec.Gcm VG.Proof.Gcm
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (tagDirect)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm.AArch64.Stitch (GatherLaws)
variable {wn : Nat} {W : Addr} {s a b u : State}

theorem finish_ok (v : GcmImpl) (c : Inner wn W s) (f : FrontOut wn W s a)
    (e : EncOut wn (s.gpr .x1).toNat (stackArg s 0).toNat (s.gpr .x0) (W+16#64) W s.sp
      (s.gpr .x6) (s.gpr .x7) (inc32 (J s)) (aadHash s) a b)
    (au : AuthOut wn W s b u) (scratch : v.ctr.scratch≤wn-512) :
    WP isa (.seq (.block finPrep) (.seq (tagDirect v.callees) (.block restore))) u
      fun z => GprAbi s z ∧ result s z := by
  have hp := returnPrep c f e au.frame
  have hb := returnPrep (t := b) c f e (Frame.refl _ _)
  refine WP.seq ((finPrep_ok (al := (s.gpr .x5).toNat) (n := (stackArg s 0).toNat) au.env.x19
    (covers_left au.env.perm.w) (by simpa using hp.alen) (by simpa using hp.len) c.lay.hWn).mono ?_)
  rintro w ⟨al,n,r⟩
  have keep : Kept w.gpr w := fun _ _ => rfl
  have rounds := (r.others .x22 (by decide)).trans ((au.kept .x22 (by decide)).trans (e.x22.trans f.input.x22))
  have tag := c.tagData.of_eq (r.rd.trans (au.rd.trans (e.rd.trans f.rd))) (r.wr.trans (au.wr.trans (e.wr.trans f.wr)))
  refine WP.seq ((tag_ok c.lay v (au.env.of_regs r) keep tag c.nr rounds (r.mem ▸ hp.tag) scratch).mono ?_)
  rintro z ⟨env,_,out,fr⟩
  rw [r.mem] at out fr
  apply finishReturn c hp env fr
  change encryptWith _ _ 16 _ _ _ = (_, _)
  rw [encryptWith_eq,gctr_eq,←hp.cipher,fullTag_eq]
  have y := au.hash
  rw [hb.cipher,←hp.cipher] at y
  change bytesAt z.mem _ 16 = toBytes (ghashFrom (ctxH u.mem _) _ _ ^^^ _) at out
  rw [hp.hash,y,hp.j,hp.key,al,n] at out
  simp only [BitVec.ofNat_toNat] at out
  rw [out]
  simp only [aadBytes,ctBytes,length_bytesAt,BitVec.setWidth_eq]

theorem body_ok (v : GcmImpl) (gh : v.calls.pmull=true → GatherLaws)
    (scratch : v.ctr.scratch≤v.calls.pwWn-512) : BodyOk v := by
  intro s W c
  apply front_then_ok
  refine WP.seq ((front_ok v c).mono fun a f => ?_)
  refine WP.seq ((encrypt_ok v c.lay f.input gh scratch).mono fun b ⟨e,_⟩ => ?_)
  apply WP.assoc
  exact WP.seq ((auth_stage v c f e).mono fun u h => finish_ok v c f e h scratch)

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
