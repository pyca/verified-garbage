module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousTail
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousCtr
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Omega
/-! Vector finalization after the shared contiguous bulk loop. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt padLen zeros ghashFrom toBytes ofBytes inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)
open Split (SealRegions)

def VecPowerPost (Ctx W SP : Addr) (H : Block) (s t : State) : Prop :=
  t.xmm .xmm0=revMask ∧ t.xmm .xmm1=poly ∧ Short.IsH1 H (t.xmm .xmm3) ∧
  Short.IsH2 H (t.xmm .xmm3) (t.xmm .xmm6) ∧ Env Ctx (W+16#64) W SP t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr

def BodyPost (Ctx W SP S D : Addr) (R n al : Nat) (H icb : Block) (a : List Byte) (s t : State) : Prop :=
  Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ Frame (oneFrameB W D SP n) s.mem t.mem ∧
  bytesAt t.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem S n) ∧
  bytesAt t.mem W 16 = toBytes (ghashFrom H (Spec.Gcm.ghash H (Spec.Gcm.blocks (padded a (bytesAt t.mem D n))))
    [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W+16#64)))

theorem finishVec_ok (prepared wide : Bool) {M : CtxMode} {Ctx W SP S D : Addr} {R n al : Nat}
    {s u : State} {H icb : Block} {a : List Byte}
    (reg : SealRegions M Ctx W SP D S R n n s) (ob : ObPre M Ctx W SP R D n s)
    (post : ObPost Ctx W SP D n s u) (bulk : BlocksResult Ctx W R S D (n/16) s u)
    (hH : blockAt s.mem (Ctx+240#64)=H) (hcb : blockAt s.mem (cbA W)=icb)
    (hal : s.mem.readW (W+184#64) 64=BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W+16#64+32#64) H (a++zeros (padLen a.length)))
    (slot : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : u.mem.readW (SP+8#64) 64=S)
    (slots : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩)
    (power : WP isa (.block (if prepared then Impl.AesGcm.X86_64.Short.finPowP else Impl.AesGcm.X86_64.Short.finPow))
      u (VecPowerPost Ctx W SP H u)) :
    WP isa (Contiguous.finishVec prepared wide) u (BodyPost Ctx W SP S D R n al H icb a s) := by
  have ha : (a++zeros (padLen a.length)).length%16=0 := by
    simp only [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨ct,cb,y⟩ := bulk
  obtain ⟨fr,rnds,_,kc,j,pfx,ctr,abs,remain⟩ := ob_factsFrom reg.lay ob reg.sW
    reg.ks reg.sD post.frame hH hcb habs ha ct cb
    (Z:=bytesAt u.mem D (16*(n/16))) (by rw [length_bytesAt]; omega_arith)
    (by change _ = _; rw [y]; change ghashFrom (blockAt s.mem (Ctx+240#64)) _ _ = _; rw [hH,Proof.Gcm.blocksAt_eq])
  have count : blockAt u.mem (cbA W) = Nat.repeat inc32 (n/16) icb := by rw [cb,hcb]
  have la : u.mem.readW (W+184#64) 64=BitVec.ofNat 64 al := by
    rw [fr.readW (r:=⟨W+184#64,8⟩) (Region.contains_self _ _)
      (kept_oneFrameB reg.lay ob.data.ok.w ob.t_w (.inl ⟨by decide,by decide⟩)) (by decide),hal]
  have eq : n-16*(n/16) = n%16 := by omega_arith
  rw [eq] at remain
  have ks : Short.KsOk (if wide then Impl.AesGcm.X86_64.Short.finKs else Impl.AesGcm.X86_64.Short.finKsA) := by
    cases wide <;> first | exact Short.finKsA_ksOk | exact Short.finKs_ksOk
  unfold Contiguous.finishVec
  refine WP.seq (power.mono fun z ⟨x0,x1,h1,h2,env,mem,rd,wr⟩ => ?_)
  apply Short.finRestFrom_ok _ ks ob (by omega_arith) (by omega_arith) fr rnds kc j reg.sW pfx count abs remain
    post.tlen post.dat post.len la env mem (rd.trans post.rd) (wr.trans post.wr) x0 x1 h1 h2
  intro t fp tr tw frame
  have i : n-n%16=16*(n/16) := by omega_arith
  have subS := (inputData reg).drop (k:=16*(n/16)) (by omega_arith)
  rw [eq] at subS
  have alias : S+BitVec.ofNat 64 (16*(n/16))=D+BitVec.ofNat 64 (16*(n/16)) ∨
      (⟨S+BitVec.ofNat 64 (16*(n/16)),n%16⟩ : Region).Disjoint ⟨D+BitVec.ofNat 64 (16*(n/16)),n%16⟩ := by
    rcases reg.sD with same|apart
    · exact .inl (by rw [same])
    · exact .inr ((apart.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)))
  have src' : t.mem.readW (SP+8#64) 64=S := by
    rw [frame.readW (Region.contains_self _ _) (fun b hb => by
      obtain rfl := List.mem_singleton.mp hb; exact slots.sub_right (Lay.wSub (by decide))) (by decide), src]
  simpa only [i] using vecTail_ok fp (Nat.mod_le _ _) (by rw [tr,tw]; exact slot) src' slots
    (by rw [i,tr,tw]; exact subS.rd) (by rw [i]; exact alias) (by rw [i]; exact subS.w)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
