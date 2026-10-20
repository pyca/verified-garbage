module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullSample
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block

/-! # The initial three-block singleton sample -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem

structure SingleContext (p out table : Addr) (s : State) : Prop where
 scratch : Covers [⟨p,2048⟩] s.wr
 output : Covers [polyRegion out] s.wr
 apart : (Region.mk p 2048).Disjoint (polyRegion out)
 artifact : Rej8.TableArtifact s.mem table
 readable : Covers [⟨table,4096⟩] (s.rd++s.wr)
 tableScratch : (Region.mk table 4096).Disjoint ⟨p,2048⟩
 tableOut : (Region.mk table 4096).Disjoint (polyRegion out)

theorem SingleContext.frame {s t : State} {p out table : Addr} (h : SingleContext p out table s)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hf : Frame (fullWrites p out) s.mem t.mem) : SingleContext p out table t := by
  refine ⟨by rw [hw]; exact h.scratch,by rw [hw]; exact h.output,h.apart,?_,
    by rw [hr,hw]; exact h.readable,h.tableScratch,h.tableOut⟩
  exact h.artifact.frame hf (by
    intro r hr; simp only [fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl; exact h.tableScratch; exact h.tableOut)

def lastStartCode (sb ss a k off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k))
  (.seq Impl.MlKem.AArch64.Paired.squeeze
   (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)))

def lastStartRegs : List Reg := startRegs++[.x9,.x16]++
 [.x22,.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]

structure LastStartPostW (w16 : Bool) (B : Nat→Byte) (p out table : Addr) (s t : State) : Prop where
 keep : Keep lastStartRegs s t
 frame : Frame (fullWrites p out) s.mem t.mem
 saved : Noise.Saved p s t.mem
 context : SingleContext p out table t
 coeffs : Rej8.Scalar.CoeffsW w16 t.mem out (sampleAfter [] B 168)
 flag : (t.gpr .x22).toNat=if (sampleAfter [] B 168).length=256 then 1 else 0
 ptr : t.gpr .x19=p

theorem lastStart_ok {w16 : Bool} {s : State} {p seed out table : Addr} {sb ss a k off : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p) (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ctx : SingleContext p out table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE"=table) :
    WP isa (lastStartCode sb ss a k off w16) s
      (LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s) := by
  have combined := WP.mono_syms (start_ok (a := a) (b := a) (k := k) hss hsb h8 hp hseed hin ctx.scratch hsep)
    (R := fun u => WP isa (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts)
      (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) u
      (LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s))
    (fun u ⟨ku,fu,svu,u19,_,_,bu,_⟩ sy => by
      have cu := ctx.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
      refine WP.seq (WP.mono_syms (Rej8.constants_ok u (by
        rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
        fun v ⟨kv,cv,mv,tv⟩ syv => ?_)
      have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
        rw [mv,u19]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
      have fvBig : Frame (fullWrites p out) u.mem v.mem := fv.sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨⟨p,2048⟩,by simp [fullWrites],Offset.sub_base p (by decide)⟩)
      have ctv := cu.frame kv.rd kv.wr fvBig
      have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
      have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
      have v16 : v.gpr .x16=table := by rw [tv,syv,sy,ht]
      have stream : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=xofByte (seedBytes s.mem seed a k) i := by
        intro i hi
        have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide)
        exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (bu.xof hk hk256 hi)
      have ready : Rej8.TableReady v out :=
        ⟨by rw [v16]; exact ctv.artifact,by rw [v16]; exact ctv.readable,by rw [v16]; exact ctv.tableOut⟩
      have env := rejection_envW (w16 := w16) (off := 400) (N := 168) (by decide) (by decide)
        ctv.scratch ctv.output ctv.apart stream (fun _ hm => ready.read hm)
        (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
      have svv := svu.frame fv (by
        simp only [List.mem_singleton,forall_eq]
        exact Offset.disjoint p (by decide) (by decide) (by decide))
      refine WP.mono (reject_ok v (by decide) hoff (by decide)
        (by rw [v19,v28,hout]; exact env) cv) fun t h => ?_
      have ft : Frame [polyRegion out] v.mem t.mem := by rw [v28,hout] at h; exact h.frame
      have ftBig := ft.mono (rs' := fullWrites p out) (by simp [fullWrites])
      have svt := svv.frame ft (by simp only [List.mem_singleton,forall_eq]; exact ctx.apart.sub_left (Offset.sub_base p (by decide)))
      refine ⟨((ku.trans kv).trans h.keep).mono (by simp [lastStartRegs,List.append_assoc]),
        ((fu.mono (by simp [fullWrites])).trans fvBig).trans ftBig,svt,
        ctv.frame h.keep.rd h.keep.wr ftBig,?_,h.flagValue,(h.keep.get .x19).trans v19⟩
      simpa only [v28,hout] using h.coeffs)
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu => WP.seq hu)

end VG.Proof.MlKem.AArch64.Paired
