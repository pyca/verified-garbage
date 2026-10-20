module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared-seed timing for the first singleton rejection pass -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

structure LastPreparedW (w16 : Bool) (B : Nat→Byte) (p out table : Addr) (s t : State) : Prop where
 keep : Keep prepareRegs s t
 env : Rej8.EnvW w16 168 B (p+400) out t
 constants : Rej8.Constants t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=table

theorem lastPrepare_ok {w16 : Bool} {s : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hk : 0<k) (hk256 : k≤256)
    (h : LastInput sb ss off p seed out table s) :
    WP isa (prepareCode sb ss a a k) s (LastPreparedW w16 (xofByte (seedBytes s.mem seed a k)) p out table s) := by
  refine WP.seq (WP.mono_syms (start_ok (a:=a) (b:=a) (k:=k) hss hsb h8
    h.ptr h.seedPtr h.readable h.context.scratch h.separate)
    fun u ⟨ku,fu,_,u19,_,_,bu,_⟩ sy => ?_)
  have cu := h.context.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
  refine WP.mono_syms (Rej8.constants_ok u (by
    rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
    fun v ⟨kv,cv,mv,tv⟩ syv => ?_
  have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
    rw [mv,u19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have fvBig : Frame (fullWrites p out) u.mem v.mem := fv.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨p,2048⟩,by simp [fullWrites],Offset.sub_base p (by decide)⟩)
  have ctv := cu.frame kv.rd kv.wr fvBig
  have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
  have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
  have v16 : v.gpr .x16=table := by rw [tv,syv,sy,h.symbol]
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
  exact ⟨ku.trans kv,env,cv,v19,v16⟩

end VG.Proof.MlKem.AArch64.Paired
