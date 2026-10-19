module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.Sha3.AArch64.Neon

def stepRegs : List Reg := nextRegs++bothRegs
structure StepPostW (w16 : Bool) (A B : Spec.Sha3.State) (L M : List Zq) (p a b c : Addr) (s t : State) : Prop where
 keep : Keep stepRegs s t
 frame : Frame (stepWrites p a b) s.mem t.mem
 frameFine : Frame [⟨p,1712⟩,polyRegion a,polyRegion b] s.mem t.mem
 context : Context p a b c t
 pointer : t.gpr .x19=p
 pair : PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)
 left : Rej8.Scalar.CoeffsW w16 t.mem a L
 right : Rej8.Scalar.CoeffsW w16 t.mem b M
 saveLeft : checkpointW w16 (p+1680) a L t.mem
 saveRight : checkpointW w16 (p+1696) b M t.mem
 flagLeft : (t.gpr .x22).toNat=if L.length=256 then 1 else 0
 flagRight : (t.gpr .x23).toNat=if M.length=256 then 1 else 0
 flagBoth : (t.gpr .x6).toNat=if L.length=256 ∧ M.length=256 then 1 else 0
 constants : Rej8.Constants t

abbrev StepPost := StepPostW false

theorem extraStep_ok {w16 : Bool} {s : State} {p a b c : Addr} {A B : Spec.Sha3.State} {L M : List Zq}
 (ctx : Context p a b c s) (hp : s.gpr .x19=p) (sym : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
 (pair : PairAt s.mem p A B) (hl : L.length≤256) (hm : M.length≤256)
 (ca : Rej8.Scalar.CoeffsW w16 s.mem a L) (cb : Rej8.Scalar.CoeffsW w16 s.mem b M)
 (sa : checkpointW w16 (p+1680) a L s.mem) (sb : checkpointW w16 (p+1696) b M s.mem) :
 WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) s
 (StepPostW w16 A B (sampleAfter L (Proof.Sha3.byteOf (Spec.Sha3.keccakF A)) 56)
 (sampleAfter M (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) 56) p a b c s) := by
 have grouped : WP isa (.seq nextBlock (extraBoth w16)) s
     (StepPostW w16 A B (sampleAfter L (Proof.Sha3.byteOf (Spec.Sha3.keccakF A)) 56)
       (sampleAfter M (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) 56) p a b c s) := by
  refine WP.seq (WP.mono_syms (nextBlock_ok hp ctx.scratch pair) fun u h hsym => ?_)
  rcases h with ⟨ku,fu,precise,up,pu,ra,rb,cs,ut⟩
  have fu' : Frame (stepWrites p a b) s.mem u.mem := fu.mono (by simp [stepWrites])
  have cu := ctx.frame ku.rd ku.wr fu'
  have ux : u.gpr .x16=c := by rw [ut,hsym,sym]
  have ua := coeffs_frame ca hl fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farA.symm)
  have ub := coeffs_frame cb hm fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farB.symm)
  have checkpoints {off : Nat} (ho : off=1680 ∨ off=1696) :
      ∀r∈nextWrites p,(Region.mk (p+BitVec.ofNat 64 off) 16).Disjoint r := by
   have hlo : 1680≤off := by omega
   have hhi : off≤1696 := by omega
   intro r hr
   simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl|rfl
   · exact Offset.disjoint_base p (d:=off) (n:=16) (k:=400) (by omega) (by omega)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=400) (k:=168) (by omega) (by omega) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=904) (k:=168) (by omega) (by omega) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=1536) (k:=136) (by omega) (by omega) (by decide)
   · exact Offset.disjoint p (d:=off) (n:=16) (e:=1408) (k:=8) (by omega) (by omega) (by decide)
  have usa := checkpoint_frame sa precise (checkpoints (Or.inl rfl))
  have usb := checkpoint_frame sb precise (checkpoints (Or.inr rfl))
  have ea := cu.envW (w16 := w16) ux (N:=56) (off:=400) (by decide) (by decide) (Or.inl rfl) (fun i hi=>ra.byte hi)
  have eb := cu.envW (w16 := w16) ux (N:=56) (off:=904) (by decide) (by decide) (Or.inr rfl) (fun i hi=>rb.byte hi)
  refine WP.mono (extraBoth_ok up cu.scratch cu.farA cu.farB cu.apart ea eb
    (by intro mask hmask; rw [ux]; exact cu.tableScratch.sub_left (Rej8.table_sub c hmask))
    cs hl hm ua ub usa usb) fun t ht => ?_
  have ft : Frame (stepWrites p a b) u.mem t.mem := ht.frame.sub (by
   intro r hr
   simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl
   · exact ⟨polyRegion a,by simp [stepWrites],fun _ h=>h⟩
   · exact ⟨polyRegion b,by simp [stepWrites],fun _ h=>h⟩
   · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩
   · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
  have fine : Frame [⟨p,1712⟩,polyRegion a,polyRegion b] s.mem t.mem := by
   apply (precise.sub ?_).trans (ht.frame.sub ?_)
   · intro r hr
     simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl|rfl
     · exact ⟨⟨p,1712⟩,by simp,Region.sub_prefix (by decide)⟩
     all_goals exact ⟨⟨p,1712⟩,by simp,Offset.sub_base p (by decide)⟩
   · intro r hr
     simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl
     · exact ⟨polyRegion a,by simp,fun _ h=>h⟩
     · exact ⟨polyRegion b,by simp,fun _ h=>h⟩
     all_goals exact ⟨⟨p,1712⟩,by simp,Offset.sub_base p (by decide)⟩
  refine ⟨(ku.trans ht.keep).mono (by decide),fu'.trans ft,fine,cu.frame ht.keep.rd ht.keep.wr ft,
    (ht.keep.get .x19).trans up,?_,ht.left,ht.right,ht.saveLeft,ht.saveRight,
    ht.flagLeft,ht.flagRight,ht.flagBoth,ht.constants⟩
  exact pair_frame pu ht.frame (by
   intro r hr; simp only [bothWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl
   · exact cu.farA.sub_left (Region.sub_prefix (by decide))
   · exact cu.farB.sub_left (Region.sub_prefix (by decide))
   · exact Offset.base_disjoint p (by decide) (by decide)
   · exact Offset.base_disjoint p (by decide) (by decide))
 exact WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc grouped)) fun _ h => WP.assoc h)
end VG.Proof.MlKem.AArch64.Paired
