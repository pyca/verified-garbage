module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Entry
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: reuse the shared argument-copy loop and its frame proof.
/-! # Outgoing split-seal stack arguments -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather


theorem stackArgs_ok {s u : State} (h : Lay s) (hb : u.gpr .r12=Pf s)
    (hsp : u.sp=Pf s) (hrd : u.rd=s.rd) (hwr : u.wr=FR s::s.wr) :
    WP isa (.block Impl.AesGcm.PPC64LE.GatherSplit.stackArgs) u
      (· = copiedState 160 u 3) := by
  have hr : ∀ j<3, InRegions (u.rd++u.wr) (u.sp+BitVec.ofNat 64 (160+96+8*j)) 8 := by
    intro j hj
    rw [hsp]
    exact h.sa_in hj u hrd
  have hw : ∀ j<3, InRegions u.wr (u.sp+BitVec.ofNat 64 (96+8*j)) 8 := by
    intro j hj
    rw [hsp,hwr]
    exact fr_in s (by omega) (by omega) s.wr
  exact WP.block ⟨_,copies_run (by rw [hb,hsp]) (by decide) 3 (by decide) hr hw,rfl⟩


theorem stackArgs_frame (u : State) :
    Frame [⟨u.sp+96,24⟩] u.mem (copiedState 160 u 3).mem :=
  (copiedState_mem 3 (by decide) (by decide)).1


theorem stackArgs_values (u : State) {j : Nat} (hj : j<3) :
    (copiedState 160 u 3).mem.readW (u.sp+BitVec.ofNat 64 (96+8*j)) 64=
      u.mem.readW (u.sp+BitVec.ofNat 64 (256+8*j)) 64 :=
  (copiedState_mem 3 (by decide) (by decide)).2 j hj


theorem stackArgs_plaintext {s e t u : State} (h : Lay s) (he : Entered s e)
    (hc : 0<Cnt s) (ht : TailResult e (Src s) (Dst s) (Cnt s) t)
    (hm : u.mem=t.mem) (hsp : u.sp=Pf s) :
    Spec.Aes.bytesAt (copiedState 160 u 3).mem (e.mem.readW (Src s) 64) (firstLen e).toNat ++
      (Spec.Aes.bytesAt (copiedState 160 u 3).mem (Dst s) (L s)).drop (firstLen e).toNat=pt s (Cnt s) := by
  have hg := gatherPre_of h he
  have hp := first_listed hg hc
  obtain ⟨hls,-⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  rw [hls] at hp
  have hs : Region.Sub ⟨Pf s+96,24⟩ ⟨Bs s,2832⟩ := by
    change Region.Sub ⟨Pf s+BitVec.ofNat 64 96,24⟩ ⟨Bs s,2832⟩
    rw [pf_off]
    exact stk_sub s _ _ (by decide)
  have fr : Frame [⟨Pf s+96,24⟩] t.mem (copiedState 160 u 3).mem := by
    rw [← hm]
    have ff := stackArgs_frame u
    rw [hsp] at ff
    exact ff
  have a : Spec.Aes.bytesAt (copiedState 160 u 3).mem (e.mem.readW (Src s) 64) (firstLen e).toNat=
      Spec.Aes.bytesAt t.mem (e.mem.readW (Src s) 64) (firstLen e).toNat := by
    exact Proof.Cmac.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact (h.bl _ hp).symm.sub_right hs) (Nat.le_of_lt (firstLen e).isLt)
  have b : Spec.Aes.bytesAt (copiedState 160 u 3).mem (Dst s) (L s)=Spec.Aes.bytesAt t.mem (Dst s) (L s) := by
    exact Proof.Cmac.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact h.bd.symm.sub_right hs) (Nat.le_of_lt (stackArg s 1).isLt)
  rw [a,b]
  exact (ht.input hg hc).trans (by rw [he.mem,h.hpt])

end VG.Proof.AesGcm.PPC64LE.GatherSplit
