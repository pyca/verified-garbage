module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Skip
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.PartialCopy
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: reuse the gather loop for all descriptors after the first.
/-! # Gathering the destination suffix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE VG.WriteBytes
open VG.Proof.Gather.PPC64LE (GatherPre GKeeps)

structure TailResult (base : State) (S D : Addr) (count : Nat) (t : State) : Prop where
  keep : GKeeps base t
  mem : t.mem=writeBytes base.mem (D+BitVec.ofNat 64 (firstLen base).toNat)
    (Spec.Gcm.gathered 64 base.mem (S+16) (count-1))
  next : t.gpr .r7=S+BitVec.ofNat 64 (16*count)


theorem tail_ok {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.GatherSplit.skip) Impl.Gather.PPC64LE.gather) s
      (TailResult s S D count) := by
  refine WP.seq (WP.mono (WP.keep VG.Proof.Gather.PPC64LE.gatherRegs (skip_ok h hc) (by decide)) fun u ⟨hu,hk⟩ => ?_)
  subst u
  have hk' : GKeeps s (skipped s) := ⟨hk.1,rfl,rfl,hk.2.1,hk.2.2⟩
  refine WP.mono (VG.Proof.Gather.PPC64LE.gather_advance_wp _ (tail_pre h hc)) fun t ht => ?_
  refine ⟨hk'.trans ht.2.1,ht.1,?_⟩
  rw [ht.2.2]
  change (S+16#64)+BitVec.ofNat 64 (16*(count-1))=S+BitVec.ofNat 64 (16*count)
  rw [Offset.add_add]
  congr 2
  omega


theorem tail_length {s : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) :
    (Spec.Gcm.gathered 64 s.mem (S+16) (count-1)).length=total-(firstLen s).toNat := by
  rw [Proof.Gcm.length_gathered]
  have hh := h.len
  rw [show count=(count-1)+1 by omega,Proof.Gcm.gatheredLen_cons] at hh
  rw [firstLen,h.r7]
  omega


theorem TailResult.frame {s t : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) (ht : TailResult s S D count t) :
    Frame [⟨D+BitVec.ofNat 64 (firstLen s).toNat,total-(firstLen s).toNat⟩] s.mem t.mem := by
  rw [ht.mem]
  apply writeBytes_frame
  rw [tail_length h hc]
  exact Region.contains_self _ _


theorem TailResult.input {s t : State} {S D : Addr} {count total : Nat}
    (h : GatherPre s S D count total) (hc : 0<count) (ht : TailResult s S D count t) :
    Spec.Aes.bytesAt t.mem (s.mem.readW S 64) (firstLen s).toNat ++
      (Spec.Aes.bytesAt t.mem D total).drop (firstLen s).toNat=Spec.Gcm.gathered 64 s.mem S count := by
  have hn := first_bound h hc
  have hl := tail_length h hc
  have hp := first_listed h hc
  have hs : Spec.Aes.bytesAt t.mem (s.mem.readW S 64) (firstLen s).toNat=
      Spec.Aes.bytesAt s.mem (s.mem.readW S 64) (firstLen s).toNat := by
    apply VG.Proof.Cmac.bytesAt_frame (ht.frame h hc) _ (by have := h.lt; omega)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact (h.lsd _ hp).sub_right (Offset.sub_base _ (by omega))
  rw [hs,SealSplit.PartialCopy.bytes_drop _ _ _ _ hn,ht.mem]
  have hr : Spec.Aes.bytesAt
      (writeBytes s.mem (D+BitVec.ofNat 64 (firstLen s).toNat) (Spec.Gcm.gathered 64 s.mem (S+16) (count-1)))
      (D+BitVec.ofNat 64 (firstLen s).toNat) (total-(firstLen s).toNat)=Spec.Gcm.gathered 64 s.mem (S+16) (count-1) := by
    rw [← hl]
    exact VG.Proof.AesGcm.bytesAt_writeBytes_self _ _ _ (by rw [hl]; have := h.lt; omega)
  rw [hr]
  have he := Proof.Gcm.gathered_cons s.mem S (count-1)
  rw [show count-1+1=count by omega] at he
  rw [he,firstLen,h.r7]

end VG.Proof.AesGcm.PPC64LE.GatherSplit
