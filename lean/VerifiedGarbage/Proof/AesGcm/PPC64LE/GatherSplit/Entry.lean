module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Arguments
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: compose the shared gather entry with suffix-only gathering.
/-! # Entering the split gather path -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather


theorem entered_wp {s : State} (h : Lay s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealGather.entry) (allocated 160 s)
      fun e => Entered s e ∧ e.gpr .r10=s.gpr .r10 := by
  refine WP.mono (WP.keep [.r0,.r7,.r8,.r9,.r12] (Gather.entered_wp h) (by decide)) fun e he => ?_
  exact ⟨he.1,he.2.gpr (by decide)⟩


theorem suffix_frame {s e t : State} (h : Lay s) (he : Entered s e) (hc : 0<Cnt s)
    (ht : TailResult e (Src s) (Dst s) (Cnt s) t) : Frame [dR s] e.mem t.mem := by
  apply (ht.frame (gatherPre_of h he) hc).sub
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  refine ⟨dR s,List.mem_singleton_self _,Offset.sub_base _ ?_⟩
  have := first_bound (gatherPre_of h he) hc
  change (firstLen e).toNat+(L s-(firstLen e).toNat)≤L s
  omega


theorem suffix_slots {s e t : State} (h : Lay s) (he : Entered s e) (hc : 0<Cnt s)
    (ht : TailResult e (Src s) (Dst s) (Cnt s) t) : Slots s t.mem := by
  have fr := suffix_frame h he hc ht
  have read {a : Nat} (ha : a+8≤160) :
      t.mem.readW (Pf s+BitVec.ofNat 64 a) 64=(eMem s).readW (Pf s+BitVec.ofNat 64 a) 64 := by
    rw [← he.mem]
    exact fr.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact h.bd.sub_left (fr_sub s ha)) (by decide)
  have sl := slots_eMem s
  exact ⟨(read (by decide)).trans sl.c,(read (by decide)).trans sl.r,
    (read (by decide)).trans sl.n,(read (by decide)).trans sl.nl,
    (read (by decide)).trans sl.a,(read (by decide)).trans sl.al,
    (read (by decide)).trans sl.ra,(read (by decide)).trans sl.tg⟩

end VG.Proof.AesGcm.PPC64LE.GatherSplit
