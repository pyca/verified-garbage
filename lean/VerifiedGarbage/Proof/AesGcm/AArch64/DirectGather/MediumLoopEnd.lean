module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumLayout
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.MediumFinish
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Framework.Offset

/-! Relate the descriptor loop's two ciphertext outputs to the bytes consumed by GHASH. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Mid

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather VG.Impl.AesGcm.AArch64.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt ctxH inc32 gctr)

structure Ready (o t : State) : Prop extends Header o t, Cursors o t where
  mask : blockAt t.mem (base o+224) = shortCipher o (shortJ0 o)
  stream : ∀ j < L o, t.mem (base o+240+BitVec.ofNat 64 j) =
    Proof.Gcm.ksByte (shortCipher o) (inc32 (shortJ0 o)) j
  input : bytesAt t.mem (ghBase o) 256 = aadLayout o
  zero : blockAt t.mem (base o+736) = 0

theorem loopFinish {o s t : State} (l : Gather.Lay .plain o) (hn : L o ≤ 224) (al : AL o ≤ 16)
    (h : Ready o s) (p : Fragment.AtDesc s (Fragment.num s) t) :
    MediumFinishPre o t (base o) (14-blocks o) ∧ Frame [scratch o,dR o] s.mem t.mem := by
  have ag := h.toLocalMem.descriptors l
  have gl : Fragment.total s = L o := by
    simpa only [Fragment.total,Fragment.gl,Fragment.ds,Fragment.num,h.ds,h.n] using
      (Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) ag).trans l.hgl
  have plain : Fragment.pt s (Fragment.num s) = pt o (Cnt o) := by
    simpa only [Fragment.pt,Fragment.ds,Fragment.num,h.ds,h.n] using
      Proof.AesGcm.gathered_congr_le (Nat.le_refl _) ag
  let slot : Region := ⟨base o+BitVec.ofNat 64 (textOff o),L o⟩
  have f : Frame [dR o,slot] s.mem t.mem := by
    simpa only [Fragment.outRegions,Fragment.dout,Fragment.gout,gl,h.d,h.auth] using p.frame
  have slotSub : slot.Sub (scratch o) := Offset.sub_base _ (by
    change 480+240-16*blocks o+L o ≤ 752
    unfold blocks; omega)
  have ds := l.bd.sub_left (scratch_sub o)
  have ts := l.bt.sub_left (scratch_sub o)
  have small : Frame [scratch o,dR o] s.mem t.mem := f.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,by simp,fun _ => id⟩
    · exact ⟨_,List.mem_cons_self ..,List.mem_singleton.mp hr ▸ slotSub⟩
  have whole := (h.frame.mono (fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))).trans small
  have hashSub : Region.Sub ⟨K o+240#64,16⟩ (kR .plain o) := Offset.sub_base _ (by decide)
  obtain ⟨_,wr,kd,_,_,_,_,_,_,_,_,dt,da,_,_,_,_,_,_,sa,_⟩ := l.pre
  let g (r : Reg) (hr : r ∉ Fragment.loopRegs) := p.gpr r hr
  have kc : Covers [kR .plain o] (t.rd ++ t.wr) := Covers.of_mem fun r hr => by
    rw [p.rd,h.rd,l.pre.1,List.mem_singleton.mp hr]; simp
  have hkey : Covers [⟨K o+240#64,16⟩] (t.rd ++ t.wr) := covers_off kc (by decide) (by decide)
  have ct := p.gctr (shortCipher o) (inc32 (shortJ0 o)) (fun j hj => by
    change j < Fragment.total s at hj; rw [gl] at hj
    simpa only [Fragment.off,h.key] using h.stream j (by omega))
  change bytesAt t.mem _ (Fragment.total s) = _ ∧ bytesAt t.mem _ (Fragment.total s) = _ at ct
  rw [h.d,h.auth,gl,plain] at ct
  have apart {r : Region} (a : (stkR o).Disjoint r) (b : r.Disjoint (dR o)) :
      ∀ q ∈ [scratch o,dR o], r.Disjoint q := by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact (a.sub_left (scratch_sub o)).symm
    · exact List.mem_singleton.mp hq ▸ b
  have args : t.mem.readW (base o+768) 64 = Tg o := by
    rw [whole.readW (r := argR o) (by
      have e := scratchArg o 2
      change base o + 768 = stackArgAddr o 2 at e
      rw [e,l.hargR,l.hA]; apply contains_off <;> decide)
      (apart sa da.symm) (by decide)]
    change o.mem.readW (base o + BitVec.ofNat 64 (Medium.work+8*2)) 64 = _
    rw [scratchArg]; rfl
  have hc : blocks o ≤ 14 := by unfold blocks; omega
  refine ⟨⟨(g _ (by decide)).trans h.x19,(g _ (by decide)).trans h.x21,
    (g _ (by decide)).trans h.x24,(g _ (by decide)).trans h.x26,p.sp.trans h.sp,
    h.saved.frame f ?_,p.wr ▸ h.scratchWr,hkey,?_,?_,args,(l.bk.sub_left (scratch_sub o)).symm.sub_left hashSub,
    ds.symm,ts.symm,dt,al,?_,?_,ct.1,?_,?_⟩,small⟩
  · intro r hr; rcases List.mem_cons.mp hr with rfl|hr
    · exact ds.sub_left (Offset.sub_base _ (by decide))
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by change 128+88 ≤ 480+240-16*blocks o; omega)) (by decide)
        (by change 480+240-16*blocks o+L o ≤ 2^64; omega)
  · rw [p.rd,p.wr]; exact h.toLocalMem.argRead l 2 (by decide)
  · rw [p.wr,h.wr,wr]; exact ⟨tgR o,by simp,Region.contains_self _ _⟩
  · apply blockAt_frame whole
    exact fun r hr => (apart l.bk kd r hr).sub_left hashSub
  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (Offset.sub_base _ (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inl (by change 224+16 ≤ 480+240-16*blocks o; omega)) (by decide)
          (by change 480+240-16*blocks o+L o ≤ 2^64; omega))]
    exact h.mask
  · exact authFilled l hn al _ (Proof.AesCcm.length_bytesAt _ _ _) f h.input (ct.2.trans ct.1.symm)


  · rw [blockAt_frame f (by
      intro r hr; rcases List.mem_cons.mp hr with rfl|hr
      · exact ds.sub_left (Offset.sub_base _ (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inr (by change 480+240-16*blocks o+L o ≤ 736; unfold blocks; omega)) (by decide)
          (by change 480+240-16*blocks o+L o ≤ 2^64; omega))]
    exact h.zero

end VG.Proof.AesGcm.AArch64.DirectGather.Mid
