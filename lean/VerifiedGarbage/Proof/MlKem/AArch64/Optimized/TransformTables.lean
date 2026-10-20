module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

def TransformTable (s : State) (symbol : String) (H : List Nat) : Prop :=
 (∀i<64,s.mem.readW (s.syms symbol+BitVec.ofNat 64 (8*i)) 64=Ntt16.hw4 H i) ∧
 Covers [⟨s.syms symbol,512⟩] (s.rd++s.wr) ∧
 ∀r∈s.wr,(Region.mk (s.syms symbol) 512).Disjoint r

structure TransformTables (s : State) : Prop where
 forward : TransformTable s "VG_MLKEM_NTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.tableHalves
 inverse : TransformTable s "VG_MLKEM_INTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.invTableHalves
 forwardStack : (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint (below s.sp 16)
 inverseStack : (Region.mk (s.syms "VG_MLKEM_INTT16_ZETAS") 512).Disjoint (below s.sp 16)

theorem TransformTable.apart {s : State} {symbol : String} {H : List Nat} (h : TransformTable s symbol H)
 {r : Region} (hc : Covers [r] s.wr) : (Region.mk (s.syms symbol) 512).Disjoint r := by
 intro addr ha hb
 have hi := hc addr 1 ⟨r,by simp,hb⟩
 obtain ⟨q,hq,hh⟩ := hi
 exact h.2.2 q hq addr ha hh

theorem TransformTable.ready {s : State} {symbol : String} {H : List Nat} {f w : Addr}
 (h : TransformTable s symbol H) (hc : Covers [polyRegion f,polyRegion w] s.wr) :
 Ntt16.Readonly.TableReady s symbol H f w := by
 exact ⟨h.1,h.2.1,(h.apart (fun a n hh=>hc a n (by
   obtain ⟨r,hr,ha⟩:=hh; exact ⟨r,by simp only [List.mem_singleton] at hr; simp [hr],ha⟩))).symm,
   (h.apart (fun a n hh=>hc a n (by
   obtain ⟨r,hr,ha⟩:=hh; exact ⟨r,by simp only [List.mem_singleton] at hr; simp [hr],ha⟩))).symm⟩

theorem TransformTable.frameFar {s t : State} {symbol : String} {H : List Nat} {rs : List Region}
 (h : TransformTable s symbol H) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hd : ∀r∈rs,(Region.mk (s.syms symbol) 512).Disjoint r) :
 TransformTable t symbol H := by
 refine ⟨?_,by simpa only [hs,hr,hw] using h.2.1,by simpa only [hs,hw] using h.2.2⟩
 intro i hi
 rw [hs,hf.readW (r:=⟨s.syms symbol,512⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
 exact h.1 i hi

theorem TransformTable.frame {s t : State} {symbol : String} {H : List Nat} {rs : List Region}
 (h : TransformTable s symbol H) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) : TransformTable t symbol H := by
 refine ⟨?_,by simpa only [hs,hr,hw] using h.2.1,by simpa only [hs,hw] using h.2.2⟩
 intro i hi
 rw [hs,hf.readW (r:=⟨s.syms symbol,512⟩) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)]
 · exact h.1 i hi
 · intro r hh
   exact h.apart (fun a n ⟨q,hq,ha⟩=>hc a n ⟨q,by rw [List.mem_singleton.mp hq]; exact hh,ha⟩)

theorem TransformTables.frame {s t : State} {rs : List Region} (h : TransformTables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
 (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) : TransformTables t :=
 ⟨h.forward.frame hs hr hw hf hc,h.inverse.frame hs hr hw hf hc,
   by simpa only [hs,hsp] using h.forwardStack,by simpa only [hs,hsp] using h.inverseStack⟩
theorem TransformTables.frameFar {s t : State} {rs : List Region} (h : TransformTables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hsp : t.sp=s.sp)
 (hf : Frame rs s.mem t.mem)
 (hd : ∀r∈rs,(Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r ∧
   (Region.mk (s.syms "VG_MLKEM_INTT16_ZETAS") 512).Disjoint r) : TransformTables t :=
 ⟨h.forward.frameFar hs hr hw hf (fun r hr=>(hd r hr).1),
   h.inverse.frameFar hs hr hw hf (fun r hr=>(hd r hr).2),
   by simpa only [hs,hsp] using h.forwardStack,by simpa only [hs,hsp] using h.inverseStack⟩

end VG.Proof.MlKem.AArch64.Optimized
