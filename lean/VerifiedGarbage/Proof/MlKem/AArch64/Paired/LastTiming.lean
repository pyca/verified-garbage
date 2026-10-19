module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStartTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming

/-! # The odd final matrix entry has public-seed-only timing -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

def lastTail (sb ss a k off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.ite (.zero .x .x22) (fullSampleCode sb ss off a k w16) (.block []))
  (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i)))

theorem LastInput.afterStart {w16 : Bool} {s t : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (h : LastInput sb ss off p seed out table s)
    (ht : LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t)
    (sy : t.syms=s.syms) : LastInput sb ss off p seed out table t :=
  ⟨by rw [ht.keep.get .x28]; exact h.ptr,by rw [ht.keep.get .x28]; exact h.seedPtr,
   by rw [ht.keep.get .x28]; exact h.outPtr,by rw [ht.keep.rd,ht.keep.wr]; exact h.readable,
   h.separate,ht.context,by rw [sy]; exact h.symbol⟩

theorem LastStartPostW.seed {w16 : Bool} {s t : State} {p seed out table : Addr} {a k : Nat}
    (h : LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t)
    (hs : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out)) :
    seedBytes t.mem seed a k=seedBytes s.mem seed a k := by
  unfold seedBytes
  rw [bytesAt_frame h.frame (by
    intro r hr; simp only [fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl; exact hs; exact ho) (by decide : 32≤2^64)]

theorem last_exec {w16 : Bool} {sb ss a k off : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (lastCode sb ss a k off w16) s tr t) :
    Exec isa (.seq (lastStartCode sb ss a k off w16) (lastTail sb ss a k off w16)) s tr t := by
  obtain ⟨_,_,_,rfl,ei,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,es,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ec,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,er,h⟩ := seq_parts h
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec er))) h
  simpa only [lastStartCode,lastTail,List.append_assoc] using ee

theorem lastCode_relCT {w16 : Bool} {s u : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out))
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (lastCode sb ss a k off w16) (fun _ _=>True) := by
  let R := fun t v : State=>LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
    LastStartPostW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v ∧ t.syms=s.syms ∧ v.syms=u.syms
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sb ss a k off w16) R := by
    intro t v tr ur t' v' h et ev
    have hh := lastStart_relCT (by omega) hsb h8 hoff hk hk256 ps pu sp base seedEq
      t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨hh.1,hh.2.1,hh.2.2,Exec.syms et,Exec.syms ev⟩
  have branch : RelCT isa R (.ite (.zero .x .x22) (fullSampleCode sb ss off a k w16) (.block []))
      (fun t v=>t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19) := by
    refine RelCT.ite ?_ ?_ (RelCT.block_nil ?_)
    · intro t v h
      have ht := h.1.flag
      have hv := h.2.1.flag
      rw [seedEq] at ht
      have hx := BitVec.eq_of_toNat_eq (ht.trans hv.symm)
      change some (t.gpr .x22==0)=some (v.gpr .x22==0)
      rw [hx]
    · intro t v tr ur t' v' h et ev
      have ht := h.1.1
      have hv := h.1.2.1
      have hh := fullSampleCode_relCT hss hsb h8 hoff hk hk256
        (ps.afterStart ht h.1.2.2.1) (pu.afterStart hv h.1.2.2.2) ht.ptr hv.ptr ht.saved hv.saved
        (ht.keep.sp.trans (sp.trans hv.keep.sp.symm))
        (by rw [ht.keep.get .x28,hv.keep.get .x28,base])
        (by rw [ht.seed ps.separate ho,hv.seed pu.separate ho,seedEq])
        t v tr ur t' v' ⟨rfl,rfl⟩ et ev
      exact ⟨hh.1,hh.2.1.keep.sp.trans ((ht.keep.sp.trans (sp.trans hv.keep.sp.symm)).trans hh.2.2.keep.sp.symm),
        hh.2.1.ptr.trans hh.2.2.ptr.symm⟩
    · intro t v h
      exact ⟨h.1.1.keep.sp.trans (sp.trans h.1.2.1.keep.sp.symm),h.1.1.ptr.trans h.1.2.1.ptr.symm⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (lastStartCode sb ss a k off w16) (lastTail sb ss a k off w16)) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.seq branch ?_)
    intro t v tr ur t' v' h et ev
    exact ⟨restore_ct t v tr ur t' v' trivial trivial
      (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) et ev,trivial⟩
  intro t v tr ur t' v' h et ev
  exact grouped t v tr ur t' v' h (last_exec et) (last_exec ev)

theorem lastSample_relCT {w16 : Bool} {s u : State} {L : Impl.MlKem.AArch64.KemLay} {kg : Bool}
    {p seed out table : Addr}
    (hss : (if kg then Impl.MlKem.AArch64.KG.SS else Impl.MlKem.AArch64.KEM.SS)<4096)
    (hsb : (if kg then Impl.MlKem.AArch64.KG.SB else Impl.MlKem.AArch64.KEM.SB)+32≤32768)
    (h8 : (if kg then Impl.MlKem.AArch64.KG.SB else Impl.MlKem.AArch64.KEM.SB)%8=0)
    (hoff : (if kg then Impl.MlKem.AArch64.KG.AH else Impl.MlKem.AArch64.KEM.AH)+1024*(L.k*L.k-1)<65536)
    (hk : 0<L.k) (hk256 : L.k≤256)
    (ps : LastInput (if kg then Impl.MlKem.AArch64.KG.SB else Impl.MlKem.AArch64.KEM.SB)
      (if kg then Impl.MlKem.AArch64.KG.SS else Impl.MlKem.AArch64.KEM.SS)
      ((if kg then Impl.MlKem.AArch64.KG.AH else Impl.MlKem.AArch64.KEM.AH)+1024*(L.k*L.k-1)) p seed out table s)
    (pu : LastInput (if kg then Impl.MlKem.AArch64.KG.SB else Impl.MlKem.AArch64.KEM.SB)
      (if kg then Impl.MlKem.AArch64.KG.SS else Impl.MlKem.AArch64.KEM.SS)
      ((if kg then Impl.MlKem.AArch64.KG.AH else Impl.MlKem.AArch64.KEM.AH)+1024*(L.k*L.k-1)) p seed out table u)
    (ho : (Region.mk seed 32).Disjoint (polyRegion out))
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed (L.k*L.k-1) L.k=seedBytes u.mem seed (L.k*L.k-1) L.k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.lastSample L kg w16) (fun _ _=>True) := by
  rw [lastSample_eq]
  exact lastCode_relCT hss hsb h8 hoff hk hk256 ps pu ho sp base seedEq

end VG.Proof.MlKem.AArch64.Paired
