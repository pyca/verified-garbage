module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
/-! # The odd final matrix entry has public-seed-only timing -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/LastPrepare.lean`, which only this module imported.
section

/-! # Shared-seed timing for the first singleton rejection pass -/
section
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
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/LastStartTiming.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

theorem lastStart_relCT {w16 : Bool} {s u : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sb ss a k off w16)
      (fun t v=>LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
        LastStartPostW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v) := by
  let R := fun t v : State=>LastPreparedW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
    LastPreparedW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (prepareCode sb ss a a k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨prepare_ct sb ss a a k s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (lastPrepare_ok hss hsb h8 hk hk256 ps) et,
      exec_post (lastPrepare_ok hss hsb h8 hk hk256 pu) ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (prepareCode sb ss a a k) (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    have ht28 := h.1.keep.get .x28
    have hv28 := h.2.keep.get .x28
    have rr := reject_relCT (by decide) hoff (by decide : Reg.x22≠.x3 ∧ Reg.x22≠.x4)
      (by rw [h.1.pointer,ht28,ps.outPtr]; exact h.1.env)
      (by rw [h.2.pointer,hv28,pu.outPtr]; rw [seedEq]; exact h.2.env)
      h.1.constants h.2.constants
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)) (h.1.pointer.trans h.2.pointer.symm)
      (by rw [ht28,hv28,base]) (h.1.tablePtr.trans h.2.tablePtr.symm)
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev
    exact ⟨rr.1,trivial⟩
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sb ss a k off w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (lastStart_ok hss hsb h8 hoff hk hk256 ps.ptr ps.seedPtr ps.outPtr ps.readable ps.separate ps.context ps.symbol) et,
    exec_post (lastStart_ok hss hsb h8 hoff hk hk256 pu.ptr pu.seedPtr pu.outPtr pu.readable pu.separate pu.context pu.symbol) ev⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

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
