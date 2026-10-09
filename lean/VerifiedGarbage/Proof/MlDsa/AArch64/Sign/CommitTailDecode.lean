import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.Framework.AArch64.Inline

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Proof.MlDsa.AArch64.Pack VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Only Keep wp_movImm wp_nil)
open VG.Spec.MlDsa

def decodeRegs : List Reg := [.x0,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]

theorem decodeWidth_ok {s a : State}
    (ha : Only [.x9,.x13] s a)
    (h13 : a.gpr .x13=BitVec.ofNat 64 q)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (buWidth 524288 20 2 5) a fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun b hb h12 => wp_nil ?_
  refine WP.mono (unpackLoop_ok (buFin_ok 524288 20)
    (show Shape 20 2 5 from ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩)
    (v:=s.gpr .x0) (p:=s.gpr .x4) (s₀:=s) hin hout hsep
    (by rw [hb.get .x0,ha.get .x0]) (by rw [hb.get .x4,ha.get .x4]) h12
    (by rw [hb.get .x13,h13]) (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.mem.trans ha.mem))
    fun t ⟨hv,hf,hk⟩ => ⟨hv,hf,((ha.keep.trans hb.keep).trans hk).mono⟩

theorem decode_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  unfold VG.Impl.MlDsa.AArch64.Pack.bitUnpack
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun a ha h13 => wp_nil ?_
  refine sel_ok (by decide) (fun b hb h => ?_) (fun b hb _ => ?_)
  · rw [ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun c hc h => ?_) (fun c hc _ => ?_)
  · rw [hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun d hd h => ?_) (fun d hd _ => ?_)
  · rw [hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun e he h => ?_) (fun e he _ => ?_)
  · rw [hd.get .x1,hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  exact decodeWidth_ok (((((ha.trans hb).trans hc).trans hd).trans he).mono (by decide))
    (by rw [he.get .x13,hd.get .x13,hc.get .x13,hb.get .x13,h13]; rfl) hin hout hsep


theorem decode_access_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  let a := s.withRegions [⟨s.gpr .x0,640⟩] [polyRegion (s.gpr .x4)]
  obtain ⟨tr,t,he,hv,hf,hk⟩ := decode_ok (s:=a) h1 (by simp [a]) (by simp [a]) hsep
  have hw := VG.AArch64.Exec.widen he (rd:=s.rd) (wr:=s.wr)
    (Covers.append_left (Covers.one hin) (Covers.right (Covers.one hout))) (Covers.one hout)
  change Exec isa _ s tr (t.withRegions s.rd s.wr) at hw
  exact ⟨tr,_,hw,hv,hf,⟨hk.gpr,rfl,rfl,hk.sp,hk.vcs⟩⟩


theorem decode_poly {m n : Mem} {a out : Addr}
    (hc : ∀i<256,coeffAt n out i=buWord 524288 (inNum m a 20 /2^(20*i)%2^20)) :
    PolyIs n out (toRq (bitUnpack (Spec.Sha3.bytesAt m a 640) 524287 524288)) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hq : q=8380417 := rfl
  have hy := field_lt (inNum m a 20) 20 i (by decide)
  have hy' := hy
  unfold inNum at hy'
  rw [hc i hi,buWord,BitVec.toNat_setWidth,subModQ_toNat (by decide) (by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 0<q by decide)) (by decide)),
    toRq,Vector.getElem_map,bitUnpack_get _ _ _ hi]
  change _=(ofInt ((524288:Nat) -
    ((VG.Proof.MlKem.digits 8 ((Spec.Sha3.bytesAt m a 640).map BitVec.toNat) /2^(20*i)%2^20 : Nat) : Int))).val
  rw [ofInt_sub (by omega)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
