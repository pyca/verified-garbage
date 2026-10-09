import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChoice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejValue

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc)
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def fourResult (m : Mem) (p : Addr) (L : List Zq) : List Zq :=
 acc (acc (acc (acc L (candidate m p)) (candidate m (p+3)))
   (candidate m (p+6))) (candidate m (p+9))

structure Constants (s : State) : Prop where
 index : s.v .v3=gatherIndex
 mask : ∀e<4,vword (s.v .v4) e=0x7fffff
 modulus : ∀e<4,vword (s.v .v5) e=8380417
 ones : s.gpr .x12=0x100000001
 qreg : (s.gpr .x9).toNat=q

/-- Four decoded coefficients are consumed in their original stream order,
regardless of whether the vector fast path or scalar fallback executes. -/
theorem fourStep_ok {s : State} {p : Addr} {L : List Zq}
    (hconst : Constants s)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+4≤256)
    (hst : Stored s.mem p L)
    (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4)
    (hw16 : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.seq (.block vectorTry)
      (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject))) s fun t =>
      Keep (([.x6,.x7] : List Reg)++fallbackRegs) s t ∧
      Frame [polyR p] s.mem t.mem ∧ Constants t ∧
      t.gpr .x3=coeffAddr p (fourResult s.mem (s.gpr .x2) L).length ∧
      (t.gpr .x4).toNat=256-(fourResult s.mem (s.gpr .x2) L).length ∧
      Stored t.mem p (fourResult s.mem (s.gpr .x2) L) := by
  refine WP.seq (WP.mono (vectorTry_ok hr hconst.index)
    fun a ⟨ha,hm,hvec,hv,hflag⟩ => ?_)
  have hval (e : Nat) (he : e<4) :
      (vword (a.v .v1) e).toNat=candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (3*e)) := by
    rw [hv]
    exact candidates_word s.mem _ _ he (hconst.mask e he)
  have hbound (e : Nat) (he : e<4) : (vword (a.v .v1) e).toNat<2^23 := by
    rw [hval e he]; exact candidate_bound _ _
  have hbranch : a.gpr .x6=0 ↔ ∀e<4,(vword (a.v .v1) e).toNat<q := by
    rw [hflag,hconst.ones]
    have hh := accepted_all (candidates (s.mem.read (s.gpr .x2) 16) (s.v .v4)) (s.v .v5)
      hconst.modulus (by intro e he; rw [←hv]; exact hbound e he)
    simpa only [hv] using hh
  have hresult : laneFold a.v fourLanes L=fourResult s.mem (s.gpr .x2) L := by
    simp only [laneFold,fourLanes]
    rw [hval 0 (by decide),hval 1 (by decide),hval 2 (by decide),hval 3 (by decide)]
    rw [show s.gpr .x2+BitVec.ofNat 64 (3*0)=s.gpr .x2 by bv_omega]
    rfl
  refine WP.mono (fourChoice_ok (p := p) (L := L) hbound hbranch (by rw [ha.get .x9]; exact hconst.qreg)
    (by rw [ha.get .x3]; exact h3) (by rw [ha.get .x4]; exact h4) hL
    (by rw [hm]; exact hst) (fun i hi => by rw [ha.wr]; exact hw i hi)
    (by rw [ha.wr,ha.get .x3]; exact hw16)) fun t ⟨ht,hvfinal,hframe,hp,hcount,hstored⟩ => ?_
  rw [hresult] at hp hcount hstored
  refine ⟨ha.trans ht,by rw [←hm]; exact hframe,?_,hp,hcount,hstored⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hvfinal,hvec .v3 (by decide) (by decide) (by decide)]; exact hconst.index
  · intro e he
    rw [hvfinal,hvec .v4 (by decide) (by decide) (by decide)]; exact hconst.mask e he
  · intro e he
    rw [hvfinal,hvec .v5 (by decide) (by decide) (by decide)]; exact hconst.modulus e he
  · rw [ht.get .x12,ha.get .x12]; exact hconst.ones
  · rw [ht.get .x9,ha.get .x9]; exact hconst.qreg

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
