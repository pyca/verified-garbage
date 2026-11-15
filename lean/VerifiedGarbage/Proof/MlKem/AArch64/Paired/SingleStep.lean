module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlKem.AArch64.Paired.SingleWords`, which only this module used -/

section

/-! # Serialize one lane of the paired permutation for the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def singleWords : List Instr := (List.range 21).flatMap fun i =>
 [.ldr .x .x6 .x19 (16*i),.str .x .x6 .x20 (8*i)]

theorem singleWords_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀i<21,InRegions s.wr (outAddr a i) 8)
    (hd : (pairR p).Disjoint (rateR21 a)) :
    WP isa (.block singleWords) s fun t =>
      Keep [.x6] s t ∧ Frame [rateR21 a] s.mem t.mem ∧ Rate21 t.mem a A := by
  apply wp_range_flatMap (M := isa) (N := 21)
    (fun k t => Keep [.x6] s t ∧ Frame [rateR21 a] s.mem t.mem ∧
      ∀i<k,t.mem.readW (outAddr a i) 64=A[i]!)
  · intro k t hk ⟨kt,ft,old⟩
    refine wp_ldrx (a := p+BitVec.ofNat 64 (16*k)) (by constructor <;> omega_arith)
      (by rw [kt.gpr .x19 (by decide),hp])
      (by rw [kt.rd,kt.wr]; exact hin k hk) fun u hu eu => ?_
    refine wp_strx (a := outAddr a k) (by constructor <;> omega_arith)
      (by rw [hu.get .x20 (by decide),kt.gpr .x20 (by decide),ha]; rfl)
      (by rw [hu.wr,kt.wr]; exact hout k hk) fun v hv => wp_nil ?_
    have hm : v.mem=t.mem.writeW (outAddr a k) (t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64) := by
      rw [hv.mem,eu,hu.mem]
    have val : t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64=A[k]! := by
      rw [ft.readW (r := pairR p) (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
      exact X2.word0 pair (by omega_using [hk])
    refine ⟨((kt.trans hu.keep).trans hv.keep).mono (by simp),?_,fun i hi => ?_⟩
    · rw [hm]
      have hca : (rateR21 a).Contains (outAddr a k) 8 := Offset.contains_base a (by omega_using [hk]) (by omega_using [hk])
      exact ft.writeW (by simp) _ hca
    · rw [hm]
      by_cases he : i=k
      · subst i; rw [Mem.readW_writeW_self64,val]
      · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (e := 8*k) (n := 8) (k := 8)
          (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])) (by decide)]
        exact old i (by omega_using [hi, he])
  · exact Nat.le_refl _
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,Frame.refl _ _,fun i hi => by omega⟩

end VG.Proof.MlKem.AArch64.Paired

end

end


/-! # One singleton fallback permutation and serialization -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def singleRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x20,.x22]
def singleBody : Prog isa := .seq (Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
 (.block (singleWords ++ [.addImm .x .x20 .x20 168,.subImm .x .x22 .x22 1]))

theorem singleStep_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀i<21,InRegions s.wr (outAddr a i) 8)
    (hd : (pairR p).Disjoint (rateR21 a))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa singleBody s fun t =>
      Keep singleRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      Rate21 t.mem a (Spec.Sha3.keccakF A) ∧
      Frame [pairR p,rateR21 a,X2.callR (p+1536)] s.mem t.mem ∧
      t.gpr .x20=a+168 ∧ t.gpr .x22=s.gpr .x22-1 := by
  refine WP.seq (WP.mono (X2.call_ok (by decide) (by decide) hp
    (by rw [hp]; rfl) hpw pair hcov) fun u ⟨ku,fu,pu⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (singleWords_ok ((ku.gpr .x19 (by decide)).trans hp)
    ((ku.gpr .x20 (by decide)).trans ha) pu
    (fun i hi => by rw [ku.rd,ku.wr]; exact hin i hi)
    (fun i hi => by rw [ku.wr]; exact hout i hi) hd) fun v ⟨kv,fv,av⟩ => ?_
  refine wp_addImm (by decide) fun w hw ew => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have ou : Keep X2.clobbered s u := ⟨ku.gpr,ku.rd,ku.wr,ku.sp,ku.vcs⟩
  have ot : Only [.x20,.x22] v t := (hw.trans ht).mono (by simp)
  refine ⟨(((ou.trans kv).trans ot.keep)).mono (by decide),?_,?_,?_,?_,?_⟩
  · intro i hi; rw [ot.mem,fv.read (pair_contains p hi)
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by decide)]; exact pu i hi
  · rw [ot.mem]; exact av
  · rw [ot.mem]; exact (fu.mono (by simp)).trans (fv.mono (by simp))
  · rw [ht.get .x20 (by decide),ew,kv.gpr .x20 (by decide),ku.gpr .x20 (by decide),ha]; rfl
  · rw [et,hw.get .x22 (by decide),kv.gpr .x22 (by decide),ku.gpr .x22 (by decide)]; rfl

end VG.Proof.MlKem.AArch64.Paired
