module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

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
    refine wp_ldrx (a := p+BitVec.ofNat 64 (16*k)) (by constructor <;> omega)
      (by rw [kt.gpr .x19 (by decide),hp])
      (by rw [kt.rd,kt.wr]; exact hin k hk) fun u hu eu => ?_
    refine wp_strx (a := outAddr a k) (by constructor <;> omega)
      (by rw [hu.get .x20 (by decide),kt.gpr .x20 (by decide),ha]; rfl)
      (by rw [hu.wr,kt.wr]; exact hout k hk) fun v hv => wp_nil ?_
    have hm : v.mem=t.mem.writeW (outAddr a k) (t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64) := by
      rw [hv.mem,eu,hu.mem]
    have val : t.mem.readW (p+BitVec.ofNat 64 (16*k)) 64=A[k]! := by
      rw [ft.readW (r := pairR p) (Offset.contains_base p (by omega) (by omega))
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
      exact X2.word0 pair (by omega)
    refine ⟨((kt.trans hu.keep).trans hv.keep).mono (by simp),?_,fun i hi => ?_⟩
    · rw [hm]
      have hca : (rateR21 a).Contains (outAddr a k) 8 := Offset.contains_base a (by omega) (by omega)
      exact ft.writeW (by simp) _ hca
    · rw [hm]
      by_cases he : i=k
      · subst i; rw [Mem.readW_writeW_self64,val]
      · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (e := 8*k) (n := 8) (k := 8)
          (by omega) (by omega) (by omega)) (by decide)]
        exact old i (by omega)
  · exact Nat.le_refl _
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,Frame.refl _ _,fun i hi => by omega⟩

end VG.Proof.MlKem.AArch64.Paired
