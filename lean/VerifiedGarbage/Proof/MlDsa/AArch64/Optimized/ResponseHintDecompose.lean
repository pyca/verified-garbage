import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

/-- Recombining high and signed low parts recovers the original field element. -/
theorem hintBase_parts {g : Nat} (hg : IsG g) (r : Zq) :
    ofInt (lowBits g r+2*(g:Int)*(highBits g r).toNat)=r := by
  -- `LowBits + 2γ₂·HighBits` is `r`, less `q` when `f = m`.
  have he : lowBits g r+2*(g:Int)*(highBits g r).toNat=
      (r.val:Int)-(if hbF g r.val=hbM g then (q:Int) else 0) := by
    rw [lowBits_eq (mem_of_isG hg),highBits_eq (mem_of_isG hg),Int.toNat_natCast,
      Int.natCast_mul,Int.natCast_mul,Int.mul_comm (2*(g:Int)),Int.sub_sub,
      Int.add_comm (_*_),←Int.sub_sub,show ((2:Nat):Int)=2 from rfl,Int.sub_add_cancel]
  rw [he]
  apply Fin.ext
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val ((r.val:Int)-(if hbF g r.val=hbM g then (q:Int) else 0))
  have hr := r.isLt
  have hq : ((q:Nat):Int)=8380417 := rfl
  by_cases hc : hbF g r.val=hbM g <;> simp only [hc,ite_true,ite_false] at hv ⊢ <;> omega

theorem responseHintBase_parts {m : Mem} {low high : Addr} {g i : Nat} (hg : IsG g) {r : Zq}
    (hl : (coeffAt m low i).toInt=lowBits g r)
    (hh : (coeffAt m high i).toNat=(highBits g r).toNat) : responseHintBase m low high g i=r := by
  unfold responseHintBase
  rw [hl,hh,hintBase_parts hg]

theorem responseDecomposed_parts {m : Mem} {low high : Addr} {g : Nat} (hg : IsG g) (f : Poly)
    (hl : ∀i<n,(coeffAt m low i).toInt=lowBits g f[i]!)
    (hh : ∀i<n,(coeffAt m high i).toNat=(highBits g f[i]!).toNat) : ResponseDecomposed m low high g := by
  intro i hi
  rw [responseHintBase_parts hg (hl i hi) (hh i hi)]
  exact ⟨hl i hi,hh i hi⟩

theorem responseHintPoly_parts {m : Mem} {low ct high : Addr} {g : Nat} (hg : IsG g) (f c : Poly)
    (hl : ∀i<n,(coeffAt m low i).toInt=lowBits g f[i]!)
    (hh : ∀i<n,(coeffAt m high i).toNat=(highBits g f[i]!).toNat)
    (hc : signedPolyAt m ct=c) :
    responseHintPoly m low ct high g=Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) c f := by
  apply Vector.ext
  intro i hi
  simp only [responseHintPoly,Vector.getElem_ofFn,Vector.getElem_zipWith]
  have hl' := hl i hi
  have hh' := hh i hi
  rw [responseHintBase_parts hg hl' hh']
  have he : ofInt (coeffAt m ct i).toInt=c[i] := by
    rw [←hc]
    simp only [signedPolyAt,Vector.getElem_ofFn]
  rw [he,getElem!_pos f i hi]

theorem small_signed_injective {a b : Int} (ha : -524288≤a ∧ a≤524288)
    (hb : -524288≤b ∧ b≤524288) (he : ofInt a=ofInt b) : a=b := by
  have h1 := VG.Proof.MlDsa.KeyGen.ofInt_val a
  have h2 := VG.Proof.MlDsa.KeyGen.ofInt_val b
  rw [he] at h1
  omega

theorem hintLow_exact {m : Mem} {low : Addr} {g : Nat} {f : Poly} (hg : IsG g)
    (hl : SignedPolyIs m low (f.map fun r=>ofInt (lowBits g r)) (-(g:Int)) g) :
    ∀i<n,(coeffAt m low i).toInt=lowBits g f[i]! := by
  intro i hi
  have hb := hl.1 i hi
  have hv := hl.2 i hi
  have hr := lowBits_bounds hg f[i]!
  have hg' : g≤524288 := by rcases hg with rfl|rfl <;> decide
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi,Vector.getElem_map,
    ←VG.Proof.MlDsa.Arith.getElem!_eq f hi] at hv
  exact small_signed_injective (by omega) (by omega) hv

theorem hintHigh_exact {m : Mem} {high : Addr} {g : Nat} {f : Poly}
    (hh : NatPolyIs m high (f.map fun r=>(highBits g r).toNat)) :
    ∀i<n,(coeffAt m high i).toNat=(highBits g f[i]!).toNat := by
  intro i hi
  have he := congrArg (fun v : Vector Nat n=>v[i]) hh
  simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map] at he
  rw [VG.Proof.MlDsa.Arith.getElem!_eq f hi]
  exact he

theorem HintNormPost.field {g : Nat} {m m' : Mem} {low ct high : Addr} {r : BitVec 64} {f c : Poly}
    (hp : HintNormPost g m m' low ct high r) (hg : IsG g)
    (hl : SignedPolyIs m low (f.map fun r=>ofInt (lowBits g r)) (-(g:Int)) g)
    (hh : NatPolyIs m high (f.map fun r=>(highBits g r).toNat))
    (hc : RawPolyIs m ct c) :
    HintIs m' low 1 [Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) c f] ∧
    r=BitVec.ofNat 64 (hintOnes [Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) c f]+
      if normRq [c]<g then 4294967296 else 0) := by
  have he := responseHintPoly_parts hg f c (hintLow_exact hg hl) (hintHigh_exact hh) hc.2
  simpa only [HintNormPost,he,hc.2] using hp

end VG.Proof.MlDsa.AArch64.Optimized.Response
