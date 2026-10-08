import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks

namespace VG.Proof.Weierstrass.AArch64.CachedInit
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.AArch64

def K : WinCfg := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256

def ops : List FOp := [.mul 6000 2912 2912,
  .mul 6032 6000 2912,
  .mul 6064 3008 3008,
  .mul 6096 6064 3008,
  .mul 6128 3104 3104,
  .mul 6160 6128 3104,
  .mul 6192 3200 3200,
  .mul 6224 6192 3200,
  .mul 6256 3296 3296,
  .mul 6288 6256 3296,
  .mul 6320 3392 3392,
  .mul 6352 6320 3392,
  .mul 6384 3488 3488,
  .mul 6416 6384 3488,
  .mul 6448 3584 3584,
  .mul 6480 6448 3584]

theorem ops_eq : CachedJac.cacheOps K=ops := rfl

def sources : List Nat := (List.range 8).map (fun i => 2912+96*i)
def outputs : List Nat := (List.range 16).map (fun i => 6000+32*i)

theorem values0 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6000=E 2912*E 2912 ∧
    runOps ops E 6032=(E 2912*E 2912)*E 2912 := by
  simp [ops,runOps,FOp.run]

theorem values1 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6064=E 3008*E 3008 ∧
    runOps ops E 6096=(E 3008*E 3008)*E 3008 := by
  simp [ops,runOps,FOp.run]

theorem values2 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6128=E 3104*E 3104 ∧
    runOps ops E 6160=(E 3104*E 3104)*E 3104 := by
  simp [ops,runOps,FOp.run]

theorem values3 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6192=E 3200*E 3200 ∧
    runOps ops E 6224=(E 3200*E 3200)*E 3200 := by
  simp [ops,runOps,FOp.run]

theorem values4 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6256=E 3296*E 3296 ∧
    runOps ops E 6288=(E 3296*E 3296)*E 3296 := by
  simp [ops,runOps,FOp.run]

theorem values5 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6320=E 3392*E 3392 ∧
    runOps ops E 6352=(E 3392*E 3392)*E 3392 := by
  simp [ops,runOps,FOp.run]

theorem values6 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6384=E 3488*E 3488 ∧
    runOps ops E 6416=(E 3488*E 3488)*E 3488 := by
  simp [ops,runOps,FOp.run]

theorem values7 {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) :
    runOps ops E 6448=E 3584*E 3584 ∧
    runOps ops E 6480=(E 3584*E 3584)*E 3584 := by
  simp [ops,runOps,FOp.run]

theorem values {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) (i : Nat) (hi : i<8) :
    runOps ops E (6000+64*i)=E (2912+96*i)*E (2912+96*i) ∧
    runOps ops E (6032+64*i)=(E (2912+96*i)*E (2912+96*i))*E (2912+96*i) := by
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact values0 E
  · exact values1 E
  · exact values2 E
  · exact values3 E
  · exact values4 E
  · exact values5 E
  · exact values6 E
  · exact values7 E

theorem reads : readsOk ops sources=true := by decide +kernel

theorem out_mem (op : FOp) (h : op∈ops) : op.out∈outputs := by
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem outputs_mem (x : Nat) (h : x∈outputs) : x∈ops.map FOp.out := by
  change x∈[6000,6032,6064,6096,6128,6160,6192,6224,6256,6288,6320,6352,6384,6416,6448,6480] at h
  exact h

theorem output_bounds (x : Nat) (h : x∈outputs) : 6000≤x ∧ x+32≤6512 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  have := List.mem_range.mp hi
  omega

theorem unchanged {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) {x : Nat} (hx : x<6000) :
    runOps ops E x=E x := by
  apply runOps_of_not_out
  intro op hop he
  have := (output_bounds op.out (out_mem op hop)).1
  omega

theorem pow_values {F : Type} [Lean.Grind.CommRing F] (E : Nat → F) (i : Nat) (hi : i<8) :
    runOps ops E (6000+64*i)=runOps ops E (2912+96*i)*runOps ops E (2912+96*i) ∧
    runOps ops E (6032+64*i)=runOps ops E (6000+64*i)*runOps ops E (2912+96*i) := by
  have h := values E i hi
  rw [unchanged E (x:=2912+96*i) (by omega),h.1,h.2]
  exact ⟨rfl,rfl⟩

theorem cache_ok {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hm : UnitMod m (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    (hS : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x) (hLo : ∀ op∈ops, Low K.M (op.out::op.ins))
    (hV : ∀ x∈sources,x∈V) :
    WP isa (CachedJac.cache K) s fun t =>
      ProgKeep K.M base outputs s t ∧
      Inv K.M base size m Sl (outputs++V) (runOps ops E) t := by
  rw [CachedJac.cache,ops_eq]
  refine WP.mono (fprogB_ok hL hAl hm ops hI hS hLo (readsOk_mono reads hV)) fun t ⟨kt,it⟩ => ?_
  refine ⟨kt.mono (fun x hx => ?_),it.sub (fun x hx => ?_)⟩
  · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact out_mem op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (outputs_mem x hx)
    · exact Or.inl hx

end VG.Proof.Weierstrass.AArch64.CachedInit
