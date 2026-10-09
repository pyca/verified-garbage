import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductWord

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- The two banks use disjoint registers, excluding the product and
butterfly temporaries and all immutable arithmetic constants. -/
theorem banks_nodup : ((List.range 16).map vr).Nodup := by decide

theorem bank_safe {j : Nat} (hj : j<16) :
    vr j∉([.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31] : List VReg) := by
  have h : ∀j∈List.range 16,vr j∉([.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31] : List VReg) := by decide
  exact h j (List.mem_range.mpr hj)

theorem bank_injective {a b : Nat} (ha : a<16) (hb : b<16) (h : vr a=vr b) : a=b := by
  have hi : ∀a b:Fin 16,vr a.val=vr b.val → a=b := by decide
  exact congrArg Fin.val (hi ⟨a,ha⟩ ⟨b,hb⟩ h)

/-- Both interleaved r0 lanes have equal length, so zip discards neither
lane's final norm accumulation. -/
theorem r0Lane_length (g : Nat) (raw a t h other : VReg) (off : Nat) :
    (r0Lane g raw a t h other off).length=if g==261888 then 24 else 26 := by
  simp only [r0Lane,List.length_append,List.length_cons,List.length_nil]
  split <;> simp_all

end VG.Proof.MlDsa.AArch64.Optimized.Paired
