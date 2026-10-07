import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntry

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem sum_relCT {C : Curve} {base : Addr} {size : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hc : Checks) (hcopy : FieldCT (.block (copyPt 4 K.R K.D))) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) E)
      (.seq (CachedJac.add K ops) (.block (copyPt 4 K.R K.D)))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈jointSlots cfg) (jointLive cfg) E' s t) := by
  have ha := add_relCT (base:=base) (E:=E) (V:=entryLive (jointLive cfg)) hL.lay hL.aligned hm hsize
    (by decide +kernel) (by decide +kernel) hOne hc
  apply RelCT.seq ha
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.lay hL.aligned
    (o:=K.R) (q:=K.D) (V:=[K.D.x,K.D.y,K.D.z]++entryLive (jointLive cfg))
    (by decide +kernel) (by decide +kernel) hcopy
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (by
    intro x hx
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hx))))⟩)

end VG.Proof.Weierstrass.AArch64.CachedField
