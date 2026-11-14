module

public import VerifiedGarbage.Proof.X448.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Instances
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit

/-!
# X448 on x86-64, without secret residue

`vg_x448_base`, with each backend of the field, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Its postcondition reads the memory
on return only within `out` (`X86_64.Scrub.PostOut`), as does that of
`vg_x448_exchange` (`exchangeOut`), which returns with its whole stack wiped
(`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem baseOut : PostOut (Spec.X448.x448BaseContract X86_64.abi 8) (Spec.X448.x448BaseSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.x448BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _
    have : Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
      simp only [Spec.X448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
    rw [this]; exact h

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X448.exchangeContract X86_64.abi stack) (Spec.X448.exchangeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _ ∧ _
    have : Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
      simp only [Spec.X448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      exact (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
    rw [this]; exact h

def baseScalarKs : List Nat := keep_for% Spec.X448.x448BaseApi.sig 8 Impl.X448.X86_64.x448Base []

theorem baseScalarOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.X448.x448BaseApi.sig 8 []) Impl.X448.X86_64.x448Base
      h).any (RScrub.resOkB · 8 baseScalarKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of baseScalarKs (by taint_decide)

def baseAdxKs : List Nat := keep_for% Spec.X448.x448BaseApi.sig 8 Impl.X448.X86_64.x448BaseAdx []

theorem baseAdxOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.X448.x448BaseApi.sig 8 []) Impl.X448.X86_64.x448BaseAdx
      h).any (RScrub.resOkB · 8 baseAdxKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of baseAdxKs (by taint_decide)

/-- The residue analysis of `vg_x448_base` with the field backend `v`. -/
def baseAnalysed : (v : Impl.Ed448.X86_64.FieldVariant) →
    RScrub.Analysed Spec.X448.x448BaseApi.sig 8 [] (codeBase v)
  | .scalar => ⟨baseScalarKs, baseScalarOk⟩
  | .adx => ⟨baseAdxKs, baseAdxOk⟩

open VG.X86_64.RScrub in
/-- `vg_x448_base` with the field backend `v`. -/
def baseReg (v : Impl.Ed448.X86_64.FieldVariant) : Registration Spec.X448.x448BaseApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := codeBase v
    stack := 8
    verified := codeBase_verified v } baseOut [] (pubOk_nil _) (some (baseAnalysed v))

end VG.Proof.X448.X86_64
