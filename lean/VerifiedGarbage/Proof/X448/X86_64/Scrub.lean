module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.X448.X86_64.Exchange
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
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
`Impl.Scrub.X86_64.scrubSel` (`X86_64.Scrub.verifiedScrubbedSel`), which clears every
caller-saved register and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Its postcondition reads the memory
on return only within `out` (`X86_64.Scrub.PostOut`), as does that of
`vg_x448_exchange` (`exchangeOut`), which returns with its whole stack wiped
(`Impl.Scrub.X86_64.scrubAll`).
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


/-! ## The functions as emitted -/

theorem exchange_codeSp (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Xdh.X86_64.exchange ("vg_x448" ++ v.suffix) (code v) 56).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases v <;> sp_safe

/-- `vg_x448_exchange` as emitted (`Impl.X448.X86_64.Fn.x448`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem exchange_scrubbed (v : Impl.Ed448.X86_64.FieldVariant) :
    VerifiedScrubbed X86_64.target (Impl.X448.X86_64.Fn.x448 v)
      (Spec.X448.exchangeApi.contract X86_64.abi 24) 32 := by
  cases v
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.X448.exchangeApi)
      { code := _
        stack := 24
        verified := Exchange.exchange_variant .scalar
        spSafe := exchange_codeSp .scalar } .sse (exchangeOut _)
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.X448.exchangeApi)
      { code := _
        stack := 24
        verified := Exchange.exchange_variant .adx
        spSafe := exchange_codeSp .adx } .sse (exchangeOut _)

theorem exchange_spSafe (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.X448.X86_64.Fn.x448 v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (exchange_codeSp v)

theorem base_codeSp (v : Impl.Ed448.X86_64.FieldVariant) :
    (codeBase v).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases v <;> sp_safe

/-- `vg_x448_base` as emitted (`Impl.X448.X86_64.Fn.x448Base`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem base_scrubbed (v : Impl.Ed448.X86_64.FieldVariant) :
    VerifiedScrubbed X86_64.target (Impl.X448.X86_64.Fn.x448Base v)
      (Spec.X448.x448BaseApi.contract X86_64.abi 8) 0 := by
  cases v
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.X448.x448BaseApi)
      { code := _
        stack := 8
        verified := codeBase_verified .scalar
        spSafe := base_codeSp .scalar } .sse (baseOut)
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.X448.x448BaseApi)
      { code := _
        stack := 8
        verified := codeBase_verified .adx
        spSafe := base_codeSp .adx } .sse (baseOut)

theorem base_spSafe (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.X448.X86_64.Fn.x448Base v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (base_codeSp v)

end VG.Proof.X448.X86_64
