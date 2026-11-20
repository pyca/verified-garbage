module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.MlKem.X86_64.Fn
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-!
# ML-KEM's encapsulation-key check on x86-64, without secret residue

`vg_mlkem768_check_ek` and `vg_mlkem1024_check_ek`, with and without AVX2,
each followed by its cleanup, which clears every register it may write
(`X86_64.Scrub.verifiedScrubbedAll`; they use no stack). Their postconditions read only the memory on entry.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

theorem checkEkOut : PostOut (Spec.MlKem.checkEkContract abi) (Spec.MlKem.checkEkSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨ek, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

theorem checkEk1024Out : PostOut (Spec.MlKem1024.checkEkContract abi) (Spec.MlKem1024.checkEkSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨ek, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

theorem checkEk_codeSp : Impl.MlKem.X86_64.checkEk.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlKem.checkEkApi`'s function as emitted (`Impl.MlKem.X86_64.Fn.checkEk`) meets its contract in constant
time and returns without secret residue. -/
theorem checkEk_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86_64.Fn.checkEk (Spec.MlKem.checkEkApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem.checkEkApi)
    { code := Impl.MlKem.X86_64.checkEk, verified := Proof.MlKem.X86_64.checkEk_verified, spSafe := checkEk_codeSp } .sse checkEkOut

theorem checkEk_spSafe : Impl.MlKem.X86_64.Fn.checkEk.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe checkEk_codeSp

theorem checkEkAvx2_codeSp : Impl.MlKem.X86_64.checkEkAvx2.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlKem.checkEkApi`'s function as emitted (`Impl.MlKem.X86_64.Fn.checkEkAvx2`) meets its contract in constant
time and returns without secret residue. -/
theorem checkEkAvx2_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86_64.Fn.checkEkAvx2 (Spec.MlKem.checkEkApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem.checkEkApi)
    { code := Impl.MlKem.X86_64.checkEkAvx2, verified := Proof.MlKem.X86_64.checkEkAvx2_verified, spSafe := checkEkAvx2_codeSp } .avx checkEkOut

theorem checkEkAvx2_spSafe : Impl.MlKem.X86_64.Fn.checkEkAvx2.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe checkEkAvx2_codeSp

theorem checkEk1024_codeSp : Impl.MlKem1024.X86_64.checkEk1024.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlKem1024.checkEkApi`'s function as emitted (`Impl.MlKem.X86_64.Fn.checkEk1024`) meets its contract in constant
time and returns without secret residue. -/
theorem checkEk1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86_64.Fn.checkEk1024 (Spec.MlKem1024.checkEkApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem1024.checkEkApi)
    { code := Impl.MlKem1024.X86_64.checkEk1024, verified := Proof.MlKem1024.X86_64.checkEk1024_verified, spSafe := checkEk1024_codeSp } .sse checkEk1024Out

theorem checkEk1024_spSafe : Impl.MlKem.X86_64.Fn.checkEk1024.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe checkEk1024_codeSp

theorem checkEk1024Avx2_codeSp : Impl.MlKem1024.X86_64.checkEk1024Avx2.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `Spec.MlKem1024.checkEkApi`'s function as emitted (`Impl.MlKem.X86_64.Fn.checkEk1024Avx2`) meets its contract in constant
time and returns without secret residue. -/
theorem checkEk1024Avx2_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86_64.Fn.checkEk1024Avx2 (Spec.MlKem1024.checkEkApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem1024.checkEkApi)
    { code := Impl.MlKem1024.X86_64.checkEk1024Avx2, verified := Proof.MlKem1024.X86_64.checkEk1024Avx2_verified, spSafe := checkEk1024Avx2_codeSp } .avx checkEk1024Out

theorem checkEk1024Avx2_spSafe : Impl.MlKem.X86_64.Fn.checkEk1024Avx2.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe checkEk1024Avx2_codeSp

end VG.Proof.MlKem.X86_64.Scrub
