module

public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
meta import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEkAvx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-!
# ML-KEM's encapsulation-key check on x86-64, without secret residue

`vg_mlkem768_check_ek` and `vg_mlkem1024_check_ek`, with and without AVX2,
each followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`),
which clears the registers that the residue analysis (`X86_64.RTaint`) finds
may hold secrets. Their postconditions read only the memory on entry.
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

def checkEkKs : List Nat := keep_for% Spec.MlKem.checkEkApi.sig 0 Impl.MlKem.X86_64.checkEk []

theorem checkEkOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.MlKem.checkEkApi.sig 0 []) Impl.MlKem.X86_64.checkEk
      h).any (RScrub.resOkB · 0 checkEkKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of checkEkKs (by taint_decide)

open VG.X86_64.RScrub in
def checkEkReg : Registration Spec.MlKem.checkEkApi X86_64.target :=
  withScrub { code := Impl.MlKem.X86_64.checkEk, verified := Proof.MlKem.X86_64.checkEk_verified } checkEkOut [] (pubOk_nil _)
    (some ⟨checkEkKs, checkEkOk⟩)

def checkEkAvx2Ks : List Nat := keep_for% Spec.MlKem.checkEkApi.sig 0 Impl.MlKem.X86_64.checkEkAvx2 []

theorem checkEkAvx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.MlKem.checkEkApi.sig 0 []) Impl.MlKem.X86_64.checkEkAvx2
      h).any (RScrub.resOkB · 0 checkEkAvx2Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of checkEkAvx2Ks (by taint_decide)

open VG.X86_64.RScrub in
def checkEkAvx2Reg : Registration Spec.MlKem.checkEkApi X86_64.target :=
  withScrub { suffix := "_avx2", code := Impl.MlKem.X86_64.checkEkAvx2, verified := Proof.MlKem.X86_64.checkEkAvx2_verified } checkEkOut [] (pubOk_nil _)
    (some ⟨checkEkAvx2Ks, checkEkAvx2Ok⟩)

def checkEk1024Ks : List Nat := keep_for% Spec.MlKem1024.checkEkApi.sig 0 Impl.MlKem1024.X86_64.checkEk1024 []

theorem checkEk1024Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.MlKem1024.checkEkApi.sig 0 []) Impl.MlKem1024.X86_64.checkEk1024
      h).any (RScrub.resOkB · 0 checkEk1024Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of checkEk1024Ks (by taint_decide)

open VG.X86_64.RScrub in
def checkEk1024Reg : Registration Spec.MlKem1024.checkEkApi X86_64.target :=
  withScrub { code := Impl.MlKem1024.X86_64.checkEk1024, verified := Proof.MlKem1024.X86_64.checkEk1024_verified } checkEk1024Out [] (pubOk_nil _)
    (some ⟨checkEk1024Ks, checkEk1024Ok⟩)

def checkEk1024Avx2Ks : List Nat := keep_for% Spec.MlKem1024.checkEkApi.sig 0 Impl.MlKem1024.X86_64.checkEk1024Avx2 []

theorem checkEk1024Avx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.MlKem1024.checkEkApi.sig 0 []) Impl.MlKem1024.X86_64.checkEk1024Avx2
      h).any (RScrub.resOkB · 0 checkEk1024Avx2Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of checkEk1024Avx2Ks (by taint_decide)

open VG.X86_64.RScrub in
def checkEk1024Avx2Reg : Registration Spec.MlKem1024.checkEkApi X86_64.target :=
  withScrub { suffix := "_avx2", code := Impl.MlKem1024.X86_64.checkEk1024Avx2, verified := Proof.MlKem1024.X86_64.checkEk1024Avx2_verified } checkEk1024Out [] (pubOk_nil _)
    (some ⟨checkEk1024Avx2Ks, checkEk1024Avx2Ok⟩)

end VG.Proof.MlKem.X86_64.Scrub
