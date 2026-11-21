module

public import VerifiedGarbage.Impl.MlKem.X86_64.Fn
public import VerifiedGarbage.Proof.MlKem.X86_64.CallWipe
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM's functions on x86-64, without secret residue

Each function as emitted (`Impl.MlKem.X86_64.Fn`), over any implementation of
`vg_mlkem_sample_ntt4` (`Sample4Impl`) and of `vg_zeroize` (`ZeroizeImpl`),
its whole stack wiped by its cleanup at the higher of their levels. Its code
is `callWipe` of the function's body, which inlines the implementation's
code, and of the zeroize function: the kernel evaluates what the cleanup
needs of `callWipe` with stubs of both once for each register and number of
bytes it wipes (`stub_*`), each implementation of `vg_mlkem_sample_ntt4`
what it needs of the bodies over it (`Sample4Impl.sides`), and each of
`vg_zeroize` what it needs of its code (`ZeroizeImpl.side`), where they are
defined.
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.MlKem.X86_64.KemScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Impl.CallWipe.X86_64
open VG.Proof.Zeroize.X86_64 (ZeroizeImpl)

/-- The stack the body and the zeroize function need. -/
def stubStack : String → Nat := fun s => if s = "b" then 32 else 0

/-- `callWipe` over stubs of the body and the zeroize function. -/
def stub (r : Reg) (n : Nat) : Prog isa := callWipe r n "b" (.block []) "z" (.block [])

theorem callWipe_fill {k : Nat} (r : Reg) (n : Nat) (name zname : String) {body zcode : Prog isa}
    (hb : calleeSide body k 32 = true) (hz : calleeSide zcode k 0 = true) :
    Fill k stubStack (stub r n) (callWipe r n name body zname zcode) := by
  unfold stub callWipe; fill_calls

theorem callWipe_fillE {k : Nat} (r : Reg) {n m : Nat} (e : n = m) (name zname : String) {body zcode : Prog isa}
    (hb : calleeSide body k 32 = true) (hz : calleeSide zcode k 0 = true) :
    Fill k stubStack (stub r m) (callWipe r n name body zname zcode) := by
  subst e; exact callWipe_fill r n name zname hb hz

theorem stub_rcx : stubSide (stub .rcx 32768) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r9 : stubSide (stub .r9 32768) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r8 : stubSide (stub .r8 32768) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_rcx16 : stubSide (stub .rcx 37376) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r916 : stubSide (stub .r9 37376) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r816 : stubSide (stub .r8 37376) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_rcx32 : stubSide (stub .rcx 49152) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r932 : stubSide (stub .r9 49152) VecLevel.sse.level stubStack 56 [] = true := by lit_decide
theorem stub_r832 : stubSide (stub .r8 49152) VecLevel.sse.level stubStack 56 [] = true := by lit_decide

theorem wiped1024_cases (c : Impl.MlKem.X86_64.Callee4) :
    Impl.MlKem.X86_64.wiped1024 c = 37376 ∨ Impl.MlKem.X86_64.wiped1024 c = 49152 := by
  unfold Impl.MlKem.X86_64.wiped1024; split <;> simp

theorem wipedEnc1024_cases (c : Impl.MlKem.X86_64.Callee4) :
    Impl.MlKem.X86_64.wipedEnc1024 c = 37376 ∨ Impl.MlKem.X86_64.wipedEnc1024 c = 49152 := by
  unfold Impl.MlKem.X86_64.wipedEnc1024; split <;> simp

/-- The level of the cleanup of the functions over `v` and `z`. -/
def level (v : Sample4Impl) (z : ZeroizeImpl) : VecLevel := v.level.join z.level

theorem body_side {v : Sample4Impl} (z : ZeroizeImpl) {c : Prog isa}
    (h : calleeSide c v.level.level 32 = true) : calleeSide c (level v z).level 32 = true :=
  calleeSide_mono (level_join_left _ _) (Nat.le_refl _) h

theorem z_side (v : Sample4Impl) (z : ZeroizeImpl) : calleeSide z.code (level v z).level 0 = true :=
  calleeSide_mono (level_join_right _ _) (Nat.le_refl _) z.side

/-- `Spec.MlKem.keyGenApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem keyGen_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.keyGen (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem.keyGenApi.contract X86_64.abi 56) 32 :=
  verifiedScrubbedAllFill (api := Spec.MlKem.keyGenApi)
    { code := Impl.MlKem.X86_64.keyGenW v.callee v.suffix z.name z.code
      verified := Proof.MlKem.X86_64.keyGenW_verified v z
      spSafe := Proof.MlKem.X86_64.keyGenW_spSafe v z } _ (Proof.MlKem.X86_64.keyGenOut _)
    (by unfold Impl.MlKem.X86_64.keyGenW; exact callWipe_fill _ _ _ _ (body_side z v.sides.keyGen) (z_side v z))
    (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx)

theorem keyGen_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.keyGen (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.keyGenW_spSafe v z)

/-- `Spec.MlKem.encapsHApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem encapsH_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.encapsH (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem.encapsHApi.contract X86_64.abi 56) 32 :=
  verifiedScrubbedAllFill (api := Spec.MlKem.encapsHApi)
    { code := Impl.MlKem.X86_64.encapsHW v.callee v.suffix z.name z.code
      verified := Proof.MlKem.X86_64.encapsHW_verified v z
      spSafe := Proof.MlKem.X86_64.encapsHW_spSafe v z } _ (Proof.MlKem.X86_64.encapsHOut _)
    (by unfold Impl.MlKem.X86_64.encapsHW; exact callWipe_fill _ _ _ _ (body_side z v.sides.encapsH) (z_side v z))
    (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r9)

theorem encapsH_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.encapsH (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.encapsHW_spSafe v z)

/-- `Spec.MlKem.encapsApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem encaps_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.encaps (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem.encapsApi.contract X86_64.abi 56) 32 :=
  verifiedScrubbedAllFill (api := Spec.MlKem.encapsApi)
    { code := Impl.MlKem.X86_64.encapsW v.callee v.suffix z.name z.code
      verified := Proof.MlKem.X86_64.encapsW_verified v z
      spSafe := Proof.MlKem.X86_64.encapsW_spSafe v z } _ (Proof.MlKem.X86_64.encapsOut _)
    (by unfold Impl.MlKem.X86_64.encapsW; exact callWipe_fill _ _ _ _ (body_side z v.sides.encaps) (z_side v z))
    (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r8)

theorem encaps_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.encaps (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.encapsW_spSafe v z)

/-- `Spec.MlKem.decapsApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem decaps_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.decaps (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem.decapsApi.contract X86_64.abi 56) 32 :=
  verifiedScrubbedAllFill (api := Spec.MlKem.decapsApi)
    { code := Impl.MlKem.X86_64.decapsW v.callee v.suffix z.name z.code
      verified := Proof.MlKem.X86_64.decapsW_verified v z
      spSafe := Proof.MlKem.X86_64.decapsW_spSafe v z } _ (Proof.MlKem.X86_64.decapsOut _)
    (by unfold Impl.MlKem.X86_64.decapsW; exact callWipe_fill _ _ _ _ (body_side z v.sides.decaps) (z_side v z))
    (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx)

theorem decaps_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.decaps (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.decapsW_spSafe v z)

/-- `Spec.MlKem1024.keyGenApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem keyGen1024_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.keyGen1024 (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem1024.keyGenApi.contract X86_64.abi 56) 32 := by
  rcases wiped1024_cases v.callee with e | e
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.keyGenApi)
      { code := Impl.MlKem.X86_64.keyGen1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.keyGen1024W_verified v z
        spSafe := Proof.MlKem.X86_64.keyGen1024W_spSafe v z } _ (Proof.MlKem.X86_64.keyGen1024Out _)
      (by unfold Impl.MlKem.X86_64.keyGen1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.keyGen1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx16)
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.keyGenApi)
      { code := Impl.MlKem.X86_64.keyGen1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.keyGen1024W_verified v z
        spSafe := Proof.MlKem.X86_64.keyGen1024W_spSafe v z } _ (Proof.MlKem.X86_64.keyGen1024Out _)
      (by unfold Impl.MlKem.X86_64.keyGen1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.keyGen1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx32)

theorem keyGen1024_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.keyGen1024 (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.keyGen1024W_spSafe v z)

/-- `Spec.MlKem1024.encapsHApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem encapsH1024_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.encapsH1024 (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem1024.encapsHApi.contract X86_64.abi 56) 32 := by
  rcases wiped1024_cases v.callee with e | e
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.encapsHApi)
      { code := Impl.MlKem.X86_64.encapsH1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.encapsH1024W_verified v z
        spSafe := Proof.MlKem.X86_64.encapsH1024W_spSafe v z } _ (Proof.MlKem.X86_64.encapsH1024Out _)
      (by unfold Impl.MlKem.X86_64.encapsH1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.encapsH1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r916)
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.encapsHApi)
      { code := Impl.MlKem.X86_64.encapsH1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.encapsH1024W_verified v z
        spSafe := Proof.MlKem.X86_64.encapsH1024W_spSafe v z } _ (Proof.MlKem.X86_64.encapsH1024Out _)
      (by unfold Impl.MlKem.X86_64.encapsH1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.encapsH1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r932)

theorem encapsH1024_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.encapsH1024 (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.encapsH1024W_spSafe v z)

/-- `Spec.MlKem1024.encapsApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem encaps1024_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.encaps1024 (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem1024.encapsApi.contract X86_64.abi 56) 32 := by
  rcases wipedEnc1024_cases v.callee with e | e
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.encapsApi)
      { code := Impl.MlKem.X86_64.encaps1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.encaps1024W_verified v z
        spSafe := Proof.MlKem.X86_64.encaps1024W_spSafe v z } _ (Proof.MlKem.X86_64.encaps1024Out _)
      (by unfold Impl.MlKem.X86_64.encaps1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.encaps1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r816)
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.encapsApi)
      { code := Impl.MlKem.X86_64.encaps1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.encaps1024W_verified v z
        spSafe := Proof.MlKem.X86_64.encaps1024W_spSafe v z } _ (Proof.MlKem.X86_64.encaps1024Out _)
      (by unfold Impl.MlKem.X86_64.encaps1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.encaps1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_r832)

theorem encaps1024_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.encaps1024 (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.encaps1024W_spSafe v z)

/-- `Spec.MlKem1024.decapsApi`'s function as emitted over `v` and `z` meets its contract in
constant time and returns without secret residue. -/
theorem decaps1024_scrubbed (v : Sample4Impl) (z : ZeroizeImpl) :
    VerifiedScrubbed target (Impl.MlKem.X86_64.Fn.decaps1024 (level v z) v.callee v.suffix z.name z.code)
      (Spec.MlKem1024.decapsApi.contract X86_64.abi 56) 32 := by
  rcases wipedEnc1024_cases v.callee with e | e
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.decapsApi)
      { code := Impl.MlKem.X86_64.decaps1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.decaps1024W_verified v z
        spSafe := Proof.MlKem.X86_64.decaps1024W_spSafe v z } _ (Proof.MlKem.X86_64.decaps1024Out _)
      (by unfold Impl.MlKem.X86_64.decaps1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.decaps1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx16)
  · exact verifiedScrubbedAllFill (api := Spec.MlKem1024.decapsApi)
      { code := Impl.MlKem.X86_64.decaps1024W v.callee v.suffix z.name z.code
        verified := Proof.MlKem.X86_64.decaps1024W_verified v z
        spSafe := Proof.MlKem.X86_64.decaps1024W_spSafe v z } _ (Proof.MlKem.X86_64.decaps1024Out _)
      (by unfold Impl.MlKem.X86_64.decaps1024W; exact callWipe_fillE _ e _ _ (body_side z v.sides.decaps1024) (z_side v z))
      (Nat.zero_le _) (Nat.le_refl _) (ha := stub_rcx32)

theorem decaps1024_spSafe (v : Sample4Impl) (z : ZeroizeImpl) :
    (Impl.MlKem.X86_64.Fn.decaps1024 (level v z) v.callee v.suffix z.name z.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlKem.X86_64.decaps1024W_spSafe v z)

end VG.Proof.MlKem.X86_64.KemScrub
