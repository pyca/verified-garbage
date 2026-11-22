module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.Scrypt.X86_64.Fn
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_scrypt` without secret residue (x86-64)

`vg_scrypt` over any implementation of ROMix (`RMImpl`) and of SHA-256's
compression function (`Proof.Sha256.X86_64.Compress`), followed by its
cleanup, which wipes its whole frame (`Impl.Scrypt.X86_64.Fn.scrypt`). Its
code is its code over a stub (`stubCode`), with the implementations' code
where it calls them (`scrypt_fill`): the kernel evaluates what the cleanup
needs of the stub once for each size of the compression function's scratch
space, which moves offsets in PBKDF2's code (`stub_side`), and each
implementation proves what it needs of its own code where it is defined
(`RMImpl.side`, `Compress.side`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Whole

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Pbkdf2.Md.X86_64 VG.Impl.Scrub.X86_64

/-- SHA-256's functions as PBKDF2 calls them, over a stub of the compression
function with `so` bytes of scratch space, and of `init`. -/
def stubHash (so : Nat) : Hash :=
  { P := Proof.Sha256.X86_64.Stream.paramsS so, D := 32, W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so),
    compN := "", compC := .block [], initN := "", initC := .block [], updN := "", finN := "",
    hmacInitN := "", hmacFinN := "", iterN := "" }

/-- `vg_scrypt`'s code over stubs of ROMix (called as `romix`) and of
SHA-256's compression function with `so` bytes of scratch space. -/
def stubCode (so : Nat) : Prog isa := Impl.Scrypt.X86_64.scrypt "romix" (.block []) "" (stubHash so).pbkdf2

/-- The stack the implementations `vg_scrypt` calls need: ROMix's 8 bytes,
SHA-256's compression function and `init` none. -/
def stubStack : String → Nat := fun s => if s = "romix" then 8 else 0

theorem init_side : calleeSide Impl.Sha256.X86_64.Stream.init VecLevel.sse.level 0 = true := by lit_decide

/-- `vg_scrypt`'s code over `R` and `c` is its code over the stub with the
same scratch space, with theirs where it calls them. -/
theorem scrypt_fill (c : Proof.Sha256.X86_64.Compress) (R : RMImpl) {k : Nat} {so : Nat} (hso : c.callee.so = so)
    (hr : calleeSide R.code k 8 = true) (hc : calleeSide c.callee.code k 0 = true)
    (hi : calleeSide Impl.Sha256.X86_64.Stream.init k 0 = true) :
    Fill k stubStack (stubCode so) (Impl.Scrypt.X86_64.scrypt R.name R.code (pbkName c) (pbkOf c)) := by
  unfold stubCode pbkOf
  have : Proof.Pbkdf2.Md.X86_64.Sha256.hash c =
      { P := Proof.Sha256.X86_64.Stream.paramsS so, D := 32, W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so),
        compN := c.callee.name, compC := c.callee.code, initN := "vg_sha256_init_core",
        initC := Impl.Sha256.X86_64.Stream.init, updN := "vg_sha256_update_scratch" ++ c.suffix,
        finN := "vg_sha256_finalize_scratch" ++ c.suffix, hmacInitN := "vg_hmac_sha256_init_scratch" ++ c.suffix,
        hmacFinN := "vg_hmac_sha256_finalize_scratch" ++ c.suffix,
        iterN := "vg_pbkdf2_hmac_sha256_iterate" ++ c.suffix,
        hmacInitAnyN := "vg_hmac_sha256_init_any_scratch" ++ c.suffix } := by
    simp only [Proof.Pbkdf2.Md.X86_64.Sha256.hash, hso]
  rw [this]
  fill_calls

theorem stub_side0 : stubSide (stubCode 0) VecLevel.sse.level stubStack 88 [] = true := by lit_decide
theorem stub_side112 : stubSide (stubCode 112) VecLevel.sse.level stubStack 88 [] = true := by lit_decide
theorem stub_side560 : stubSide (stubCode 560) VecLevel.sse.level stubStack 88 [] = true := by lit_decide

/-- `vg_scrypt` over `R` and `c`, before its cleanup. -/
def plain (c : Proof.Sha256.X86_64.Compress) (R : RMImpl) : Unscrubbed Spec.Scrypt.scryptApi target where
  suffix := c.suffix ++ R.suffix
  code := Impl.Scrypt.X86_64.scrypt R.name R.code (pbkName c) (pbkOf c)
  stack := 88
  verified := scrypt_verified c R
  spSafe := scrypt_spSafe c R

/-- `Spec.Scrypt.scryptApi`'s function as emitted over `R` and `c`
(`Impl.Scrypt.X86_64.Fn.scrypt`), its cleanup at the higher of their levels,
meets its contract in constant time and returns without secret residue. -/
theorem scrypt_scrubbed (c : Proof.Sha256.X86_64.Compress) (R : RMImpl) :
    VerifiedScrubbed target
      (Impl.Scrypt.X86_64.Fn.scrypt (c.level.join R.level) R.name R.code (pbkName c) (pbkOf c))
      (Spec.Scrypt.scryptApi.contract X86_64.abi 88) 0 := by
  have hk₁ := level_join_left c.level R.level
  have hk₂ := level_join_right c.level R.level
  have hr := calleeSide_mono hk₂ (Nat.le_refl _) R.side
  have hc := calleeSide_mono hk₁ (Nat.le_refl _) c.side
  have hi : calleeSide Impl.Sha256.X86_64.Stream.init (c.level.join R.level).level 0 = true :=
    calleeSide_mono (Nat.zero_le _) (Nat.le_refl _) init_side
  have hs : VecLevel.sse.level ≤ (c.level.join R.level).level := Nat.zero_le _
  rcases c.hso with h | h | h
  · exact verifiedScrubbedAllFill (plain c R) _ (scrypt_postOut 88) (scrypt_fill c R h hr hc hi) hs
      (Nat.le_refl _) (ha := stub_side0)
  · exact verifiedScrubbedAllFill (plain c R) _ (scrypt_postOut 88) (scrypt_fill c R h hr hc hi) hs
      (Nat.le_refl _) (ha := stub_side112)
  · exact verifiedScrubbedAllFill (plain c R) _ (scrypt_postOut 88) (scrypt_fill c R h hr hc hi) hs
      (Nat.le_refl _) (ha := stub_side560)

theorem scrypt_spSafeFn (c : Proof.Sha256.X86_64.Compress) (R : RMImpl) :
    (Impl.Scrypt.X86_64.Fn.scrypt (c.level.join R.level) R.name R.code (pbkName c) (pbkOf c)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (scrypt_spSafe c R)

end VG.Proof.Scrypt.X86_64.Whole
