module

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopVerified
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGen
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubVerifyLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubVerifyLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# SLH-DSA (SHAKE) on x86-64: verification without secret residue

Verification as emitted (`Impl.SlhDsa.X86_64.Fn.verify`), over any
implementation `T` of `thash4`, with the 112 bytes below its stack pointer
wiped and the registers cleared at `T`'s level: its code is its code over the
stub `KeyGen.stubFns` (`ScrubVerifyLit.lean`), with `T`'s where it calls it
(`Fill`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64 VG.X86_64.Scrub
open VG.Spec.SlhDsa
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Proof.SlhDsa.X86_64.KeyGen (fnsOf spSafe_of_nosp)

/-- The names of `verify`'s own functions, for the parameter set named `set` and `T`. -/
abbrev vfnsOf {n : Nat} (T : Thash4Impl n) (set : String) : Impl.SlhDsa.X86_64.Verify.VFns :=
  Impl.SlhDsa.X86_64.Verify.VFns.ofVariant set T.sfx

theorem S6.of_shake {p : Params} (hp : KeyGen.Shake6 p) : S6 p := hp

/-- `verify` never writes `rsp` but in its frame's push and pop. -/
theorem verify_spSafe {p : Params} (hS : S6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) (gv : Impl.SlhDsa.X86_64.Verify.VFns) :
    (Impl.SlhDsa.X86_64.Verify.verify p f gv).all (fun i => !isa.writesSp i) = true :=
  verify_codeAll _ (by rw [ht]; exact spSafe_of_nosp T.nosp) (verify_own_wsp hS)

theorem verifyOut (p : Params) (stack : Nat) :
    PostOut (verifyContract p X86_64.abi stack) ((verifySig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

theorem verify_scrubbed_of {p : Params} (hp : S6 p) (T : Thash4Impl p.n) (module name set : String)
    {a : Prog isa} (ha : stubSide a VecLevel.sse.level (fun _ => 16) 112 [] = true)
    (hf : Fill T.level.level (fun _ => 16) a (Impl.SlhDsa.X86_64.Verify.verify p (fnsOf p T set) (vfnsOf T set))) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level p (fnsOf p T set) (vfnsOf T set))
      ((verifyApi p module name).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFill (api := verifyApi p module name)
    { suffix := T.sfx
      code := Impl.SlhDsa.X86_64.Verify.verify p (fnsOf p T set) (vfnsOf T set)
      verified := verify_verified hp T rfl _ (st := 32) (by have := T.stack_le; omega) (by decide)
      spSafe := verify_spSafe hp T rfl _ }
    T.level (verifyOut p 112) hf (by cases T.level <;> decide) (Nat.le_refl _) (ha := ha)

/-- `vg_slhdsa_shake_*_verify` as emitted, over any implementation `T` of
`thash4`, meets its contract in constant time and returns without secret
residue. -/
theorem verify_scrubbed {p : Params} (hp : S6 p) (T : Thash4Impl p.n) (module name set : String) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level p (fnsOf p T set) (vfnsOf T set))
      ((verifyApi p module name).contract X86_64.abi 112) 32 := by
  have := T.side
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact verify_scrubbed_of (.inl rfl) T module name set (a := stubV128s) (by lit_decide) (by fill_calls)
  · exact verify_scrubbed_of (.inr (.inl rfl)) T module name set (a := stubV128f) (by lit_decide) (by fill_calls)
  · exact verify_scrubbed_of (.inr (.inr (.inl rfl))) T module name set (a := stubV192s) (by lit_decide)
      (by fill_calls)
  · exact verify_scrubbed_of (.inr (.inr (.inr (.inl rfl)))) T module name set (a := stubV192f) (by lit_decide)
      (by fill_calls)
  · exact verify_scrubbed_of (.inr (.inr (.inr (.inr (.inl rfl))))) T module name set (a := stubV256s)
      (by lit_decide) (by fill_calls)
  · exact verify_scrubbed_of (.inr (.inr (.inr (.inr (.inr rfl))))) T module name set (a := stubV256f)
      (by lit_decide) (by fill_calls)

theorem verify_spSafeFn {p : Params} (hp : S6 p) (T : Thash4Impl p.n) (set : String) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level p (fnsOf p T set) (vfnsOf T set)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verify_spSafe hp T rfl _)

/-! The parameter sets, as their registrations name them. -/

theorem verify128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_128s (fnsOf shake_128s T "128s") (vfnsOf T "128s"))
      (verifyShake_128sApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inl rfl) T _ _ "128s"

theorem verify128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_128s (fnsOf shake_128s T "128s") (vfnsOf T "128s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inl rfl) T "128s"

theorem verify128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_128f (fnsOf shake_128f T "128f") (vfnsOf T "128f"))
      (verifyShake_128fApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inr (.inl rfl)) T _ _ "128f"

theorem verify128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_128f (fnsOf shake_128f T "128f") (vfnsOf T "128f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inr (.inl rfl)) T "128f"

theorem verify192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_192s (fnsOf shake_192s T "192s") (vfnsOf T "192s"))
      (verifyShake_192sApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s"

theorem verify192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_192s (fnsOf shake_192s T "192s") (vfnsOf T "192s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inr (.inr (.inl rfl))) T "192s"

theorem verify192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_192f (fnsOf shake_192f T "192f") (vfnsOf T "192f"))
      (verifyShake_192fApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f"

theorem verify192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_192f (fnsOf shake_192f T "192f") (vfnsOf T "192f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inr (.inr (.inr (.inl rfl)))) T "192f"

theorem verify256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_256s (fnsOf shake_256s T "256s") (vfnsOf T "256s"))
      (verifyShake_256sApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s"

theorem verify256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_256s (fnsOf shake_256s T "256s") (vfnsOf T "256s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s"

theorem verify256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.verify T.level shake_256f (fnsOf shake_256f T "256f") (vfnsOf T "256f"))
      (verifyShake_256fApi.contract X86_64.abi 112) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f"

theorem verify256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.verify T.level shake_256f (fnsOf shake_256f T "256f") (vfnsOf T "256f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafeFn (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f"

end VG.Proof.SlhDsa.X86_64.VerifyTop
