module

public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillVerified
public import VerifiedGarbage.Impl.Dsa.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.SideFillN
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub

/-!
# DSA on AArch64, without secret residue

The postconditions of `vg_dsa_validate_public_key` and
`vg_dsa_validate_private_key` do not read the memory on return, and that of
`vg_dsa_parameter_search` reads it only within its outputs
(`Ffdh.AArch64.Scrub.bytesAt_of`, `wordsAt_of`; `ScrubAll.ScrubAllOk`, as
x86-64's `Proof/Dsa/X86_64/Scrub.lean` proves them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`Impl.Dsa.AArch64.Fn`, with the registers `Fn.clear`;
the parameter search, whose registers differ with its hash functions, with
those its code may write, `Impl.Residue.AArch64.scrubOf`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

theorem validatePublicKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePublicKeyContract abi stack) stack
      (Spec.Dsa.validatePublicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePublicKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePrivateKeyContract abi stack) stack
      (Spec.Dsa.validatePrivateKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePrivateKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem parameterSearchOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.parameterSearchContract abi stack) stack
      (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.parameterSearchSig) (Nat.le_of_ble_eq_true rfl) fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw outLen


/-! ## With arguments on the stack -/

theorem verifyPrevalidatedOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.verifyPrevalidatedContract abi stack) stack (Spec.Dsa.verifySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.verifySig) fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem deriveKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.deriveKeyContract abi stack) stack (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.deriveKeySig) fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX]
      · exact h
      · exact toNat_sw outLen

theorem generateKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.generateKeyContract abi stack) stack (Spec.Dsa.generateKeySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.generateKeySig) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw outLen

theorem randomSignPrevalidatedOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.randomSignPrevalidatedContract abi stack) stack (Spec.Dsa.randomSignSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Dsa.randomSignSig) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw outLen


/-! ## The functions, as emitted

Each function with its cleanup (`Impl.Dsa.AArch64.Fn`), over an arithmetic
backend `v`: it meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds.
What the cleanup needs of the code (`ScrubAll.scrubSide`) is the backend's
(`Backend.validateScrub` and the others), proved where it is defined. -/

open VG.Proof.Dsa.AArch64 (Backend prevalidatedSignerName keygenCheckName keygenDeriveName)

/-- `vg_dsa_random_sign_prevalidated`. -/
theorem randomSignPrevalidated (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.randomSignPrevalidated (prevalidatedSignerName v) v.mul v.stack)
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) 32 :=
  verifiedScrubbed (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := Impl.Dsa.AArch64.RandomSign.code (prevalidatedSignerName v) (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul)
      verified := Proof.Dsa.AArch64.random_sign_prevalidated_verified v } _
    (randomSignPrevalidatedOk _) v.randomSignScrub

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivateKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.validatePrivateKey v.mul v.stack)
      (Spec.Dsa.validatePrivateKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePrivateKeyApi)
    { code := Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul, verified := v.validatePrivateVerified } _
    (validatePrivateKeyOk _) v.validatePrivateScrub

/-- `vg_dsa_validate_public_key`. -/
theorem validatePublicKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.validatePublicKey v.mul v.stack)
      (Spec.Dsa.validatePublicKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.validatePublicKeyApi)
    { code := Impl.Dsa.AArch64.Prevalidated.validate v.mul, verified := v.validateVerified } _
    (validatePublicKeyOk _) v.validateScrub

/-- `vg_dsa_verify_prevalidated`. -/
theorem verifyPrevalidated (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.verifyPrevalidated v.mul v.stack)
      (Spec.Dsa.verifyPrevalidatedContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.verifyPrevalidatedApi)
    { code := Impl.Dsa.AArch64.Prevalidated.verify v.mul, verified := v.prevalidatedVerified } _
    (verifyPrevalidatedOk _) v.prevalidatedScrub

/-- `vg_dsa_generate_key`. -/
theorem generateKey (v : Backend) :
    VerifiedScrubbed target
      (Impl.Dsa.AArch64.Fn.generateKey (keygenCheckName v) (keygenDeriveName v) v.mul v.stack)
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) 32 :=
  verifiedScrubbed (api := Spec.Dsa.generateKeyApi)
    { code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul)
      verified := Proof.Dsa.AArch64.keygen_verified v } _
    (generateKeyOk _) v.generateKeyScrub

/-- `vg_dsa_derive_key`. -/
theorem deriveKey (v : Backend) :
    VerifiedScrubbed target (Impl.Dsa.AArch64.Fn.deriveKey v.mul v.stack)
      (Spec.Dsa.deriveKeyContract abi v.stack) 32 :=
  verifiedScrubbed (api := Spec.Dsa.deriveKeyApi)
    { code := Impl.Dsa.AArch64.Generate.deriveKey v.mul, verified := v.deriveVerified } _
    (deriveKeyOk _) v.deriveScrub

/-! ## `vg_dsa_parameter_search`, as emitted

What the cleanup needs of the search's code, a property of every instruction
and the depth of the stack, is evaluated once, with holes where the hash
functions, the generator stages and the tests are (`Code.fillN`); theirs are
the facts their records carry (`MdHash.side`, `RoundImpl.side`). -/

open VG.Proof.MillerRabin.AArch64 (RoundImpl)

/-- Hole `k` (`Code.holeIx`). -/
def hole : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (.block []) (hole k)

/-- `G` with its streaming functions as the holes `k`, `k + 1` and `k + 2`. -/
def holeHash (G : Impl.Pbkdf2.Md.AArch64.Hash) (k : Nat) : Impl.Pbkdf2.Md.AArch64.Hash :=
  { G with initN := "", initC := hole k, updN := "", updC := hole (k + 1), finN := "", finC := hole (k + 2) }

/-- The generator stages as the holes 6 to 8. -/
def holeGen (pLen : Nat) : Prog isa :=
  .call "" (hole (if pLen = 128 then 6 else if pLen = 256 then 7 else 8))

/-- The tests as the holes 9 to 13. -/
def holePrime (bits : Nat) : Prog isa :=
  .call "" (hole (if bits = 160 then 9 else if bits = 256 then 10 else if bits = 1024 then 11 else
    if bits = 2048 then 12 else 13))

/-- What fills the holes of the search. -/
def fills (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash) (gen prime : Nat → Prog isa) : List (Prog isa) :=
  [.call G1.initN G1.initC, .call G1.updN G1.updC, .call G1.finN G1.finC,
   .call G256.initN G256.initC, .call G256.updN G256.updC, .call G256.finN G256.finC,
   gen 128, gen 256, gen 384, prime 160, prime 256, prime 1024, prime 2048, prime 3072]

private theorem le17 {d : Nat} (h : 16 * d ≤ 272) : d ≤ 17 := by omega

/-- `vg_dsa_parameter_search` as emitted, with the hash functions `p` and the
arithmetic of the round's implementation `v`, cleanup included. -/
theorem parameterSearch (p : Generation.Refill.Hashes) (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Dsa.AArch64.Fn.parameterSearch p.sha1.H p.sha256.H v.suffix v.mont.mm v.roundMont.mm)
      (Spec.Dsa.parameterSearchContract abi 768) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fillN (p := fun i => !i.writesDit)
    (c := Impl.Dsa.AArch64.Generation.code p.sha1.H p.sha256.H (Impl.Dsa.AArch64.Fn.generator v.suffix v.mont.mm)
      (Impl.Dsa.AArch64.Fn.probablePrime v.suffix v.mont.mm v.roundMont.mm))
    (e := Impl.Dsa.AArch64.Generation.code (holeHash p.sha1.H 0) (holeHash p.sha256.H 3) holeGen holePrime)
    (bs := fills p.sha1.H p.sha256.H (Impl.Dsa.AArch64.Fn.generator v.suffix v.mont.mm)
      (Impl.Dsa.AArch64.Fn.probablePrime v.suffix v.mont.mm v.roundMont.mm))
    (ds := [1, 1, 1, 1, 1, 1, 17, 17, 17, 17, 17, 17, 17, 17]) (d := 47)
    (by kernel_rfl)
    (by
      intro b hb
      simp only [fills, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p.sha1.side.init, p.sha1.side.upd, p.sha1.side.fin, p.sha256.side.init, p.sha256.side.upd,
        p.sha256.side.fin, Generator.code_side v (.inl rfl), Generator.code_side v (.inr (.inl rfl)),
        Generator.code_side v (.inr (.inr rfl)), ProbablePrime.testCode_side v (.inl rfl),
        ProbablePrime.testCode_side v (.inr (.inl rfl)), ProbablePrime.testCode_side v (.inr (.inr (.inl rfl))),
        ProbablePrime.testCode_side v (.inr (.inr (.inr (.inl rfl)))),
        ProbablePrime.testCode_side v (.inr (.inr (.inr (.inr rfl))))])
    (.cons p.sha1.ok.stream.initDepth (.cons p.sha1.ok.stream.updDepth (.cons p.sha1.ok.stream.finDepth
      (.cons p.sha256.ok.stream.initDepth (.cons p.sha256.ok.stream.updDepth (.cons p.sha256.ok.stream.finDepth
      (.cons (le17 (Generator.code_depth v 128)) (.cons (le17 (Generator.code_depth v 256))
      (.cons (le17 (Generator.code_depth v 384)) (.cons (le17 (ProbablePrime.testCode_depth v 160))
      (.cons (le17 (ProbablePrime.testCode_depth v 256)) (.cons (le17 (ProbablePrime.testCode_depth v 1024))
      (.cons (le17 (ProbablePrime.testCode_depth v 2048)) (.cons (le17 (ProbablePrime.testCode_depth v 3072))
      .nil))))))))))))))
    (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  exact verifiedScrubbedOf (W := 768)
    (Generation.Refill.backend_verified p.sha1 p.sha256 v p.h1 p.h256) (parameterSearchOk 768) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

end VG.Proof.Dsa.AArch64.Scrub
