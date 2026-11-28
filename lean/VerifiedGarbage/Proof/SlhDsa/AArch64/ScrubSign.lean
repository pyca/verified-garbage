module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignCT
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ScrubKeyGen
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTFin
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: signing without secret residue

Signing as emitted (`Impl.SlhDsa.AArch64.Fn.sign`), over any implementation
`T` of `thash4`: its code with every register the calling convention does
not preserve cleared and the 16 bytes below its stack pointer, the frame of
the sponge functions, zeroed (`scrubAll 16 32 Clear.all`). What the cleanup
needs of the code is evaluated by the kernel once for each parameter set and
each single-state Keccak, of the code with `thash4`'s calls holes
(`KeyGen.stubOf`), whatever the names of the functions (`sign_fill`), and
`T` gives it of its own code (`Thash4Impl.side`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64 VG.AArch64.Scrub
open VG.Spec.SlhDsa
open VG.Proof.SlhDsa.AArch64.KeyGen (Shake6 fnsOf stubOf)

theorem fors_fill {p : Params} (hp : Shake6 p) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    Impl.SlhDsa.AArch64.Shake.forsCode p f =
      Code.fillCalls f.t4name f.t4 (Impl.SlhDsa.AArch64.Shake.forsCode p (stubOf f)) := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

/-- The functions of a variant, by its Keccak. -/
abbrev fnsOf' (p : Params) (sha3 : Bool) (sfx set : String) : Impl.SlhDsa.AArch64.Shake.Fns :=
  Impl.SlhDsa.AArch64.Shake.Fns.ofVariant p sha3 sfx set

theorem sign_fill {p : Params} (hp : Shake6 p) (sha3 : Bool) (sfx set : String) :
    Impl.SlhDsa.AArch64.Shake.sign p (fnsOf' p sha3 sfx set) =
      Code.fillCalls (fnsOf' p sha3 sfx set).t4name (fnsOf' p sha3 sfx set).t4
        (Impl.SlhDsa.AArch64.Shake.sign p (stubOf (fnsOf' p sha3 sfx set))) := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases sha3 <;> kernel_rfl

/-- What the kernel evaluates of signing, for each parameter set and Keccak:
with `thash4` a hole, its frames nest once and it writes no PSTATE.DIT. -/
theorem stub_ok {p : Params} (hp : Shake6 p) (sha3 : Bool) (sfx set : String) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Shake.sign p (stubOf (fnsOf' p sha3 sfx set))) = true ∧
      Nat.ble (Impl.SlhDsa.AArch64.Shake.sign p (stubOf (fnsOf' p sha3 sfx set))).aarch64Depth 1 = true ∧
      (Impl.SlhDsa.AArch64.Shake.forsCode p (stubOf (fnsOf' p sha3 sfx set))).noFrames = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases sha3 <;>
    exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem sign_side {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Shake.sign p (fnsOf p T set)) = true ∧
      (Impl.SlhDsa.AArch64.Shake.sign p (fnsOf p T set)).aarch64Depth ≤ 1 := by
  have h := stub_ok hp T.sha3 T.sfx set
  have ht := KeyGen.t4_side T set
  rw [show fnsOf p T set = fnsOf' p T.sha3 T.sfx set from rfl, sign_fill hp]
  refine ⟨sideAll_fillCalls ht.1 h.1, ?_⟩
  have := Code.aarch64Depth_fillCalls_le (fnsOf' p T.sha3 T.sfx set).t4name (fnsOf' p T.sha3 T.sfx set).t4
    (Impl.SlhDsa.AArch64.Shake.sign p (stubOf (fnsOf' p T.sha3 T.sfx set)))
  have h2 : (Impl.SlhDsa.AArch64.Shake.sign p (stubOf (fnsOf' p T.sha3 T.sfx set))).aarch64Depth ≤ 1 :=
    Nat.le_of_ble_eq_true h.2.1
  rw [ht.2.1] at this
  omega

theorem fors_noFrames {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    (Impl.SlhDsa.AArch64.Shake.forsCode p (fnsOf p T set)).noFrames = true := by
  rw [fors_fill hp]
  exact KeyGen.noFrames_fillCalls (KeyGen.t4_side T set).2.2 (stub_ok hp T.sha3 T.sfx set).2.2

theorem signOk (p : Params) :
    ScrubAllOk (signContract p AArch64.abi 16) 16 ((signSig p).retBits AArch64.abi.ptrBits) :=
  scrubAllOk_regs (sig := signSig p) (Nat.le_of_ble_eq_true rfl) (by decide) (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := KeyGen.bytesAt_of (n := p.sigLen) (Nat.le_refl _) hb.2.2.2.2.1
      show match formatMessage (Spec.Sha3.bytesAt m ctx ((ArgWord.int AArch64.abi.ptrBits).ofRaw cl).toNat)
          (Spec.Sha3.bytesAt m msg ((ArgWord.int AArch64.abi.ptrBits).ofRaw ml).toNat) with
        | none => r = 2 ∧ Spec.Sha3.bytesAt m₂ sig p.sigLen = Spec.Sha3.bytesAt m sig p.sigLen
        | some M' => r = 1 ∧ Spec.Sha3.bytesAt m₂ sig p.sigLen = signInternal p M' (Spec.Sha3.bytesAt m sk p.skLen)
            (Spec.Sha3.bytesAt m rnd p.n)
      rw [e]
      exact h

theorem Shake6.lp {p : Params} (hp : Shake6 p) : LP p := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
      by decide⟩

/-- `vg_slhdsa_shake_*_sign` as emitted, over any implementation `T` of
`thash4` and `forsSign` and `xmssTree` over it verified against their
contracts, meets its contract in constant time and returns without secret
residue. -/
theorem sign_scrubbed {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p (fnsOf p T set)) (xmssContract p))
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p (fnsOf p T set)) (forsContract p)) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign p (fnsOf p T set))
      ((signApi p module name).contract AArch64.abi 16) 32 := by
  have hv := sign_verified hp (VG.Proof.SlhDsa.X86_64.VerifyTop.S6.par hp) (Shake6.lp hp) (kperm T.sha3)
    (kperm_callee T.sha3).symm hx (KeyGen.xmss_noFrames hp T set) hf (fors_noFrames hp T set)
  have hs := sign_side hp T set
  exact verifiedScrubbedClearAll hv (signOk p) ⟨by decide, by decide, by decide⟩ (by omega) hs.1 (by decide)

theorem sign_spSafe (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    (Impl.SlhDsa.AArch64.Fn.sign p f).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

/-- `forsSign` over `T`, as signing calls it. -/
theorem forsV {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p (fnsOf p T set)) (forsContract p) := by
  have e : Impl.SlhDsa.AArch64.Shake.forsCode p (fnsOf p T set) =
      Impl.SlhDsa.AArch64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k (fnsOf p T set).t4name
        (fnsOf p T set).levelsName T.code := by
    rw [T.code_eq]; rfl
  have hA : Fors.As p := by unfold Fors.As; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e]
  exact Fors.fors_verified hp.sz hA T _ _

/-! The parameter sets, as their registrations name them. -/

theorem sign128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_128s (fnsOf shake_128s T "128s"))
      (signShake_128sApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inl rfl) T _ _ "128s" (KeyGen.xmssV (.inl rfl) T "128s") (forsV (.inl rfl) T "128s")

theorem sign128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_128s (fnsOf shake_128s T "128s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

theorem sign128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_128f (fnsOf shake_128f T "128f"))
      (signShake_128fApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inr (.inl rfl)) T _ _ "128f" (KeyGen.xmssV (.inr (.inl rfl)) T "128f") (forsV (.inr (.inl rfl)) T "128f")

theorem sign128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_128f (fnsOf shake_128f T "128f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

theorem sign192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_192s (fnsOf shake_192s T "192s"))
      (signShake_192sApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s" (KeyGen.xmssV (.inr (.inr (.inl rfl))) T "192s") (forsV (.inr (.inr (.inl rfl))) T "192s")

theorem sign192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_192s (fnsOf shake_192s T "192s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

theorem sign192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_192f (fnsOf shake_192f T "192f"))
      (signShake_192fApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f" (KeyGen.xmssV (.inr (.inr (.inr (.inl rfl)))) T "192f") (forsV (.inr (.inr (.inr (.inl rfl)))) T "192f")

theorem sign192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_192f (fnsOf shake_192f T "192f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

theorem sign256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_256s (fnsOf shake_256s T "256s"))
      (signShake_256sApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s" (KeyGen.xmssV (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s") (forsV (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s")

theorem sign256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_256s (fnsOf shake_256s T "256s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

theorem sign256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.sign shake_256f (fnsOf shake_256f T "256f"))
      (signShake_256fApi.contract AArch64.abi 16) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f" (KeyGen.xmssV (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f") (forsV (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f")

theorem sign256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.sign shake_256f (fnsOf shake_256f T "256f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafe _ _

end VG.Proof.SlhDsa.AArch64.Sign
