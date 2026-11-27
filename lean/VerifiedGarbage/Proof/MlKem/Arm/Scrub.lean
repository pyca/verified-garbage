module

public import VerifiedGarbage.Impl.MlKem.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.MlKem.Arm.CallWipe
public import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-KEM-768 and ML-KEM-1024 on ARMv7, without secret residue

`Impl.MlKem.Arm.Fn` has each function with its cleanup; `Fn` below has the
theorem of each, which its registration binds.

The key checks have no frames (`Arm.Scrub.verifiedScrubbed`). Key
generation, encapsulation (with `H(ek)` given or not) and decapsulation call
their code and `vg_zeroize`'s from a frame (`Impl.MlKem.Arm.Wipe`): what the
cleanup needs of them (`CodeOk`, `Arm.Scrub.scrubSideF_of`) is proven once
for the wrapper, `wiped_ok` and `wipedStack_ok`, from what each body states
of its own code: frames of at most 8 bytes (`Wipe.keyGen_stack`, …) and no
indirect call.

Their postconditions read the memory on return only within their buffers
(`PostOut`, by `postOut_of_local`): the outputs, and `scratch`, which each
leaves scrubbed. What reads them is the same for both parameter sets, whose
outputs differ only in their sizes: `outs_congr` (two outputs: key
generation and both encapsulations) and `out_congr` (one: decapsulation)
state it once.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.MlKem.Arm.Wipe

/-! ## What the cleanup needs of the code -/

theorem zeroize_ok : CodeOk Impl.Zeroize.Arm.zeroize 0 := ⟨zeroize_stack, by decide⟩

/-- A body called by `wiped`, with `vg_zeroize` after it, in a frame of 16 bytes. -/
theorem wiped_ok {r : Reg} {n : Nat} {fn : String} {body : Prog isa} (h : CodeOk body 8) :
    CodeOk (Impl.MlKem.Arm.Wipe.wiped r n fn body) 24 :=
  CodeOk.push (n := 8) (CodeOk.seq (CodeOk.mono (CodeOk.block _) (Nat.zero_le _)) (CodeOk.seq (CodeOk.call h)
    (CodeOk.seq (CodeOk.mono (CodeOk.block _) (Nat.zero_le _)) (CodeOk.seq (CodeOk.call (zeroize_ok.mono
      (Nat.zero_le _))) (CodeOk.mono (CodeOk.block _) (Nat.zero_le _))))))

/-- A body called by `wipedStack` with one or two stack arguments, which it
copies into a frame of 8 bytes. -/
theorem wipedStack_ok {k off n : Nat} {fn : String} {body : Prog isa} (hk : Impl.CallWipe.ArmStack.allocSize k = 8)
    (h : CodeOk body 8) : CodeOk (Impl.MlKem.Arm.Wipe.wipedStack k off n fn body) 32 := by
  have ha : CodeOk (.frame (.alloc (Impl.CallWipe.ArmStack.allocSize k))
      (.seq (.block (Impl.CallWipe.ArmStack.copyArgs k off)) (.call (fn ++ "_body") body))
      (.free (Impl.CallWipe.ArmStack.allocSize k))) 16 := by
    have := CodeOk.alloc (k := Impl.CallWipe.ArmStack.allocSize k) (j := .free (Impl.CallWipe.ArmStack.allocSize k))
      (CodeOk.seq (CodeOk.mono (CodeOk.block (Impl.CallWipe.ArmStack.copyArgs k off)) (Nat.zero_le 8))
        (CodeOk.call (name := fn ++ "_body") h))
    rw [hk] at this ⊢
    exact this
  exact CodeOk.push (n := 16) (CodeOk.seq ha (CodeOk.seq (CodeOk.mono (CodeOk.block _) (Nat.zero_le _))
    (CodeOk.seq (CodeOk.call (zeroize_ok.mono (Nat.zero_le _))) (CodeOk.mono (CodeOk.block _) (Nat.zero_le _)))))

theorem keyGen_ok : CodeOk Impl.MlKem.Arm.Wipe.keyGen 24 := wiped_ok ⟨keyGen_stack, by decide⟩
theorem encapsH_ok : CodeOk Impl.MlKem.Arm.Wipe.encapsH 32 := wipedStack_ok rfl ⟨encapsH_stack, by decide⟩
theorem encaps_ok : CodeOk Impl.MlKem.Arm.Wipe.encaps 32 := wipedStack_ok rfl ⟨encaps_stack, by decide⟩
theorem decaps_ok : CodeOk Impl.MlKem.Arm.Wipe.decaps 24 := wiped_ok ⟨decaps_stack, by decide⟩
theorem keyGen1024_ok : CodeOk Impl.MlKem.Arm.Wipe.keyGen1024 24 := wiped_ok ⟨keyGen1024_stack, by decide⟩
theorem encapsH1024_ok : CodeOk Impl.MlKem.Arm.Wipe.encapsH1024 32 :=
  wipedStack_ok rfl ⟨encapsH1024_stack, by decide⟩
theorem encaps1024_ok : CodeOk Impl.MlKem.Arm.Wipe.encaps1024 32 := wipedStack_ok rfl ⟨encaps1024_stack, by decide⟩
theorem decaps1024_ok : CodeOk Impl.MlKem.Arm.Wipe.decaps1024 24 := wiped_ok ⟨decaps1024_stack, by decide⟩

/-! ## Postconditions -/

/-- A postcondition on the bytes of two outputs and a wiped `scratch`
holds of any memory on return that agrees with it on the three buffers. -/
theorem outs_congr {w : Nat} {Q : List Byte × List Byte → Prop} {m m₁ m₂ : Mem} {p q s : Addr} {P R S : Nat}
    (hP : P < 2 ^ 64) (hR : R < 2 ^ 64)
    (hp : ∀ a, Region.Contains ⟨p, P⟩ a 1 → m₁ a = m₂ a)
    (hq : ∀ a, Region.Contains ⟨q, R⟩ a 1 → m₁ a = m₂ a)
    (hs : ∀ a, Region.Contains ⟨s, S⟩ a 1 → m₁ a = m₂ a)
    (h : Q (Spec.Sha3.bytesAt m₁ p P, Spec.Sha3.bytesAt m₁ q R) ∧ Scrubbed.Wiped w m m₁ s S) :
    Q (Spec.Sha3.bytesAt m₂ p P, Spec.Sha3.bytesAt m₂ q R) ∧ Scrubbed.Wiped w m m₂ s S := by
  rw [← bytesAt_agree0 hp hP (Nat.le_refl P), ← bytesAt_agree0 hq hR (Nat.le_refl R)]
  exact ⟨h.1, Scrubbed.wiped_congr hs h.2⟩

/-- `outs_congr` for one output. -/
theorem out_congr {w : Nat} {Q : List Byte → Prop} {m m₁ m₂ : Mem} {p s : Addr} {P S : Nat} (hP : P < 2 ^ 64)
    (hp : ∀ a, Region.Contains ⟨p, P⟩ a 1 → m₁ a = m₂ a)
    (hs : ∀ a, Region.Contains ⟨s, S⟩ a 1 → m₁ a = m₂ a)
    (h : Q (Spec.Sha3.bytesAt m₁ p P) ∧ Scrubbed.Wiped w m m₁ s S) :
    Q (Spec.Sha3.bytesAt m₂ p P) ∧ Scrubbed.Wiped w m m₂ s S := by
  rw [← bytesAt_agree0 hp hP (Nat.le_refl P)]
  exact ⟨h.1, Scrubbed.wiped_congr hs h.2⟩

theorem keyGenOut : PostOut (Scrubbed.keyGenContract abi 24) (Spec.MlKem.keyGenSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.1 hb.2.2.1 hb.2.2.2 h

theorem keyGen1024Out : PostOut (Scrubbed.keyGen1024Contract abi 24) (Spec.MlKem1024.keyGenSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.1 hb.2.2.1 hb.2.2.2 h

theorem encapsOut : PostOut (Scrubbed.encapsContract abi 32) (Spec.MlKem.encapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 h

theorem encaps1024Out : PostOut (Scrubbed.encaps1024Contract abi 32) (Spec.MlKem1024.encapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 h

theorem encapsHOut : PostOut (Scrubbed.encapsHContract abi 32) (Spec.MlKem.encapsHSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 h

theorem encapsH1024Out :
    PostOut (Scrubbed.encapsH1024Contract abi 32) (Spec.MlKem1024.encapsHSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 h

theorem decapsOut : PostOut (Scrubbed.decapsContract abi 24) (Spec.MlKem.decapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact out_congr (by decide) hb.2.2.1 hb.2.2.2 h

theorem decaps1024Out : PostOut (Scrubbed.decaps1024Contract abi 24) (Spec.MlKem1024.decapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact out_congr (by decide) hb.2.2.1 hb.2.2.2 h

end VG.Proof.MlKem.Arm.Scrub

namespace VG.Proof.MlKem.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.MlKem.Arm.Wipe

/-- `keyGen`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGenContract`). -/
theorem keyGen_wiped : VerifiedScrubbed target Impl.MlKem.Arm.Fn.keyGen (Scrubbed.keyGenContract abi 24) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGenApi)
    { code := Impl.MlKem.Arm.Wipe.keyGen, contract := Scrubbed.keyGenContract abi 24, verified := keyGen_scrubbed }
    Scrub.keyGenOut (scrubSideF_of Scrub.keyGen_ok (by decide) _)

/-- `vg_mlkem768_keygen`. -/
theorem keyGen : VerifiedScrubbed target Impl.MlKem.Arm.Fn.keyGen (Spec.MlKem.keyGenContract abi 24) 32 :=
  Scrubbed.keyGen_spec keyGen_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen_public :
    Spec.MlKem.keyGenOut.Of abi Impl.MlKem.Arm.Fn.keyGen
      (Spec.MlKem.keyGenContract abi 24) :=
  Scrubbed.keyGen_public keyGen_wiped

/-- `encapsH`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsHContract`). -/
theorem encapsH_wiped : VerifiedScrubbed target Impl.MlKem.Arm.Fn.encapsH (Scrubbed.encapsHContract abi 32) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsHApi)
    { code := Impl.MlKem.Arm.Wipe.encapsH, contract := Scrubbed.encapsHContract abi 32,
      verified := encapsH_scrubbed }
    Scrub.encapsHOut (scrubSideF_of Scrub.encapsH_ok (by decide) _)

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH : VerifiedScrubbed target Impl.MlKem.Arm.Fn.encapsH (Spec.MlKem.encapsHContract abi 32) 32 :=
  Scrubbed.encapsH_spec encapsH_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH_public :
    Spec.MlKem.encapsHOut.Of abi Impl.MlKem.Arm.Fn.encapsH
      (Spec.MlKem.encapsHContract abi 32) :=
  Scrubbed.encapsH_public encapsH_wiped

/-- `encaps`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsContract`). -/
theorem encaps_wiped : VerifiedScrubbed target Impl.MlKem.Arm.Fn.encaps (Scrubbed.encapsContract abi 32) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsApi)
    { code := Impl.MlKem.Arm.Wipe.encaps, contract := Scrubbed.encapsContract abi 32, verified := encaps_scrubbed }
    Scrub.encapsOut (scrubSideF_of Scrub.encaps_ok (by decide) _)

/-- `vg_mlkem768_encaps`. -/
theorem encaps : VerifiedScrubbed target Impl.MlKem.Arm.Fn.encaps (Spec.MlKem.encapsContract abi 32) 32 :=
  Scrubbed.encaps_spec encaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps_public :
    Spec.MlKem.encapsOut.Of abi Impl.MlKem.Arm.Fn.encaps
      (Spec.MlKem.encapsContract abi 32) :=
  Scrubbed.encaps_public encaps_wiped

/-- `decaps`, with the bytes of `scratch` it zeroes (`Scrubbed.decapsContract`). -/
theorem decaps_wiped : VerifiedScrubbed target Impl.MlKem.Arm.Fn.decaps (Scrubbed.decapsContract abi 24) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decapsApi)
    { code := Impl.MlKem.Arm.Wipe.decaps, contract := Scrubbed.decapsContract abi 24, verified := decaps_scrubbed }
    Scrub.decapsOut (scrubSideF_of Scrub.decaps_ok (by decide) _)

/-- `vg_mlkem768_decaps`. -/
theorem decaps : VerifiedScrubbed target Impl.MlKem.Arm.Fn.decaps (Spec.MlKem.decapsContract abi 24) 32 :=
  Scrubbed.decaps_spec decaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps_public :
    Spec.MlKem.decapsOut.Of abi Impl.MlKem.Arm.Fn.decaps
      (Spec.MlKem.decapsContract abi 24) :=
  Scrubbed.decaps_public decaps_wiped

/-- `vg_mlkem768_check_ek`. -/
theorem checkEk : VerifiedScrubbed target Impl.MlKem.Arm.Fn.checkEk (Spec.MlKem.checkEkContract abi) 32 :=
  verifiedScrubbed (api := Spec.MlKem.checkEkApi)
    { code := Impl.MlKem.Arm.checkEk, verified := Proof.MlKem.Arm.CheckEk.verified } rfl

/-- `keyGen1024`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGen1024Contract`). -/
theorem keyGen1024_wiped :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.keyGen1024 (Scrubbed.keyGen1024Contract abi 24) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGen1024Api)
    { code := Impl.MlKem.Arm.Wipe.keyGen1024, contract := Scrubbed.keyGen1024Contract abi 24,
      verified := keyGen1024_scrubbed }
    Scrub.keyGen1024Out (scrubSideF_of Scrub.keyGen1024_ok (by decide) _)

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024 :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.keyGen1024 (Spec.MlKem1024.keyGenContract abi 24) 32 :=
  Scrubbed.keyGen1024_spec keyGen1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen1024_public :
    Spec.MlKem1024.keyGenOut.Of abi Impl.MlKem.Arm.Fn.keyGen1024
      (Spec.MlKem1024.keyGenContract abi 24) :=
  Scrubbed.keyGen1024_public keyGen1024_wiped

/-- `encapsH1024`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsH1024Contract`). -/
theorem encapsH1024_wiped :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.encapsH1024 (Scrubbed.encapsH1024Contract abi 32) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsH1024Api)
    { code := Impl.MlKem.Arm.Wipe.encapsH1024, contract := Scrubbed.encapsH1024Contract abi 32,
      verified := encapsH1024_scrubbed }
    Scrub.encapsH1024Out (scrubSideF_of Scrub.encapsH1024_ok (by decide) _)

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024 :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.encapsH1024 (Spec.MlKem1024.encapsHContract abi 32) 32 :=
  Scrubbed.encapsH1024_spec encapsH1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH1024_public :
    Spec.MlKem1024.encapsHOut.Of abi Impl.MlKem.Arm.Fn.encapsH1024
      (Spec.MlKem1024.encapsHContract abi 32) :=
  Scrubbed.encapsH1024_public encapsH1024_wiped

/-- `encaps1024`, with the bytes of `scratch` it zeroes (`Scrubbed.encaps1024Contract`). -/
theorem encaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.encaps1024 (Scrubbed.encaps1024Contract abi 32) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encaps1024Api)
    { code := Impl.MlKem.Arm.Wipe.encaps1024, contract := Scrubbed.encaps1024Contract abi 32,
      verified := encaps1024_scrubbed }
    Scrub.encaps1024Out (scrubSideF_of Scrub.encaps1024_ok (by decide) _)

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024 :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.encaps1024 (Spec.MlKem1024.encapsContract abi 32) 32 :=
  Scrubbed.encaps1024_spec encaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps1024_public :
    Spec.MlKem1024.encapsOut.Of abi Impl.MlKem.Arm.Fn.encaps1024
      (Spec.MlKem1024.encapsContract abi 32) :=
  Scrubbed.encaps1024_public encaps1024_wiped

/-- `decaps1024`, with the bytes of `scratch` it zeroes (`Scrubbed.decaps1024Contract`). -/
theorem decaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.decaps1024 (Scrubbed.decaps1024Contract abi 24) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decaps1024Api)
    { code := Impl.MlKem.Arm.Wipe.decaps1024, contract := Scrubbed.decaps1024Contract abi 24,
      verified := decaps1024_scrubbed }
    Scrub.decaps1024Out (scrubSideF_of Scrub.decaps1024_ok (by decide) _)

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024 :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.decaps1024 (Spec.MlKem1024.decapsContract abi 24) 32 :=
  Scrubbed.decaps1024_spec decaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps1024_public :
    Spec.MlKem1024.decapsOut.Of abi Impl.MlKem.Arm.Fn.decaps1024
      (Spec.MlKem1024.decapsContract abi 24) :=
  Scrubbed.decaps1024_public decaps1024_wiped

/-- `vg_mlkem1024_check_ek`. -/
theorem checkEk1024 :
    VerifiedScrubbed target Impl.MlKem.Arm.Fn.checkEk1024 (Spec.MlKem1024.checkEkContract abi) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.checkEkApi)
    { code := Impl.MlKem1024.Arm.checkEk1024, verified := Proof.MlKem1024.Arm.CheckEk.verified } rfl

end VG.Proof.MlKem.Arm.Fn
