module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.MlKem.X86.Wipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.X86.CallWipe
public import VerifiedGarbage.Proof.MlKem.X86.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.MlKem.X86.Wipe
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.MlKem.X86.CallWipe
meta import VerifiedGarbage.Proof.MlKem.X86.CheckEk
meta import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-KEM-768 and ML-KEM-1024 on x86, without secret residue

Key generation, encapsulation (with `H(ek)` given or not), decapsulation and
the encapsulation key check call other functions and have frames: each is
followed, as emitted (`Impl.MlKem.X86.Fn`), by the zeroing of the stack its
contract reserves below `esp` (120 bytes, 136 for encapsulation with
`H(ek)`, 16 for the key check), then by `Impl.Scrub.X86.tail`, which clears
the registers a callee may change but the result's bits, the flags and
`xmm0`–`xmm7` (`X86.Scrub.verifiedScrubbedAll`).

Their postconditions read the memory on return only within their buffers
(`X86.Scrub.PostOut`, by `postOut_of_local`): the outputs, and `scratch`,
which each leaves scrubbed. What reads them is the same for both parameter
sets, whose outputs differ only in their sizes: `outs_congr` (two outputs:
key generation and both encapsulations) and `out_congr` (one: decapsulation)
state it once. What the scrub needs of the code is one Boolean,
`X86.Scrub.scrubFSide`, proved by evaluating the code once (`lit_decide`)
when this module is built.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.MlKem.X86.Wipe

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

theorem keyGenOut (stack : Nat) :
    PostOut (Scrubbed.keyGenContract abi stack) (Spec.MlKem.keyGenSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.1 hb.2.2.1 hb.2.2.2 h

theorem keyGen1024Out (stack : Nat) :
    PostOut (Scrubbed.keyGen1024Contract abi stack) (Spec.MlKem1024.keyGenSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.1 hb.2.2.1 hb.2.2.2 h

theorem encapsOut (stack : Nat) :
    PostOut (Scrubbed.encapsContract abi stack) (Spec.MlKem.encapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 h

theorem encaps1024Out (stack : Nat) :
    PostOut (Scrubbed.encaps1024Contract abi stack) (Spec.MlKem1024.encapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 h

theorem encapsHOut (stack : Nat) :
    PostOut (Scrubbed.encapsHContract abi stack) (Spec.MlKem.encapsHSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 h

theorem encapsH1024Out (stack : Nat) :
    PostOut (Scrubbed.encapsH1024Contract abi stack) (Spec.MlKem1024.encapsHSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact outs_congr (by decide) (by decide) hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 h

theorem decapsOut (stack : Nat) :
    PostOut (Scrubbed.decapsContract abi stack) (Spec.MlKem.decapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact out_congr (by decide) hb.2.2.1 hb.2.2.2 h

theorem decaps1024Out (stack : Nat) :
    PostOut (Scrubbed.decaps1024Contract abi stack) (Spec.MlKem1024.decapsSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    exact out_congr (by decide) hb.2.2.1 hb.2.2.2 h

/-- The key check's postcondition reads only the memory on entry. -/
theorem checkEkOut (stack : Nat) :
    PostOut (Spec.MlKem.checkEkContract abi stack) (Spec.MlKem.checkEkSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen _ h => by
    obtain ⟨a, rfl⟩ : ∃ a, vs = [a] := match vs, hlen with | [a], _ => ⟨a, rfl⟩
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    exact h

/-- ML-KEM-1024's. -/
theorem checkEk1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.checkEkContract abi stack) (Spec.MlKem1024.checkEkSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen _ h => by
    obtain ⟨a, rfl⟩ : ∃ a, vs = [a] := match vs, hlen with | [a], _ => ⟨a, rfl⟩
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    exact h

/-! ## The functions as emitted -/

/-- `keyGen_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGenContract`). -/
theorem keyGen_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.keyGen (Scrubbed.keyGenContract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGenApi)
    { code := Impl.MlKem.X86.Wipe.keyGen, verified := Proof.MlKem.X86.Wipe.keyGen_scrubbed }
    (by exact keyGenOut _)

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.keyGen (Spec.MlKem.keyGenContract X86.abi 120) 32 :=
  Scrubbed.keyGen_spec keyGen_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen_public :
    Spec.MlKem.keyGenOut.Of X86.abi Impl.MlKem.X86.Fn.keyGen
      (Spec.MlKem.keyGenContract X86.abi 120) :=
  Scrubbed.keyGen_public keyGen_wiped

/-- `encapsH_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsHContract`). -/
theorem encapsH_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encapsH (Scrubbed.encapsHContract X86.abi 136) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsHApi)
    { code := Impl.MlKem.X86.Wipe.encapsH, verified := Proof.MlKem.X86.Wipe.encapsH_scrubbed }
    (by exact encapsHOut _)

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encapsH (Spec.MlKem.encapsHContract X86.abi 136) 32 :=
  Scrubbed.encapsH_spec encapsH_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH_public :
    Spec.MlKem.encapsHOut.Of X86.abi Impl.MlKem.X86.Fn.encapsH
      (Spec.MlKem.encapsHContract X86.abi 136) :=
  Scrubbed.encapsH_public encapsH_wiped

/-- `encaps_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsContract`). -/
theorem encaps_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encaps (Scrubbed.encapsContract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsApi)
    { code := Impl.MlKem.X86.Wipe.encaps, verified := Proof.MlKem.X86.Wipe.encaps_scrubbed }
    (by exact encapsOut _)

/-- `vg_mlkem768_encaps`. -/
theorem encaps_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encaps (Spec.MlKem.encapsContract X86.abi 120) 32 :=
  Scrubbed.encaps_spec encaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps_public :
    Spec.MlKem.encapsOut.Of X86.abi Impl.MlKem.X86.Fn.encaps
      (Spec.MlKem.encapsContract X86.abi 120) :=
  Scrubbed.encaps_public encaps_wiped

/-- `decaps_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.decapsContract`). -/
theorem decaps_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.decaps (Scrubbed.decapsContract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decapsApi)
    { code := Impl.MlKem.X86.Wipe.decaps, verified := Proof.MlKem.X86.Wipe.decaps_scrubbed }
    (by exact decapsOut _)

/-- `vg_mlkem768_decaps`. -/
theorem decaps_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.decaps (Spec.MlKem.decapsContract X86.abi 120) 32 :=
  Scrubbed.decaps_spec decaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps_public :
    Spec.MlKem.decapsOut.Of X86.abi Impl.MlKem.X86.Fn.decaps
      (Spec.MlKem.decapsContract X86.abi 120) :=
  Scrubbed.decaps_public decaps_wiped

/-- `vg_mlkem768_check_ek`. -/
theorem checkEk_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.checkEk (Spec.MlKem.checkEkContract X86.abi 16) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem.checkEkApi)
    { code := Impl.MlKem.X86.checkEk, verified := Proof.MlKem.X86.CheckEk.verified }
    (by exact checkEkOut _)

/-- `keyGen1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGen1024Contract`). -/
theorem keyGen1024_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.keyGen1024 (Scrubbed.keyGen1024Contract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGen1024Api)
    { code := Impl.MlKem.X86.Wipe.keyGen1024, verified := Proof.MlKem.X86.Wipe.keyGen1024_scrubbed }
    (by exact keyGen1024Out _)

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.keyGen1024 (Spec.MlKem1024.keyGenContract X86.abi 120) 32 :=
  Scrubbed.keyGen1024_spec keyGen1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen1024_public :
    Spec.MlKem1024.keyGenOut.Of X86.abi Impl.MlKem.X86.Fn.keyGen1024
      (Spec.MlKem1024.keyGenContract X86.abi 120) :=
  Scrubbed.keyGen1024_public keyGen1024_wiped

/-- `encapsH1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsH1024Contract`). -/
theorem encapsH1024_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encapsH1024 (Scrubbed.encapsH1024Contract X86.abi 136) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsH1024Api)
    { code := Impl.MlKem.X86.Wipe.encapsH1024, verified := Proof.MlKem.X86.Wipe.encapsH1024_scrubbed }
    (by exact encapsH1024Out _)

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encapsH1024 (Spec.MlKem1024.encapsHContract X86.abi 136) 32 :=
  Scrubbed.encapsH1024_spec encapsH1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH1024_public :
    Spec.MlKem1024.encapsHOut.Of X86.abi Impl.MlKem.X86.Fn.encapsH1024
      (Spec.MlKem1024.encapsHContract X86.abi 136) :=
  Scrubbed.encapsH1024_public encapsH1024_wiped

/-- `encaps1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encaps1024Contract`). -/
theorem encaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encaps1024 (Scrubbed.encaps1024Contract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encaps1024Api)
    { code := Impl.MlKem.X86.Wipe.encaps1024, verified := Proof.MlKem.X86.Wipe.encaps1024_scrubbed }
    (by exact encaps1024Out _)

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.encaps1024 (Spec.MlKem1024.encapsContract X86.abi 120) 32 :=
  Scrubbed.encaps1024_spec encaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps1024_public :
    Spec.MlKem1024.encapsOut.Of X86.abi Impl.MlKem.X86.Fn.encaps1024
      (Spec.MlKem1024.encapsContract X86.abi 120) :=
  Scrubbed.encaps1024_public encaps1024_wiped

/-- `decaps1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.decaps1024Contract`). -/
theorem decaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.decaps1024 (Scrubbed.decaps1024Contract X86.abi 120) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decaps1024Api)
    { code := Impl.MlKem.X86.Wipe.decaps1024, verified := Proof.MlKem.X86.Wipe.decaps1024_scrubbed }
    (by exact decaps1024Out _)

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.decaps1024 (Spec.MlKem1024.decapsContract X86.abi 120) 32 :=
  Scrubbed.decaps1024_spec decaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps1024_public :
    Spec.MlKem1024.decapsOut.Of X86.abi Impl.MlKem.X86.Fn.decaps1024
      (Spec.MlKem1024.decapsContract X86.abi 120) :=
  Scrubbed.decaps1024_public decaps1024_wiped

/-- `vg_mlkem1024_check_ek`. -/
theorem checkEk1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.X86.Fn.checkEk1024 (Spec.MlKem1024.checkEkContract X86.abi 16) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem1024.checkEkApi)
    { code := Impl.MlKem1024.X86.checkEk, verified := Proof.MlKem1024.X86.CheckEk.verified }
    (by exact checkEk1024Out _)

end VG.Proof.MlKem.X86.Scrub
