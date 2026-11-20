module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM-768 and ML-KEM-1024 on PPC64LE, without secret residue

Key generation, encapsulation (with `H(ek)` given or not), decapsulation and
the encapsulation key check, followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbed`), which clears the volatile registers and the
stack their frames used. Their postconditions read the memory on return only
within their buffers: the outputs, and `scratch`, which each leaves scrubbed
(`Proof/MlKem/Scrubbed.lean`). The proofs are x86-64's
(`Proof/MlKem/X86_64/CallWipe.lean`), for this target's scrub.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.MlKem.PPC64LE.Wipe

/-- A buffer scrubbed in one memory on return is in another that agrees on it. -/
theorem scrubbed_congr {m m₁ m₂ : Mem} {p : Addr} {len : Nat}
    (hb : ∀ a, Region.Contains ⟨p, len⟩ a 1 → m₁ a = m₂ a) (h : Spec.Zeroize.scrubbed m m₁ p len) :
    Spec.Zeroize.scrubbed m m₂ p len := fun a ha => hb a ha ▸ h a ha

theorem keyGenOut (stack : Nat) :
    PostOut (Spec.MlKem.keyGenContract abi stack) (Spec.MlKem.keyGenSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 1184) (by decide),
      ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 2400) (by decide)]
    exact h1

theorem encapsHOut (stack : Nat) :
    PostOut (Spec.MlKem.encapsHContract abi stack) (Spec.MlKem.encapsHSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.2.1 (by decide) (n := 1088) (by decide)]
    exact h1

theorem encapsOut (stack : Nat) :
    PostOut (Spec.MlKem.encapsContract abi stack) (Spec.MlKem.encapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 1088) (by decide)]
    exact h1

theorem decapsOut (stack : Nat) :
    PostOut (Spec.MlKem.decapsContract abi stack) (Spec.MlKem.decapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
    exact h1

theorem keyGen1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.keyGenContract abi stack) (Spec.MlKem1024.keyGenSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide),
      ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 3168) (by decide)]
    exact h1

theorem encapsH1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.encapsHContract abi stack) (Spec.MlKem1024.encapsHSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.2.1 (by decide) (n := 1568) (by decide)]
    exact h1

theorem encaps1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.encapsContract abi stack) (Spec.MlKem1024.encapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 1568) (by decide)]
    exact h1

theorem decaps1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.decapsContract abi stack) (Spec.MlKem1024.decapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, scrubbed_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
    exact h1

/-- The key check's postcondition reads only the memory on entry. -/
theorem checkEkOut (stack : Nat) :
    PostOut (Spec.MlKem.checkEkContract abi stack) (Spec.MlKem.checkEkSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen _ h => by
    obtain ⟨a, rfl⟩ : ∃ a, vs = [a] := match vs, hlen with | [a], _ => ⟨a, rfl⟩
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    exact h

/-- ML-KEM-1024's. -/
theorem checkEk1024Out (stack : Nat) :
    PostOut (Spec.MlKem1024.checkEkContract abi stack) (Spec.MlKem1024.checkEkSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen _ h => by
    obtain ⟨a, rfl⟩ : ∃ a, vs = [a] := match vs, hlen with | [a], _ => ⟨a, rfl⟩
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    exact h

/-- `Spec.MlKem.keyGenApi`'s function as emitted (`Impl.MlKem.PPC64LE.Fn.keyGen`)
meets its contract in constant time and returns without secret residue. -/
theorem keyGen_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.keyGen
      (Spec.MlKem.keyGenContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem.keyGenApi) { code := Impl.MlKem.PPC64LE.Wipe.keyGen, verified := Proof.MlKem.PPC64LE.Wipe.keyGen_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact keyGenOut _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem.encapsApi`'s function as emitted (`Impl.MlKem.PPC64LE.Fn.encaps`)
meets its contract in constant time and returns without secret residue. -/
theorem encaps_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.encaps
      (Spec.MlKem.encapsContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem.encapsApi) { code := Impl.MlKem.PPC64LE.Wipe.encaps, verified := Proof.MlKem.PPC64LE.Wipe.encaps_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact encapsOut _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem.encapsHApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.encapsH`) meets its contract in constant time and
returns without secret residue. -/
theorem encapsH_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.encapsH
      (Spec.MlKem.encapsHContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem.encapsHApi) { code := Impl.MlKem.PPC64LE.Wipe.encapsH, verified := Proof.MlKem.PPC64LE.Wipe.encapsH_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact encapsHOut _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem.decapsApi`'s function as emitted (`Impl.MlKem.PPC64LE.Fn.decaps`)
meets its contract in constant time and returns without secret residue. -/
theorem decaps_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.decaps
      (Spec.MlKem.decapsContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem.decapsApi) { code := Impl.MlKem.PPC64LE.Wipe.decaps, verified := Proof.MlKem.PPC64LE.Wipe.decaps_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact decapsOut _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem.checkEkApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.checkEk`) meets its contract in constant time and
returns without secret residue. -/
theorem checkEk_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.checkEk
      (Spec.MlKem.checkEkContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.MlKem.checkEkApi) { code := Impl.MlKem.PPC64LE.checkEk, verified := Proof.MlKem.PPC64LE.CheckEk.verified }
    0 ⟨false, true, [.r4, .r5, .r6, .r7], false, []⟩
    (by exact checkEkOut _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem1024.checkEkApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.checkEk1024`) meets its contract in constant time and
returns without secret residue. -/
theorem checkEk1024_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.checkEk1024
      (Spec.MlKem1024.checkEkContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.checkEkApi) { code := Impl.MlKem1024.PPC64LE.checkEk1024, verified := Proof.MlKem1024.PPC64LE.CheckEk.verified }
    0 ⟨false, true, [.r4, .r5, .r6, .r7], false, []⟩
    (by exact checkEk1024Out _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem1024.keyGenApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.keyGen1024`) meets its contract in constant time and
returns without secret residue. -/
theorem keyGen1024_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.keyGen1024
      (Spec.MlKem1024.keyGenContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.keyGenApi) { code := Impl.MlKem.PPC64LE.Wipe.keyGen1024, verified := Proof.MlKem.PPC64LE.Wipe.keyGen1024_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact keyGen1024Out _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem1024.encapsApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.encaps1024`) meets its contract in constant time and
returns without secret residue. -/
theorem encaps1024_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.encaps1024
      (Spec.MlKem1024.encapsContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.encapsApi) { code := Impl.MlKem.PPC64LE.Wipe.encaps1024, verified := Proof.MlKem.PPC64LE.Wipe.encaps1024_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact encaps1024Out _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem1024.encapsHApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.encapsH1024`) meets its contract in constant time and
returns without secret residue. -/
theorem encapsH1024_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.encapsH1024
      (Spec.MlKem1024.encapsHContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.encapsHApi) { code := Impl.MlKem.PPC64LE.Wipe.encapsH1024, verified := Proof.MlKem.PPC64LE.Wipe.encapsH1024_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact encapsH1024Out _)
    (by dsimp only; lit_decide)

/-- `Spec.MlKem1024.decapsApi`'s function as emitted
(`Impl.MlKem.PPC64LE.Fn.decaps1024`) meets its contract in constant time and
returns without secret residue. -/
theorem decaps1024_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.MlKem.PPC64LE.Fn.decaps1024
      (Spec.MlKem1024.decapsContract PPC64LE.abi 96) 32 :=
  verifiedScrubbed (api := Spec.MlKem1024.decapsApi) { code := Impl.MlKem.PPC64LE.Wipe.decaps1024, verified := Proof.MlKem.PPC64LE.Wipe.decaps1024_verified }
    96 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    (by exact decaps1024Out _)
    (by dsimp only; lit_decide)

end VG.Proof.MlKem.PPC64LE.Scrub
