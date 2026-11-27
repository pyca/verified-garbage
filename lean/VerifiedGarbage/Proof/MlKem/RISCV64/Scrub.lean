module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.MlKem.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.RISCV64.CallWipe
public import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk

/-!
# ML-KEM-768 and ML-KEM-1024 on RISC-V, without secret residue

Key generation, encapsulation (with `H(ek)` given or not), decapsulation and
the encapsulation key check, as emitted (`Impl.MlKem.RISCV64.Fn`): each
followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the caller-saved
registers and the stack their frames used (1200 bytes, `Wipe.*_scrubbed`).
Each theorem below states that one meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`), which is what its registration binds.
Their postconditions read the memory on return only
within their buffers: the outputs, and `scratch`, which each leaves scrubbed
(`Proof/MlKem/Scrubbed.lean`). The proofs are PPC64LE's
(`Proof/MlKem/PPC64LE/Scrub.lean`), for this target's scrub.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.MlKem.RISCV64.Wipe

theorem keyGenOut (stack : Nat) :
    PostOut (Scrubbed.keyGenContract abi stack) (Spec.MlKem.keyGenSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe4, Scrubbed.keyGenPost] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 1184) (by decide),
      ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 2400) (by decide)]
    exact h1

theorem encapsHOut (stack : Nat) :
    PostOut (Scrubbed.encapsHContract abi stack) (Spec.MlKem.encapsHSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe6, Scrubbed.encapsHPost] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.2.1 (by decide) (n := 1088) (by decide)]
    exact h1

theorem encapsOut (stack : Nat) :
    PostOut (Scrubbed.encapsContract abi stack) (Spec.MlKem.encapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe5, Scrubbed.encapsPost] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 1088) (by decide)]
    exact h1

theorem decapsOut (stack : Nat) :
    PostOut (Scrubbed.decapsContract abi stack) (Spec.MlKem.decapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe4, Scrubbed.decapsPost] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
    exact h1

theorem keyGen1024Out (stack : Nat) :
    PostOut (Scrubbed.keyGen1024Contract abi stack) (Spec.MlKem1024.keyGenSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe4, Scrubbed.keyGen1024Post] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide),
      ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 3168) (by decide)]
    exact h1

theorem encapsH1024Out (stack : Nat) :
    PostOut (Scrubbed.encapsH1024Contract abi stack) (Spec.MlKem1024.encapsHSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
    simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe6, Scrubbed.encapsH1024Post] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.2.1 (by decide) (n := 1568) (by decide)]
    exact h1

theorem encaps1024Out (stack : Nat) :
    PostOut (Scrubbed.encaps1024Contract abi stack) (Spec.MlKem1024.encapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
    simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe5, Scrubbed.encaps1024Post] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2.2 h2⟩
    rw [← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide),
      ← bytesAt_agree0 hb.2.2.2.1 (by decide) (n := 1568) (by decide)]
    exact h1

theorem decaps1024Out (stack : Nat) :
    PostOut (Scrubbed.decaps1024Contract abi stack) (Spec.MlKem1024.decapsSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
    simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
    change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
    dsimp only [Curry.apply, ArgWord.ofRaw, Scrubbed.wipe4, Scrubbed.decaps1024Post] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, Scrubbed.wiped_congr hb.2.2.2 h2⟩
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

/-- `keyGen_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGenContract`). -/
theorem keyGen_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.keyGen (Scrubbed.keyGenContract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGenApi) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.keyGen, verified := Proof.MlKem.RISCV64.Wipe.keyGen_scrubbed }
    (keyGenOut _) (by lit_decide)

/-- `vg_mlkem768_keygen` as emitted (`Impl.MlKem.RISCV64.Fn.keyGen`) meets its contract in
constant time and returns without secret residue. -/
theorem keyGen_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.keyGen (Spec.MlKem.keyGenContract abi 1200) 32 :=
  Scrubbed.keyGen_spec keyGen_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen_public :
    Spec.MlKem.keyGenOut.Of abi Impl.MlKem.RISCV64.Fn.keyGen
      (Spec.MlKem.keyGenContract abi 1200) :=
  Scrubbed.keyGen_public keyGen_wiped

/-- `encaps_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsContract`). -/
theorem encaps_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encaps (Scrubbed.encapsContract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsApi) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.encaps, verified := Proof.MlKem.RISCV64.Wipe.encaps_scrubbed }
    (encapsOut _) (by lit_decide)

/-- `vg_mlkem768_encaps` as emitted (`Impl.MlKem.RISCV64.Fn.encaps`) meets its contract in
constant time and returns without secret residue. -/
theorem encaps_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encaps (Spec.MlKem.encapsContract abi 1200) 32 :=
  Scrubbed.encaps_spec encaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps_public :
    Spec.MlKem.encapsOut.Of abi Impl.MlKem.RISCV64.Fn.encaps
      (Spec.MlKem.encapsContract abi 1200) :=
  Scrubbed.encaps_public encaps_wiped

/-- `encapsH_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsHContract`). -/
theorem encapsH_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encapsH (Scrubbed.encapsHContract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsHApi) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.encapsH, verified := Proof.MlKem.RISCV64.Wipe.encapsH_scrubbed }
    (encapsHOut _) (by lit_decide)

/-- `vg_mlkem768_encaps_h` as emitted (`Impl.MlKem.RISCV64.Fn.encapsH`) meets its contract in
constant time and returns without secret residue. -/
theorem encapsH_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encapsH (Spec.MlKem.encapsHContract abi 1200) 32 :=
  Scrubbed.encapsH_spec encapsH_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH_public :
    Spec.MlKem.encapsHOut.Of abi Impl.MlKem.RISCV64.Fn.encapsH
      (Spec.MlKem.encapsHContract abi 1200) :=
  Scrubbed.encapsH_public encapsH_wiped

/-- `decaps_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.decapsContract`). -/
theorem decaps_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.decaps (Scrubbed.decapsContract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decapsApi) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.decaps, verified := Proof.MlKem.RISCV64.Wipe.decaps_scrubbed }
    (decapsOut _) (by lit_decide)

/-- `vg_mlkem768_decaps` as emitted (`Impl.MlKem.RISCV64.Fn.decaps`) meets its contract in
constant time and returns without secret residue. -/
theorem decaps_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.decaps (Spec.MlKem.decapsContract abi 1200) 32 :=
  Scrubbed.decaps_spec decaps_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps_public :
    Spec.MlKem.decapsOut.Of abi Impl.MlKem.RISCV64.Fn.decaps
      (Spec.MlKem.decapsContract abi 1200) :=
  Scrubbed.decaps_public decaps_wiped

/-- `vg_mlkem768_check_ek` as emitted (`Impl.MlKem.RISCV64.Fn.checkEk`) meets its contract in
constant time and returns without secret residue. -/
theorem checkEk_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.checkEk (Spec.MlKem.checkEkContract abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem.checkEkApi) (W := 0)
    { code := Impl.MlKem.RISCV64.checkEk, verified := Proof.MlKem.RISCV64.CheckEk.verified }
    (checkEkOut _) (by lit_decide)

/-- `vg_mlkem1024_check_ek` as emitted (`Impl.MlKem.RISCV64.Fn.checkEk1024`) meets its contract in
constant time and returns without secret residue. -/
theorem checkEk1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.checkEk1024 (Spec.MlKem1024.checkEkContract abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.MlKem1024.checkEkApi) (W := 0)
    { code := Impl.MlKem1024.RISCV64.checkEk1024, verified := Proof.MlKem1024.RISCV64.CheckEk.verified }
    (checkEk1024Out _) (by lit_decide)

/-- `keyGen1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.keyGen1024Contract`). -/
theorem keyGen1024_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.keyGen1024 (Scrubbed.keyGen1024Contract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.keyGen1024Api) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.keyGen1024, verified := Proof.MlKem.RISCV64.Wipe.keyGen1024_scrubbed }
    (keyGen1024Out _) (by lit_decide)

/-- `vg_mlkem1024_keygen` as emitted (`Impl.MlKem.RISCV64.Fn.keyGen1024`) meets its contract in
constant time and returns without secret residue. -/
theorem keyGen1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.keyGen1024 (Spec.MlKem1024.keyGenContract abi 1200) 32 :=
  Scrubbed.keyGen1024_spec keyGen1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem keyGen1024_public :
    Spec.MlKem1024.keyGenOut.Of abi Impl.MlKem.RISCV64.Fn.keyGen1024
      (Spec.MlKem1024.keyGenContract abi 1200) :=
  Scrubbed.keyGen1024_public keyGen1024_wiped

/-- `encaps1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encaps1024Contract`). -/
theorem encaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encaps1024 (Scrubbed.encaps1024Contract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encaps1024Api) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.encaps1024, verified := Proof.MlKem.RISCV64.Wipe.encaps1024_scrubbed }
    (encaps1024Out _) (by lit_decide)

/-- `vg_mlkem1024_encaps` as emitted (`Impl.MlKem.RISCV64.Fn.encaps1024`) meets its contract in
constant time and returns without secret residue. -/
theorem encaps1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encaps1024 (Spec.MlKem1024.encapsContract abi 1200) 32 :=
  Scrubbed.encaps1024_spec encaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encaps1024_public :
    Spec.MlKem1024.encapsOut.Of abi Impl.MlKem.RISCV64.Fn.encaps1024
      (Spec.MlKem1024.encapsContract abi 1200) :=
  Scrubbed.encaps1024_public encaps1024_wiped

/-- `encapsH1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.encapsH1024Contract`). -/
theorem encapsH1024_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encapsH1024 (Scrubbed.encapsH1024Contract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.encapsH1024Api) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.encapsH1024, verified := Proof.MlKem.RISCV64.Wipe.encapsH1024_scrubbed }
    (encapsH1024Out _) (by lit_decide)

/-- `vg_mlkem1024_encaps_h` as emitted (`Impl.MlKem.RISCV64.Fn.encapsH1024`) meets its contract in
constant time and returns without secret residue. -/
theorem encapsH1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.encapsH1024 (Spec.MlKem1024.encapsHContract abi 1200) 32 :=
  Scrubbed.encapsH1024_spec encapsH1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem encapsH1024_public :
    Spec.MlKem1024.encapsHOut.Of abi Impl.MlKem.RISCV64.Fn.encapsH1024
      (Spec.MlKem1024.encapsHContract abi 1200) :=
  Scrubbed.encapsH1024_public encapsH1024_wiped

/-- `decaps1024_scrubbed`, with the bytes of `scratch` it zeroes (`Scrubbed.decaps1024Contract`). -/
theorem decaps1024_wiped :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.decaps1024 (Scrubbed.decaps1024Contract abi 1200) 32 :=
  verifiedScrubbedAll (api := Scrubbed.decaps1024Api) (W := 1200)
    { code := Impl.MlKem.RISCV64.Wipe.decaps1024, verified := Proof.MlKem.RISCV64.Wipe.decaps1024_scrubbed }
    (decaps1024Out _) (by lit_decide)

/-- `vg_mlkem1024_decaps` as emitted (`Impl.MlKem.RISCV64.Fn.decaps1024`) meets its contract in
constant time and returns without secret residue. -/
theorem decaps1024_scrubbed :
    VerifiedScrubbed target Impl.MlKem.RISCV64.Fn.decaps1024 (Spec.MlKem1024.decapsContract abi 1200) 32 :=
  Scrubbed.decaps1024_spec decaps1024_wiped id

/-- What it leaves in `scratch` is public. -/
theorem decaps1024_public :
    Spec.MlKem1024.decapsOut.Of abi Impl.MlKem.RISCV64.Fn.decaps1024
      (Spec.MlKem1024.decapsContract abi 1200) :=
  Scrubbed.decaps1024_public decaps1024_wiped

end VG.Proof.MlKem.RISCV64.Scrub
