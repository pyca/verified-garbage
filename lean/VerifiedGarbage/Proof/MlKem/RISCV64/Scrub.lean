module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.RISCV64.CallWipe
public import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.RISCV64.CheckEk

/-!
# ML-KEM-768 and ML-KEM-1024 on RISC-V, without secret residue

Key generation, encapsulation (with `H(ek)` given or not), decapsulation and
the encapsulation key check, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and
the stack their frames used (1200 bytes, `Wipe.*_verified`). Their postconditions read the memory on return only
within their buffers: the outputs, and `scratch`, which each leaves scrubbed
(`Proof/MlKem/Scrubbed.lean`). The proofs are PPC64LE's
(`Proof/MlKem/PPC64LE/Scrub.lean`), for this target's scrub.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.MlKem.RISCV64.Wipe

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

def keyGenReg : Registration Spec.MlKem.keyGenApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.keyGen, verified := Proof.MlKem.RISCV64.Wipe.keyGen_verified }
    (by exact keyGenOut _)

def encapsReg : Registration Spec.MlKem.encapsApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.encaps, verified := Proof.MlKem.RISCV64.Wipe.encaps_verified }
    (by exact encapsOut _)

def encapsHReg : Registration Spec.MlKem.encapsHApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.encapsH, verified := Proof.MlKem.RISCV64.Wipe.encapsH_verified }
    (by exact encapsHOut _)

def decapsReg : Registration Spec.MlKem.decapsApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.decaps, verified := Proof.MlKem.RISCV64.Wipe.decaps_verified }
    (by exact decapsOut _)

def checkEkReg : Registration Spec.MlKem.checkEkApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.checkEk, verified := Proof.MlKem.RISCV64.CheckEk.verified }
    (by exact checkEkOut _)

def checkEk1024Reg : Registration Spec.MlKem1024.checkEkApi RISCV64.target :=
  scrubOf { code := Impl.MlKem1024.RISCV64.checkEk1024, verified := Proof.MlKem1024.RISCV64.CheckEk.verified }
    (by exact checkEk1024Out _)

def keyGen1024Reg : Registration Spec.MlKem1024.keyGenApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.keyGen1024, verified := Proof.MlKem.RISCV64.Wipe.keyGen1024_verified }
    (by exact keyGen1024Out _)

def encaps1024Reg : Registration Spec.MlKem1024.encapsApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.encaps1024, verified := Proof.MlKem.RISCV64.Wipe.encaps1024_verified }
    (by exact encaps1024Out _)

def encapsH1024Reg : Registration Spec.MlKem1024.encapsHApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.encapsH1024, verified := Proof.MlKem.RISCV64.Wipe.encapsH1024_verified }
    (by exact encapsH1024Out _)

def decaps1024Reg : Registration Spec.MlKem1024.decapsApi RISCV64.target :=
  scrubOf { code := Impl.MlKem.RISCV64.Wipe.decaps1024, verified := Proof.MlKem.RISCV64.Wipe.decaps1024_verified }
    (by exact decaps1024Out _)

end VG.Proof.MlKem.RISCV64.Scrub
