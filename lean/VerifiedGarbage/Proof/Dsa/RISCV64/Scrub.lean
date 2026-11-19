module

public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# DSA on RISC-V, without secret residue

The postconditions of `vg_dsa_validate_public_key`,
`vg_dsa_validate_private_key` and `vg_dsa_verify_prevalidated` do not read
the memory on return, and those of the other functions read it only within
their outputs (`bytesAt_of`, `wordsAt_of`; `RISCV64.Scrub.PostOut`), as
AArch64's `Proof/Dsa/AArch64/Scrub.lean` proves them: each implementation,
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`),
returns with the caller-saved registers cleared and the stack its frames used
zeroed. Each lemma takes the tables of constants `cs` the code reads, which
may be none.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, n * 1⟩`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨o, n * 1⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this]))).symm

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

variable (stack : Nat) (cs : List (String × List (BitVec 64)))

theorem toNat_sw (x : BitVec 64) : (x.setWidth (RISCV64.abi.withConsts cs).ptrBits).toNat = x.toNat := by
  rw [(ScrubAbi.consts cs).ptrBits]
  exact congrArg BitVec.toNat (BitVec.setWidth_eq x)

theorem validatePublicKeyOut :
    PostOut (Spec.Dsa.validatePublicKeyContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.validatePublicKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOut :
    PostOut (Spec.Dsa.validatePrivateKeyContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.validatePrivateKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem verifyPrevalidatedOut :
    PostOut (Spec.Dsa.verifyPrevalidatedContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.verifySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem parameterInitOut :
    PostOut (Spec.Dsa.parameterInitContract (RISCV64.abi.withConsts cs))
      (Spec.Dsa.parameterInitSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [state, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterInitSig.retBits 64) → Prop) [_, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterInitSig.retBits 64) → Prop) [_, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [wordsAt_of hb]
      exact h

theorem parameterSearchOut :
    PostOut (Spec.Dsa.parameterSearchContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.parameterSearchSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits 64) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits 64) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw cs outLen

theorem deriveKeyOut :
    PostOut (Spec.Dsa.deriveKeyContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.deriveKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.deriveKeySig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX]
      · exact h
      · exact toNat_sw cs outLen

theorem generateKeyOut :
    PostOut (Spec.Dsa.generateKeyContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.generateKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.generateKeySig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw cs outLen

theorem randomSignPrevalidatedOut :
    PostOut (Spec.Dsa.randomSignPrevalidatedContract (RISCV64.abi.withConsts cs) stack)
      (Spec.Dsa.randomSignSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.randomSignSig.retBits 64) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw cs outLen

end VG.Proof.Dsa.RISCV64.Scrub
