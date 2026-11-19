module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA on RISC-V, without secret residue

The postconditions of RSA's functions read the memory on return only within
their outputs (`RISCV64.Scrub.PostOut`), as on x86-64
(`Proof/Rsa/X86_64/Scrub.lean`) and AArch64 (`Proof/Rsa/AArch64/Scrub.lean`):
the key check not at all, the others the octets at `out` (or the key's
buffer, or `p` and `q`, or `dp`, `dq` and `qinv`) and the words at `pre`,
`used` and `state`. Each implementation is followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the whole stack its frames use.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Scrub

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

theorem toNat_sw {A : Abi isa} (hA : ScrubAbi A) (x : BitVec 64) : (x.setWidth A.ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, hA.ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

/-! ## Precomputation and keys -/

theorem publicPrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.publicPrecomputeContract abi stack) (Spec.Rsa.publicPrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.publicPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = preLen.toNat → Spec.Rsa.wordsAt m₂ pre X = Spec.Rsa.wordsAt m₁ pre X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw ScrubAbi.plain preLen)]
      exact h

theorem privatePrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.privatePrecomputeContract abi stack) (Spec.Rsa.privatePrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := wordsAt_of (n := (preLen.setWidth abi.ptrBits).toNat) hb.1 (by rw [toNat_sw ScrubAbi.plain])
      revert h
      split
      · exact fun h => ⟨h.1, e.trans h.2⟩
      · exact fun h => ⟨h.1, e.trans h.2⟩

theorem crtValuesOut (stack : Nat) :
    PostOut (Spec.Rsa.crtValuesContract abi stack) (Spec.Rsa.crtValuesSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [dp, dpLen, dq, dqLen, qinv, qinvLen, _, _, _, pLen, _, qLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.crtValuesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, -, -, -, -, hdp, hqi, hdq, -⟩ := hp
      have e₁ : ∀ X, X = dpLen.toNat → Spec.Rsa.bytesAt m₂ dp X = Spec.Rsa.bytesAt m₁ dp X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have e₂ : ∀ X, X = dqLen.toNat → Spec.Rsa.bytesAt m₂ dq X = Spec.Rsa.bytesAt m₁ dq X :=
        fun X hX => hX ▸ bytesAt_of hb.2.1
      have e₃ : ∀ X, X = qinvLen.toNat → Spec.Rsa.bytesAt m₂ qinv X = Spec.Rsa.bytesAt m₁ qinv X :=
        fun X hX => hX ▸ bytesAt_of hb.2.2.1
      revert h
      generalize Option.map _ _ = v
      rw [toNat_sw ScrubAbi.plain] at hdp hdq hqi
      have ep := e₁ _ hdp.symm
      have eq := e₂ _ hdq.symm
      have ei := e₃ _ hqi.symm
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq, ei] <;> exact id

theorem checkKeyOut (stack : Nat) :
    PostOut (Spec.Rsa.checkKeyContract abi stack) (Spec.Rsa.checkKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem recoverPrimesDetOut (stack : Nat) :
    PostOut (Spec.Rsa.recoverPrimesDetContract abi stack) (Spec.Rsa.recoverPrimesDetSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [p, pLen, q, qLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.recoverPrimesDetSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, hpl, hql, -⟩ := hp
      have e₁ : ∀ X, X = pLen.toNat → Spec.Rsa.bytesAt m₂ p X = Spec.Rsa.bytesAt m₁ p X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have e₂ : ∀ X, X = qLen.toNat → Spec.Rsa.bytesAt m₂ q X = Spec.Rsa.bytesAt m₁ q X :=
        fun X hX => hX ▸ bytesAt_of hb.2.1
      revert h
      generalize Option.map _ _ = v
      rw [toNat_sw ScrubAbi.plain] at hpl hql
      have ep := e₁ _ hpl.symm
      have eq := e₂ _ hql.symm
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq] <;> exact id

/-! ## Key generation -/

/-- The 8 octets at `state + 48` lie in the 56 bytes of `state`. -/
theorem bytesAt48_of {m₁ m₂ : Mem} {o : Addr}
    (h : ∀ a, Region.Contains ⟨o, 7 * 8⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ (o + 48) 8 = Spec.Rsa.bytesAt m₁ (o + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  have e : o + 48 + BitVec.ofNat 64 i = o + BitVec.ofNat 64 (48 + i) := Offset.add_add o 48 i
  rw [e]
  exact (h _ (contains_of (by omega))).symm

theorem keyInitOut : PostOut (Spec.RsaKeyGen.keyInitContract abi) (Spec.RsaKeyGen.keyInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun
    | [state, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.RsaKeyGen.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply] at h ⊢
      rw [show ArgWord.addr.ofRaw state = state from rfl, wordsAt_of (n := 7) hb.1,
        wordsAt_of (n := 6) hb.1, bytesAt48_of hb.1]
      exact h

theorem keySearchOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.RsaKeyGen.keySearchContract (abi.withConsts cs) stack)
      (Spec.RsaKeyGen.keySearchSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = keyLen.toNat → Spec.Rsa.bytesAt m₂ key X = Spec.Rsa.bytesAt m₁ key X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.1]; exact toNat_sw (ScrubAbi.consts cs) keyLen), wordsAt_of hb.2.1,
        wordsAt_of hb.2.2.2.2, bytesAt48_of hb.2.2.2.2]
      exact h

end VG.Proof.Rsa.RISCV64.Scrub
