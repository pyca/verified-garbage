module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# FFDH on x86-64, without secret residue

The postconditions of the domain, key and exchange functions read the memory
on return only within their outputs (`X86_64.Scrub.PostOut`): the checks not
at all, `vg_ffdh_exchange` and `vg_ffdh_derive_public` the octets at `out`
and `y` (`bytesAt_of`, `written_of`), the precomputation the words at `ctx`
(`wordsAt_of`). Each implementation returns with its whole stack wiped
(`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

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

theorem toNat_sw (cs : List (String × List (BitVec 64))) (x : BitVec 64) :
    (x.setWidth (abi.withConsts cs).ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, (ScrubAbi.consts cs).ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem checkDomainOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkDomainContract (abi.withConsts cs) stack) (Spec.Ffdh.checkDomainSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPublicContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPublicSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPrivateOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPrivateContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPrivateSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem exchangeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.exchangeContract (abi.withConsts cs) stack) (Spec.Ffdh.exchangeSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      have e := bytesAt_of hb.1
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      exact fun hd hp => written_of (by rw [toNat_sw]; exact e) (h hd hp)

theorem derivePublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.derivePublicContract (abi.withConsts cs) stack) (Spec.Ffdh.derivePublicSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun
    | [y, yLen, _, _, pLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Ffdh.derivePublicSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = yLen.toNat → Spec.Rsa.bytesAt m₂ y X = Spec.Rsa.bytesAt m₁ y X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.2.1]; exact toNat_sw cs yLen)]
      exact h

theorem generationPrecomputeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.generationPrecomputeContract (abi.withConsts cs) stack)
      (Spec.Ffdh.generationPrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [ctx, ctxLen, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.generationPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = ctxLen.toNat → Spec.Rsa.wordsAt m₂ ctx X = Spec.Rsa.wordsAt m₁ ctx X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw cs ctxLen)]
      exact h

theorem sievedParameterSearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts cs) stack)
      (Spec.Ffdh.parameterSearchSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw cs outLen

theorem cachedKeySearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.cachedKeySearchContract (abi.withConsts cs) stack)
      (Spec.Ffdh.cachedKeySearchSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hp hb h => by
    obtain ⟨x, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 14) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨xLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨y, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨yLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨used, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 7
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, List.cons_append, List.nil_append,
      Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
    have ex : ∀ X, X = xLen.toNat → Spec.Rsa.bytesAt m₂ x X = Spec.Rsa.bytesAt m₁ x X :=
      fun X hX => hX ▸ bytesAt_of hb.1
    have ey : ∀ X, X = yLen.toNat → Spec.Rsa.bytesAt m₂ y X = Spec.Rsa.bytesAt m₁ y X :=
      fun X hX => hX ▸ bytesAt_of hb.2.1
    rw [ex _ (by rw [← hp.2.2.1]; exact toNat_sw cs xLen), ey _ (by rw [← hp.2.2.2.1]; exact toNat_sw cs yLen),
      wordsAt_of hb.2.2.2.2.2.2.1, wordsAt_of hb.2.2.1]
    exact h

end VG.Proof.Ffdh.X86_64.Scrub
