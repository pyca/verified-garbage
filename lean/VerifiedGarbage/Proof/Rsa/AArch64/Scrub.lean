module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA's precomputation and key generation on AArch64, without secret residue

The postconditions of `vg_rsa_public_precompute`, `vg_rsa_generate_init` and
`vg_rsa_generate` read the memory on return only within their outputs
(`ScrubAll.ScrubAllOk`, as x86-64's `Proof/Rsa/X86_64/Scrub.lean` and
`Proof/RsaKeyGen/X86_64/KeyInitScrub.lean` prove them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

theorem publicPrecomputeOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.publicPrecomputeContract abi stack) stack
      (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Rsa.publicPrecomputeSig) (Nat.le_of_ble_eq_true rfl) fun
    | [pre, preLen, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.publicPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = preLen.toNat → Spec.Rsa.wordsAt m₂ pre X = Spec.Rsa.wordsAt m₁ pre X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw preLen)]
      exact h

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 * n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega_using [hk, ht, this]) (by omega_using [hk, hN, ht, this]))).symm

theorem keyInitOk :
    ScrubAllOk (Spec.RsaKeyGen.keyInitContract abi) 0 (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.RsaKeyGen.keyInitSig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.RsaKeyGen.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    have h7 := wordsAt_congr (k := 7) (by decide) (by decide) hb.1
    have h6 := wordsAt_congr (k := 6) (by decide) (by decide) hb.1
    have hB : Spec.Rsa.bytesAt m₂ (a0 + 48) 8 = Spec.Rsa.bytesAt m₁ (a0 + 48) 8 := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [show (a0 + 48 : Addr) = a0 + BitVec.ofNat 64 48 from rfl, Offset.add_add]
      exact (hb.1 _ (Offset.contains_base _ (by omega_using [this]) (by omega_using [this]))).symm
    change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) → Prop) [_, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) → Prop) [_, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, h7, h6, hB]; exact h

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

theorem keySearchOk (stack : Nat) (hW : 0 < stack := by decide) :
    ScrubAllOk (Spec.RsaKeyGen.keySearchContract abi stack) stack
      (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) :=
  scrubAllOk_regs_pre (sig := Spec.RsaKeyGen.keySearchSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = keyLen.toNat → Spec.Rsa.bytesAt m₂ key X = Spec.Rsa.bytesAt m₁ key X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.1]; exact toNat_sw keyLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2,
        bytesAt48_of hb.2.2.2.2]
      exact h

end VG.Proof.Rsa.AArch64.Scrub
