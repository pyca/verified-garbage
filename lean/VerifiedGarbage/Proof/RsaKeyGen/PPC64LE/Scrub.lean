module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA key generation on PPC64LE, without secret residue

`vg_rsa_generate_init` and `vg_rsa_generate`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`): `init` has no
frame, so the tail only clears the volatile registers it may write;
`vg_rsa_generate` keeps the candidates, the Miller–Rabin state and its
callers' state in frames it does not wipe themselves, which the tail zeroes.
Their postconditions read the memory on return only within the state, and
the key's buffer and `used` (`keyInitOut`, `keySearchOut`), as on x86-64
(`Proof/RsaKeyGen/X86_64/KeyInitScrub.lean`, `Proof/Rsa/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Rsa.PPC64LE.Scrub

/-! ## Postconditions -/

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 * n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega_using [hk, ht, this]) (by omega_using [hk, hN, ht, this]))).symm

theorem keyInitOut : PostOut (Spec.RsaKeyGen.keyInitContract abi) (Spec.RsaKeyGen.keyInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
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
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₂ r
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
      rw [e _ (by rw [← hp.2.1]; exact toNat_swC cs keyLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2,
        bytesAt48_of hb.2.2.2.2]
      exact h

/-! ## The registrations -/

/-- `Spec.RsaKeyGen.keyInitApi`. -/
def keyInitReg : Registration Spec.RsaKeyGen.keyInitApi PPC64LE.target :=
  scrubOf {
      code := Impl.RsaKeyGen.PPC64LE.KeyInit.init
      verified := Proof.RsaKeyGen.PPC64LE.KeyInit.init_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    keyInitOut
    (by dsimp only; lit_decide)

/-- What `scrubOf` needs of the search with each Miller–Rabin round:
evaluated here. -/
theorem keySearchSide (v : Proof.MillerRabin.PPC64LE.RoundImpl)
    (hv : v ∈ Proof.Variants.MillerRabin.PPC64LE.variants) :
    scrubSide (Proof.RsaKeyGen.PPC64LE.Generate.genCode v) 1088 (Spec.RsaKeyGen.keySearchSig.retBits 64)
      ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
        [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩ = true := by
  have h : (Proof.Variants.MillerRabin.PPC64LE.variants.all fun v =>
      scrubSide (Proof.RsaKeyGen.PPC64LE.Generate.genCode v) 1088 (Spec.RsaKeyGen.keySearchSig.retBits 64)
        ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
          [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `Spec.RsaKeyGen.keySearchApi`, with the Miller–Rabin round `v`. -/
def keySearchReg (v : Proof.MillerRabin.PPC64LE.RoundImpl)
    (hv : v ∈ Proof.Variants.MillerRabin.PPC64LE.variants) :
    Registration Spec.RsaKeyGen.keySearchApi PPC64LE.target :=
  scrubOf {
      suffix := v.suffix
      code := Proof.RsaKeyGen.PPC64LE.Generate.genCode v
      verified := Proof.RsaKeyGen.PPC64LE.Generate.gen_verified v }
    1088 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (keySearchOut Proof.RsaKeyGen.PPC64LE.Generate.tables Proof.RsaKeyGen.PPC64LE.Generate.stackUse)
    (keySearchSide v hv)

end VG.Proof.RsaKeyGen.PPC64LE.Scrub
