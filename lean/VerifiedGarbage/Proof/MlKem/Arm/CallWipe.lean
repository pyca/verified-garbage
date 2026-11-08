module

public import VerifiedGarbage.Impl.MlKem.Arm.Wipe
public import VerifiedGarbage.Proof.Framework.Arm.CallWipe
public import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
public import VerifiedGarbage.Proof.Zeroize.Arm
public import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.EncapsHSat

/-!
# ML-KEM on 32-bit ARM: the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/Arm.lean`) of its code, for key generation and
decapsulation, which get `scratch` in `r3`, or `callWipeStack`
(`Impl/CallWipe/ArmStack.lean`), for encapsulation, which gets it on the
stack, and zeroes all of `scratch` with `vg_zeroize` once that code returns.
It is verified against the same contract with 16 more bytes of stack, 24
(`Verified.callWipe'`), or 24 more, 32 (`Verified.callWipeStack'`: its frame
and the copy of the stack arguments, 8 bytes for one word or two), with
`scratch` left scrubbed (`*_scrubbed`, the contracts of
`Proof/MlKem/Scrubbed.lean`), since every byte of it is zero
(`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Wipe

open VG VG.Arm VG.Arm.FrameStack

/-- `vg_zeroize` has no frames. -/
theorem zeroize_stack : armStack Impl.Zeroize.Arm.zeroize ≤ 0 := by decide

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega) (by omega))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega)
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega) hj hij hw

/-! ## The functions, with any code verified against their contracts -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 32768 "vg_mlkem768_keygen" body) (Scrubbed.keyGenContract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 2 4 32768 "vg_mlkem768_encaps_h" body) (Scrubbed.encapsHContract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (k := 2) (off := 4) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 1 0 32768 "vg_mlkem768_encaps" body) (Scrubbed.encapsContract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (k := 1) (off := 0) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 32768 "vg_mlkem768_decaps" body) (Scrubbed.decapsContract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 49152 "vg_mlkem1024_keygen" body) (Scrubbed.keyGen1024Contract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 2 4 49152 "vg_mlkem1024_encaps_h" body) (Scrubbed.encapsH1024Contract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := []) (i := 5) (k := 2) (off := 4) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 32).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wipedStack 1 0 49152 "vg_mlkem1024_encaps" body) (Scrubbed.encaps1024Contract abi 32) :=
  Verified.callWipeStack' (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := []) (i := 4) (k := 1) (off := 0) (stack := 8) h
    Proof.Zeroize.Arm.verified (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 8))
    (hd : armStack body ≤ 8)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 24).pre s) :
    Verified target (Impl.MlKem.Arm.Wipe.wiped .r3 49152 "vg_mlkem1024_decaps" body) (Scrubbed.decaps1024Contract abi 24) :=
  Verified.callWipe' (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := []) (i := 3) (stack := 8) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) hd zeroize_stack (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    hsat
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])

/-! ## The stack the functions use: their callees' frames, at most 8 bytes -/

theorem keyGen_stack : armStack Impl.MlKem.Arm.keygen ≤ 8 := by decide
theorem encapsH_stack : armStack Impl.MlKem.Arm.encapsH ≤ 8 := by decide
theorem encaps_stack : armStack Impl.MlKem.Arm.encaps ≤ 8 := by decide
theorem decaps_stack : armStack Impl.MlKem.Arm.decaps ≤ 8 := by decide
theorem keyGen1024_stack : armStack Impl.MlKem1024.Arm.keygen1024 ≤ 8 := by decide
theorem encapsH1024_stack : armStack Impl.MlKem1024.Arm.encapsH1024 ≤ 8 := by decide
theorem encaps1024_stack : armStack Impl.MlKem1024.Arm.encaps1024 ≤ 8 := by decide
theorem decaps1024_stack : armStack Impl.MlKem1024.Arm.decaps1024 ≤ 8 := by decide

/-! ## The states satisfying the preconditions, with the frames' bytes of stack -/

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem.Arm.KeyGen.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

/-- The state `w`, `satStateH n ctLen scr`, satisfies `encapsH`'s
precondition, after `sig_apply_check`: `H(ek)` is at `h` (`hMem_h_of`). -/
macro "wipe_satH " w:term:max n:num " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (sig_apply_check
   · decide +kernel
   · sig_reduce [$ls,*]
     sig_and_intros
     all_goals first
       | (show Spec.Sha3.bytesAt ($w).mem (0x2000 : BitVec 64) 32 =
             Spec.MlKem.H (Spec.Sha3.bytesAt ($w).mem (0x1000 : BitVec 64) $n)
          exact VG.Proof.MlKem.hMem_h_of (by decide) Proof.MlKem.Arm.Encaps.satStateH_mem)
       | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
          decide +kernel)))

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satStateH 1184 1088 32768, ?_⟩
  wipe_satH (Proof.MlKem.Arm.Encaps.satStateH 1184 1088 32768) 1184 [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem.Arm.Decaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem1024.Arm.KeyGen.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem1024.Arm.Encaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 32).pre s := by
  refine ⟨Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152, ?_⟩
  wipe_satH (Proof.MlKem.Arm.Encaps.satStateH 1568 1568 49152) 1568 [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 24).pre s := by
  refine ⟨Proof.MlKem1024.Arm.Decaps.satState, ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]

/-! ## The functions -/

theorem keyGen_scrubbed : Verified target Impl.MlKem.Arm.Wipe.keyGen (Scrubbed.keyGenContract abi 24) :=
  keyGen_wipe Proof.MlKem.Arm.KeyGen.verified keyGen_stack keyGen_sat

theorem keyGen_verified : Verified target Impl.MlKem.Arm.Wipe.keyGen (Spec.MlKem.keyGenContract abi 24) :=
  keyGen_scrubbed

theorem encapsH_scrubbed : Verified target Impl.MlKem.Arm.Wipe.encapsH (Scrubbed.encapsHContract abi 32) :=
  encapsH_wipe Proof.MlKem.Arm.Encaps.verifiedH encapsH_stack encapsH_sat

theorem encapsH_verified : Verified target Impl.MlKem.Arm.Wipe.encapsH (Spec.MlKem.encapsHContract abi 32) :=
  encapsH_scrubbed

theorem encaps_scrubbed : Verified target Impl.MlKem.Arm.Wipe.encaps (Scrubbed.encapsContract abi 32) :=
  encaps_wipe Proof.MlKem.Arm.Encaps.verified encaps_stack encaps_sat

theorem encaps_verified : Verified target Impl.MlKem.Arm.Wipe.encaps (Spec.MlKem.encapsContract abi 32) :=
  encaps_scrubbed

theorem decaps_scrubbed : Verified target Impl.MlKem.Arm.Wipe.decaps (Scrubbed.decapsContract abi 24) :=
  decaps_wipe Proof.MlKem.Arm.Decaps.verified decaps_stack decaps_sat

theorem decaps_verified : Verified target Impl.MlKem.Arm.Wipe.decaps (Spec.MlKem.decapsContract abi 24) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 24) :=
  keyGen1024_wipe Proof.MlKem1024.Arm.KeyGen.verified keyGen1024_stack keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 24) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 32) :=
  encapsH1024_wipe Proof.MlKem1024.Arm.Encaps.verifiedH encapsH1024_stack encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 32) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 32) :=
  encaps1024_wipe Proof.MlKem1024.Arm.Encaps.verified encaps1024_stack encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 32) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.Arm.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 24) :=
  decaps1024_wipe Proof.MlKem1024.Arm.Decaps.verified decaps1024_stack decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.Arm.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 24) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.Arm.Wipe
