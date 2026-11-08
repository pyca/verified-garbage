module

public import VerifiedGarbage.Impl.MlKem.X86.Wipe
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.MlKem.X86.KeyGen
public import VerifiedGarbage.Proof.MlKem.X86.Encaps
public import VerifiedGarbage.Proof.MlKem.X86.Decaps
public import VerifiedGarbage.Proof.MlKem1024.X86.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.X86.Encaps
public import VerifiedGarbage.Proof.MlKem1024.X86.Decaps
public import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.MlKem.EncapsHSat

/-!
# ML-KEM on x86 (32-bit): the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/X86.lean`) of its code, which gets all its
arguments on the stack, `scratch` the last: it copies them into its frame
for the call, then zeroes all of `scratch` with `vg_zeroize` once that code
returns. It is verified against the same contract (`Verified.callWipe'`) with
the frame and the return address more stack than the code's 88 bytes: 120
for key generation, encapsulation and decapsulation (a frame of 28 bytes,
padded: four or five arguments and the result), 136 for encapsulation with
`H(ek)` (44 bytes: six arguments and the result, padded); and with `scratch`
left scrubbed (`*_scrubbed`, the contracts of `Proof/MlKem/Scrubbed.lean`),
since every byte of it is zero (`Scrubbed.keyGen_wiped`, …). `*_verified`
are those weakened to the contracts of `Spec/MlKem/`, which do not state it
yet.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Wipe

open VG VG.X86 VG.Impl.CallWipe.X86

theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

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
    (h : Verified target body (Spec.MlKem.keyGenContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem.keyGenContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 32768 "vg_mlkem768_keygen" body)
      (Scrubbed.keyGenContract abi 120) := by
  have e : slots Spec.MlKem.keyGenSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.keyGenSig) (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 32768) (name := "vg_mlkem768_keygen_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem.encapsHContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem.encapsHContract abi 136).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 6 32768 "vg_mlkem768_encaps_h" body)
      (Scrubbed.encapsHContract abi 136) := by
  have e : slots Spec.MlKem.encapsHSig = 6 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.encapsHSig) (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := [])
    (i := 5) (j := 5) (n := 32768) (name := "vg_mlkem768_encaps_h_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 6 + 4 = 136 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])
  rw [e, show 88 + frameSize 6 + 4 = 136 by decide] at h'
  exact h'

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem.encapsContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem.encapsContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 5 32768 "vg_mlkem768_encaps" body)
      (Scrubbed.encapsContract abi 120) := by
  have e : slots Spec.MlKem.encapsSig = 5 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.encapsSig) (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := [])
    (i := 4) (j := 4) (n := 32768) (name := "vg_mlkem768_encaps_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 5 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])
  rw [e, show 88 + frameSize 5 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem.decapsContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem.decapsContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 32768 "vg_mlkem768_decaps" body)
      (Scrubbed.decapsContract abi 120) := by
  have e : slots Spec.MlKem.decapsSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.decapsSig) (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 32768) (name := "vg_mlkem768_decaps_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem1024.keyGenContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem1024.keyGenContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 49152 "vg_mlkem1024_keygen" body)
      (Scrubbed.keyGen1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.keyGenSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.keyGenSig) (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 49152) (name := "vg_mlkem1024_keygen_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem1024.encapsHContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem1024.encapsHContract abi 136).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 6 49152 "vg_mlkem1024_encaps_h" body)
      (Scrubbed.encapsH1024Contract abi 136) := by
  have e : slots Spec.MlKem1024.encapsHSig = 6 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.encapsHSig) (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := [])
    (i := 5) (j := 5) (n := 49152) (name := "vg_mlkem1024_encaps_h_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 6 + 4 = 136 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])
  rw [e, show 88 + frameSize 6 + 4 = 136 by decide] at h'
  exact h'

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem1024.encapsContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem1024.encapsContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 5 49152 "vg_mlkem1024_encaps" body)
      (Scrubbed.encaps1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.encapsSig = 5 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.encapsSig) (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := [])
    (i := 4) (j := 4) (n := 49152) (name := "vg_mlkem1024_encaps_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 5 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])
  rw [e, show 88 + frameSize 5 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa}
    (h : Verified target body (Spec.MlKem1024.decapsContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Spec.MlKem1024.decapsContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 49152 "vg_mlkem1024_decaps" body)
      (Scrubbed.decaps1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.decapsSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.decapsSig) (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 49152) (name := "vg_mlkem1024_decaps_body") (zname := "vg_zeroize") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
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
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-! ## The stack the functions use: at most 88 bytes -/

theorem keyGen_stack : stackUse Impl.MlKem.X86.keyGen ≤ 88 := by lit_decide
theorem encapsH_stack : stackUse Impl.MlKem.X86.encapsH ≤ 88 := by lit_decide
theorem encaps_stack : stackUse Impl.MlKem.X86.encaps ≤ 88 := by lit_decide
theorem decaps_stack : stackUse Impl.MlKem.X86.decaps ≤ 88 := by lit_decide
theorem keyGen1024_stack : stackUse Impl.MlKem1024.X86.keyGen ≤ 88 := by lit_decide
theorem encapsH1024_stack : stackUse Impl.MlKem1024.X86.encapsH ≤ 88 := by lit_decide
theorem encaps1024_stack : stackUse Impl.MlKem1024.X86.encaps ≤ 88 := by lit_decide
theorem decaps1024_stack : stackUse Impl.MlKem1024.X86.decaps ≤ 88 := by lit_decide

/-! ## The states satisfying the preconditions, with the frame's bytes of stack -/

theorem keyGen_sat : ∃ s, (Spec.MlKem.keyGenContract abi 120).pre s := by
  refine ⟨satState KeyGen.satMem [⟨0, 64⟩]
      [⟨0x100, 1184⟩, ⟨0x1000, 2400⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem encapsH_sat : ∃ s, (Spec.MlKem.encapsHContract abi 136).pre s := by
  refine ⟨Encaps.satStH, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.MlKem.encapsHContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | (rw [Encaps.satStH_ek, Encaps.satStH_h]
         exact VG.Proof.MlKem.hMem_h_of (by decide) Encaps.satMemH_low)

theorem encaps_sat : ∃ s, (Spec.MlKem.encapsContract abi 120).pre s := by
  refine ⟨satState Encaps.satMem [⟨0, 1184⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1088⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 20⟩], ?_⟩
  sig_sat_check [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem decaps_sat : ∃ s, (Spec.MlKem.decapsContract abi 120).pre s := by
  refine ⟨satState Decaps.satMem [⟨0, 2400⟩, ⟨0x1000, 1088⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem keyGen1024_sat : ∃ s, (Spec.MlKem1024.keyGenContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.KeyGen.satMem [⟨0, 64⟩]
      [⟨0x100, 1568⟩, ⟨0x1000, 3168⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem encapsH1024_sat : ∃ s, (Spec.MlKem1024.encapsHContract abi 136).pre s := by
  refine ⟨Proof.MlKem1024.X86.Encaps.satStH1024, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.MlKem1024.encapsHContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | (rw [Proof.MlKem1024.X86.Encaps.satStH1024_ek, Proof.MlKem1024.X86.Encaps.satStH1024_h]
         exact VG.Proof.MlKem.hMem_h_of (by decide) Encaps.satMemH_low)

theorem encaps1024_sat : ∃ s, (Spec.MlKem1024.encapsContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.Encaps.satMem [⟨0, 1568⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 20⟩], ?_⟩
  sig_sat_check [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem decaps1024_sat : ∃ s, (Spec.MlKem1024.decapsContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.Decaps.satMem [⟨0, 3168⟩, ⟨0x1000, 1568⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-! ## The functions -/

theorem keyGen_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.keyGen (Scrubbed.keyGenContract abi 120) :=
  keyGen_wipe Proof.MlKem.X86.KeyGen.verified (NoSp.of_all (by lit_decide)) keyGen_stack keyGen_sat

theorem keyGen_verified :
    Verified target Impl.MlKem.X86.Wipe.keyGen (Spec.MlKem.keyGenContract abi 120) :=
  Scrubbed.Verified.keyGen_of_scrubbed keyGen_scrubbed

theorem encapsH_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encapsH (Scrubbed.encapsHContract abi 136) :=
  encapsH_wipe Proof.MlKem.X86.Encaps.verifiedH (NoSp.of_all (by lit_decide)) encapsH_stack encapsH_sat

theorem encapsH_verified :
    Verified target Impl.MlKem.X86.Wipe.encapsH (Spec.MlKem.encapsHContract abi 136) :=
  Scrubbed.Verified.encapsH_of_scrubbed encapsH_scrubbed

theorem encaps_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encaps (Scrubbed.encapsContract abi 120) :=
  encaps_wipe Proof.MlKem.X86.Encaps.verified (NoSp.of_all (by lit_decide)) encaps_stack encaps_sat

theorem encaps_verified :
    Verified target Impl.MlKem.X86.Wipe.encaps (Spec.MlKem.encapsContract abi 120) :=
  Scrubbed.Verified.encaps_of_scrubbed encaps_scrubbed

theorem decaps_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.decaps (Scrubbed.decapsContract abi 120) :=
  decaps_wipe Proof.MlKem.X86.Decaps.verified (NoSp.of_all (by lit_decide)) decaps_stack decaps_sat

theorem decaps_verified :
    Verified target Impl.MlKem.X86.Wipe.decaps (Spec.MlKem.decapsContract abi 120) :=
  Scrubbed.Verified.decaps_of_scrubbed decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 120) :=
  keyGen1024_wipe Proof.MlKem1024.X86.KeyGen.verified (NoSp.of_all (by lit_decide)) keyGen1024_stack keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.X86.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 120) :=
  Scrubbed.Verified.keyGen1024_of_scrubbed keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 136) :=
  encapsH1024_wipe Proof.MlKem1024.X86.Encaps.verifiedH (NoSp.of_all (by lit_decide)) encapsH1024_stack encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.X86.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 136) :=
  Scrubbed.Verified.encapsH1024_of_scrubbed encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 120) :=
  encaps1024_wipe Proof.MlKem1024.X86.Encaps.verified (NoSp.of_all (by lit_decide)) encaps1024_stack encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.X86.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 120) :=
  Scrubbed.Verified.encaps1024_of_scrubbed encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 120) :=
  decaps1024_wipe Proof.MlKem1024.X86.Decaps.verified (NoSp.of_all (by lit_decide)) decaps1024_stack decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.X86.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 120) :=
  Scrubbed.Verified.decaps1024_of_scrubbed decaps1024_scrubbed

end VG.Proof.MlKem.X86.Wipe
