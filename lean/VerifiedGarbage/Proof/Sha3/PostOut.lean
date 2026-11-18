module

public import VerifiedGarbage.Spec.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SHA-3's postconditions read the memory on return only within the buffers

The postcondition of `vg_<instance>_update` reads the memory on return only
through `stateAt` of the state, its 200 bytes (`updatePostOut_local`); those of
`update`, `finalize`, SHAKE's `finalize` and `squeeze` read only their buffers
(`PostOut.updatePost_out`, `finalizePost_out`, `xofFinalizePost_out`,
`xofSqueezePost_out`): what a scrub tail needs of them, which changes the
memory only outside the buffers (`X86_64.Scrub.PostOut`,
`RISCV64.Scrub.PostOut`, `PPC64LE.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Instances

open VG.Spec.Sha3

/-- `updatePost` reads the memory on return only within the state. -/
theorem updatePostOut_local (rate pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  refine ⟨fun msg hr hc => ?_, h.2⟩
  show stateAt m₂ st = _
  rw [stateAt_agree hb.1]
  exact h.1 msg hr hc

end VG.Proof.Sha3.Instances

namespace VG.Proof.Sha3.PostOut

open VG.Spec.Sha3

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem stateAgree {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 25 * Elem.size .u64⟩ a 1 → m₁ a = m₂ a) :
    stateAt m₂ p = stateAt m₁ p :=
  Proof.Sha3.stateAt_congr fun i hi =>
    agreeBuf (n := 25 * Elem.size .u64) (by decide) h i (by simp only [Elem.size]; omega_using [hi])

theorem updatePost_out (rate pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost rate pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  refine ⟨fun msg hr hc => ?_, h.2⟩
  show stateAt m₂ st = _
  rw [stateAgree hb.1]
  exact h.1 msg hr hc

/-- A fixed digest's postcondition reads only its output buffer. -/
theorem finalizePost_out (H : HashFn) (pb : Nat) (hlen : H.len < 2 ^ 64) :
    ∀ vs m m₁ m₂ r, vs.length = ((finalizeSig H.len).words pb).length →
    (∀ b ∈ Sig.bufs (finalizeSig H.len).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((finalizeSig H.len).words pb) (finalizePost H pb) vs m m₁ r →
      Curry.apply ((finalizeSig H.len).words pb) (finalizePost H pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hvs hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hvs
  replace hvs := Nat.succ.inj hvs
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hvs
  replace hvs := Nat.succ.inj hvs
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hvs
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hvs)
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hb
  intro msg hr hc
  show bytesAt m₂ ot H.len = _
  rw [bytesAt_congr fun i hi => agreeBuf (n := H.len * Elem.size .u8)
    (by simpa only [Elem.size, Nat.mul_one] using hlen) hb.2 i
    (by simpa only [Elem.size, Nat.mul_one] using hi)]
  exact h msg hr hc

theorem xofFinalizePost_out (X : Xof) (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (xofFinalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs xofFinalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofFinalizeSig.words pb) (xofFinalizePost X pb) vs m m₁ r →
      Curry.apply (xofFinalizeSig.words pb) (xofFinalizePost X pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [xofFinalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
  intro msg hr hc d
  show squeezeFrom X.rate (stateAt m₂ st) 0 d = _
  rw [stateAgree hb]
  exact h msg hr hc d

/-- On a target with 64-bit pointers, whose `outlen` is the whole word. -/
theorem xofSqueezePost_out (X : Xof) : ∀ vs m m₁ m₂ r, vs.length = (xofSqueezeSig.words 64).length →
    (∀ b ∈ Sig.bufs xofSqueezeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (xofSqueezeSig.words 64) (xofSqueezePost X 64) vs m m₁ r →
      Curry.apply (xofSqueezeSig.words 64) (xofSqueezePost X 64) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [xofSqueezeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hb
  refine ⟨fun msg n hx => ?_, h.2⟩
  obtain ⟨h1, h2⟩ := h.1 msg n hx
  refine ⟨?_, fun d => ?_⟩
  · show bytesAt m₂ ot ol.toNat = _
    rw [bytesAt_congr fun i hi => agreeBuf (n := ol.toNat * Elem.size .u8)
      (by simp only [Elem.size]; have := ol.isLt; omega_using []) hb.2 i
      (by simp only [Elem.size]; omega_using [hi])]
    exact h1
  · show squeezeFrom X.rate (stateAt m₂ st) _ d = _
    rw [stateAgree hb.1]
    exact h2 d

end VG.Proof.Sha3.PostOut
