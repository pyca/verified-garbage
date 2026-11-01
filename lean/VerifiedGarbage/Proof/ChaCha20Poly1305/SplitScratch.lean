module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

/-!
# `vg_chacha20_poly1305_seal_split` with its working space as an argument

As `seal` (`Scratch.lean`), `vg_chacha20_poly1305_seal_split` keeps its
working space in a frame of its own, around code proved with the working
space as a last argument (`sealSplitScratchContract n`). Its precondition
and postcondition read the memory only within its buffers
(`sealSplitPre_local`, `sealSplitPost_local`, `sealSplitPost_out`): the
precondition reads none, the postcondition the key, the nonce, the
additional data, `src`, the data and the tag.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec.ChaCha20Poly1305

/-- `sealSplitContract`, with `work: *mut [u64; n]` after its arguments,
whatever it holds. -/
def sealSplitScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  Sig.scratchContract A sealSplitSig "work" .u64 n (sealSplitPre A.ptrBits) (sealSplitPost A.ptrBits) true stack

variable (pb : Nat)

theorem sealSplitPre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₁ →
      Curry.apply (sealSplitSig.words pb) (sealSplitPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

theorem sealSplitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₁ m' r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
    bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := src) (agree_of hb.2.2.2.1),
    bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1)]
  exact h

theorem sealSplitPost_out : ∀ vs m m₁ m₂ r, vs.length = (sealSplitSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSplitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₁ r →
      Curry.apply (sealSplitSig.words pb) (sealSplitPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealSplitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealSplitPost pb) _ m m₂ r
  dsimp only [Curry.apply, sealSplitPost, ArgWord.ofRaw] at h ⊢
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2.2)]
  exact h

end VG.Proof.ChaCha20Poly1305
