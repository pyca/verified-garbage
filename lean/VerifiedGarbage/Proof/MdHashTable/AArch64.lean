module

public import VerifiedGarbage.Impl.MdHashTable.AArch64
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Block

/-!
# The digest of a hash value on AArch64

`digestK H`: the contract of `digest P` (`Impl/MdHashTable/AArch64.lean`) for
a hash function `H` whose streaming code has the parameters `P`: it writes
`H.digest` of the hash value at `x0` to `x1` (`digest_verified`, from what
`Shape` says of `P.out`), as on x86-64 (`Proof/MdHashTable/X86_64.lean`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.AArch64

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.Pbkdf2.AArch64
open VG.Impl.MdHashTable.AArch64 (digest)
open VG.Impl.Pbkdf2.AArch64 (Params)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)

variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of `digest(value = x0, out = x1)`: the `N` bytes of the
hash value readable, the `N` bytes of `out` writable, apart; `out` then holds
the digest of the hash value. -/
def digestK : Contract isa where
  pre s :=
    let value : Region := ⟨s.gpr .x0, P.N⟩
    let out : Region := ⟨s.gpr .x1, P.N⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out
  post s s' := s'.mem = WriteBytes.writeBytes s.mem (s.gpr .x1) (H.digest (H.stateAt s.mem (s.gpr .x0)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

variable {H}

theorem digest_wp (hs : Shape H) {s : State} (hpre : (digestK H).pre s) :
    WP isa (digest P) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = WriteBytes.writeBytes s.mem (s.gpr .x1) (H.digest (H.stateAt s.mem (s.gpr .x0))) := by
  obtain ⟨hrd, hwr, hvo⟩ := hpre
  unfold digest
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_mov fun t o₄ e₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x19 → r ≠ .x21 → t.gpr r = s.gpr r := fun r a b c d => by
    rw [o₄.get r (by simpa using d), o₃.get r (by simpa using c), o₂.get r (by simpa using b),
      o₁.get r (by simpa using a)]
  have h19 : t.gpr .x19 = s.gpr .x0 := by rw [o₄.get .x19, e₃, o₂.get .x0, o₁.get .x0]
  have h21 : t.gpr .x21 = s.gpr .x1 := by rw [e₄, o₃.get .x1, o₂.get .x1, o₁.get .x1]
  have h10 : t.gpr .x10 = s.gpr .x19 := by rw [o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁]
  have h11 : t.gpr .x11 = s.gpr .x21 := by rw [o₄.get .x11, o₃.get .x11, e₂, o₁.get .x21]
  have tm : t.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have trd : t.rd = s.rd := by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd]
  have twr : t.wr = s.wr := by rw [o₄.wr, o₃.wr, o₂.wr, o₁.wr]
  have tsp : t.sp = s.sp := by rw [o₄.sp, o₃.sp, o₂.sp, o₁.sp]
  have i₁ : InRegions (t.rd ++ t.wr) (t.gpr .x19) P.N := by
    rw [h19, trd, hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  have i₂ : InRegions t.wr (t.gpr .x21) P.N := by
    rw [h21, twr, hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have i₃ : Region.Disjoint ⟨t.gpr .x19, P.N⟩ ⟨t.gpr .x21, P.N⟩ := by rw [h19, h21]; exact hvo
  refine WP.mono (hs.out t i₁ i₂ i₃) fun u ⟨hg, urd, uwr, usp, hmu⟩ => ?_
  refine wp_mov fun v₁ p₁ f₁ => wp_mov fun v p₂ f₂ => WP.block_nil ⟨fun r a b c => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases r19 : r = .x19
    · subst r19; rw [p₂.get .x19, f₁, hg .x10 (by decide), h10]
    by_cases r21 : r = .x21
    · subst r21; rw [f₂, p₁.get .x11, hg .x11 (by decide), h11]
    rw [p₂.get r (by simpa using r21), p₁.get r (by simpa using r19), hg r a, g r b c r19 r21]
  · rw [p₂.sp, p₁.sp, usp, tsp]
  · rw [p₂.rd, p₁.rd, urd, trd]
  · rw [p₂.wr, p₁.wr, uwr, twr]
  · rw [p₂.mem, p₁.mem, hmu, tm, h19, h21]

/-- `digest P` meets `digestK H`. -/
theorem digest_verified (hs : Shape H) (hv : (digest P).allInstrs keepsV = true) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest P) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' :=
  fun _ hpre =>
    let ⟨t, s', he, ⟨hg, hsp, _, _, hm⟩, hvv⟩ := WP.preservedV (digest_wp hs hpre) hv
    ⟨t, s', he, ⟨fun r hr => hg r (by intro h; subst h; revert hr; decide)
      (by intro h; subst h; revert hr; decide) (by intro h; subst h; revert hr; decide), hsp, hvv⟩, hm⟩

end VG.Proof.MdHashTable.AArch64
