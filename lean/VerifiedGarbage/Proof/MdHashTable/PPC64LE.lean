module

public import VerifiedGarbage.Impl.MdHashTable.PPC64LE
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Taint

/-!
# The digest of a hash value on PPC64LE

`digestK H`: the contract of `digest P` (`Impl/MdHashTable/PPC64LE.lean`)
for a Merkle–Damgård hash function `H` whose code has the parameters `P`:
it writes `H.digest` of the hash value at `r3` to `r4` (`digest_correct`,
from what `ShapeD` says of `P.out`), in constant time (`digest_ct`, from
the taint analysis with `r3` and `r4` public, which each instance decides).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE VG.Impl.MdStream.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdHashTable.PPC64LE (digest)
open VG.WriteBytes (writeBytes)

variable {P : Params}

/-- The contract of `digest(value = r3, out = r4)`: the `N` bytes of the
hash value readable, the `N` bytes of `out` writable, apart; `out` then
holds the digest of the hash value. -/
def digestK (H : Md P.B P.N P.L) : Contract isa where
  pre s :=
    let value : Region := ⟨s.gpr .r3, P.N⟩
    let out : Region := ⟨s.gpr .r4, P.N⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out
  post s s' := s'.mem = writeBytes s.mem (s.gpr .r4) (H.digest (H.stateAt s.mem (s.gpr .r3)))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

variable {H : Md P.B P.N P.L}

theorem digest_wp (hs : ShapeD H P.N) {s : State} (hpre : (digestK H).pre s) :
    WP isa (digest P) s fun s' => (∀ r, r ∉ [.r8, .r9, .r10, .r11] → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .r4) (H.digest (H.stateAt s.mem (s.gpr .r3))) := by
  obtain ⟨hrd, hwr, hd⟩ := hpre
  unfold digest
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_nil ?_
  have e26 : s₄.gpr .r26 = s.gpr .r3 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
    u₁.other _ (by decide)]
  have e28 : s₄.gpr .r28 = s.gpr .r4 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]
  have rd4 : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr4 : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m4 : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine (hs.out s₄ ?_ ?_ ?_).mono fun s₅ ⟨g₅, _, _, sp₅, m₅⟩ => ?_
  · rw [e26, rd4, hrd]; exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩
  · rw [e28, wr4, hwr]; exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩
  · rw [e26, e28]; exact hd
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_nil ⟨fun r hr => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h9, h10, h11⟩ := hr
    by_cases h26 : r = .r26
    · subst h26
      rw [u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide) (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    by_cases h28 : r = .r28
    · subst h28
      rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    rw [u₇.other _ h28, u₆.other _ h26, g₅ _ h8 h11, u₄.other _ h28, u₃.other _ h26, u₂.other _ h10,
      u₁.other _ h9]
  · rw [u₇.sp, u₆.sp, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₇.mem, u₆.mem, m₅, e26, e28, m4, List.take_of_length_le (Nat.le_of_eq (H.digest_length _))]

/-- `digest P` meets `digestK H`. -/
theorem digest_correct (hs : ShapeD H P.N) (hn : (digest P).noCalls = true)
    (hl : (instrs (digest P)).all (fun i => !i.writesLr) = true) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest P) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' :=
  fun _ hpre => let ⟨t, s', he, hg, hsp, hm⟩ := digest_wp hs hpre
    ⟨t, s', he, ⟨fun r hr => hg r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> decide), hsp, Exec.lr he hn hl⟩, hm⟩

theorem digest_agree : ∀ s₁ s₂, (digestK H).pre s₁ → (digestK H).pre s₂ → (digestK H).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.r3, .r4]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

/-- `digest P` is constant time, given the taint analysis of its code. -/
theorem digest_ct {hc : VG.Taint.Hint VG.PPC64LE.Taint.T}
    (h : (VG.Taint.check taint (Taint.ofRegs [.r3, .r4]) (digest P) hc).isSome = true) :
    ConstantTime isa (digestK H).pre (digestK H).pub (digest P) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) digest_agree h

end VG.Proof.MdHashTable.PPC64LE
