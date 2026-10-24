module

import VerifiedGarbage.Proof.Bignum.X86_64.R2Squares
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Bignum.X86_64.R2Squares
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Squares
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Squares
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! # Setup's counted squarings use only a public fixed count -/

@[expose] public section
namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def R2SqCount (p : Lay × Nat) (s : State) : Prop :=
  SqPre p.1 s ∧ word s.mem p.1.B (8 * sCnt) = BitVec.ofNat 64 p.2

theorem sqPre_counter {L : Lay} {s t : State} {v : Nat} (h : SqPre L s)
    (hm : t.mem = s.mem.writeW (off L.B (8 * sCnt)) (BitVec.ofNat 64 v))
    (hk : Keep [.rax] s t) : SqPre L t := by
  obtain ⟨hg, hw, hw', hinv, hlt⟩ := h
  obtain ⟨hgt, _, values, wordN, _⟩ := r2Counter_change hg.1 hg.2 hm hk
  refine ⟨⟨hgt, hg.2⟩, hw, hw', ?_, ?_⟩
  · rw [wordN]; exact hinv
  · rw [values aR2 (by decide), values aN (by decide)]; exact hlt

theorem r2Sq_count_post (M : Mont) {p : Lay × Nat} {s : State} (h : R2SqCount p s) :
    WP isa (M.mm aR2 aR2 aR2) s (R2SqCount p) := by
  obtain ⟨⟨hg, hw, hw', hinv, hlt⟩, count⟩ := h
  refine WP.mono (mm_mid M hg hw hw' (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hinv hlt) ?_
  intro t ⟨hgt, nEq, inv, lt, arr⟩
  exact ⟨⟨hgt, hw, hw', inv, by rw [nEq]; exact lt⟩,
    (arr.hslot (by decide)).trans count⟩

theorem rolled_sqs_ct_of (M : Mont) (n : Nat) (hn32 : n + 1 < 2 ^ 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (R2Squares.init n)) hc).isSome = true) :
    RelCT isa (Two SqPre) (R2Squares.run M.mm n) (fun _ _ => True) := by
  have pin : ∀ L s, SqPre L s → s.gpr .rdi = L.B := fun _ _ h => h.1.1.rdi
  have one : RelCT isa (Two R2SqCount) (M.mm aR2 aR2 aR2) (Two R2SqCount) :=
    two_post (two_map (fun p : Lay × Nat => p.1) (fun _ _ h => h.1)
      (sqs_ct M 0)) (fun _ _ h => r2Sq_count_post M h)
  unfold R2Squares.run
  refine RelCT.seq (two_piece (Ψ := fun L s => R2SqCount (L, n + 1) s)
    [.rdi] (fun L s t hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (pin L s hs).trans (pin L t ht).symm) ht ?_) ?_
  · intro L s h
    exact WP.mono (r2Squares_init h.1.1 h.1.2 hn32) fun t ⟨hm, hk⟩ =>
      ⟨sqPre_counter h hm hk, by rw [hm, word_writeW_self]⟩
  · have loop := two_loop (body := .seq (M.mm aR2 aR2 aR2) (.block R2Squares.next)) (cond := .ne)
      (Φ := fun (L : Lay) j s => R2SqCount (L, n + 1 - j) s)
      (Ψ := fun _ _ => True) (fun _ => n + 1) ?_ ?_
    exact loop.mono (by
      rintro s t ⟨L, hs, ht⟩
      exact ⟨L, ⟨by omega, hs⟩, ⟨by omega, ht⟩⟩) (fun _ _ _ => trivial)
    · refine RelCT.seq (two_post (Ψ := fun (p : Lay × Nat) s =>
        p.2 < n + 1 ∧ R2SqCount (p.1, n + 1 - p.2) s)
        (two_map (fun p : Lay × Nat => (p.1, n + 1 - p.2))
          (fun _ _ h => h.2) (one.mono (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_) ?_
      · intro p s ⟨hj, h⟩
        exact WP.mono (r2Sq_count_post M h) fun t ht => ⟨hj, ht⟩
      · exact two_taint [.rdi] (fun p s t hs ht r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact (pin p.1 s hs.2.1).trans (pin p.1 t ht.2.1).symm) (by taint_decide)
    · intro L j s hj h
      refine WP.seq (WP.mono (r2Sq_count_post M h) fun t ht => ?_)
      refine WP.mono (r2Squares_next ht.1.1.1 ht.1.1.2 ht.2 (by omega) (by omega))
        fun u ⟨hm, hz, hk⟩ => ?_
      have hu : R2SqCount (L, n + 1 - j - 1) u :=
        ⟨sqPre_counter ht.1 hm hk, by rw [hm, word_writeW_self]⟩
      refine ⟨?_, ?_, fun _ => True.intro⟩
      · by_cases hnext : j + 1 < n + 1
        · simp [eval, hz, hnext, show n + 1 - j - 1 ≠ 0 by omega]
        · simp [eval, hz, hnext, show n + 1 - j - 1 = 0 by omega]
      · intro _
        simpa only [Nat.sub_sub, Nat.add_comm j 1] using hu

theorem rolled_sqs_ct (M : Mont) (n : Nat) (hn : n = 1 ∨ n = 5) :
    RelCT isa (Two SqPre) (R2Squares.run M.mm n) (fun _ _ => True) := by
  rcases hn with rfl | rfl
  all_goals exact rolled_sqs_ct_of M _ (by decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
