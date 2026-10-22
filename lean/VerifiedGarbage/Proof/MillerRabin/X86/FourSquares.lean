module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareFour

/-! # The fixed four squarings at the start of an exponent window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem four_squares {σ s : State} {base : Addr} {bytes w : Nat} {F : Bool}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (flag : w32 s.mem base sF = F.toNat)
    (reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)) :
    WP isa (.seq (.block sqFour) sqLoop) s fun t =>
      Stage base bytes w σ t ∧
      numAt t.mem base w 6 = (squareRun σ s base w 4 0 F 4).1 ∧
      w32 t.mem base sF = (squareRun σ s base w 4 0 F 4).2.toNat ∧
      numAt t.mem base w 6 < val32 σ.mem base 256 (2 * w) ∧
      (∀ a, 5 ≤ a → a < 28 → a ≠ 6 → numAt t.mem base w a = numAt s.mem base w a) ∧
      (∀ d, d = sV ∨ d = sK → t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32) := by
  refine WP.seq (WP.mono (square_four_init h facts.fit) ?_)
  rintro u ⟨hu, threshold, count, frame⟩
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have bounds : ∀ d ∈ [sR, sQ], d + 4 ≤ bytes := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact Nat.le_trans (by decide) hdrFit
  have sameHeader (d : Nat) (hd : d + 4 ≤ bytes)
      (sep : ∀ k ∈ [sR, sQ], d + 4 ≤ k ∨ k + 4 ≤ d) :
      u.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    headers_frame_word h.context.ws.nowrap hd bounds sep frame
  have sameArray (a : Nat) (ha : a < 28) : numAt u.mem base w a = numAt s.mem base w a :=
    headers_frame_num h.context.ws.nowrap facts.fit ha
      (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl <;> decide) frame
  have flagU : w32 u.mem base sF = F.toNat :=
    (congrArg BitVec.toNat (sameHeader sF (Nat.le_trans (by decide) hdrFit)
      (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl <;> decide))).trans flag
  refine WP.mono (square_loop facts hu (q0 := 4) (r := 0) (F := F) (by decide) (by decide) count
    (readW_of_w32 (by decide) threshold) flagU (by rw [sameArray 6 (by decide)]; exact reduced)) ?_
  intro t result
  have runEq : squareRun σ u base w 4 0 F 4 = squareRun σ s base w 4 0 F 4 := by
    unfold squareRun
    rw [sameArray 8 (by decide), sameArray 6 (by decide)]
  refine ⟨result.stage, result.value.trans (congrArg Prod.fst runEq),
    result.flag.trans (congrArg (fun p : Nat × Bool => p.2.toNat) runEq), result.reduced, ?_, ?_⟩
  · intro a lo hi ne6
    exact (square_frame_num hu.context hu.room facts.fit ⟨lo, hi⟩ ne6 result.frame).trans (sameArray a hi)
  · intro d hd
    have small : d + 4 ≤ 256 := by rcases hd with rfl | rfl <;> decide
    have sqSep : ∀ k ∈ [sE2, sF, sQ], d + 4 ≤ k ∨ k + 4 ≤ d := by
      intro k hk
      rcases hd with rfl | rfl
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
    have initSep : ∀ k ∈ [sR, sQ], d + 4 ≤ k ∨ k + 4 ≤ d := by
      intro k hk
      rcases hd with rfl | rfl
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> decide
    exact (square_frame_header hu.context hu.room facts.fit small sqSep result.frame).trans
      (sameHeader d (Nat.le_trans small hdrFit) initSep)

end VG.Proof.MillerRabin.X86
