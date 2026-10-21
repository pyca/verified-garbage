module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.ShortRest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ChaCha20-Poly1305 on AArch64, 257 to 511 bytes: the state copied

`ShortRest.stash`: the ChaCha20 state at `ctx[0, 64)` copied to
`ctx[64, 128)` a word at a time, with its counter (word 12) set to 5.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.ShortRest

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.ShortRest
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_ldr32 wp_str32)
open VG.Spec.ChaCha20 (stateAt initState)

variable {e : Bool}

/-- The word `stashW k` stores: 5 for the counter, else the source's word. -/
abbrev stashVal (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k = 12 then 5 else m.readW (off c (4 * k)) 32

theorem five32 : ((((5 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 5 := rfl

/-- One word copied. -/
theorem stashW_ok {s₀ s : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (stashW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (64 + 4 * k)) (stashVal s.mem (cx s₀) k) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : InRegions s.wr (off (cx s₀) (64 + 4 * k)) 4 := by
    rw [hwr]; exact hp.in_ctx (by omega)
  unfold stashW stashVal
  split
  · next h12 =>
    subst h12
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) (64 + 4 * 12)) (by decide) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
    · rw [g₂.mem, u₁.gpr, u₁.mem, five32]
    · rw [g₂.gpr, u₁.other r hr]
    · rw [g₂.rd, u₁.rd]
    · rw [g₂.wr, u₁.wr]
  · next h12 =>
    have i : InRegions (s.rd ++ s.wr) (off (cx s₀) (4 * k)) 4 := by
      rw [hrd, hwr]; exact hp.in_ctx' (by omega)
    refine wp_ldr32 (a := off (cx s₀) (4 * k)) ⟨by omega, by omega⟩ (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) (64 + 4 * k)) ⟨by omega, by omega⟩
      (by rw [u₁.other _ (by decide), hx21]) (by rw [u₁.wr]; exact o) fun s₂ g₂ =>
        WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
    · rw [g₂.mem, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · rw [g₂.gpr, u₁.other r hr]
    · rw [g₂.rd, u₁.rd]
    · rw [g₂.wr, u₁.wr]

/-- The first `n` words of the copy. -/
def stashN (n : Nat) : List Instr := (List.range n).flatMap stashW

theorem stashN_succ (n : Nat) : stashN (n + 1) = stashN n ++ stashW n := by
  simp only [stashN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Words `j` and `k` of `ctx`, for `j ≠ k < 32`, do not overlap. -/
theorem word_sep (c : Addr) {j k : Nat} (hj : j < 32) (hk : k < 32) (h : j ≠ k) :
    Mem.Sep (off c (4 * j)) 4 (off c (4 * k)) 4 := Offset.sep c (by omega) (by omega) (by omega)

/-- After the first `n` words. -/
structure Copied (s₀ s : State) (n : Nat) (s' : State) : Prop where
  word : ∀ j < n, s'.mem.readW (off (cx s₀) (64 + 4 * j)) 32 = stashVal s.mem (cx s₀) j
  frame : Frame [sub s₀ 64 64] s.mem s'.mem
  gpr : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stashN_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 16, WP isa (.block (stashN n)) s (Copied s₀ s n)
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [stashN_succ]
    refine WP.block_append ((stashN_ok hp hx21 hrd hwr n (by omega)).mono fun s₁ h₁ => ?_)
    refine (stashW_ok hp (k := n) (by omega) (by rw [h₁.gpr _ (by decide), hx21])
      (by rw [h₁.rd, hrd]) (by rw [h₁.wr, hwr])).mono fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    -- The source word `n` is outside the copy written so far.
    have src : stashVal s₁.mem (cx s₀) n = stashVal s.mem (cx s₀) n := by
      unfold stashVal
      split
      · rfl
      · refine h₁.frame.readW (r := sub s₀ (4 * n) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by omega) (by omega) (by omega)
    refine ⟨fun j hj => ?_, ?_, fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [rd₂, h₁.rd],
      by rw [wr₂, h₁.wr]⟩
    · rw [m₂, src]
      by_cases hjn : j = n
      · subst hjn; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
            rw [show off (cx s₀) (64 + 4 * j) = off (cx s₀) (4 * (16 + j)) by congr 1; omega,
              show off (cx s₀) (64 + 4 * n) = off (cx s₀) (4 * (16 + n)) by congr 1; omega]
            exact word_sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.word j (by omega)
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ (by
        show (sub s₀ 64 64).Contains (off (cx s₀) (64 + 4 * n)) 4
        exact Offset.contains _ (e := 64) (k := 64) (by omega) (by omega) (by omega))

theorem stash_eq : stash = stashN 16 := rfl

/-- The state copied, with counter 5. -/
theorem stateAt_copy {s₀ s s' : State} (h : Copied s₀ s 16 s')
    (hst : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)) :
    stateAt s'.mem (off (cx s₀) 64) = initState (K s₀) 5 (N s₀) := by
  apply Vector.ext
  intro j hj
  have w := h.word j hj
  simp only [stateAt, Vector.getElem_ofFn] at hst ⊢
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (64 + 4 * j) from off_off _ _ _, w]
  unfold stashVal
  have hs := congrArg (·[j]) hst
  simp only [Vector.getElem_ofFn, off_off, Nat.zero_add] at hs
  split
  · next h12 => subst h12; simp [Spec.ChaCha20.initState]
  · next h12 =>
    rw [hs]
    simp only [Spec.ChaCha20.initState, Vector.getElem_ofFn]
    split <;> simp_all

end VG.Proof.ChaCha20Poly1305.AArch64.ShortRest
