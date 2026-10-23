module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Stash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ChaCha20-Poly1305 on AArch64, 513 to 704 bytes: the state copied

`OpenKey.copy`: the ChaCha20 state at `ctx[64, 128)` copied to
`ctx[640, 704)` a word at a time, as `ShortRest.stash` copies it.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenKey
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_ldr32 wp_str32)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

/-- One word copied. -/
theorem copyW_ok {s₀ s : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (copyW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (640 + 4 * k)) (s.mem.readW (off (cx s₀) (64 + 4 * k)) 32) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : InRegions s.wr (off (cx s₀) (640 + 4 * k)) 4 := by
    rw [hwr]; exact hp.in_ctx (by omega)
  have i : InRegions (s.rd ++ s.wr) (off (cx s₀) (64 + 4 * k)) 4 := by
    rw [hrd, hwr]; exact hp.in_ctx' (by omega)
  unfold copyW
  refine wp_ldr32 (a := off (cx s₀) (64 + 4 * k)) ⟨by omega, by omega⟩ (by rw [hx21]) i fun s₁ u₁ => ?_
  refine wp_str32 (a := off (cx s₀) (640 + 4 * k)) ⟨by omega, by omega⟩
    (by rw [u₁.other _ (by decide), hx21]) (by rw [u₁.wr]; exact o) fun s₂ g₂ =>
      WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · rw [g₂.mem, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · rw [g₂.gpr, u₁.other r hr]
  · rw [g₂.rd, u₁.rd]
  · rw [g₂.wr, u₁.wr]

/-- The first `n` words of the copy. -/
def copyN (n : Nat) : List Instr := (List.range n).flatMap copyW

theorem copyN_succ (n : Nat) : copyN (n + 1) = copyN n ++ copyW n := by
  simp only [copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- After the first `n` words. -/
structure Copied (s₀ s : State) (n : Nat) (s' : State) : Prop where
  word : ∀ j < n, s'.mem.readW (off (cx s₀) (640 + 4 * j)) 32 = s.mem.readW (off (cx s₀) (64 + 4 * j)) 32
  frame : Frame [sub s₀ 640 64] s.mem s'.mem
  gpr : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copyN_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 16, WP isa (.block (copyN n)) s (Copied s₀ s n)
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [copyN_succ]
    refine WP.block_append ((copyN_ok hp hx21 hrd hwr n (by omega)).mono fun s₁ h₁ => ?_)
    refine (copyW_ok hp (k := n) (by omega) (by rw [h₁.gpr _ (by decide), hx21])
      (by rw [h₁.rd, hrd]) (by rw [h₁.wr, hwr])).mono fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    -- The source word `n` is outside the copy written so far.
    have src : s₁.mem.readW (off (cx s₀) (64 + 4 * n)) 32 = s.mem.readW (off (cx s₀) (64 + 4 * n)) 32 := by
      refine h₁.frame.readW (r := sub s₀ (64 + 4 * n) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by omega)
    refine ⟨fun j hj => ?_, ?_, fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [rd₂, h₁.rd],
      by rw [wr₂, h₁.wr]⟩
    · rw [m₂, src]
      by_cases hjn : j = n
      · subst hjn; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
            rw [show off (cx s₀) (640 + 4 * j) = off (cx s₀) (4 * (160 + j)) by congr 1; omega,
              show off (cx s₀) (640 + 4 * n) = off (cx s₀) (4 * (160 + n)) by congr 1; omega]
            exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.word j (by omega)
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ (by
        show (sub s₀ 640 64).Contains (off (cx s₀) (640 + 4 * n)) 4
        exact Offset.contains _ (e := 640) (k := 64) (by omega) (by omega) (by omega))

theorem copy_eq : copy = copyN 16 := rfl

/-- The state copied. -/
theorem stateAt_copy {s₀ s s' : State} (h : Copied s₀ s 16 s') :
    stateAt s'.mem (off (cx s₀) 640) = stateAt s.mem (off (cx s₀) 64) := by
  apply Vector.ext
  intro j hj
  have w := h.word j hj
  simp only [stateAt, Vector.getElem_ofFn]
  rw [show off (cx s₀) 640 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (640 + 4 * j) from off_off _ _ _,
    show off (cx s₀) 64 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (64 + 4 * j) from off_off _ _ _, w]

/-- `copy`, with the registers but `x9` kept. -/
theorem copy_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : WP isa (.block copy) s (Copied s₀ s 16) := by
  rw [copy_eq]; exact copyN_ok hp hx21 hrd hwr 16 (Nat.le_refl _)

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey
