module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Prepare
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Chunk
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ChaCha20-Poly1305 on AArch64, 64 to 256 bytes: the prologue

`Short.prologue`: the registers saved and moved, the ChaCha20 state for
counter 0 at `ctx[0, 64)`, the keystream of counters 0 to 4 at `ctx[64, 384)`
from the five-block kernel, and the Poly1305 state for the one-time key.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_mov wp_str wp_ldr)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream serialize block initState)

variable {e : Bool}

/-- The keystream byte `k` of the five blocks from counter 0. -/
abbrev ks5 (s₀ : State) (k : Nat) : Byte :=
  (serialize (block (ctr (initState (K s₀) 0 (N s₀)) (k / 64)))).getD (k % 64) 0

/-- After the first block. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  x21 : s.gpr .x21 = cx s₀
  x22 : s.gpr .x22 = dp s₀
  x23 : s.gpr .x23 = s₀.gpr .x5
  x24 : s.gpr .x24 = ad s₀
  x25 : s.gpr .x25 = s₀.gpr .x3
  x27 : s.gpr .x27 = s₀.gpr .x27
  x28 : s.gpr .x28 = s₀.gpr .x28
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  x19 : s.mem.readW (off (cx s₀) 632) 64 = s₀.gpr .x19
  x20 : s.mem.readW (off (cx s₀) 640) 64 = s₀.gpr .x20
  x26 : s.mem.readW (off (cx s₀) 648) 64 = s₀.gpr .x26
  fine : Frame [workR s₀] s₀.mem s.mem
  st : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)
  zero : ∀ k < 320, s.mem (off (cx s₀) 64 + BitVec.ofNat 64 k) = 0
  x0 : s.gpr .x0 = off (cx s₀) 0
  x1 : s.gpr .x1 = off (cx s₀) 64
  x3 : s.gpr .x3 = off (cx s₀) 384
  x20r : s.gpr .x20 = s.gpr .x3

theorem block1_eq : save ++ moves ++ initState0 ++ zero ++ enter =
    (save ++ moves) ++ (initState0 ++ (zero ++ enter)) := by
  simp only [List.append_assoc]

/-- The three stores of `enter`, then its moves. -/
theorem enter_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block enter) s fun s' =>
      s'.mem = ((s.mem.writeW (off (cx s₀) 632) (s.gpr .x19)).writeW (off (cx s₀) 640) (s.gpr .x20)).writeW
        (off (cx s₀) 648) (s.gpr .x26) ∧
      s'.gpr .x0 = off (cx s₀) 0 ∧ s'.gpr .x1 = off (cx s₀) 64 ∧ s'.gpr .x3 = off (cx s₀) 384 ∧
      s'.gpr .x20 = off (cx s₀) 384 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ a, a + 8 ≤ 760 → InRegions s.wr (off (cx s₀) a) 8 := fun a h => by
    rw [hwr]; exact hp.in_ctx h
  unfold enter
  refine wp_str (a := off (cx s₀) 632) (by decide) (by rw [hx21]) (o _ (by decide)) fun s₁ m₁ => ?_
  refine wp_str (a := off (cx s₀) 640) (by decide) (by rw [m₁.gpr, hx21]) (by rw [m₁.wr]; exact o _ (by decide))
    fun s₂ m₂ => ?_
  refine wp_str (a := off (cx s₀) 648) (by decide) (by rw [m₂.gpr, m₁.gpr, hx21])
    (by rw [m₂.wr, m₁.wr]; exact o _ (by decide)) fun s₃ m₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ => wp_addImm (by decide)
    fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have g₃ : s₃.gpr = s.gpr := by rw [m₃.gpr, m₂.gpr, m₁.gpr]
  have x21₆ : s₃.gpr .x21 = cx s₀ := by rw [g₃, hx21]
  refine ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃.mem, m₂.mem, m₁.mem, m₂.gpr, m₁.gpr], ?_, ?_,
    ?_, ?_, fun r h0 h1 h3 h20 => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, m₃.rd, m₂.rd, m₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, m₃.wr, m₂.wr, m₁.wr]⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, x21₆]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), x21₆]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), x21₆]
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), x21₆]
  · rw [u₇.other _ h20, u₆.other _ h3, u₅.other _ h1, u₄.other _ h0, g₃]

/-- `enter`'s stores, as a frame. -/
theorem enter_frame {s₀ : State} (m : Mem) (a b c : BitVec 64) :
    Frame [sub s₀ 632 24] m (((m.writeW (off (cx s₀) 632) a).writeW (off (cx s₀) 640) b).writeW
      (off (cx s₀) 648) c) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_sub s₀ (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_sub s₀ (by decide) (by decide) (by decide))

theorem block1_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ initState0 ++ zero ++ enter)) s₀ (Post1 s₀) := by
  rw [block1_eq]
  refine WP.block_append (WP.mono (WP.withSp (saveMoves_ok hp))
    fun s₁ ⟨⟨e21, e24, e25, e22, e23, e0, e1, un₁, rd₁, wr₁, f₁, sv₁⟩, sp₁⟩ => ?_)
  have hc₁ : CtxOk (cx s₀) (kp s₀) (np s₀) s₁ := by
    refine ⟨fun a w h => by rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩, fun a ha => ?_, fun a ha => ?_⟩
    · rw [rd₁, wr₁]
      exact ⟨kR s₀, by simp [hp.k_rd], Offset.contains_base _ ha (by lit_omega)⟩
    · rw [rd₁, wr₁]
      exact ⟨nR s₀, by simp [hp.n_rd], Offset.contains_base _ ha (by lit_omega)⟩
  refine WP.block_append (WP.mono (WP.withSp (initState_ok (b := 0) (j := 16) (by decide) (by decide)
    (Nat.le_refl _) e21 e0 e1 hc₁
    (hp.c_k.sub_left (sub_ctx s₀ (k := 0) (n := 64) (by lit_omega)))
    (hp.c_n.sub_left (sub_ctx s₀ (k := 0) (n := 64) (by lit_omega)))))
    fun s₂ ⟨⟨g₂, rd₂, wr₂, f₂, w₂⟩, sp₂⟩ => ?_)
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (by decide), e21]
  refine WP.block_append (WP.mono (WP.withSp (zero_ok x21₂ fun a ha => by
      rw [wr₂, wr₁]; exact hp.in_ctx (a := 64 + a) (by lit_omega)))
    fun s₃ ⟨⟨g₃, rd₃, wr₃, sp₃, _, z₃⟩, sp₃'⟩ => ?_)
  have x21₃ : s₃.gpr .x21 = cx s₀ := by rw [g₃, x21₂]
  refine WP.mono (WP.withSp (enter_ok hp x21₃ (by rw [wr₃, wr₂, wr₁])))
    fun s₄ ⟨⟨m₄, x0₄, x1₄, x3₄, x20₄, g₄, rd₄, wr₄⟩, sp₄⟩ => ?_
  have g : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x9 → s₄.gpr r = s₁.gpr r := by
    intro r h0 h1 h3 h20 h9; rw [g₄ r h0 h1 h3 h20, g₃, g₂ r h9]
  have gs : ∀ r ∈ untouched, r ≠ .x20 → s₃.gpr r = s₀.gpr r := by
    intro r hr _; rw [g₃, g₂ r (by rintro rfl; simp [untouched] at hr), un₁ r hr]
  have f₂' : Frame [sub s₀ 0 64] s₁.mem s₂.mem := f₂
  have f₃ : Frame [sub s₀ 64 320] s₂.mem s₃.mem := z₃.frame
  have f₄ : Frame [sub s₀ 632 24] s₃.mem s₄.mem := by rw [m₄]; exact enter_frame _ _ _ _
  have sub' : ∀ k n, k + n ≤ 760 → ∀ r ∈ [sub s₀ k n], ∃ r' ∈ [workR s₀], Region.Sub r r' :=
    fun k n h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by lit_omega) h⟩
  have dj : ∀ k n a w, k + n ≤ a ∨ a + w ≤ k → k + n ≤ 760 → a + w ≤ 760 →
      ∀ r ∈ [sub s₀ k n], (sub s₀ a w).Disjoint r := fun k n a w h h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by omega) h₂ h₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), e21]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), e22]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), e23]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), e24]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), e25]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), un₁ _ (by decide)]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), un₁ _ (by decide)]
  · rw [sp₄, sp₃', sp₂, sp₁]
  · rw [rd₄, rd₃, rd₂, rd₁]
  · rw [wr₄, wr₃, wr₂, wr₁]
  · exact ((sv₁.frame f₂' (dj 0 64 576 56 (by decide) (by decide) (by decide))).frame f₃
      (dj 64 320 576 56 (by decide) (by decide) (by decide))).frame f₄ (dj 632 24 576 56 (by decide) (by decide) (by decide))
  · rw [m₄, readW64_off _ _ _ (by decide) (by decide) (by decide), readW64_off _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, gs _ (by decide) (by decide)]
  · rw [m₄, readW64_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, g₃, g₂ _ (by decide),
      un₁ _ (by decide)]
  · rw [m₄, Mem.readW_writeW_self64, gs _ (by decide) (by decide)]
  · exact (f₁.sub (sub' 576 56 (by decide))).trans ((f₂'.sub (sub' 0 64 (by decide))).trans
      ((f₃.sub (sub' 64 320 (by decide))).trans (f₄.sub (sub' 632 24 (by decide)))))
  · rw [stateAt_frame f₄ (dj 632 24 0 64 (by decide) (by decide) (by decide)),
      stateAt_frame f₃ (dj 64 320 0 64 (by decide) (by decide) (by decide))]
    exact stateAt_initState hp (b := 0) f₁ w₂
  · intro k hk
    rw [f₄.bytes (R := sub s₀ 64 320) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide)) (show 320 ≤ 2 ^ 64 by decide) hk]
    rw [show (sub s₀ 64 320).base + BitVec.ofNat 64 k = off (cx s₀) (64 + k) from off_off _ _ _]
    exact z₃.byte hk
  · exact x0₄
  · exact x1₄
  · exact x3₄
  · rw [x20₄, x3₄]

open VG.Proof.ChaCha20.AArch64.Mixed5 in
/-- The kernel's precondition. -/
theorem Post1.cp {s₀ s : State} (hp : APre e s₀) (h : Post1 s₀ s) : CP s := by
  have w : ∀ a n, a + n ≤ 760 → InRegions s.wr (off (cx s₀) a) n := fun a n hn => by
    rw [h.wr]; exact hp.in_ctx hn
  refine ⟨h.x20r, fun k => ?_, ?_, fun d n hd => ?_, fun d n hd => ?_, ?_, ?_, ?_⟩
  · rw [h.x0, off_add, h.rd, h.wr]; exact hp.in_ctx' (by have := k.isLt; omega)
  · rw [h.x0, off_add]; exact w _ _ (by decide)
  · rw [h.x3, off_add]; exact w _ _ (by omega)
  · rw [h.x1, off_add]; exact w _ _ (by omega)
  · show (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 320⟩
    rw [h.x0, h.x3]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  · show (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x1, 320⟩
    rw [h.x0, h.x1]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  · show (⟨s.gpr .x1, 320⟩ : Region).Disjoint ⟨s.gpr .x3, 320⟩
    rw [h.x1, h.x3]; exact sub_disj s₀ (by decide) (by decide) (by decide)

/-- `leave`: the three registers loaded, and `vg_poly1305_init`'s arguments. -/
theorem leave_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    WP isa (.block leave) s fun s' =>
      s'.gpr .x19 = s.mem.readW (off (cx s₀) 632) 64 ∧ s'.gpr .x20 = s.mem.readW (off (cx s₀) 640) 64 ∧
      s'.gpr .x26 = s.mem.readW (off (cx s₀) 648) 64 ∧ s'.gpr .x0 = off (cx s₀) 448 ∧
      s'.gpr .x1 = off (cx s₀) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x26 → r ≠ .x0 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ a, a + 8 ≤ 760 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a ha => by
    rw [hrd, hwr]; exact hp.in_ctx' ha
  unfold leave
  refine wp_ldr (a := off (cx s₀) 632) (by decide) (by rw [hx21]) (i _ (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (a := off (cx s₀) 640) (by decide) (by rw [u₃.other _ (by decide), hx21])
    (by rw [u₃.rd, u₃.wr]; exact i _ (by decide)) fun s₄ u₄ => ?_
  refine wp_ldr (a := off (cx s₀) 648) (by decide) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), hx21])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i _ (by decide)) fun s₅ u₅ => ?_
  refine wp_addImm (by decide) fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => WP.block_nil ?_
  have x21₅ : s₅.gpr .x21 = cx s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hx21]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h19 h20 h26 h0 h1 => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem]
  · rw [u₇.other _ (by decide), u₆.gpr, x21₅]
  · rw [u₇.gpr, u₆.other _ (by decide), x21₅]
  · rw [u₇.other _ h1, u₆.other _ h0, u₅.other _ h26, u₄.other _ h20, u₃.other _ h19]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]

/-- After the kernel and `leave`. -/
structure Post2 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  ks : ∀ k < 320, s.mem (off (cx s₀) 64 + BitVec.ofNat 64 k) = ks5 s₀ k
  x0 : s.gpr .x0 = off (cx s₀) 448
  x1 : s.gpr .x1 = off (cx s₀) 64
  st0 : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)

open VG.Proof.ChaCha20.AArch64.Mixed5 in
theorem chunkLeave_ok {sve : Bool} {s₀ s : State} (hp : APre e s₀) (h : Post1 s₀ s) :
    WP isa (.seq (VG.Impl.ChaCha20.AArch64.Mixed5.chunk sve) (.block leave)) s (Post2 s₀) := by
  refine WP.seq ((chunk_ok s (h.cp hp)).mono fun s₂ c₂ => ?_)
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [c₂.cs _ (by decide) (by decide) (by decide), h.x21]
  have hf₂ : Frame [sub s₀ 0 64, sub s₀ 384 64, sub s₀ 64 320] s.mem s₂.mem := by
    have := c₂.frame; simp only [sr, lowBuf, dr, h.x0, h.x3, h.x1] at this; exact this
  have dj : ∀ a w, 448 ≤ a → a + w ≤ 760 →
      ∀ r ∈ [sub s₀ 0 64, sub s₀ 384 64, sub s₀ 64 320], (sub s₀ a w).Disjoint r := by
    intro a w ha haw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by omega) haw (by decide)
  have rd : ∀ a, 632 ≤ a → a + 8 ≤ 760 → s₂.mem.readW (off (cx s₀) a) 64 = s.mem.readW (off (cx s₀) a) 64 :=
    fun a h₁ h₂ => hf₂.readW (r := sub s₀ a 8) (Region.contains_self _ _) (dj a 8 (by omega) h₂) (by decide)
  refine WP.mono (WP.withSp (leave_ok hp x21₂ (by rw [c₂.rd, h.rd]) (by rw [c₂.wr, h.wr])))
    fun s₇ ⟨⟨x19₇, x20₇, x26₇, x0₇, x1₇, g, hm, rd₇, wr₇⟩, sp₇⟩ => ?_
  have cs : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x27, .x28], s₇.gpr r = s.gpr r := by
    intro r hr
    have hp' : r ∈ preserved := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g r (by rintro rfl; simp at hr) (by rintro rfl; simp at hr) (by rintro rfl; simp at hr)
      (by rintro rfl; simp at hr) (by rintro rfl; simp at hr),
      c₂.cs r hp' (by rintro rfl; simp at hr) (by rintro rfl; simp at hr)]
  have fr₂ : Frame [workR s₀] s.mem s₂.mem := hf₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by decide) (by decide)⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun k hk => ?_, x0₇, x1₇, ?_⟩
  · rw [cs _ (by decide), h.x21]
  · rw [cs _ (by decide), h.x22]
  · rw [cs _ (by decide), h.x23]
  · rw [cs _ (by decide), h.x24]
  · rw [cs _ (by decide), h.x25]
  · simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [x19₇, rd _ (by decide) (by decide), h.x19]
    · rw [x20₇, rd _ (by decide) (by decide), h.x20]
    · rw [x26₇, rd _ (by decide) (by decide), h.x26]
    · rw [cs _ (by decide), h.x27]
    · rw [cs _ (by decide), h.x28]
  · rw [sp₇, c₂.sp, h.sp]
  · rw [rd₇, c₂.rd, h.rd]
  · rw [wr₇, c₂.wr, h.wr]
  · rw [hm]; exact h.saved.frame hf₂ (dj 576 56 (by decide) (by decide))
  · rw [hm]; exact (h.fine.trans fr₂).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]; exact h.fine.trans fr₂
  · rw [hm]
    have hd := c₂.data k hk
    rw [h.x1] at hd
    rw [hd, h.zero k hk]
    exact BitVec.zero_xor.trans (by simp only [source, h.x0, h.st])
  · have hc := c₂.cnt
    simp only [source, c₂.x0, h.x0] at hc
    rw [hm, hc, h.st]

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  ks : ∀ k < 320, s.mem (off (cx s₀) 64 + BitVec.ofNat 64 k) = ks5 s₀ k
  st0 : stateAt s.mem (off (cx s₀) 0) = initState (K s₀) 0 (N s₀)

theorem otk_eq {s₀ : State} {m : Mem} (h : ∀ k < 320, m (off (cx s₀) 64 + BitVec.ofNat 64 k) = ks5 s₀ k) :
    bytesAt m (off (cx s₀) 64) 32 = otk s₀ := by
  apply List.ext_getElem
  · simp [bytesAt, Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block,
      VG.Proof.ChaCha20.length_serialize]
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, h i (by omega), ks5,
      show i / 64 = 0 by omega, show i % 64 = i by omega, VG.Proof.ChaCha20.ctr_zero,
      Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block, List.getElem_take]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some]

theorem prologue_ok {sve : Bool} {s₀ : State} (hp : APre e s₀) :
    WP isa (Short.prologue sve) s₀ (PostP s₀) := by
  unfold Short.prologue
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq ((chunkLeave_ok hp h₁).mono fun s₂ h₂ => ?_)
  refine init_call h₂.x0 h₂.x1 (sub_disj s₀ (a := 448) (n := 128) (b := 64) (m := 32) (by lit_omega)
      (by lit_omega) (by lit_omega))
    (covers2 hp h₂.inv.wr (a := 448) (n := 128) (b := 64) (m := 32) (by lit_omega) (by lit_omega))
    (covers1 hp h₂.inv.wr (a := 448) (n := 128) (by lit_omega)) fun s₃ k₃ repr₃ => ?_
  refine ⟨h₂.inv.step1 (k := 448) (n := 128) k₃ (by lit_omega) (by lit_omega) (by lit_omega),
    h₂.fine.trans (frame_work1 (k := 448) (n := 128) k₃ (by lit_omega) (by lit_omega)), ?_, fun k hk => ?_, ?_⟩
  · rw [← otk_eq h₂.ks]; exact repr₃
  · rw [k₃.frame.bytes (R := sub s₀ 64 320) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide)) (show 320 ≤ 2 ^ 64 by decide) hk]
    exact h₂.ks k hk
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame k₃.frame (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide))]
    exact h₂.st0

end VG.Proof.ChaCha20Poly1305.AArch64.Short
