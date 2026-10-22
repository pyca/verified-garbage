module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the first 256 bytes

From 512 bytes, `Short.lean`'s pass of five blocks computes the one-time key
with the keystream of the first 256 bytes, which `ShortRest.first` XORs in
(`ShortRest.lean`'s proofs); `absorbFirst` absorbs them (`absorbFirst_ok`), and
`skipFirst` points `x22` and `x23` at the data after them (`skipFirst_ok`),
from where `cryptStitched` continues (`Entry`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_subImm wp_mov wp_movz)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

/-- The data's first 256 bytes absorbed. -/
theorem absorbFirst_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (hL : 256 ≤ L s₀) :
    WP isa absorbFirst s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) 256) := by
  unfold absorbFirst
  have core : WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 .x22, .movz .x .x2 16 0]) s fun s₁ =>
      s₁.gpr .x0 = off (cx s₀) 448 ∧ s₁.gpr .x1 = dp s₀ ∧ s₁.gpr .x2 = BitVec.ofNat 64 16 ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x21],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x22],
        by rw [u₃.gpr]; rfl, by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
        by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.seq ((WP.kept core (by simp [mov, clobbers, dstOf, preserved])).mono
    fun s₁ ⟨⟨h0, h1, h2, m₁, rd₁, wr₁⟩, g₁, sp₁⟩ => ?_)
  have k₁ : Kept [] s s₁ := Kept.of g₁ sp₁ rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  have hs := srcD hp
  have hsub : Region.Sub ⟨dp s₀, 16 * 16⟩ ⟨dp s₀, L s₀⟩ := Region.sub_prefix hL
  refine blocks_call (P := off (cx s₀) 448) (p := dp s₀) (n := 16) h0 h1 h2 (by decide)
    ((hs.ctx.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hsub)
    (by have := hs.wrap; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [rd₁, wr₁, h.rd, h.wr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · exact covers1 hp (by rw [wr₁, h.wr]) (a := 448) (n := 128) (by lit_omega) a w
          ⟨_, List.mem_singleton_self _, hc⟩ |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (covers1 hp (by rw [wr₁, h.wr]) (a := 448) (n := 128) (by lit_omega))
    fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ :=
    (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂)
  exact ⟨mac_inv h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- `x22` and `x23` past the first 256 bytes: `Inv` without them. -/
theorem skipFirst_ok {s₀ : State} {s : State} (h : Inv s₀ s) (hL : 256 ≤ L s₀) :
    WP isa (.block skipFirst) s fun s' => Inv0 s₀ s' ∧
      s'.gpr .x22 = dp s₀ + BitVec.ofNat 64 256 ∧ s'.gpr .x23 = BitVec.ofNat 64 (L s₀ - 256) ∧
      s'.mem = s.mem ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have core : WP isa (.block skipFirst) s fun s' =>
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 256 ∧ s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_subImm (by decide) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  refine (WP.preservedV (WP.withSp core) (by lit_decide)).mono
    fun s' ⟨⟨⟨x22, x23, g, m, rd, wr⟩, sp⟩, hv⟩ => ⟨?_, by rw [x22, h.x22], ?_, m, hv⟩
  · have hu : ∀ r ∈ untouched, r ≠ .x22 ∧ r ≠ .x23 := by decide
    exact ⟨by rw [g _ (by decide) (by decide), h.x21],
      fun r hr => by rw [g r (hu r hr).1 (hu r hr).2, h.un r hr], by rw [sp, h.sp], by rw [rd, h.rd],
      by rw [wr, h.wr], by rw [m]; exact h.saved, by rw [m]; exact h.frame⟩
  · rw [x23, h.x23, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hL]

end VG.Proof.ChaCha20Poly1305.AArch64
