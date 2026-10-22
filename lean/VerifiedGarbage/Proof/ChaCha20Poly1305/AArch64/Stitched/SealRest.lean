module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `seal`'s rest

`sealRest` runs `openRest` (`openRest_ok`) on the stream's arguments the
chunks left, with `x22` and `x23` kept meanwhile in `x24` and `x25`
(`sealRest_ok`): it keeps what `Kept` keeps, but `x24` and
`x25` (`KeptS`), which `Inv0` does not need (`Inv0.stepS`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

/-- `Kept` but for `x24` and `x25`. -/
structure KeptS (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x24 → r ≠ .x25 → r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Inv0.stepS {s₀ s s' : State} {rs : List Region} (h : Inv0 s₀ s) (hk : KeptS rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 576 56).Disjoint r) : Inv0 s₀ s' where
  x21 := by rw [hk.cs _ (pres .x21) (by decide) (by decide) (pres30 .x21), h.x21]
  un r hr := by
    have hu : ∀ r ∈ untouched, r ≠ .x24 ∧ r ≠ .x25 := by decide
    rw [hk.cs _ (untouched_preserved r hr).1 (hu r hr).1 (hu r hr).2 (untouched_preserved r hr).2,
      h.un r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- `sealRest`'s first block: `x22` and `x23` kept in `x24` and `x25`, and
the stream's arguments moved into them. -/
theorem stash_ok (w : State) :
    WP isa (.block [mov .x24 .x22, mov .x25 .x23, mov .x22 .x1, mov .x23 .x2]) w fun u =>
      u.gpr .x22 = w.gpr .x1 ∧ u.gpr .x23 = w.gpr .x2 ∧ u.gpr .x24 = w.gpr .x22 ∧
      u.gpr .x25 = w.gpr .x23 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → u.gpr r = w.gpr r) ∧
      u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr ∧ u.sp = w.sp ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  refine WP.mono (WP.preservedV (WP.withSp (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ =>
    wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil
      (⟨by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 h24 h25 => by rw [u₄.other _ h23, u₃.other _ h22, u₂.other _ h25, u₁.other _ h24],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)))
    (by lit_decide)) fun u ⟨⟨⟨a, b, c, d, o, m, rd, wr⟩, sp⟩, hv⟩ => ⟨a, b, c, d, o, m, rd, wr, sp, hv⟩

/-- `sealRest`'s last block: `x22` and `x23` restored from `x24` and `x25`. -/
theorem unstash_ok (w : State) :
    WP isa (.block [mov .x22 .x24, mov .x23 .x25]) w fun u =>
      u.gpr .x22 = w.gpr .x24 ∧ u.gpr .x23 = w.gpr .x25 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = w.gpr r) ∧
      u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr ∧ u.sp = w.sp ∧
      ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  refine WP.mono (WP.preservedV (WP.withSp (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      (⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22],
        by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩ :
        _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)))
    (by lit_decide)) fun u ⟨⟨⟨a, b, o, m, rd, wr⟩, sp⟩, hv⟩ => ⟨a, b, o, m, rd, wr, sp, hv⟩

/-- `sealRest`: the data from `P` (the stream's arguments) encrypted as a
call of the stream would, but for `ctx[768, 1280)` and `x24`, `x25`. -/
theorem sealRest_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {P : Nat} (hle : P ≤ L s₀) (hlt : L s₀ - P < 512) (hP : P < L s₀ → P % 64 = 0)
    (hx21 : w.gpr .x21 = cx s₀) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 P)
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)) (hrd : w.rd = s₀.rd) (hwr : w.wr = s₀.wr)
    (hcnt : P < L s₀ →
      stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (sealRest v.callee) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      KeptS [sub s₀ 64 384, dR s₀, sub s₀ 768 512] w s' ∧
      Frame [sub s₀ 64 384, restR s₀ P, sub s₀ 768 512] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold sealRest
  refine WP.seq (WP.mono (stash_ok w) fun w₁ ⟨a22, a23, a24, a25, o₁, m₁, rd₁, wr₁, sp₁, v₁⟩ => ?_)
  refine WP.seq ((openRest_ok (s := s) v hp hle hlt hP (by rw [o₁ _ (by decide) (by decide)
      (by decide) (by decide), hx21]) (by rw [a22, hx1]) (by rw [a23, hx2]) (by rw [rd₁, hrd])
      (by rw [wr₁, hwr]) (fun h => by rw [m₁]; exact hcnt h)
      (fun k hk => by rw [m₁]; exact hdata k hk)).mono fun u ⟨vu, ku, fu, cu⟩ => ?_)
  refine WP.mono (unstash_ok u) fun s' ⟨b22, b23, o', m', rd', wr', sp', v'⟩ => ?_
  refine ⟨fun r hr => (v' r hr).trans ((vu r hr).trans (v₁ r hr)), ⟨fun r hr h24 h25 h30 => ?_,
    by rw [sp', ku.sp, sp₁], by rw [rd', ku.rd, rd₁], by rw [wr', ku.wr, wr₁], ?_⟩, ?_, by rw [m']; exact cu⟩
  · by_cases h22 : r = .x22
    · subst h22; rw [b22, ku.cs _ (pres .x24) (pres30 .x24), a24]
    by_cases h23 : r = .x23
    · subst h23; rw [b23, ku.cs _ (pres .x25) (pres30 .x25), a25]
    rw [o' _ h22 h23, ku.cs _ hr h30, o₁ _ h22 h23 h24 h25]
  · rw [m', ← m₁]; exact ku.frame
  · rw [m', ← m₁]; exact fu

end VG.Proof.ChaCha20Poly1305.AArch64
