module
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step

import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Setup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit

/-!
# X25519 on x86-64 with AVX512_IFMA: the ladder

`vladder`: `vsetup`, then the loop and `vfinish`, leaves
the ladder's final `(x₂, z₂, x₃, z₃)` in the slots `x2, z2, x3, z3`, and its
`swap` at `SWAP`, as `vg_x25519`'s ladder does (`LPost`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E fe clob contains_sc ea_sc
  writeW_outside LPost)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The loop -/

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem vloop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} {x1 : Nat → Nat}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 255 → VInv base k u x1 s₀ s n →
      WP isa (.loop (.block vstep) .ne) s fun s' => VInv base k u x1 s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block vstep) (c := .ne)
    (Q := fun s' => VInv base k u x1 s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 255 ∧ VInv base k u x1 s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (vstep_ok (by omega_arith) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, hi'⟩

/-! ## The ladder -/

theorem movRbx_wp (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 255)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl, rfl, rfl⟩

theorem fe5_one' : fe5 (fun i => if i = 0 then 1 else 0) = 1 := fe5_one
theorem fe5_zero : fe5 (fun _ => 0) = 0 := rfl

/-- The ladder: from the words of `x₁` at `X1` and `swap = 0`, the ladder's
final state. -/
theorem vladder_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} (hs : Scr s₀ base)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hx1 : E s₀.mem base 2 = u) (hsw : word s₀.mem base SWAP = 0) :
    WP isa vladder s₀ (LPost base k u s₀) := by
  refine WP.seq (WP.mono (vsetup_wp hs) fun s₁ ⟨g₁, rd₁, wr₁, mx₁, o₁, hk₁, l₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (movRbx_wp s₁) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄, x₄, y₄⟩ => ?_)
  have hs₄ : Scr s₄ base := ⟨by rw [g₄ _ (by decide)]; exact hs₁.rdi, by rw [wr₄]; exact hs₁.wr, hs.nowrap⟩
  -- memory up to the loop
  have O₄ : Outside base 64 2152 s₀.mem s₄.mem := by rw [m₄]; exact o₁.mono (by decide) (by decide)
  have hk₄ : Consts s₄.mem base (xl s₀.mem base) := by rw [m₄]; exact hk₁
  have lan₄ : ∀ l < 4, ∀ i < 5, lanes s₄ 0 l i =
      if l = 2 then xl s₀.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0 := fun l hl i hi => by
    rw [lanes_of_vec x₄ y₄, l₁ l hl i hi]
  have bits₄ : ∀ t < 255, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t) := fun t ht => by
    have ho : ofs base (off base (BITS + t)) = BITS + t :=
      VG.Proof.X25519.X86_64.ofs_off' base (by simp only [BITS]; omega_arith)
    rw [m₄, o₁ _ (by rw [ho]; simp only [BITS]; omega_arith)]
    exact hbits t ht
  have fx1 : fe5 (xl s₀.mem base) = u := by
    rw [← hx1]
    show toFe _ = toFe _
    congr 1
    rw [xl, limbNat_lv _ (fun k _ => BitVec.isLt _)]
    rfl
  have I : VInv base k u (xl s₀.mem base) s₄ s₄ 255 := by
    refine ⟨hs₄, fun _ _ => rfl, b₄, rfl, rfl, VFrame.refl _ _, hk₄, fx1, ?_, fun l hl i hi => ?_, ?_, ?_, ?_, ?_⟩
    · show word s₄.mem base SWAP = BitVec.ofNat 64 0
      rw [m₄, o₁.word (by simp only [SWAP]; omega_arith) (by simp only [SWAP]; omega_arith), hsw]; rfl
    · rw [lan₄ l hl i hi]; have := hk₄.x1 i hi; split <;> [omega_arith; split <;> omega_arith]
    · rw [fe5_congr (fun i hi => lan₄ 0 (by decide) i hi)]; exact fe5_one'
    · rw [fe5_congr (fun i hi => lan₄ 1 (by decide) i hi)]; simp only [Nat.one_ne_zero, false_or,
        show (1 : Nat) ≠ 3 by decide, and_false, ite_false]; exact fe5_zero
    · rw [fe5_congr (fun i hi => lan₄ 2 (by decide) i hi)]; simp only [ite_true]; exact fx1
    · rw [fe5_congr (fun i hi => lan₄ 3 (by decide) i hi)]
      simp only [show (3 : Nat) ≠ 2 by decide, ite_false, or_true, and_true]; exact fe5_one'
  refine WP.seq (WP.mono (vloop_ok bits₄ 255 s₄ (by decide) (by decide) I) fun s₅ V => ?_)
  refine WP.mono (vfinish_wp V.scr V.consts V.lim) fun s₆ ⟨g₆, rd₆, wr₆, _, o₆, f₆⟩ => ?_
  have hs₆ : Scr s₆ base := ⟨by rw [g₆]; exact V.scr.rdi, by rw [wr₆]; exact V.scr.wr, hs.nowrap⟩
  have fe6 : ∀ m (hm : m < 4), E s₆.mem base ⟨3 + m, by omega_arith⟩ = fe5 (lanes s₅ 0 m) := fun m hm => by
    show toFe (fe s₆.mem base (32 * (3 + m))) = _
    have := f₆ m hm
    simp only [X2] at this
    rw [show 32 * (3 + m) = 96 + 32 * m by omega_arith]
    exact this
  refine LPost.of hs₆ (fun r hr hb => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h1 : r ∉ cregs := fun h => hr (by simp only [cregs, clob, List.mem_cons] at h ⊢; grind)
    have h4 : r ∉ [Reg.rax, .rbx, .rcx, .rdx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      rcases h with h | h | h | h <;> subst h
      · exact hr (by decide)
      · exact hb rfl
      · exact hr (by decide)
      · exact hr (by decide)
    rw [g₆, V.gpr r h4, g₄ r hb, g₁ r h1]
  · rw [rd₆, V.rd, rd₄, rd₁]
  · rw [wr₆, V.wr, wr₄, wr₁]
  · have F₅ : Outside base 64 2152 s₄.mem s₅.mem := fun x hx => V.mem x (by omega_arith)
    exact (O₄.trans F₅).trans (o₆.mono (by decide) (by decide))
  · exact (fe6 0 (by decide)).trans V.x2
  · exact (fe6 1 (by decide)).trans V.z2
  · exact (fe6 2 (by decide)).trans V.x3
  · exact (fe6 3 (by decide)).trans V.z3
  · rw [o₆.word (by simp only [SWAP]; omega_arith) (by simp only [SWAP]; omega_arith)]
    exact V.swap

end VG.Proof.X25519.X86_64.Ifma
