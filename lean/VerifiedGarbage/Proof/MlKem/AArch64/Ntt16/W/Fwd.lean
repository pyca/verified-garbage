module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass1
public import VerifiedGarbage.Proof.Framework.Covers

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM's 16-bit NTT on AArch64, of a polynomial stored with 16 bits

`Impl.MlKem.AArch64.Ntt16.Readonly.fwdW` transforms the polynomial at `x0`,
stored with 16-bit coefficients, in place, with 512 bytes of working space
at `x1` and the table `VG_MLKEM_NTT16_ZETAS` (`fwdW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG.Impl.MlKem.AArch64.Ntt16

/-- What the transform needs: its precondition, and the table at `symbol`, readable and apart
from the polynomial and the working space. -/
structure Input (s : State) (symbol : String) (H : List Nat) : Prop extends W.Pre s where
  table : ∀ j < 64, s.mem.readW (s.syms symbol + BitVec.ofNat 64 (8 * j)) 64 = hw4 H j
  readable : Covers [⟨s.syms symbol, 512⟩] (s.rd ++ s.wr)
  apartOutput : (fR s).Disjoint ⟨s.syms symbol, 512⟩
  apartScratch : (sR s).Disjoint ⟨s.syms symbol, 512⟩

theorem Input.read {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {o : Nat} (ho : o + 16 ≤ 512) : InRegions (s.rd ++ s.wr) (s.syms symbol + BitVec.ofNat 64 o) 16 :=
  h.readable _ _ (in_regions (List.mem_singleton_self _) (contains_off ho (by decide)))

theorem Input.table_frame {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {m : Mem} (hf : Frame [sR s] s.mem m) :
    ∀ j < 64, m.readW (s.syms symbol + BitVec.ofNat 64 (8 * j)) 64 = hw4 H j := by
  intro j hj
  rw [hf.readW (r := ⟨s.syms symbol, 512⟩) (contains_off (by omega) (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.apartScratch.symm) (by decide)]
  exact h.table j hj

theorem fwdW_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_NTT16_ZETAS" tableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwdW s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (fP s₀) (Spec.MlKem.ntt (P₀ s₀)) := by
  have hp := hi.toPre
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (consts_ok s₀) fun s₂ c₂ sy₂ => ?_
  refine WP.mono_syms (WP.keepV (Q := fun s₃ => Keep [.x2, .x3, .x5] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x2 = s₂.gpr .x0 ∧ s₃.gpr .x3 = s₂.gpr .x1 ∧ (s₃.gpr .x5).toNat = 4)
    (by decide) (wp_movS fun w₁ k₁ e₁ _ => wp_movS fun w₂ k₂ e₂ _ => wp_movz fun w₃ k₃ e₃ =>
      wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono, by rw [k₃.mem, k₂.mem, k₁.mem],
        by rw [k₃.get .x2, k₂.get .x2, e₁], by rw [k₃.get .x3, e₂, k₁.get .x1], by rw [e₃]; rfl⟩))
    fun s₃ ⟨⟨k₃, m₃, e2, e3, e5⟩, hv₃⟩ sy₃ => ?_
  have kk := c₂.keep.trans k₃
  have st₃ : St s₀ s₃ := ⟨kk.rd, kk.wr, kk.sp, kk.get .x0, kk.get .x1⟩
  have i₀ : L1 s₀ 0 s₃ := by
    refine ⟨st₃, ?_, ?_, by rw [e5], ?_, fun r _ c' hc' => absurd hc' (Nat.not_lt_zero _),
      fun k hk => by rw [hv₃]; exact c₂.z k hk, by rw [hv₃]; exact c₂.q, by rw [hv₃]; exact c₂.c10,
      by rw [hv₃]; exact c₂.c0⟩
    · rw [e2, c₂.keep.get .x0]; exact (BitVec.add_zero _).symm
    · rw [e3, c₂.keep.get .x1]; exact (BitVec.add_zero _).symm
    · rw [m₃, c₂.mem]; exact Frame.refl _ _
  refine WP.seq (WP.mono_syms (count_loop (n := 4) (by decide) (fun c s => L1 s₀ c s)
    (fun c hc w hw => p1_body hp hc hw) i₀) fun s₄ h₄ sy₄ => ?_)
  refine WP.seq ?_
  refine WP.mono (WP.keepV (Q := fun s₅ => Keep [.x2, .x6, .x4, .x5] s₄ s₅ ∧ s₅.mem = s₄.mem ∧
      s₅.gpr .x2 = s₄.gpr .x1 ∧ s₅.gpr .x6 = s₄.syms "VG_MLKEM_NTT16_ZETAS" ∧
      s₅.gpr .x4 = s₄.gpr .x0 ∧ (s₅.gpr .x5).toNat = 8)
    (by decide) (wp_movS fun w₁ k₁ e₁ sy₁ => wp_x (by rfl) fun w₂ k₂ e₂ =>
      wp_movS fun w₃ k₃ e₃ _ => wp_movz fun w₄ k₄ e₄ =>
      wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
        by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
        by rw [k₄.get .x2, k₃.get .x2, k₂.get .x2, e₁],
        by rw [k₄.get .x6, k₃.get .x6, e₂, sy₁],
        by rw [k₄.get .x4, e₃, k₂.get .x0, k₁.get .x0], by rw [e₄]; rfl⟩))
    fun s₅ ⟨⟨k₅, m₅, e2', e6', e4', e5'⟩, hv₅⟩ => ?_
  have j₀ : L2 s₀ s₄.mem 0 s₅ (s₀.syms "VG_MLKEM_NTT16_ZETAS") := by
    refine ⟨h₄.st.keep k₅, ?_, ?_, ?_, by rw [e5'], by rw [m₅]; exact Frame.refl _ _,
      (fun o ho => hi.read ho), hi.apartOutput, hi.table_frame h₄.frame,
      fun r hr c' hc' => h₄.scr r hr c' hc', ?_, by rw [hv₅]; exact h₄.q, by rw [hv₅]; exact h₄.c10⟩
    · rw [e2', h₄.st.x1]; exact (BitVec.add_zero _).symm
    · rw [e6', sy₄, sy₃, sy₂]; exact (BitVec.add_zero _).symm
    · rw [e4', h₄.st.x0]; exact (BitVec.add_zero _).symm
    · rw [m₅]; exact BytesUpTo.zero _
  refine WP.mono (count_loop (n := 8) (by decide) (fun b s => L2 s₀ s₄.mem b s (s₀.syms "VG_MLKEM_NTT16_ZETAS"))
    (fun b hb w hw => p2_body hp hb hw) j₀) fun s' h' => ⟨h'.st.sp, ?_⟩
  rw [ntt_eq_nttL]
  exact polyIsW16_of_bytes' h'.out

end VG.Proof.MlKem.AArch64.Ntt16.W
