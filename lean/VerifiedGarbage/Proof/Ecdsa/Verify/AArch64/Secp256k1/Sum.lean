import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points

/-! # General complete addition for secp256k1 verification -/

namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64

variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

abbrev sumR : List Nat := [AP, EXPP, UX, UY, UZ, RX, RY, RZ]
abbrev sumSl : List Nat := sumR ++ [T0, T1, T2, T3, T4, T5, DX, DY, DZ]

theorem sum_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (sum c) s fun s' =>
      Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c sumW) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧ (sv c base s' RZ < c.C.p ∧ sv c base s' RX < c.C.p) ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl EXPP))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hA : RcbApart (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ) :=
    rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := sumR) rfl rfl (by decide)
      (by decide)
  have hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (sumR.map c.sl)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ sumR, i ∈ sumSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  unfold sum
  have hAl : Aligned c.MP' (· ∈ sumSl.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 c i, MP'_A c,
    fun f m' h => (hc.call_p f m' h).2⟩
  have hLow : Low c.MP' (rcbW (slots c) (c.pt DX DY DZ) ++ rcbR (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ)) :=
    Low.of_call fun _ _ _ x hx => by
      rw [show rcbW (slots c) (c.pt DX DY DZ) ++ rcbR (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) =
        ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have key : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own c hc.n10 (key i hi).1 (key i hi).2
  refine WP.seq (WP.mono (rcb_ok hL hAl hpR hA (fun x hx => ?_) hLow hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_)
  · rw [show rcbW (slots c) (c.pt DX DY DZ) ++ rcbR (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) =
      ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i ∈ sumSl := by decide
    exact List.mem_map_of_mem (sub i hi)
  have hs₁ := k₁.scr hs
  have hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ rcbW (slots c) (c.pt DX DY DZ) ++
      sumR.map c.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [rcbW, Cfg.pt]
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₁ (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copySl_ok hc hs₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 82 → sv c base s' i = sv c base s i := fun O hi hij hj => VG.Proof.Ecdh.AArch64.sv_out O h7 hn hi hij hj
  have x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide) (by decide), o O₃ (by decide) (by decide) (by decide), e₂]
  have y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide) (by decide), e₃, o O₂ (by decide) (by decide) (by decide)]
  have z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide) (by decide), o O₂ (by decide) (by decide) (by decide)]
  have U₄ : Unch base (slW c sumW) s.mem s₄.mem := by
    have := (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch)))
    refine this.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rcases hw with (⟨y, hy, rfl⟩ | hw) | hw | hw | hw
    · simp only [rcbW, slots, Cfg.rcbSlots, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [MP'_n]
    all_goals (subst hw; simp [MP'_n, MP'_tmp])
  refine ⟨hs₃.of_keepRegs k₄ (by decide), by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], U₄, ?_, ?_, ?_⟩
  · have hM₁ := I₁.mod
    refine ⟨hM₁.n0, hM₁.n10, hM₁.mo, hM₁.tmp, hM₁.sep, ?_, hM₁.inv, hM₁.red, hM₁.call⟩
    rw [U₄.wordsVal (fun w hw => ?_) (by have := hM₁.mo; omega)]
    · exact hM.val
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have ne : ∀ i ∈ sumW, MP ≠ i := by decide
      exact sl_apart c (ne i hi)
  · constructor
    · rw [z₄]; exact I₁.lt _ (hD DZ (by simp))
    · rw [x₄]; exact I₁.lt _ (hD DX (by simp))
  · have vx := I₁.val _ (hD DX (by simp))
    have vy := I₁.val _ (hD DY (by simp))
    have vz := I₁.val _ (hD DZ (by simp))
    show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk vx (congrArg₂ Prod.mk vy vz)).trans t₁

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1
