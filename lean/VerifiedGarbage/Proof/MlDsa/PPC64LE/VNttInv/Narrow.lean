module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Narrow
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Wide
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector inverse NTT on PPC64LE: the layers of `len = 1` and `len = 2`, and the product by `f`

As the forward transform's (`VNtt/Narrow.lean`): sixteen coefficients at a
time, transposed, the inverse butterflies of `len = 1` and then of `len = 2`
(`igroup_ok`); then each coefficient times `f` (`scale_ok`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt
open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add polyRegion polyIs_toNat polyIs_of_toNat bflyInv blockN
  nttInvLayer layF layF1_get layF2_get nttInvBlk_ok)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz)
open VG.Spec.MlDsa (Poly Zq zetas)

/-! ## The two layers, coefficient by coefficient -/

theorem ilayer1_get (W : Poly) {j : Nat} (hj : j < 256) :
    (nttInvLayer W 1)[j]! = if j % 2 = 0 then W[j]! + W[j + 1]!
      else zetas (255 - j / 2) * (W[j]! - W[j - 1]!) := by
  have h := layF1_get nttInvBlk_ok W (fun c => 255 - c) (b := 128) (by decide) hj
  rw [ite_eq_left (by omega)] at h
  exact h

theorem ilayer2_get (W : Poly) {j : Nat} (hj : j < 256) :
    (nttInvLayer W 2)[j]! = if j % 4 < 2 then W[j]! + W[j + 2]!
      else zetas (127 - j / 4) * (W[j]! - W[j - 2]!) := by
  have h := layF2_get nttInvBlk_ok W (fun c => 127 - c) (b := 64) (by decide) hj
  rw [ite_eq_left (by omega)] at h
  exact h

/-- The two inverse layers on block `r` of group `g`, from `W`. -/
theorem ilayers_block (W : Poly) {g r : Nat} (hg : g < 16) (hr : r < 4) :
    let b := 16 * g + 4 * r
    let L := nttInvLayer W 1
    let za := zetas (255 - 8 * g - 2 * r)
    let zb := zetas (254 - 8 * g - 2 * r)
    let z2 := zetas (127 - 4 * g - r)
    L[b]! = W[b]! + W[b + 1]! ∧ L[b + 1]! = za * (W[b + 1]! - W[b]!) ∧
    L[b + 2]! = W[b + 2]! + W[b + 3]! ∧ L[b + 3]! = zb * (W[b + 3]! - W[b + 2]!) ∧
    (nttInvLayer L 2)[b]! = L[b]! + L[b + 2]! ∧ (nttInvLayer L 2)[b + 1]! = L[b + 1]! + L[b + 3]! ∧
    (nttInvLayer L 2)[b + 2]! = z2 * (L[b + 2]! - L[b]!) ∧
    (nttInvLayer L 2)[b + 3]! = z2 * (L[b + 3]! - L[b + 1]!) := by
  intro b L za zb z2
  have hb : b + 3 < 256 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ilayer1_get W (by omega), ite_eq_left (by omega)]
  · rw [ilayer1_get W (by omega), ite_eq_right (by omega), show 255 - (b + 1) / 2 = 255 - 8 * g - 2 * r by omega,
      show b + 1 - 1 = b by omega]
  · rw [ilayer1_get W (by omega), ite_eq_left (by omega), show b + 2 + 1 = b + 3 by omega]
  · rw [ilayer1_get W (by omega), ite_eq_right (by omega), show 255 - (b + 3) / 2 = 254 - 8 * g - 2 * r by omega,
      show b + 3 - 1 = b + 2 by omega]
  · rw [ilayer2_get L (by omega), ite_eq_left (by omega)]
  · rw [ilayer2_get L (by omega), ite_eq_left (by omega), show b + 1 + 2 = b + 3 by omega]
  · rw [ilayer2_get L (by omega), ite_eq_right (by omega), show 127 - (b + 2) / 4 = 127 - 4 * g - r by omega,
      show b + 2 - 2 = b by omega]
  · rw [ilayer2_get L (by omega), ite_eq_right (by omega), show 127 - (b + 3) / 4 = 127 - 4 * g - r by omega,
      show b + 3 - 2 = b + 1 by omega]

/-! ## A group's arithmetic -/

abbrev ICEnv := CEnvK invK

/-- An inverse butterfly whose operands' lanes are known. -/
theorem ibfly_lanesV {K : Nat → Nat} {s₀ u t : State} {a b : VReg} {x y : Nat → Zq} {z : Nat → Zq}
    (hc : CEnvK K s₀ u)
    (hz : Lanes (u.vpr .v2) z) (hzp : ∀ r < 4, (vword (u.vpr .v3) r).toNat = (z r).val * 2 ^ 32 / Spec.MlDsa.q)
    (ha : Lanes (u.vpr a) x) (hb : Lanes (u.vpr b) y)
    (hta : t.vpr a = ibflyA (u.vpr a) (u.vpr b) (u.vpr .v4))
    (htb : t.vpr b = ibflyB (u.vpr a) (u.vpr b) (u.vpr .v2) (u.vpr .v3) (u.vpr .v4) (u.vpr .v5)) :
    Lanes (t.vpr a) (fun r => x r + y r) ∧ Lanes (t.vpr b) (fun r => z r * (y r - x r)) := by
  rw [hc.v5] at htb
  exact ⟨fun r hr => by rw [hta]; exact (ibfly_lanes hr (ha r hr) (hb r hr) (hz r hr) (hzp r hr) (hc.v4 r hr)).1,
    fun r hr => by rw [htb]; exact (ibfly_lanes hr (ha r hr) (hb r hr) (hz r hr) (hzp r hr) (hc.v4 r hr)).2⟩

/-- A group's code between its loads and its stores. -/
def icore : List Instr :=
  transpose ++ ((.lxvd2x .v3 .r7 .r9 :: zcalc) ++ (ibfly .v9 .v8 .v2 .v3 ++ ((.lxvd2x .v3 .r7 .r8 :: zcalc) ++
  (ibfly .v11 .v10 .v2 .v3 ++ ((.lxvd2x .v3 .r6 .r9 :: zcalc) ++
  (.addi .r6 .r6 16 :: .addi .r7 .r7 32 :: (ibfly .v9 .v11 .v2 .v3 ++ (ibfly .v8 .v10 .v2 .v3 ++ transpose))))))))

theorem iGroupBody_eq : iGroupBody = loads4 ++ (icore ++ stores4) := by
  simp only [iGroupBody, loads4, icore, stores4, List.append_assoc, List.cons_append, List.nil_append]

theorem invK_even {g e : Nat} (hg : g < 16) (he : e < 4) :
    zeta (invK (128 + 8 * g + swap1 e)) = (zetas (255 - 8 * g - 2 * e)).val := by
  rw [invK, ite_eq_right (by omega), ite_eq_right (by omega), scrK_even hg he,
    show 383 - (128 + 8 * g + 2 * e) = 255 - 8 * g - 2 * e by omega, zeta_eq]

theorem invK_odd {g e : Nat} (hg : g < 16) (he : e < 4) :
    zeta (invK (132 + 8 * g + swap1 e)) = (zetas (254 - 8 * g - 2 * e)).val := by
  rw [invK, ite_eq_right (by omega), ite_eq_right (by omega), scrK_odd hg he,
    show 383 - (128 + 8 * g + 2 * e + 1) = 254 - 8 * g - 2 * e by omega, zeta_eq]

theorem invK_two {g e : Nat} (hg : g < 16) (he : e < 4) :
    zeta (invK (64 + 4 * g + swap1 e)) = (zetas (127 - 4 * g - e)).val := by
  have := flip_lt he
  rw [invK, ite_eq_right (by omega), ite_eq_left (by omega), scrK_two hg he,
    show 191 - (64 + 4 * g + e) = 127 - 4 * g - e by omega, zeta_eq]

theorem icore_run {s₀ : State} (hp : Pre s₀) (u : State) (hc : ICEnv s₀ u) {g : Nat} (hg : g < 16)
    (h6 : u.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * g)))
    (h7 : u.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * g)))
    (h8 : u.gpr .r8 = 16#64) (h9 : u.gpr .r9 = 0#64) {W : Poly}
    (hin : ∀ r < 4, Lanes (u.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]!)) :
    WP isa (.block icore) u fun t =>
      (∀ r < 4, Lanes (t.vpr (tv r)) (fun e => (nttInvLayer (nttInvLayer W 1) 2)[16 * g + 4 * r + (e ^^^ 1)]!)) ∧
      Fr coreV [.r6, .r7] u t ∧ t.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * (g + 1))) ∧
      t.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * (g + 1))) := by
  unfold icore
  rw [WP.block_append_iff]
  refine WP.mono (transpose_run u hc.v16 hc.v17 hc.v18 hc.v19) fun u₁ ⟨l₁, vo₁, sy₁⟩ => ?_
  have f₁ : Fr coreV [.r6, .r7] u u₁ := (Fr.of_vonly vo₁ sy₁).mono (by decide) (by simp)
  have c₁ : ICEnv s₀ u₁ := hc.fr f₁ coreV_ok
  have L : ∀ k < 4, Lanes (u₁.vpr (tv k)) (fun r => W[16 * g + 4 * r + (k ^^^ 1)]!) := fun k hk r hr => by
    rw [l₁ k hk r hr]; exact hin r hr k hk
  have L9 := L 1 (by decide); have L8 := L 0 (by decide); have L11 := L 3 (by decide); have L10 := L 2 (by decide)
  simp only [tv, Nat.reduceXor, Nat.add_zero] at L9 L8 L11 L10
  -- `len = 1`, the even pairs
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₁ c₁ (a := .r7) (b := .r9) (by decide) (P := 128 + 8 * g) (by omega) (by omega)
    (by rw [vo₁.gpr, h7, h9, BitVec.add_zero]) (z := fun r => zetas (255 - 8 * g - 2 * r))
    fun e he => invK_even hg he) fun u₂ ⟨Z₂, P₂, f₂⟩ => ?_
  have c₂ : ICEnv s₀ u₂ := c₁.fr f₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ibfly_exec u₂ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))) fun u₃ ⟨a₃, b₃, vo₃, sy₃⟩ => ?_
  obtain ⟨N9, N8⟩ := ibfly_lanesV c₂ Z₂ P₂ (by rw [f₂.v _ (by decide)]; exact L9)
    (by rw [f₂.v _ (by decide)]; exact L8) a₃ b₃
  have f₃ := Fr.of_vonly vo₃ sy₃
  have c₃ : ICEnv s₀ u₃ := c₂.fr f₃ (by decide)
  have g₃ : ∀ r, u₃.gpr r = u.gpr r := fun r => by rw [f₃.g _ (by simp), f₂.g _ (by simp), vo₁.gpr]
  -- `len = 1`, the odd pairs
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₃ c₃ (a := .r7) (b := .r8) (by decide) (P := 132 + 8 * g) (by omega) (by omega)
    (by rw [g₃, g₃, h7, h8, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (128 + 8 * g) + 16 = 4 * (132 + 8 * g) by omega])
    (z := fun r => zetas (254 - 8 * g - 2 * r)) fun e he => invK_odd hg he) fun u₄ ⟨Z₄, P₄, f₄⟩ => ?_
  have c₄ : ICEnv s₀ u₄ := c₃.fr f₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ibfly_exec u₄ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))) fun u₅ ⟨a₅, b₅, vo₅, sy₅⟩ => ?_
  obtain ⟨N11, N10⟩ := ibfly_lanesV c₄ Z₄ P₄
    (by rw [f₄.v _ (by decide), f₃.v _ (by decide), f₂.v _ (by decide)]; exact L11)
    (by rw [f₄.v _ (by decide), f₃.v _ (by decide), f₂.v _ (by decide)]; exact L10) a₅ b₅
  have f₅ := Fr.of_vonly vo₅ sy₅
  have c₅ : ICEnv s₀ u₅ := c₄.fr f₅ (by decide)
  have g₅ : ∀ r, u₅.gpr r = u.gpr r := fun r => by rw [f₅.g _ (by simp), f₄.g _ (by simp), g₃]
  -- `len = 2`
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₅ c₅ (a := .r6) (b := .r9) (by decide) (P := 64 + 4 * g) (by omega) (by omega)
    (by rw [g₅, g₅, h6, h9, BitVec.add_zero]) (z := fun r => zetas (127 - 4 * g - r))
    fun e he => invK_two hg he) fun u₆ ⟨Z₆, P₆, f₆⟩ => ?_
  have c₆ : ICEnv s₀ u₆ := c₅.fr f₆ (by decide)
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, ?_⟩⟩
  generalize hu₇ : State.write (State.write u₆ _ _) _ _ = u₇
  have f₇ : Fr [] [.r6, .r7] u₆ u₇ := by
    rw [← hu₇]; exact (Fr.write _ _ _ (by decide) _).trans' (Fr.write _ _ _ (by decide) _)
  have r6₇ : u₇.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * (g + 1))) := by
    rw [← hu₇]; simp only [State.write, reduceCtorEq, ite_false, ite_true]
    rw [f₆.g _ (by simp), g₅, h6, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (64 + 4 * g) + 16 = 4 * (64 + 4 * (g + 1)) by omega]
  have r7₇ : u₇.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * (g + 1))) := by
    rw [← hu₇]; simp only [State.write, reduceCtorEq, ite_false, ite_true]
    rw [f₆.g _ (by simp), g₅, h7, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (128 + 8 * g) + 32 = 4 * (128 + 8 * (g + 1)) by omega]
  have c₇ : ICEnv s₀ u₇ := c₆.fr f₇ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (ibfly_exec u₇ (.inr (.inl ⟨rfl, rfl⟩))) fun u₈ ⟨a₈, b₈, vo₈, sy₈⟩ => ?_
  obtain ⟨M9, M11⟩ := ibfly_lanesV c₇ (by rw [f₇.v _ (by simp)]; exact Z₆)
    (by intro r hr; rw [f₇.v _ (by simp)]; exact P₆ r hr)
    (by rw [f₇.v _ (by simp), f₆.v _ (by decide), f₅.v _ (by decide), f₄.v _ (by decide)]; exact N9)
    (by rw [f₇.v _ (by simp), f₆.v _ (by decide)]; exact N11) a₈ b₈
  have f₈ := Fr.of_vonly vo₈ sy₈
  have c₈ : ICEnv s₀ u₈ := c₇.fr f₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ibfly_exec u₈ (.inr (.inr (.inl ⟨rfl, rfl⟩)))) fun u₉ ⟨a₉, b₉, vo₉, sy₉⟩ => ?_
  obtain ⟨M8, M10⟩ := ibfly_lanesV c₈ (by rw [f₈.v _ (by decide), f₇.v _ (by simp)]; exact Z₆)
    (by intro r hr; rw [f₈.v _ (by decide), f₇.v _ (by simp)]; exact P₆ r hr)
    (by rw [f₈.v _ (by decide), f₇.v _ (by simp), f₆.v _ (by decide), f₅.v _ (by decide), f₄.v _ (by decide)]
        exact N8)
    (by rw [f₈.v _ (by decide), f₇.v _ (by simp), f₆.v _ (by decide)]; exact N10) a₉ b₉
  have f₉ := Fr.of_vonly vo₉ sy₉
  have c₉ : ICEnv s₀ u₉ := c₈.fr f₉ (by decide)
  -- back
  refine WP.mono (transpose_run u₉ c₉.v16 c₉.v17 c₉.v18 c₉.v19) fun u₁₀ ⟨l₁₀, vo₁₀, sy₁₀⟩ => ?_
  have f₁₀ := Fr.of_vonly vo₁₀ sy₁₀
  have P9 := M9
  rw [← f₉.v .v9 (by decide)] at P9
  have P11 := M11
  rw [← f₉.v .v11 (by decide)] at P11
  refine ⟨fun r hr e he => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e0, e1, e2, e3, t0, t1, t2, t3⟩ := ilayers_block W hg hr
    rw [l₁₀ r hr e he]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
      simp only [tv, Nat.reduceXor]
    · rw [M8 r hr, t1, e1, e3]
    · rw [P9 r hr, Nat.add_zero, t0, e0, e2]
    · rw [M10 r hr, t3, e3, e1]
    · rw [P11 r hr, t2, e2, e0]
  · exact (((((((((f₁.trans' (f₂.mono (by decide) (by simp))).trans' (f₃.mono (by decide) (by simp))).trans'
      (f₄.mono (by decide) (by simp))).trans' (f₅.mono (by decide) (by simp))).trans' (f₆.mono (by decide) (by simp))).trans'
      (f₇.mono (by simp) (by simp))).trans' (f₈.mono (by decide) (by simp))).trans' (f₉.mono (by decide) (by simp))).trans'
      (f₁₀.mono (by decide) (by simp)))
  · rw [f₁₀.g _ (by simp), f₉.g _ (by simp), f₈.g _ (by simp), r6₇]
  · rw [f₁₀.g _ (by simp), f₉.g _ (by simp), f₈.g _ (by simp), r7₇]

/-! ## Groups -/

/-- The polynomial after `g` groups, from `W`. -/
def imix (g : Nat) (W : Poly) : Poly :=
  Vector.ofFn fun i => if i.val < 16 * g then (nttInvLayer (nttInvLayer W 1) 2)[i.val]! else W[i.val]!

theorem imix_get (g : Nat) (W : Poly) {i : Nat} (hi : i < 256) :
    (imix g W)[i]! = if i < 16 * g then (nttInvLayer (nttInvLayer W 1) 2)[i]! else W[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [imix, Vector.getElem_ofFn]

/-- After `g` groups, from `W`. -/
structure IGInv (s₀ : State) (W : Poly) (g : Nat) (s : State) : Prop where
  env : IEnv s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (16 * g)
  r9 : s.gpr .r9 = 0#64
  r8 : s.gpr .r8 = 16#64
  r11 : s.gpr .r11 = 32#64
  r12 : s.gpr .r12 = 48#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (16 - g)
  r6 : s.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * g))
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * g))
  poly : PolyIs s.mem (F s₀) (imix g W)

theorem igroup_ok {s₀ : State} (hp : Pre s₀) {W : Poly} {g : Nat} (hg : g < 16) {s : State}
    (h : IGInv s₀ W g s) :
    WP isa (.block iGroupBody) s fun s' => IGInv s₀ W (g + 1) s' ∧ (s'.gpr .r10 != 0) = decide (g + 1 ≠ 16) := by
  have ea : ∀ k, coeffAddr (F s₀) (16 * g) + BitVec.ofNat 64 (4 * k) = coeffAddr (F s₀) (16 * g + k) :=
    fun k => coeffAddr_add _ _ _
  have e16 : coeffAddr (F s₀) (16 * g) + 16#64 = coeffAddr (F s₀) (16 * g + 4) := ea 4
  have e32 : coeffAddr (F s₀) (16 * g) + 32#64 = coeffAddr (F s₀) (16 * g + 8) := ea 8
  have e48 : coeffAddr (F s₀) (16 * g) + 48#64 = coeffAddr (F s₀) (16 * g + 12) := ea 12
  rw [iGroupBody_eq, WP.block_append_iff]
  refine WP.mono (loads4_run s h.r5 h.r9 h.r8 h.r11 h.r12 (h.env.inR hp (by omega))
    (by rw [e16]; exact h.env.inR hp (by omega)) (by rw [e32]; exact h.env.inR hp (by omega))
    (by rw [e48]; exact h.env.inR hp (by omega))) fun u₁ ⟨l₁, f₁⟩ => ?_
  have c₁ : ICEnv s₀ u₁ := (CEnvK.of_env h.env).fr f₁ (by decide)
  have hin : ∀ r < 4, Lanes (u₁.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]!) := fun r hr e he => by
    have hx := xor1_lt he
    rw [l₁ r hr, show 16 * r = 4 * (4 * r) by omega, ea, vword_loadC _ _ _ he, polyIs_toNat h.poly (by show _ < 256; omega),
      imix_get _ _ (by omega), ite_eq_right (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (icore_run hp u₁ c₁ hg (by rw [f₁.g _ (by simp)]; exact h.r6) (by rw [f₁.g _ (by simp)]; exact h.r7)
    (by rw [f₁.g _ (by simp)]; exact h.r8) (by rw [f₁.g _ (by simp)]; exact h.r9) hin)
    fun u₂ ⟨l₂, f₂, r6₂, r7₂⟩ => ?_
  have g₂ : ∀ r, r ∉ [.r6, .r7] → u₂.gpr r = s.gpr r := fun r hr => by
    rw [f₂.g r hr, f₁.g r (by simp)]
  refine WP.mono (stores4_run u₂ (x := coeffAddr (F s₀) (16 * g)) (by rw [g₂ _ (by decide), h.r5])
    (by rw [g₂ _ (by decide), h.r9]) (by rw [g₂ _ (by decide), h.r8]) (by rw [g₂ _ (by decide), h.r11])
    (by rw [g₂ _ (by decide), h.r12]) (by rw [f₂.wr, f₁.wr]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e16]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e32]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e48]; exact h.env.inW hp (by omega)))
    fun u₃ ⟨m₃, r5₃, r10₃, gk₃, v₃, sy₃, rd₃, wr₃, sp₃, lr₃⟩ => ?_
  have hm : u₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have hv : ∀ r, r ∉ [.v8, .v9, .v10, .v11] ++ coreV → u₃.vpr r = s.vpr r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [v₃, f₂.v r hr.2, f₁.v r hr.1]
  have hg₃ : ∀ r, r ≠ .r5 → r ≠ .r10 → r ∉ [.r6, .r7] → u₃.gpr r = s.gpr r := fun r h5 h10 h67 => by
    rw [gk₃ r h5 h10, g₂ r h67]
  have g₂10 : u₂.gpr .r10 = s.gpr .r10 := g₂ _ (by decide)
  refine ⟨⟨⟨(hg₃ .r3 (by decide) (by decide) (by decide)).trans h.env.r3,
      fun i hi => by rw [hv .v4 (by decide)]; exact h.env.v4 i hi,
      (hv .v5 (by decide)).trans h.env.v5, (hv .v16 (by decide)).trans h.env.v16,
      (hv .v17 (by decide)).trans h.env.v17, (hv .v18 (by decide)).trans h.env.v18,
      (hv .v19 (by decide)).trans h.env.v19,
      fun r hr => (hg₃ r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
        (fun e => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at e
          rcases e with rfl | rfl <;> decide))).trans (h.env.keep r hr),
      by rw [rd₃, f₂.rd, f₁.rd, h.env.rd], by rw [wr₃, f₂.wr, f₁.wr, h.env.wr],
      by rw [sp₃, f₂.sp, f₁.sp, h.env.sp], by rw [lr₃, f₂.lr, f₁.lr, h.env.lr], ?_, ?_⟩,
    ?_, (hg₃ .r9 (by decide) (by decide) (by decide)).trans h.r9,
    (hg₃ .r8 (by decide) (by decide) (by decide)).trans h.r8,
    (hg₃ .r11 (by decide) (by decide) (by decide)).trans h.r11,
    (hg₃ .r12 (by decide) (by decide) (by decide)).trans h.r12, ?_,
    by rw [gk₃ _ (by decide) (by decide), r6₂], by rw [gk₃ _ (by decide) (by decide), r7₂], ?_⟩, ?_⟩
  · rw [m₃, hm, e16, e32, e48]
    exact (((h.env.frame.write (by simp) _ (vector_contains _ (j := 16 * g) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 4) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 8) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 12) (by omega))
  · rw [m₃, hm, e16, e32, e48]
    exact tab_write hp (j := 16 * g + 12) (tab_write hp (j := 16 * g + 8) (tab_write hp (j := 16 * g + 4)
      (tab_write hp (j := 16 * g) h.env.tab (by omega) _) (by omega) _) (by omega) _) (by omega) _
  · rw [r5₃, show (64 : BitVec 64) = BitVec.ofNat 64 (4 * 16) from rfl, ea]
    exact congrArg _ (by omega)
  · rw [r10₃, g₂10, h.r10]; exact count_sub hg
  · rw [m₃, hm]
    refine polyIs_store4 (x := fun r => u₂.vpr (tv r)) h.poly (by omega) (fun r hr e he => ?_) (fun i hi hn => ?_)
    · rw [imix_get _ _ (by have := xor1_lt he; omega), ite_eq_left (by have := xor1_lt he; omega)]
      exact l₂ r hr e he
    · rw [imix_get _ _ hi, imix_get _ _ hi]
      by_cases hi' : i < 16 * g
      · rw [ite_eq_left (by omega), ite_eq_left hi']
      · rw [ite_eq_right (by omega), ite_eq_right hi']
  · rw [r10₃, g₂10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
    exact count_nz hg (by decide)

theorem imix_zero (W : Poly) : imix 0 W = W :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [imix_get _ _ hi, ite_eq_right (by omega)]

theorem imix_sixteen (W : Poly) : imix 16 W = nttInvLayer (nttInvLayer W 1) 2 :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [imix_get _ _ hi, ite_eq_left (by show i < 256; exact hi)]

theorem inarrow_ok {s₀ : State} (hp : Pre s₀) {R : Poly} {s : State} (h : IEnv s₀ s)
    (hR : PolyIs s.mem (F s₀) R) :
    WP isa narrowInv s fun s' => IEnv s₀ s' ∧ PolyIs s'.mem (F s₀) (nttInvLayer (nttInvLayer R 1) 2) := by
  unfold narrowInv
  refine WP.seq (WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl,
    WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl,
    WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩⟩⟩⟩⟩⟩⟩)
  refine wp_loop_nz (fun g t => IGInv s₀ R g t) (N := 16) (by decide) (fun g hg t ht => igroup_ok hp hg ht)
    (fun t ht => ⟨ht.env, by rw [← imix_sixteen]; exact ht.poly⟩) ?_
  have r4 : s.gpr .r4 = S s₀ := h.keep .r4 (by decide)
  refine ⟨(((((((h.write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _).write (by decide) (by decide) _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.write, reduceCtorEq, ite_false, ite_true]
  · rw [h.r3, coeffAddr]
  · rw [r4]
  · rw [r4]
  · rw [imix_zero]; exact hR

/-! ## The product by `f` -/

/-- The polynomial after `g` groups of sixteen coefficients times `f`. -/
def smix (g : Nat) (W : Poly) : Poly :=
  Vector.ofFn fun i => if i.val < 16 * g then W[i.val]! * 8347681 else W[i.val]!

theorem smix_get (g : Nat) (W : Poly) {i : Nat} (hi : i < 256) :
    (smix g W)[i]! = if i < 16 * g then W[i]! * 8347681 else W[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [smix, Vector.getElem_ofFn]

/-- After `g` groups, from `W`. -/
structure SclInv (s₀ : State) (W : Poly) (g : Nat) (s : State) : Prop where
  env : IEnv s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (16 * g)
  r9 : s.gpr .r9 = 0#64
  r8 : s.gpr .r8 = 16#64
  r11 : s.gpr .r11 = 32#64
  r12 : s.gpr .r12 = 48#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (16 - g)
  v2 : ∀ i < 4, (vword (s.vpr .v2) i).toNat = (8347681 : Zq).val
  v3 : ∀ i < 4, (vword (s.vpr .v3) i).toNat = (8347681 : Zq).val * 2 ^ 32 / Spec.MlDsa.q
  poly : PolyIs s.mem (F s₀) (smix g W)

theorem tv_cases {r : Nat} (hr : r < 4) : tv r = .v8 ∨ tv r = .v9 ∨ tv r = .v10 ∨ tv r = .v11 := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> simp [tv]

/-- `smul` of one of `v8 … v11`, the lanes of the others and of `v2 … v5` kept. -/
theorem smul_run {s₀ u : State} (hc : ICEnv s₀ u) {a : VReg} (ha : a = .v8 ∨ a = .v9 ∨ a = .v10 ∨ a = .v11)
    {x : Nat → Zq} (hx : Lanes (u.vpr a) x)
    (h2 : ∀ i < 4, (vword (u.vpr .v2) i).toNat = (8347681 : Zq).val)
    (h3 : ∀ i < 4, (vword (u.vpr .v3) i).toNat = (8347681 : Zq).val * 2 ^ 32 / Spec.MlDsa.q) :
    WP isa (.block (smul a)) u fun t =>
      Lanes (t.vpr a) (fun r => x r * 8347681) ∧ Fr [a, .v6, .v7] [] u t := by
  refine WP.mono (smul_exec u ha) fun t ⟨e, vo, sy⟩ => ⟨fun r hr => ?_, Fr.of_vonly vo sy⟩
  rw [e, hc.v5, smul_lanes hr (hx r hr) (h2 r hr) (h3 r hr) (hc.v4 r hr), Fin.mul_comm]

theorem sgroup_ok {s₀ : State} (hp : Pre s₀) {W : Poly} {g : Nat} (hg : g < 16) {s : State}
    (h : SclInv s₀ W g s) :
    WP isa (.block scaleBody) s fun s' => SclInv s₀ W (g + 1) s' ∧ (s'.gpr .r10 != 0) = decide (g + 1 ≠ 16) := by
  have ea : ∀ k, coeffAddr (F s₀) (16 * g) + BitVec.ofNat 64 (4 * k) = coeffAddr (F s₀) (16 * g + k) :=
    fun k => coeffAddr_add _ _ _
  have e16 : coeffAddr (F s₀) (16 * g) + 16#64 = coeffAddr (F s₀) (16 * g + 4) := ea 4
  have e32 : coeffAddr (F s₀) (16 * g) + 32#64 = coeffAddr (F s₀) (16 * g + 8) := ea 8
  have e48 : coeffAddr (F s₀) (16 * g) + 48#64 = coeffAddr (F s₀) (16 * g + 12) := ea 12
  unfold scaleBody
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads4_run s h.r5 h.r9 h.r8 h.r11 h.r12 (h.env.inR hp (by omega))
    (by rw [e16]; exact h.env.inR hp (by omega)) (by rw [e32]; exact h.env.inR hp (by omega))
    (by rw [e48]; exact h.env.inR hp (by omega))) fun u₁ ⟨l₁, f₁⟩ => ?_
  have c₁ : ICEnv s₀ u₁ := (CEnvK.of_env h.env).fr f₁ (by decide)
  have hin : ∀ r < 4, Lanes (u₁.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]!) := fun r hr e he => by
    have hx := xor1_lt he
    rw [l₁ r hr, show 16 * r = 4 * (4 * r) by omega, ea, vword_loadC _ _ _ he, polyIs_toNat h.poly (by show _ < 256; omega),
      smix_get _ _ (by omega), ite_eq_right (by omega)]
  have k2 : ∀ i < 4, (vword (u₁.vpr .v2) i).toNat = (8347681 : Zq).val := by
    rw [f₁.v _ (by decide)]; exact h.v2
  have k3 : ∀ i < 4, (vword (u₁.vpr .v3) i).toNat = (8347681 : Zq).val * 2 ^ 32 / Spec.MlDsa.q := by
    rw [f₁.v _ (by decide)]; exact h.v3
  rw [WP.block_append_iff]
  refine WP.mono (smul_run c₁ (.inl rfl) (hin 0 (by decide)) k2 k3) fun u₂ ⟨S8, f₂⟩ => ?_
  have c₂ : ICEnv s₀ u₂ := c₁.fr f₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (smul_run c₂ (.inr (.inl rfl)) (x := fun e => W[16 * g + 4 * 1 + (e ^^^ 1)]!) (by rw [f₂.v _ (by decide)]; exact hin 1 (by decide))
    (by rw [f₂.v _ (by decide)]; exact k2) (by rw [f₂.v _ (by decide)]; exact k3)) fun u₃ ⟨S9, f₃⟩ => ?_
  have c₃ : ICEnv s₀ u₃ := c₂.fr f₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (smul_run c₃ (.inr (.inr (.inl rfl))) (x := fun e => W[16 * g + 4 * 2 + (e ^^^ 1)]!)
    (by rw [f₃.v _ (by decide), f₂.v _ (by decide)]; exact hin 2 (by decide))
    (by rw [f₃.v _ (by decide), f₂.v _ (by decide)]; exact k2)
    (by rw [f₃.v _ (by decide), f₂.v _ (by decide)]; exact k3)) fun u₄ ⟨S10, f₄⟩ => ?_
  have c₄ : ICEnv s₀ u₄ := c₃.fr f₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (smul_run c₄ (.inr (.inr (.inr rfl))) (x := fun e => W[16 * g + 4 * 3 + (e ^^^ 1)]!)
    (by rw [f₄.v _ (by decide), f₃.v _ (by decide), f₂.v _ (by decide)]; exact hin 3 (by decide))
    (by rw [f₄.v _ (by decide), f₃.v _ (by decide), f₂.v _ (by decide)]; exact k2)
    (by rw [f₄.v _ (by decide), f₃.v _ (by decide), f₂.v _ (by decide)]; exact k3)) fun u₅ ⟨S11, f₅⟩ => ?_
  have f₂₅ : Fr [.v8, .v9, .v10, .v11, .v6, .v7] [] u₁ u₅ :=
    (((f₂.mono (by decide) (by simp)).trans' (f₃.mono (by decide) (by simp))).trans'
      (f₄.mono (by decide) (by simp))).trans' (f₅.mono (by decide) (by simp))
  have out : ∀ r < 4, Lanes (u₅.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]! * 8347681) := by
    intro r hr
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> simp only [tv]
    · rw [f₅.v _ (by decide), f₄.v _ (by decide), f₃.v _ (by decide)]; exact S8
    · rw [f₅.v _ (by decide), f₄.v _ (by decide)]; exact S9
    · rw [f₅.v _ (by decide)]; exact S10
    · exact S11
  have g₅ : ∀ r, u₅.gpr r = s.gpr r := fun r => by rw [f₂₅.g _ (by simp), f₁.g _ (by simp)]
  refine WP.mono (stores4_run u₅ (x := coeffAddr (F s₀) (16 * g)) (by rw [g₅, h.r5])
    (by rw [g₅, h.r9]) (by rw [g₅, h.r8]) (by rw [g₅, h.r11])
    (by rw [g₅, h.r12]) (by rw [f₂₅.wr, f₁.wr]; exact h.env.inW hp (by omega))
    (by rw [f₂₅.wr, f₁.wr, e16]; exact h.env.inW hp (by omega))
    (by rw [f₂₅.wr, f₁.wr, e32]; exact h.env.inW hp (by omega))
    (by rw [f₂₅.wr, f₁.wr, e48]; exact h.env.inW hp (by omega)))
    fun u₆ ⟨m₆, r5₆, r10₆, gk₆, v₆, sy₆, rd₆, wr₆, sp₆, lr₆⟩ => ?_
  have hm : u₅.mem = s.mem := by rw [f₂₅.mem, f₁.mem]
  have hv : ∀ r, r ∉ [.v8, .v9, .v10, .v11] ++ [.v8, .v9, .v10, .v11, .v6, .v7] → u₆.vpr r = s.vpr r :=
    fun r hr => by rw [List.mem_append, not_or] at hr; rw [v₆, f₂₅.v r hr.2, f₁.v r hr.1]
  have hg₆ : ∀ r, r ≠ .r5 → r ≠ .r10 → u₆.gpr r = s.gpr r := fun r h5 h10 => by rw [gk₆ r h5 h10, g₅]
  refine ⟨⟨⟨(hg₆ .r3 (by decide) (by decide)).trans h.env.r3,
      fun i hi => by rw [hv .v4 (by decide)]; exact h.env.v4 i hi,
      (hv .v5 (by decide)).trans h.env.v5, (hv .v16 (by decide)).trans h.env.v16,
      (hv .v17 (by decide)).trans h.env.v17, (hv .v18 (by decide)).trans h.env.v18,
      (hv .v19 (by decide)).trans h.env.v19,
      fun r hr => (hg₆ r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))).trans (h.env.keep r hr),
      by rw [rd₆, f₂₅.rd, f₁.rd, h.env.rd], by rw [wr₆, f₂₅.wr, f₁.wr, h.env.wr],
      by rw [sp₆, f₂₅.sp, f₁.sp, h.env.sp], by rw [lr₆, f₂₅.lr, f₁.lr, h.env.lr], ?_, ?_⟩,
    ?_, (hg₆ .r9 (by decide) (by decide)).trans h.r9,
    (hg₆ .r8 (by decide) (by decide)).trans h.r8,
    (hg₆ .r11 (by decide) (by decide)).trans h.r11,
    (hg₆ .r12 (by decide) (by decide)).trans h.r12, ?_,
    by rw [hv .v2 (by decide)]; exact h.v2, by rw [hv .v3 (by decide)]; exact h.v3, ?_⟩, ?_⟩
  · rw [m₆, hm, e16, e32, e48]
    exact (((h.env.frame.write (by simp) _ (vector_contains _ (j := 16 * g) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 4) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 8) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 12) (by omega))
  · rw [m₆, hm, e16, e32, e48]
    exact tab_write hp (j := 16 * g + 12) (tab_write hp (j := 16 * g + 8) (tab_write hp (j := 16 * g + 4)
      (tab_write hp (j := 16 * g) h.env.tab (by omega) _) (by omega) _) (by omega) _) (by omega) _
  · rw [r5₆, show (64 : BitVec 64) = BitVec.ofNat 64 (4 * 16) from rfl, ea]
    exact congrArg _ (by omega)
  · rw [r10₆, g₅, h.r10]; exact count_sub hg
  · rw [m₆, hm]
    refine polyIs_store4 (x := fun r => u₅.vpr (tv r)) h.poly (by omega) (fun r hr e he => ?_) (fun i hi hn => ?_)
    · rw [smix_get _ _ (by have := xor1_lt he; omega), ite_eq_left (by have := xor1_lt he; omega)]
      exact out r hr e he
    · rw [smix_get _ _ hi, smix_get _ _ hi]
      by_cases hi' : i < 16 * g
      · rw [ite_eq_left (by omega), ite_eq_left hi']
      · rw [ite_eq_right (by omega), ite_eq_right hi']
  · rw [r10₆, g₅, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
    exact count_nz hg (by decide)

theorem smix_zero (W : Poly) : smix 0 W = W :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [smix_get _ _ hi, ite_eq_right (by omega)]

theorem smix_sixteen (W : Poly) : smix 16 W = W.map (· * 8347681) :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by
    rw [smix_get _ _ hi, ite_eq_left (by show i < 256; exact hi), VG.Proof.MlDsa.Arith.getElem!_eq _ hi,
      VG.Proof.MlDsa.Arith.getElem!_eq _ hi, Vector.getElem_map]

end VG.Proof.MlDsa.PPC64LE.VNtt
