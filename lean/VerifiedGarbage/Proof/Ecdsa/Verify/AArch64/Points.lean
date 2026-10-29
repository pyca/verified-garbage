module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.Block

/-!
# ECDSA verification on AArch64: `[u]G + [v]Q`

`points_ok`: from what `mid_ok` leaves, the table of `u`'s bits, the
signature's comb (`[u]G`), `save` (`[u]G` to `U`, and `R = O`), ECDH's
window method (`[v]Q`, from the key's point) and `sum` (the complete
addition of `U` and `R`, into `R`): `R` holds `rcbAdd` of representatives of
`[u]G` and `[v]Q`, as `Q₁ 0` and `Q₂ 0` accept them.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

theorem tbl_le (h7 : c.n < 10) : bitsAt c.n 0 + 64 * c.n ≤ size := by
  have := bitsAt0_le c h7; show _ ≤ 8192; omega_arith

theorem sl_lt4096 (h0 : 0 < c.n) (h7 : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i < 4096 := by
  by_cases hT : i = TMP
  · subst hT; rw [Cfg.sl]; split
    · simp only [Mont.moAt]; omega_arith
    · simp only [slot, TMP]; omega_arith
  have := sl_below_bits c hi 0 0 hT; have := bitsAt0_le c h7; omega_arith

/-- `[o] = [a]`, on numbered slots. -/
theorem copySl_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o a : Nat}
    (ho : o < 45) (ha : a < 45) (hoa : o ≠ a) :
    WP isa (.block (copy c.n (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ KeepRegs [.x1] s s' ∧
      Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_apart c hoa
  exact copy_ok c.n hs (sl_le c hc.n10 ho) (sl_le c hc.n10 ha) (sl_mod8 c o) (sl_mod8 c a) (by omega_arith)

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ KeepRegs [.x1] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem :=
  setConst_ok hs (sl_le c hc.n10 ho) (sl_mod8 c o) hx

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.save c =
    copy c.n (c.sl UX) (c.sl RX) ++ (copy c.n (c.sl UY) (c.sl RY) ++ (copy c.n (c.sl UZ) (c.sl RZ) ++
    (setConst c.n (c.sl RX) 0 ++ (setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.AArch64.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.x1] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  have hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega_arith)
    omega_arith
  rw [save_eq]
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (setSl_ok hc hs₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 → sv c base s' i = sv c base s i := fun O hi hij hj => sv_out O h7 hn hi hij hj
  refine ⟨hs₅.of_keepRegs k₆ (by decide),
    (k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆))))).mono (by intro r hr; simpa using hr), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW] using hw
  · rw [o O₆ (by decide) (by decide) (by decide), o O₅ (by decide) (by decide) (by decide), o O₄ (by decide) (by decide) (by decide),
      o O₃ (by decide) (by decide) (by decide), o O₂ (by decide) (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide) (by decide), o O₅ (by decide) (by decide) (by decide), o O₄ (by decide) (by decide) (by decide),
      o O₃ (by decide) (by decide) (by decide), e₂, o O₁ (by decide) (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide) (by decide), o O₅ (by decide) (by decide) (by decide), o O₄ (by decide) (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide) (by decide), o O₁ (by decide) (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide) (by decide), o O₅ (by decide) (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide) (by decide), e₅]

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, RX, RY, RZ, EM, TX, TY, TZ]

/-- The slots of the addition. -/
abbrev sumSl : List Nat := [AP, BM, T0, T1, T2, T3, T4, T5, DX, DY, DZ, UX, UY, UZ, RX, RY, RZ, TX, TY, TZ]

/-- The slots it reads. -/
abbrev sumR : List Nat := [AP, BM, UX, UY, UZ, RX, RY, RZ]

theorem map_sl_sub {l l' : List Nat} (h : ∀ i ∈ l, i ∈ l') : ∀ x ∈ l.map c.sl, x ∈ l'.map c.sl :=
  fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact List.mem_map_of_mem (h i hi)

theorem slW_sub {l l' : List Nat} (h : ∀ i ∈ l, i ∈ l') : ∀ w ∈ slW c l, w ∈ slW c l' :=
  fun w hw => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact List.mem_map_of_mem (h i hi)

/-- `R = D`. -/
theorem fromD_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.fromD c)) s fun s' =>
      Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c [RX, RY, RZ]) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧ sv c base s' RX = sv c base s DX ∧
      sv c base s' RY = sv c base s DY ∧ sv c base s' RZ = sv c base s DZ := by
  have h7 := hc.n10
  have hn := hs.nowrap
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.fromD, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copySl_ok hc hs₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 → sv c base s' i = sv c base s i := fun O hi hij hj => sv_out O h7 hn hi hij hj
  have U₄ : Unch base (slW c [RX, RY, RZ]) s.mem s₄.mem :=
    (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      rcases hw with rfl | rfl | rfl <;> simp
  refine ⟨hs₃.of_keepRegs k₄ (by decide), by rw [k₄.rd, k₃.rd, k₂.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr], U₄, hM.unch U₄ (apart_slW (c := c) (i := MP) (by decide)) hn, ?_, ?_, ?_⟩
  · rw [o O₄ (by decide) (by decide) (by decide), o O₃ (by decide) (by decide) (by decide), e₂]
  · rw [o O₄ (by decide) (by decide) (by decide), e₃, o O₂ (by decide) (by decide) (by decide)]
  · rw [e₄, o O₃ (by decide) (by decide) (by decide), o O₂ (by decide) (by decide) (by decide)]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.sum c) s fun s' =>
      Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c sumW) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧ (sv c base s' RZ < c.C.p ∧ sv c base s' RX < c.C.p) ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd3 (tmv c.C c.n base s (c.sl BM))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ sumSl.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 c i, MP'_A c,
    fun f m' h => (hc.call_p f m' h).2⟩
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 → sv c base s' i = sv c base s i := fun O hi hij hj => sv_out O h7 hn hi hij hj
  -- The end: `R = D`, for `D` the sum.
  have tail : ∀ {s₁ : State} {W : List Nat}, Scr s₁ base size → s₁.rd = s.rd → s₁.wr = s.wr →
      Unch base (slW c W) s.mem s₁.mem → (∀ i ∈ W, i ∈ sumW) → ModOkA c.MP' size c.C.p s₁.mem base →
      sv c base s₁ DZ < c.C.p → sv c base s₁ DX < c.C.p →
      (tmv c.C c.n base s₁ (c.sl DX), tmv c.C c.n base s₁ (c.sl DY), tmv c.C c.n base s₁ (c.sl DZ)) =
        rcbAdd3 (tmv c.C c.n base s (c.sl BM))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) →
      WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.fromD c)) s₁ fun s' =>
        Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c sumW) s.mem s'.mem ∧
        ModOkA c.MP' size c.C.p s'.mem base ∧ (sv c base s' RZ < c.C.p ∧ sv c base s' RX < c.C.p) ∧
        (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
          rcbAdd3 (tmv c.C c.n base s (c.sl BM))
            (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
            (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) :=
    fun hs₁ rd₁ wr₁ U₁ hW M₁ z₁ x₁ t₁ =>
      WP.mono (fromD_ok hc hs₁ M₁) fun s₂ ⟨hs₂, rd₂, wr₂, U₂, M₂, x₂, y₂, z₂⟩ =>
        ⟨hs₂, rd₂.trans rd₁, wr₂.trans wr₁,
          (U₁.trans U₂).mono fun w hw => (List.mem_append.mp hw).elim (slW_sub hW w)
            (slW_sub (by decide) w),
          M₂, ⟨z₂ ▸ z₁, x₂ ▸ x₁⟩, by
            show (toM _ _ (sv c base s₂ RX), toM _ _ (sv c base s₂ RY), toM _ _ (sv c base s₂ RZ)) = _
            rw [x₂, y₂, z₂]; exact t₁⟩
  cases hp : c.padd with
  | none =>
    simp only [Impl.Ecdsa.Verify.AArch64.Cfg.sum, hp]
    have hA : RcbApart c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ) :=
      rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := sumR) rfl rfl (by decide)
        (by decide)
    have hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (sumR.map c.sl)
        (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
      refine ⟨hs, hM, map_sl_sub (by decide), fun x hx => ?_, fun _ _ => rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
    have hLow : Low c.MP' (rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ)) :=
      Low.of_call fun _ _ _ x hx => by
        rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) =
          ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have key : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i < 45 ∧ i ≠ TMP := by decide
        exact sl_own c hc.n10 (key i hi).1 (key i hi).2
    refine WP.seq (WP.mono (rcb3_ok hL hAl hpR hA (map_sl_sub (l := [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR)
      (by decide)) hLow hI (fun x hx => hx)) fun s₁ ⟨k₁, I₁, t₁⟩ => ?_)
    have hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ [(c.pt DX DY DZ).x, (c.pt DX DY DZ).y, (c.pt DX DY DZ).z] ++
        sumR.map c.sl := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [Cfg.pt]
    have U₁ : Unch base (slW c [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) s.mem s₁.mem := k₁.unch
    refine tail (k₁.scr hs) k₁.rd k₁.wr U₁ (by decide) I₁.mod (I₁.lt _ (hD DZ (by simp)))
      (I₁.lt _ (hD DX (by simp))) ?_
    exact (congrArg₂ Prod.mk (I₁.val _ (hD DX (by simp)))
      (congrArg₂ Prod.mk (I₁.val _ (hD DY (by simp))) (I₁.val _ (hD DZ (by simp))))).trans t₁
  | some f =>
    obtain ⟨name, bAt⟩ := f
    obtain rfl := padd_bAt hp
    simp only [Impl.Ecdsa.Verify.AArch64.Cfg.sum, hp]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    -- `b` to `EM`.
    refine WP.mono (copySl_ok hc hs (o := EM) (a := BM) (by decide) (by decide) (by decide))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    -- `T = R`.
    have dT : ∀ x ∈ ([TX, TY, TZ] : List Nat).map c.sl, x ∉ ([RX, RY, RZ] : List Nat).map c.sl :=
      map_sl_disj h0 (by decide)
    refine WP.mono (copyPt_ok hs₁ (o := c.pt TX TY TZ) (a := c.pt RX RY RZ) (n := c.n)
      (fun x hx => hL.le x (map_sl_sub (l := [TX, TY, TZ, RX, RY, RZ]) (by decide) x hx))
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp (show x ∈ ([TX, TY, TZ, RX, RY, RZ] : List Nat).map c.sl from hx)
        exact sl_mod8 c i)
      (fun x hx y hy hxy => hL.apart x y (map_sl_sub (l := [TX, TY, TZ]) (by decide) x hx)
        (map_sl_sub (l := [TX, TY, TZ, RX, RY, RZ]) (by decide) y hy) hxy)
      (fun x hx => dT x hx)
      ⟨fun e => absurd (sl_inj c h0 (i := TX) (j := TY) e) (by decide),
        fun e => absurd (sl_inj c h0 (i := TX) (j := TZ) e) (by decide),
        fun e => absurd (sl_inj c h0 (i := TY) (j := TZ) e) (by decide)⟩)
      fun s₂ ⟨cx₂, cy₂, cz₂, k₂, U₂⟩ => ?_
    have hs₂ := hs₁.of_keepRegs k₂ (by decide)
    have U₂' : Unch base (slW c [TX, TY, TZ]) s₁.mem s₂.mem := U₂
    have v₂ : ∀ {i}, i < 45 → i ∉ [TX, TY, TZ] → i ≠ EM → i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 → sv c base s₂ i = sv c base s i :=
      fun hi hl he ha => (sv_unch U₂' h7 hn hi (apart_slW hl ha)).trans (o O₁ hi he (by decide))
    have em₂ : sv c base s₂ EM = sv c base s BM :=
      (sv_unch U₂' h7 hn (i := EM) (by decide) (apart_slW (by decide))).trans e₁
    have tx₂ : sv c base s₂ TX = sv c base s RX := cx₂.trans (o O₁ (i := RX) (by decide) (by decide) (by decide))
    have ty₂ : sv c base s₂ TY = sv c base s RY := cy₂.trans (o O₁ (i := RY) (by decide) (by decide) (by decide))
    have tz₂ : sv c base s₂ TZ = sv c base s RZ := cz₂.trans (o O₁ (i := RZ) (by decide) (by decide) (by decide))
    have M₂ : ModOkA c.MP' size c.C.p s₂.mem base :=
      (hM.unch O₁.unch (apart_slW (c := c) (l := [EM]) (i := MP) (by decide)) hn).unch U₂'
        (apart_slW (c := c) (l := [TX, TY, TZ]) (i := MP) (by decide)) hn
    -- `R = U`, and `D = R + T`.
    obtain ⟨E, hE⟩ : ∃ E : Nat → Fin c.C.p, E = fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base x c.n) :=
      ⟨_, rfl⟩
    have hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (([AP, BM, UX, UY, UZ, TX, TY, TZ] : List Nat).map c.sl)
        E s₂ := by
      refine ⟨hs₂, M₂, map_sl_sub (by decide), fun x hx => ?_, fun x _ => by subst hE; rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      show sv c base s₂ i < c.C.p
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hlt _ (by decide)
      · rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hlt _ (by decide)
      · rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hlt _ (by decide)
      · rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hlt _ (by decide)
      · rw [v₂ (by decide) (by decide) (by decide) (by decide)]; exact hlt _ (by decide)
      · rw [tx₂]; exact hlt _ (by decide)
      · rw [ty₂]; exact hlt _ (by decide)
      · rw [tz₂]; exact hlt _ (by decide)
    have hA : RcbApart c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ) (c.pt DX DY DZ) :=
      rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := [AP, BM, RX, RY, RZ, TX, TY, TZ]) rfl rfl
        (by decide) (by decide)
    have hLow : Low c.MP' (rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ)) :=
      Low.of_call fun _ _ _ x hx => by
        rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ) =
          ([T0, T1, T2, T3, T4, T5, DX, DY, DZ, AP, BM, RX, RY, RZ, TX, TY, TZ] : List Nat).map c.sl from rfl] at hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have key : ∀ i ∈ ([T0, T1, T2, T3, T4, T5, DX, DY, DZ, AP, BM, RX, RY, RZ, TX, TY, TZ] : List Nat),
          i < 45 ∧ i ≠ TMP := by decide
        exact sl_own c hc.n10 (key i hi).1 (key i hi).2
    have hpa : AddOk c.MP' size (· ∈ sumSl.map c.sl) c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ)
        (c.pt DX DY DZ) (some (name, c.sl EM)) := by
      have := addOk_of hc.toBaseCfgOk (Sl := (· ∈ sumSl.map c.sl))
        (lay_map_em hc.toBaseCfgOk rfl rfl rfl (l := sumSl) (by decide))
      rw [hp] at this; exact this
    have hrd : (c.pt RX RY RZ).x ≠ (c.pt RX RY RZ).y ∧ (c.pt RX RY RZ).x ≠ (c.pt RX RY RZ).z ∧
        (c.pt RX RY RZ).y ≠ (c.pt RX RY RZ).z :=
      ⟨fun e => absurd (sl_inj c h0 (i := RX) (j := RY) e) (by decide),
        fun e => absurd (sl_inj c h0 (i := RX) (j := RZ) e) (by decide),
        fun e => absurd (sl_inj c h0 (i := RY) (j := RZ) e) (by decide)⟩
    have hr : AddReady base c.MP' s₂.mem c.rcbSlots (some (name, c.sl EM)) := by
      show sv c base s₂ EM = sv c base s₂ BM
      rw [em₂, v₂ (by decide) (by decide) (by decide) (by decide)]
    have hfar : AddFar c.MP' c.rcbSlots (slW c [RX, RY, RZ]) (some (name, c.sl EM)) := fun w hw =>
      ⟨(apart_slW (c := c) (l := [RX, RY, RZ]) (i := EM) (by decide)) w hw,
        (apart_slW (c := c) (l := [RX, RY, RZ]) (i := BM) (by decide)) w hw⟩
    refine WP.seq (WP.mono (copyAdd_ok hL hAl hpR hA
      (map_sl_sub (l := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, AP, BM, RX, RY, RZ, TX, TY, TZ]) (by decide))
      hLow hpa hI (map_sl_sub (l := [RX, RY, RZ]) (by decide)) (map_sl_sub (l := [UX, UY, UZ]) (by decide))
      (map_sl_disj h0 (l₁ := [RX, RY, RZ]) (by decide)) hrd
      (map_sl_sub (l := [AP, BM, RX, RY, RZ, TX, TY, TZ]) (l' := [RX, RY, RZ, AP, BM, UX, UY, UZ, TX, TY, TZ])
        (by decide)) hr hfar) fun s₃ ⟨k₃, I₃, t₃⟩ => ?_)
    have U₃ : Unch base (slW c [EM, TX, TY, TZ, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP])
        s.mem s₃.mem := O₁.unch.trans (U₂'.trans k₃.unch)
    have hD : ∀ i ∈ ([DX, DY, DZ] : List Nat), c.sl i ∈ [(c.pt DX DY DZ).x, (c.pt DX DY DZ).y, (c.pt DX DY DZ).z] ++
        ([(c.pt RX RY RZ).x, (c.pt RX RY RZ).y, (c.pt RX RY RZ).z] ++
          ([AP, BM, UX, UY, UZ, TX, TY, TZ] : List Nat).map c.sl) := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [Cfg.pt]
    have er := rext_r E (c.pt UX UY UZ) hrd
    have ro : ∀ {i j}, c.sl i ∉ ([RX, RY, RZ] : List Nat).map c.sl → sv c base s₂ i = sv c base s j →
        rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h e => by
      rw [rext_of h, hE]
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _)
      rw [e]
    have ru : ∀ {i}, i ∈ ([UX, UY, UZ] : List Nat) → E (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
      rw [hE]
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rw [v₂ (by decide) (by decide) (by decide) (by decide)]
    have nR : ∀ i ∈ ([BM, TX, TY, TZ] : List Nat), c.sl i ∉ ([RX, RY, RZ] : List Nat).map c.sl :=
      fun i hi => (map_sl_disj h0 (l₁ := [BM, TX, TY, TZ]) (l₂ := [RX, RY, RZ]) (by decide)) _ (List.mem_map_of_mem hi)
    refine tail (k₃.scr hs₂) (by rw [k₃.rd, k₂.rd, k₁.rd]) (by rw [k₃.wr, k₂.wr, k₁.wr]) U₃ (by decide) I₃.mod
      (I₃.lt _ (hD DZ (by simp))) (I₃.lt _ (hD DX (by simp))) ?_
    refine (congrArg₂ Prod.mk (I₃.val _ (hD DX (by simp)))
      (congrArg₂ Prod.mk (I₃.val _ (hD DY (by simp))) (I₃.val _ (hD DZ (by simp))))).trans (t₃.trans ?_)
    show rcbAdd3 (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.sl BM))
      (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.pt RX RY RZ).x)
      (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.pt RX RY RZ).y)
      (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.pt RX RY RZ).z)
      (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.sl TX)) (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.sl TY))
      (rext E (c.pt RX RY RZ) (c.pt UX UY UZ) (c.sl TZ)) = _
    rw [er.1, er.2.1, er.2.2, ro (nR BM (by decide)) (v₂ (by decide) (by decide) (by decide) (by decide)),
      ro (nR TX (by decide)) tx₂, ro (nR TY (by decide)) ty₂, ro (nR TZ (by decide)) tz₂,
      show E (c.pt UX UY UZ).x = _ from ru (i := UX) (by decide),
      show E (c.pt UX UY UZ).y = _ from ru (i := UY) (by decide),
      show E (c.pt UX UY UZ).z = _ from ru (i := UZ) (by decide)]

/-- After `[u]G + [v]Q`, for what `Q₁` and `Q₂` accept of representatives of
`[u]G` and `[v]Q`: `R` holds their complete addition. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64)
    (Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Q₁ 0 X1 Y1 Z1 ∧ Q₂ 0 X2 Y2 Z2 ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2
  unch : Unch base [(0, size)] s₀.mem s.mem
  k : sv c base s K = sigR c s₀
  rx_lt : sv c base s RX < c.C.p

theorem points_eq (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.points c =
    .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.seq (TCombCfg.comb c.combCfg true)
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c)) (.seq (c.winPrep (c.sl V))
      (.seq (WinCfg.window (winQ c)) (Impl.Ecdsa.Verify.AArch64.Cfg.sum c))))) := rfl

/-- The slots the comb, the window method but its table, and `save` write. -/
abbrev ptsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP, UX, UY, UZ, PT, EM]

/-- `[u]G + [v]Q`, into `R`. -/
theorem points_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hM : Mid c s₀ base g s) {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    (hTP : TblPre c s₀ (s₀.syms c.tsym) base)
    (hQ₁ : ∀ X Y Z, Rep c.C X Y Z (mul (sv c base s U) (G c.C)) → Q₁ 0 X Y Z)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hQ₂ : ∀ X Y Z, Rep c.C X Y Z (mul (sv c base s V) P) → Q₂ 0 X Y Z)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base g Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.points c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0 h7
  rw [points_eq]
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega_arith) (sl_le c h7 (i := U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := U) (by decide)) (by have := bitsAt0_le c h7; omega_arith) (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  obtain ⟨hTM, hout⟩ := tbl_of hTP hM.rd hM.unch
  have hTM₁ : TblMem s₁ (s₀.syms c.tsym) c.combWords :=
    TblMem.of_unch hTM (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact tbl_le h7) hout
  have hF : TCombFixed c.combCfg c.C base size s₁ (sv c base s U) (s₀.syms c.tsym) c.combWords := by
    refine ⟨?_, ?_, ?_, F₁.zero, ?_, wordsVal_lt _ _ _ _, by rw [sy₁, hM.syms]; rfl, hTM₁, hout⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl AP) c.n) = _
      rw [F₁.ap]; exact toM_cmont hc _
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl BM) c.n) = _
      rw [F₁.bm]; exact toM_cmont hc _
    · intro x hx
      simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · show wordsVal s₁.mem base (c.sl AP) c.n < _; rw [F₁.ap]; exact hmont _
      · show wordsVal s₁.mem base (c.sl BM) c.n < _; rw [F₁.bm]; exact hmont _
      · show wordsVal s₁.mem base (c.sl ZERO) c.n < _; rw [F₁.zero]; omega_arith
    · intro t ht
      show s₁.mem (off base (bitsAt c.n 0 + t)) = _
      rw [b₁ t ht]
  have WC := tcomb_ok (publicLookup := true) (tcombLay hc) (combA hc) hC hc.am3 hc.onG (tcombVals hc hC hT) hc.p_lt hs₁
    (modP_of hc F₁.mp) hF (pa := none) trivial trivial trivial
  refine WP.seq (WP.mono WC fun s₂ h₂ => ?_)
  obtain ⟨K₂, U₂, M₂, L₂, R₂⟩ := h₂
  have q₂ := hQ₁ _ _ _ R₂
  have F₂ := F₁.unch h7 hn fixedOk_tcombW U₂
  rw [tcombW_eq] at U₂
  have hs₂ := hs₁.of_keepRegs K₂ (x0_not_tcombClob hc.n10)
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₂ : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
      i ∈ ptsW := by decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_append (apart_slW (fun h => hl (sub₂ _ h))) (apart_zw hi)))).trans (v₁ hi)
  -- `[v]Q`.
  have tv₃ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _)
      rw [W₃ hi hl]
  refine winMul_ok hc hC hs₃ F₃ hP (by rw [W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [tv₃ (by decide) (by decide), tv₃ (by decide) (by decide), tv₃ (by decide) (by decide)]
        exact hrep) (ks := V) (by decide) (hpa := (trivial : AddOk _ _ _ _ _ _ _ none)) (hr := trivial)
    (hfar := trivial) fun s₅ W => ?_
  have hs₅ := W.scr
  have F₅ := F₃.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
  have nw : ∀ i < 45, i ∉ ptsW → i ∉ otherI ++ tblI ++ [TMP] := by decide
  have v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₅ i = sv c base s₃ i := fun hi hl =>
    sv_unch W.unch h7 hn hi (apart_append (apart_winX hi) (apart_slW (nw _ hi hl)))
  have q₅ := hQ₂ _ _ _ (by rw [← W₃ (i := V) (by decide) (by decide)]; exact W.q)
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact sv_unch W.unch h7 hn (by decide) (apart_append (apart_winX (by decide)) (apart_slW (by decide)))
  refine WP.mono (sum_ok hc hs₅ W.mod (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.bm (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact W.lt _ (List.mem_cons_self ..)
    · exact W.lt _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact W.lt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have v₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₆ i = sv c base s i := fun hi hl =>
    (sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))).trans ((v₅ hi hl).trans (W₃ hi hl))
  have sub₅ : ∀ i ∈ otherI ++ tblI ++ [TMP], i ∈ ptsW ++ tblI := by decide
  have UW : Unch base ([(bitsAt c.n 0, 64 * c.n), (bitsAt c.n 0 + 64 * c.n, 8 * c.combCfg.zw)] ++
      winX c ++ slW c (ptsW ++ tblI)) s.mem s₆.mem := by
    refine (U₁.trans (U₂.trans (U₃.trans (W.unch.trans U₆)))).mono fun w hw => ?_
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | (hw | hw) | hw | (hw | hw) | hw
    · exact Or.inl (Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hw))))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₂ i hi)))
    · exact Or.inl (Or.inl (List.mem_cons_of_mem _ hw))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₃ i hi)))
    · exact Or.inl (Or.inr hw)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact Or.inr (List.mem_map_of_mem (sub₅ i hi))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₆ i hi)))
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, BM] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), W₃ (by decide) (by decide)]
  have hb : tmv c.C c.n base s (c.sl BM) = Fin.ofNat c.C.p c.C.b := by
    show toM _ _ (wordsVal s.mem base (c.sl BM) c.n) = _
    rw [F.bm]; exact toM_cmont hc _
  refine ⟨hs₆, by rw [wr₆, W.wr, k₃.wr, K₂.wr, k₁.wr, hM.wr],
    by rw [rd₆, W.rd, k₃.rd, K₂.rd, k₁.rd, hM.rd], F₆, ?_,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm, rz₆.1,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, tR₅ (by decide), hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃, rcbAdd3_eq, ← hc.am3,
        ← ofNat_three_mul]
      rfl⟩, ?_, by rw [v₆ (by decide) (by decide)]; exact hM.k, rz₆.2⟩
  · rw [UW.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)]
    · exact hM.flag
    · simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have := sl_below_bits c (i := FLAG) (by decide) 0 0
        rcases hw with rfl | rfl <;> exact Or.inl (by dsimp only; omega_arith)
      · exact (apart_winX (c := c) (i := FLAG) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega_arith)) (fun h => Or.inr h)
      · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega_arith)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact tbl_le h7
      · have := (tcombLay hc.toBaseCfgOk).bits; exact this
    · simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
      have := sl_le' c h7 (i := WT) (by decide)
      have e1 : c.sl WK + 16 * c.n ≤ c.sl WT := by simp (disch := decide) only [sl_eq]; unfold WK WT; omega_arith
      have e2 : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
        simp (disch := decide) only [sl_eq]; unfold WB WT
        have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega_arith
        omega_arith
      rcases hw with rfl | rfl
      · show c.sl WK + 16 * c.n ≤ size; omega_arith
      · show c.sl WB + 64 * (c.n + 1) ≤ size; omega_arith
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact sl_le' c h7 ((show ∀ i ∈ ptsW ++ tblI, i < 112 by decide) i hi)

end VG.Proof.Ecdsa.Verify.AArch64
