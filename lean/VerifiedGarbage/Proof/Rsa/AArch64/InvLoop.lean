module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.TcS
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Rsa.AArch64.InvStage
import VerifiedGarbage.Proof.Rsa.AArch64.InvHead
import VerifiedGarbage.Proof.Rsa.Divstep.Batch64
import VerifiedGarbage.Proof.Divstep.MredWords
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

/-!
# RSA private keys on AArch64: the batches of divsteps

The batches of `Keys.inverseB` keep `LInv`: after `k` of them, `f`, `g`,
`a` and `b` in their arrays and `d` in lane 0 of `v18` are those of
`Divstep.invRunS 59` after `k` batches (`ICfg.st`), the modulus unchanged
and only the batches' arrays changed (`batch_ok`: `batchHead_ok`, then
`fgStage_ok` and `abStage_ok`, with `Rsa.Divstep.batch64` for what they
need). `batches_ok`: the `3 n + 2` batches.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The batched inverse's fixed data: the working space, the width `n`
and the arrays' stride `w`, the arrays, the modulus `p`, `-p⁻¹ mod 2^64`
and the start `x` of `g`. -/
structure ICfg where
  B : Addr
  Z : Nat
  w : Nat
  n : Nat
  iU : Nat
  iV : Nat
  iX₁ : Nat
  iX₂ : Nat
  iM : Nat
  iT : Nat
  p : Nat
  mi : BitVec 64
  x : Nat

/-- What the batches need of it. -/
structure ICfg.Ok (C : ICfg) : Prop where
  n1 : 1 ≤ C.n
  nw : C.n ≤ C.w
  w24 : C.w < 2 ^ 24
  n21 : C.n < 2 ^ 21
  hZ : slot C.w 16 ≤ C.Z
  hU : C.iU < 16
  hV : C.iV < 16
  hX₁ : C.iX₁ < 16
  hX₂ : C.iX₂ < 16
  hM : C.iM < 16
  hT : C.iT < 16
  dUV : C.iU ≠ C.iV
  dUX₁ : C.iU ≠ C.iX₁
  dUX₂ : C.iU ≠ C.iX₂
  dUM : C.iU ≠ C.iM
  dUT : C.iU ≠ C.iT
  dVX₁ : C.iV ≠ C.iX₁
  dVX₂ : C.iV ≠ C.iX₂
  dVM : C.iV ≠ C.iM
  dVT : C.iV ≠ C.iT
  dX : C.iX₁ ≠ C.iX₂
  dX₁M : C.iX₁ ≠ C.iM
  dX₁T : C.iX₁ ≠ C.iT
  dX₂M : C.iX₂ ≠ C.iM
  dX₂T : C.iX₂ ≠ C.iT
  dMT : C.iM ≠ C.iT
  podd : C.p % 2 = 1
  p1 : 1 < C.p
  pC : C.p < 2 ^ (64 * C.n)
  xC : C.x < 2 ^ (64 * C.n + 1)
  hm : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0

/-- The state after `k` batches. -/
def ICfg.st (C : ICfg) (k : Nat) : Divstep.IState := Divstep.invRunS 59 C.p C.mi.toNat C.x k

/-- The arrays the batches change. -/
def ICfg.ranges (C : ICfg) : List (Nat × Nat) :=
  [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iV, 8 * (C.w + 2)), (slot C.w C.iX₁, 8 * (C.w + 2)),
    (slot C.w C.iX₂, 8 * (C.w + 2)), (slot C.w C.iT, 8 * (C.w + 2))]

/-- The state between batches, after `k` of them from `s₀`. -/
structure LInv (C : ICfg) (s₀ : State) (k : Nat) (s : State) : Prop where
  scr : Scr s C.B C.Z
  x0 : s.gpr .x0 = C.B
  x11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2))
  x12 : s.gpr .x12 = BitVec.ofNat 64 C.n
  f : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iV) (C.n + 1)) = (C.st k).f
  g : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iU) (C.n + 1)) = (C.st k).g
  a : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st k).a
  b : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st k).b
  d : laneOf s .v18 0 = BitVec.ofInt 64 (C.st k).d
  mi : laneOf s .v18 1 = C.mi
  m : wv s.mem C.B (slot C.w C.iM) C.n = C.p
  frm : Frm C.B C.ranges s₀.mem s.mem
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ s
  v19 : s.v .v19 = s₀.v .v19

/-- Array `j` is apart from three others' parts. -/
theorem apart3 {w j a b c L la lb lc : Nat} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) (hL : L ≤ w + 2)
    (ha : la ≤ 8 * (w + 2)) (hb : lb ≤ 8 * (w + 2)) (hc : lc ≤ 8 * (w + 2)) :
    ∀ r ∈ [(slot w a, la), (slot w b, lb), (slot w c, lc)], slot w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact slot_apart (w := w) hja (by omega) ha
  · exact slot_apart (w := w) hjb (by omega) hb
  · exact slot_apart (w := w) hjc (by omega) hc

/-- Array `j` is apart from the batches' arrays. -/
theorem apart5 {w j a b c d e L : Nat} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) (hjd : j ≠ d) (hje : j ≠ e)
    (hL : L ≤ w + 2) :
    ∀ r ∈ [(slot w a, 8 * (w + 2)), (slot w b, 8 * (w + 2)), (slot w c, 8 * (w + 2)), (slot w d, 8 * (w + 2)),
      (slot w e, 8 * (w + 2))], slot w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact slot_apart (w := w) hja (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjb (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjc (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjd (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hje (by omega) (Nat.le_refl _)

/-- A batch keeps `LInv`, one batch on. -/
theorem batch_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} {k : Nat} (hk : k < 3 * C.n + 2) (hI : LInv C s₀ k s) :
    WP isa (batch C.iV C.iU C.iX₂ C.iX₁ C.iT C.iM) s fun t =>
      LInv C s₀ (k + 1) t ∧ t.gpr .x15 = s.gpr .x15 - 1#64 := by
  have hn' := hI.scr.nowrap
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by have := hC.hZ; omega
  have hL : (1 : Nat) ≤ C.n + 1 := by omega
  have hpC : (C.p : Int) < 2 ^ (64 * C.n + 1) := by
    have := hC.pC; have : C.p < 2 ^ (64 * C.n + 1) := by rw [Nat.pow_succ]; omega
    exact_mod_cast this
  have hxC : (C.x : Int) < 2 ^ (64 * C.n + 1) := by exact_mod_cast hC.xC
  obtain ⟨fodd, dbnd, bf, bg, ⟨a0, a1, b0, b1⟩, buv, bqr, ef, eg, ea, eb, ed⟩ :=
    Rsa.Divstep.batch64 (n := C.n) (k := k) (p := C.p) (m := C.mi.toNat) (x := C.x)
      (by exact_mod_cast hC.podd) (by exact_mod_cast hC.p1) hC.hm (by omega) hpC hxC
      (by have := hC.n21; omega)
  -- The low words of `f` and `g`.
  have low : ∀ {j : Nat} {y : Int}, sgn (C.n + 1) (wv s.mem C.B (slot C.w j) (C.n + 1)) = y →
      ((word s.mem C.B (slot C.w j)).toNat : Int) % 2 ^ 64 = y % 2 ^ 64 := fun {j y} h => by
    rw [← h, Divstep.sgn_mod64 hL (wv_lt _ _ _ _), wv_mod64 _ _ _ hL]
    exact Int.emod_eq_of_lt (by omega) (by have := (word s.mem C.B (slot C.w j)).isLt; omega)
  unfold batch
  rw [show ([Code.block (batchHead C.iV C.iU), rowP .v16 C.iV C.iU C.iT, rowP .v17 C.iV C.iU C.iU, shrP C.iT C.iV,
      shrP C.iU C.iU, rowP .v16 C.iX₂ C.iX₁ C.iT, rowP .v17 C.iX₂ C.iX₁ C.iX₁] ++ mredP C.iT C.iM C.iX₂ ++
      mredP C.iX₁ C.iM C.iX₁) = [Code.block (batchHead C.iV C.iU)] ++ ([rowP .v16 C.iV C.iU C.iT,
      rowP .v17 C.iV C.iU C.iU, shrP C.iT C.iV, shrP C.iU C.iU] ++ ([rowP .v16 C.iX₂ C.iX₁ C.iT,
      rowP .v17 C.iX₂ C.iX₁ C.iX₁] ++ mredP C.iT C.iM C.iX₂ ++ mredP C.iX₁ C.iM C.iX₁)) by simp]
  refine wp_seqs_append ?_ ?_ ?_
  · simp
  · simp
  simp only [seqs]
  refine WP.mono (batchHead_ok hI.scr hI.x0 hI.x11 hI.x12 hC.nw hC.w24 hC.hZ hC.hV hC.hU dbnd fodd hI.d
    (low hI.f) (low hI.g)) fun s₁ ⟨l1, l2, l3, l4, l5, l6, lv, h11, h12, h15, hm₁, k₁⟩ => ?_
  have ar : ∀ j, wv s₁.mem C.B (slot C.w j) = wv s.mem C.B (slot C.w j) := fun j => by rw [hm₁]
  refine wp_seqs_append ?_ ?_ ?_
  · simp
  · simp
  refine WP.mono (fgStage_ok (hI.scr.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans hI.x0) (h11.trans hI.x11)
    (h12.trans hI.x12) hC.n1 hC.nw hC.w24 hC.hZ hC.hV hC.hU hC.hT hC.dUV.symm hC.dVT hC.dUT buv bqr l3 l4 l5 l6
    (by rw [ar]; exact hI.f) (by rw [ar]; exact hI.g) bf bg ef eg) fun s₂ ⟨f₂, g₂, fr₂, k₂, v₂⟩ => ?_
  have k12 := k₁.trans k₂
  have keepFG : ∀ {j : Nat} {L : Nat}, j ≠ C.iT → j ≠ C.iU → j ≠ C.iV → L ≤ C.w + 2 → j < 16 →
      wv s₂.mem C.B (slot C.w j) L = wv s.mem C.B (slot C.w j) L := fun {j L} a b c hL' hj => by
    rw [fr₂.wv_eq (apart3 a b c hL' (by have := hC.nw; omega) (by have := hC.nw; omega)
      (by have := hC.nw; omega)) (by have := slot_lt (w := C.w) hj; omega), ar]
  have lmi : laneOf s₂ .v18 1 = C.mi := by rw [laneOf, v₂, ← laneOf, l2, hI.mi]
  have lv' : ∀ (r : VReg) (i : Nat), r = .v16 ∨ r = .v17 → laneOf s₂ r i = laneOf s₁ r i := fun r i _ => by
    rw [laneOf, v₂]
  obtain ⟨ra0, ra1, rb0, rb1⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat) (x := C.x) (by decide)
    (by exact_mod_cast hC.p1) hC.hm (k + 1)
  refine WP.mono (abStage_ok (hI.scr.congr k12.wr) ((k12.gpr .x0 (by decide)).trans hI.x0)
    ((k₂.gpr .x11 (by decide)).trans (h11.trans hI.x11)) ((k₂.gpr .x12 (by decide)).trans (h12.trans hI.x12))
    hC.n1 hC.nw hC.w24 hC.hZ hC.hX₂ hC.hX₁ hC.hT hC.hM hC.dX.symm hC.dX₂T hC.dX₁T hC.dX₂M hC.dX₁M hC.dMT.symm hC.pC
    buv bqr (by rw [lv' _ _ (.inl rfl)]; exact l3) (by rw [lv' _ _ (.inl rfl)]; exact l4)
    (by rw [lv' _ _ (.inr rfl)]; exact l5) (by rw [lv' _ _ (.inr rfl)]; exact l6) (by rw [lmi]; exact hC.hm)
    (by rw [keepFG hC.dMT hC.dUM.symm hC.dVM.symm (by have := hC.nw; omega) hC.hM]; exact hI.m)
    (by rw [keepFG hC.dX₂T hC.dUX₂.symm hC.dVX₂.symm (by have := hC.nw; omega) hC.hX₂]; exact hI.a)
    (by rw [keepFG hC.dX₁T hC.dUX₁.symm hC.dVX₁.symm (by have := hC.nw; omega) hC.hX₁]; exact hI.b)
    ⟨a0, a1⟩ ⟨b0, b1⟩ (by rw [lmi]; exact ea) (by rw [lmi]; exact eb) ⟨ra0, ra1⟩ ⟨rb0, rb1⟩) fun t ⟨a₃, b₃, fr₃, k₃, v₃⟩ => ?_
  have k13 := k12.trans k₃
  have keepAB : ∀ {j : Nat} {L : Nat}, j ≠ C.iT → j ≠ C.iX₂ → j ≠ C.iX₁ → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₂.mem C.B (slot C.w j) L := fun {j L} a b c hL' hj =>
    fr₃.wv_eq (apart3 a b c hL' (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (by have := slot_lt (w := C.w) hj; omega)
  have wid : ∀ {j : Nat} {L : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → L ≤ 8 * (C.w + 2) →
      ∃ r' ∈ C.ranges, r'.1 ≤ slot C.w j ∧ slot C.w j + L ≤ r'.1 + r'.2 := fun {j L} h hL' =>
    ⟨_, h, Nat.le_refl _, Nat.add_le_add_left hL' _⟩
  refine ⟨⟨hI.scr.congr k13.wr, (k13.gpr .x0 (by decide)).trans hI.x0,
    (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans (h11.trans hI.x11)),
    (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans (h12.trans hI.x12)),
    by rw [keepAB hC.dVT hC.dVX₂ hC.dVX₁ (by have := hC.nw; omega) hC.hV]; exact f₂,
    by rw [keepAB hC.dUT hC.dUX₂ hC.dUX₁ (by have := hC.nw; omega) hC.hU]; exact g₂, a₃, b₃,
    by rw [laneOf, v₃, v₂, ← laneOf, l1]; exact congrArg _ ed.symm,
    by rw [laneOf, v₃, v₂, ← laneOf, l2, hI.mi],
    by rw [keepAB hC.dMT hC.dX₂M.symm hC.dX₁M.symm (by have := hC.nw; omega) hC.hM,
      keepFG hC.dMT hC.dUM.symm hC.dVM.symm (by have := hC.nw; omega) hC.hM]; exact hI.m, ?_,
    ((hI.keep.trans k13).mono (by decide)), by rw [v₃, v₂, lv _ (by decide) (by decide) (by decide), hI.v19]⟩, ?_⟩
  · refine (hI.frm.trans (by rw [hm₁]; exact Frm.refl _ _ _)).trans ((Frm.widen fr₂ ?_).trans (Frm.widen fr₃ ?_))
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> refine wid (by simp [ICfg.ranges]) (by have := hC.nw; omega)
  · rw [k₃.gpr .x15 (by decide), k₂.gpr .x15 (by decide), h15]

/-- The `3 n + 2` batches, counted by `x15`. -/
theorem batches_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ 0 s)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 (3 * C.n + 2)) :
    WP isa (.loop (batch C.iV C.iU C.iX₂ C.iX₁ C.iT C.iM) (.nonzero .x .x15)) s (LInv C s₀ (3 * C.n + 2)) :=
  wp_countdown (N := 3 * C.n + 2) (by have := hC.n21; omega) (by omega) (LInv C s₀)
    (fun _ hj _ hI' _ => batch_ok hC hj hI') hI h15

end VG.Proof.Rsa.AArch64
