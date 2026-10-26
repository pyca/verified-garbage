module

public import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop
import VerifiedGarbage.Proof.MlKem.Arith
import Mathlib.Tactic.SplitIfs

/-! # Scalar tail without preinitializing unused output coefficients

Only the accepted prefix is represented. The sampler clears the suffix on
bounded failure, so rejection does not require redundant whole-polynomial
initialization before a successful pass.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8.Scalar
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Sample (cvW cvW_append cvW_last lt_q_arith sampleStepCap_eq)
variable {initial : List Zq}

/-- The coefficients are stored 32 bits apart, or with `w16` 16 bits apart; the names
without `W` are the 32-bit case. -/
structure LPreW (w16 : Bool) (N : Nat) (B : Nat → Byte) (bP aP : Addr) (s : State) : Prop where
  buf : ∀ p < 3 * N, s.mem (bP + BitVec.ofNat 64 p) = B p
  inb : ∀ p < 3 * N, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  ina : ∀ i < 256, InRegions s.wr (cAddr w16 aP i) 4
  disj : (⟨bP, 3 * N⟩ : Region).Disjoint (polyRegion aP)
  bound : N ≤ 280

abbrev LPre := LPreW false

/-- Only coefficients already accepted have prescribed contents. -/
def CoeffsW (w16 : Bool) (m : Mem) (p : Addr) (L : List Zq) : Prop :=
  ∀ i < L.length, coeffAtW (cw w16) m p i = cvW w16 L i

abbrev Coeffs := CoeffsW false

structure AccW (w16 : Bool) (aP : Addr) (s₀ : State) (L : List Zq) (u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  len : L.length ≤ 256
  x3 : u.gpr .x3 = cAddr w16 aP L.length
  x4 : (u.gpr .x4).toNat = 256 - L.length
  x9 : (u.gpr .x9).toNat = q
  coeffs : CoeffsW w16 u.mem aP L
  frame : Frame [polyRegion aP] s₀.mem u.mem

abbrev Acc := AccW false

theorem CoeffsW.reject {w16 : Bool} {m : Mem} {p : Addr} {L : List Zq} (h : CoeffsW w16 m p L)
    (hl : L.length < 256) (w : BitVec 32) (hw : w.toNat < 2 ^ 16) :
    CoeffsW w16 (m.writeW (cAddr w16 p L.length) w) p L := by
  intro i hi
  rw [coeffAtW_writeW32 m p (show i<256 by omega_arith) hl _ hw, ite_eq_right (by omega_arith),
    ite_eq_right (by omega_arith), h i hi]

theorem CoeffsW.accept {w16 : Bool} {m : Mem} {p : Addr} {L : List Zq} (h : CoeffsW w16 m p L)
    (hl : L.length < 256) {x : Zq} {w : BitVec 32} (hw : w=BitVec.ofNat 32 x.val) :
    CoeffsW w16 (m.writeW (cAddr w16 p L.length) w) p (L++[x]) := by
  intro i hi
  have hi' : i < L.length+1 := by simpa using hi
  have hx : x.val < 3329 := x.isLt
  have hw' : w.toNat = x.val := by rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  rw [coeffAtW_writeW32 m p (show i<256 by omega_arith) hl _ (by omega_arith)]
  by_cases he : L.length=i
  · subst i
    rw [ite_eq_left rfl,cvW_last,hw']
  · rw [ite_eq_right he,ite_eq_right (by omega_arith),h i (by omega_arith),←cvW_append L x (by omega_arith)]

theorem accept_ok {w16 : Bool} {aP : Addr} {s₀ : State}
    (hina : ∀ i < 256, InRegions s₀.wr (cAddr w16 aP i) 4)
    {L : List Zq} {u : State} (h : AccW w16 aP s₀ L u) (hlt : L.length < 256) {d : Reg}
    (hd : d ≠ .x13 ∧ d ≠ .x14) {v : Nat} (hv : (u.gpr d).toNat = v) (hv' : v < 2 ^ 12) :
    WP isa (.block (sampleAccept d w16)) u fun u' =>
      AccW w16 aP s₀ (if v < q then L ++ [ofNat v] else L) u' ∧
        Keep [.x3, .x4, .x13, .x14, .x15] u u' := by
  have hq : q = 3329 := rfl
  refine wp_sub fun u₁ h₁ e₁ => wp_lsr (by decide) fun u₂ h₂ e₂ => ?_
  have v14 : (u₂.gpr .x14).toNat = if v < q then 1 else 0 := by
    rw [e₂, e₁]
    exact lt_q_arith hv hv' h.x9
  have dv : (u₂.gpr d).toNat = v := by
    rw [h₂.gpr d (by simpa using hd.2), h₁.gpr d (by simpa using hd.1), hv]
  refine wp_strw (a := cAddr w16 aP L.length) (by decide)
    (by rw [h₂.gpr .x3 (by decide), h₁.gpr .x3 (by decide), h.x3, ptr_zero])
    (by rw [h₂.wr, h₁.wr, h.wr]; exact hina _ hlt) fun u₃ h₃ =>
    wp_lsl (by cases w16 <;> decide) fun u₄ h₄ e₄ => wp_add fun u₅ h₅ e₅ => wp_sub fun u₆ h₆ e₆ => wp_nil ?_
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).mono (rs' := [.x3, .x4, .x13, .x14, .x15]) (by decide)
  have m₆ : u₆.mem = u.mem.writeW (cAddr w16 aP L.length) ((u₂.gpr d).setWidth 32) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x14 : u₅.gpr .x14 = u₂.gpr .x14 := by
    rw [h₅.gpr .x14 (by decide), h₄.gpr .x14 (by decide), h₃.gpr]
  have x15 : u₄.gpr .x15 = BitVec.ofNat 64 (cs w16 * if v < q then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    cases w16 <;>
    · rw [e₄, toNat_lsl_n (by rw [h₃.gpr, v14]; split <;> decide), h₃.gpr, v14, BitVec.toNat_ofNat]
      split <;> decide
  have x3 : u₆.gpr .x3 = cAddr w16 aP (L.length + if v < q then 1 else 0) := by
    rw [h₆.gpr .x3 (by decide), e₅, h₄.gpr .x3 (by decide), h₃.gpr, h₂.gpr .x3 (by decide),
      h₁.gpr .x3 (by decide), h.x3, x15, cAddr_add]
  have c4 : (u₅.gpr .x4).toNat = 256 - L.length := by
    rw [h₅.gpr .x4 (by decide), h₄.gpr .x4 (by decide), h₃.gpr, h₂.gpr .x4 (by decide),
      h₁.gpr .x4 (by decide), h.x4]
  have x4 : (u₆.gpr .x4).toNat = 256 - L.length - if v < q then 1 else 0 := by
    rw [e₆, toNat_sub_n (by rw [x14, v14, c4]; split <;> omega_arith), c4, x14, v14]
  have fr : Frame [polyRegion aP] s₀.mem u₆.mem := by
    rw [m₆]
    exact h.frame.writeW (List.mem_singleton_self _) _ (cAddr_contains4 w16 _ hlt)
  have acc : ∀ L' : List Zq, L'.length = L.length + (if v < q then 1 else 0) →
      CoeffsW w16 u₆.mem aP L' → AccW w16 aP s₀ L' u₆ := fun L' hl hc =>
    ⟨by rw [k₆.rd, h.rd], by rw [k₆.wr, h.wr], by rw [k₆.sp, h.sp], by rw [hl]; split <;> omega_arith,
      by rw [x3, hl], by rw [x4, hl]; split <;> omega_arith, by rw [k₆.get .x9, h.x9], hc, fr⟩
  refine ⟨acc _ ?_ ?_, k₆⟩
  · split <;> simp
  · rw [m₆]
    by_cases hvq : v < q
    · rw [ite_eq_left hvq]
      exact h.coeffs.accept hlt (by rw [setWidth32_of_toNat dv, val_ofNat, Nat.mod_eq_of_lt hvq])
    · rw [ite_eq_right hvq]
      exact h.coeffs.reject hlt _ (by rw [setWidth32_of_toNat dv]; simp; omega_arith)

/-- The first candidate of chunk `t`. -/
abbrev d₁ (B : Nat → Byte) (t : Nat) : Nat :=
  (B (3 * t)).toNat + 256 * ((B (3 * t + 1)).toNat % 16)

/-- The second candidate of chunk `t`. -/
abbrev d₂ (B : Nat → Byte) (t : Nat) : Nat :=
  (B (3 * t + 1)).toNat / 16 + 16 * (B (3 * t + 2)).toNat

/-- The coefficients accepted after `t` iterations. -/
abbrev LA (initial : List Zq) (B : Nat → Byte) (t : Nat) : List Zq := sampleAfter initial B t

/-- The registers the loop changes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14, .x15]

/-- After `t` of `N` iterations. -/
structure InvW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr) (s₀ : State)
    (t : Nat) (u : State) : Prop where
  acc : AccW w16 aP s₀ (LA initial B t) u
  keep : Keep lRegs s₀ u
  x2 : u.gpr .x2 = bP + BitVec.ofNat 64 (3 * t)
  x5 : (u.gpr .x5).toNat = N - t
  x10 : (u.gpr .x10).toNat = 15

abbrev Inv := InvW false

theorem sampleStepCap_eq (L : List Zq) (c₀ c₁ c₂ : Byte) (hL : L.length ≠ n) :
    sampleStepCap L c₀ c₁ c₂ =
      let a := if c₀.toNat + 256 * (c₁.toNat % 16) < q
        then L ++ [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else L
      if c₁.toNat / 16 + 16 * c₂.toNat < q ∧ a.length < n
        then a ++ [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else a := by
  unfold sampleStepCap sampleStep
  rw [ite_eq_right hL]

theorem acc_keep {w16 : Bool} {aP : Addr} {s₀ : State} {L : List Zq} {u u' : State}
    (h : AccW w16 aP s₀ L u)
    {rs : List Reg} (hk : Keep rs u u') (hm : u'.mem = u.mem) (h3 : Reg.x3 ∉ rs := by decide)
    (h4 : Reg.x4 ∉ rs := by decide) (h9 : Reg.x9 ∉ rs := by decide) : AccW w16 aP s₀ L u' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], h.len, by rw [hk.get .x3 h3, h.x3],
    by rw [hk.get .x4 h4, h.x4], by rw [hk.get .x9 h9, h.x9], by rw [hm]; exact h.coeffs,
    by rw [hm]; exact h.frame⟩

/-- The candidates of chunk `t`. -/
theorem chunk_ok {w16 : Bool} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s₀ : State}
    (hp : LPreW w16 N B bP aP s₀)
    {t : Nat} (ht : t < N) {u : State} (h : InvW w16 initial N B bP aP s₀ t u) :
    WP isa (.block sampleChunk) u fun u' => AccW w16 aP s₀ (LA initial B t) u' ∧
      Keep [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13] u u' ∧
      u'.gpr .x2 = bP + BitVec.ofNat 64 (3 * (t + 1)) ∧ (u'.gpr .x5).toNat = N - (t + 1) ∧
      (u'.gpr .x11).toNat = d₁ B t ∧ (u'.gpr .x12).toNat = d₂ B t := by
  have hin : ∀ p < 3 * N, InRegions (u.rd ++ u.wr) (bP + BitVec.ofNat 64 p) 1 := fun p hp' => by
    rw [h.acc.rd, h.acc.wr]; exact hp.inb p hp'
  have hb : ∀ p < 3 * N, (u.mem (bP + BitVec.ofNat 64 p)).toNat = (B p).toNat := fun p hp' => by
    rw [byte_frame h.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by have := hp.bound; omega_arith) hp', hp.buf p hp']
  have a : ∀ r, u.gpr .x2 + BitVec.ofNat 64 r = bP + BitVec.ofNat 64 (3 * t + r) := fun r => by
    rw [h.x2, ptr_add]
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 0)) (by decide) (a 0) (hin _ (by omega_arith))
    fun u₁ h₁ e₁ => ?_
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 1)) (by decide) (by rw [h₁.get .x2, a])
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega_arith)) fun u₂ h₂ e₂ => ?_
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 2)) (by decide)
    (by rw [h₂.get .x2, h₁.get .x2, a]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hin _ (by omega_arith))
    fun u₃ h₃ e₃ => ?_
  refine wp_addImm (by decide) fun u₄ h₄ e₄ => wp_subImm (by decide) fun u₅ h₅ e₅ =>
    wp_and fun u₆ h₆ e₆ => wp_lsl (by decide) fun u₇ h₇ e₇ => wp_add fun u₈ h₈ e₈ =>
    wp_lsr (by decide) fun u₉ h₉ e₉ => wp_lsl (by decide) fun u₁₀ h₁₀ e₁₀ =>
    wp_add fun u₁₁ h₁₁ e₁₁ => wp_nil ?_
  have l0 := (B (3 * t)).isLt
  have l1 := (B (3 * t + 1)).isLt
  have l2 := (B (3 * t + 2)).isLt
  have v6 : (u₅.gpr .x6).toNat = (B (3 * t)).toNat := by
    rw [h₅.get .x6, h₄.get .x6, h₃.get .x6, h₂.get .x6, e₁, toNat_byte, Nat.add_zero, hb _ (by omega_arith)]
  have v7 : (u₅.gpr .x7).toNat = (B (3 * t + 1)).toNat := by
    rw [h₅.get .x7, h₄.get .x7, h₃.get .x7, e₂, toNat_byte, h₁.mem, hb _ (by omega_arith)]
  have v8 : (u₅.gpr .x8).toNat = (B (3 * t + 2)).toNat := by
    rw [h₅.get .x8, h₄.get .x8, e₃, toNat_byte, h₂.mem, h₁.mem, hb _ (by omega_arith)]
  have k₁₁ := (((((((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep
  have m₁₁ : u₁₁.mem = u.mem := by
    rw [h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨acc_keep h.acc (k₁₁.mono (rs' := [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13]) (by decide))
    m₁₁, k₁₁.mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [h₁₁.get .x2, h₁₀.get .x2, h₉.get .x2, h₈.get .x2, h₇.get .x2, h₆.get .x2, h₅.get .x2, e₄,
      h₃.get .x2, h₂.get .x2, h₁.get .x2, h.x2, ptr_add, show 3 * t + 3 = 3 * (t + 1) by omega_arith]
  · have c5 : (u₄.gpr .x5).toNat = N - t := by
      rw [h₄.get .x5, h₃.get .x5, h₂.get .x5, h₁.get .x5, h.x5]
    rw [h₁₁.get .x5, h₁₀.get .x5, h₉.get .x5, h₈.get .x5, h₇.get .x5, h₆.get .x5, e₅,
      toNat_sub_n (by rw [c5]; simp; omega_arith), c5]
    simp
    omega_arith
  · have c6 : (u₆.gpr .x11).toNat = (B (3 * t + 1)).toNat % 16 := by
      rw [e₆, toNat_and_mask _ _ (k := 4) (by
        rw [h₅.get .x10, h₄.get .x10, h₃.get .x10, h₂.get .x10, h₁.get .x10, h.x10]), v7]
    have c7 : (u₇.gpr .x11).toNat = (B (3 * t + 1)).toNat % 16 * 256 := by
      rw [e₇, toNat_lsl_n (by rw [c6]; omega_arith), c6]
    rw [h₁₁.get .x11, h₁₀.get .x11, h₉.get .x11, e₈,
      toNat_add_n (by rw [c7, h₇.get .x6, h₆.get .x6, v6]; omega_arith), c7, h₇.get .x6, h₆.get .x6, v6]
    simp only [d₁]
    omega_arith
  · have c9 : (u₉.gpr .x12).toNat = (B (3 * t + 1)).toNat / 16 := by
      rw [e₉, toNat_lsr, h₈.get .x7, h₇.get .x7, h₆.get .x7, v7]
    have c10 : (u₁₀.gpr .x13).toNat = (B (3 * t + 2)).toNat * 16 := by
      rw [e₁₀, toNat_lsl_n (by rw [h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]; omega_arith),
        h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]
    rw [e₁₁, toNat_add_n (by rw [h₁₀.get .x12, c9, c10]; omega_arith), h₁₀.get .x12, c9, c10]
    simp only [d₂]
    omega_arith

/-- Whether the candidates are accepted: nothing once there are 256
coefficients. -/
theorem tail_ok {w16 : Bool} {aP : Addr} {s₀ : State}
    (hina : ∀ i < 256, InRegions s₀.wr (cAddr w16 aP i) 4)
    {L : List Zq} {u : State} (h : AccW w16 aP s₀ L u) {c₀ c₁ c₂ : Byte}
    (h11 : (u.gpr .x11).toNat = c₀.toNat + 256 * (c₁.toNat % 16))
    (h12 : (u.gpr .x12).toNat = c₁.toNat / 16 + 16 * c₂.toNat) :
    WP isa (.ite (.zero .x .x4) (.block [])
      (.seq (.block (sampleAccept .x11 w16)) (.ite (.zero .x .x4) (.block [])
        (.block (sampleAccept .x12 w16))))) u
      fun u' => AccW w16 aP s₀ (sampleStepCap L c₀ c₁ c₂) u' ∧ Keep [.x3, .x4, .x13, .x14, .x15] u u' := by
  have l0 := c₀.isLt
  have l1 := c₁.isLt
  have l2 := c₂.isLt
  have hn : n = 256 := rfl
  have hL := h.len
  refine WP.ite (u.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, h.x4] at hz
    rw [sampleStepCap_full (by omega_arith)]
    exact wp_nil ⟨h, Keep.refl _ _⟩
  rw [eq_zero_iff, decide_eq_false_iff_not, h.x4] at hz
  rw [sampleStepCap_eq L c₀ c₁ c₂ (by omega_arith)]
  refine WP.seq (WP.mono (accept_ok hina h (by omega_arith) (d := .x11) (by decide) h11 (by omega_arith))
    fun u₂ ⟨a₂, k₂⟩ => ?_)
  have hl1 := a₂.len
  refine WP.ite (u₂.gpr .x4 == 0) (eval_zero _ _) (fun hz' => ?_) (fun hz' => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, a₂.x4] at hz'
    dsimp only
    rw [ite_eq_right (fun hc => by omega_arith)]
    exact wp_nil ⟨a₂, k₂⟩
  · rw [eq_zero_iff, decide_eq_false_iff_not, a₂.x4] at hz'
    refine WP.mono (accept_ok hina a₂ (by omega_arith) (d := .x12) (v := c₁.toNat / 16 + 16 * c₂.toNat)
      (by decide)
      (by rw [k₂.get .x12]; exact h12) (by omega_arith)) fun u₃ ⟨a₃, k₃⟩ => ⟨?_, (k₂.trans k₃).mono⟩
    dsimp only
    by_cases hd : c₁.toNat / 16 + 16 * c₂.toNat < q
    · rw [ite_eq_left ⟨hd, by omega_arith⟩]; rw [ite_eq_left hd] at a₃; exact a₃
    · rw [ite_eq_right (fun hc => hd hc.1)]; rw [ite_eq_right hd] at a₃; exact a₃

/-- One iteration. -/
theorem body_ok {w16 : Bool} {N : Nat} {B : Nat → Byte} {bP aP : Addr} {s₀ : State}
    (hp : LPreW w16 N B bP aP s₀)
    {t : Nat} (ht : t < N) {u : State} (h : InvW w16 initial N B bP aP s₀ t u) :
    WP isa (sampleBody w16) u fun u' =>
      InvW w16 initial N B bP aP s₀ (t + 1) u' ∧ ((u'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ N) := by
  refine WP.seq (WP.mono (chunk_ok hp ht h) fun u₁ ⟨a₁, k₁, x2₁, x5₁, x11₁, x12₁⟩ =>
    WP.mono (tail_ok hp.ina a₁ x11₁ x12₁) fun u' ⟨a', k'⟩ => ?_)
  have x5' : (u'.gpr .x5).toNat = N - (t + 1) := by rw [k'.get .x5, x5₁]
  refine ⟨⟨a', ((h.keep.trans k₁).trans k').mono (by decide), by rw [k'.get .x2, x2₁], x5',
    by rw [k'.get .x10, k₁.get .x10, h.x10]⟩, by rw [x5']; omega_arith⟩


end VG.Proof.MlKem.AArch64.Rej8.Scalar
