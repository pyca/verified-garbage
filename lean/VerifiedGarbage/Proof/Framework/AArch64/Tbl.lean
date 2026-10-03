import VerifiedGarbage.Impl.Tbl.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# AArch64: table lookups with `tbl`

Byte `k` of the table registers (`tbyte`) is lane `k % 16` of `treg (k / 16)`.
`select_run`: with an index in each lane of `v0` (and it XORed with 64, 128
and 192 in `v1`, `v2`, `v3`), `select` leaves the table's byte at each index
in that lane of `v0`.
-/

namespace VG.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Tbl.AArch64

/-- Byte `k` of the table registers. -/
def tbyte (v : VReg → BitVec 128) (k : Nat) : BitVec 8 := vbyte (v (treg (k / 16))) (k % 16)

theorem treg_quarter : ∀ q < 4, ∀ k < 4,
    Nat.repeat VReg.succ k (quarter q) = treg (4 * q + k) := by
  decide

theorem treg_inj : ∀ a < 16, ∀ b < 16, treg a = treg b → a = b := by decide

/-- The vector registers outside the table. -/
theorem treg_ne : ∀ a < 16, treg a ≠ .v0 ∧ treg a ≠ .v1 ∧ treg a ≠ .v2 ∧ treg a ≠ .v3 ∧
    treg a ≠ .v4 ∧ treg a ≠ .v5 := by decide

/-- The table byte that a quarter's `tbl` reads, for an index in the quarter. -/
theorem tableByte_quarter (v : VReg → BitVec 128) {q : Nat} (hq : q < 4) {idx : Nat}
    (hi : idx < 64) : tableByte v (quarter q) idx = tbyte v (64 * q + idx) := by
  simp only [tableByte, tbyte, treg_quarter q hq _ (by omega : idx / 16 < 4)]
  rw [show (64 * q + idx) / 16 = 4 * q + idx / 16 by omega,
    show (64 * q + idx) % 16 = idx % 16 by omega]

/-- The quarter of each byte, and its index there. -/
theorem xor_quarter : ∀ x < 256, ∀ q < 4,
    (x ^^^ 64 * q < 64 ↔ x / 64 = q) ∧ (x / 64 = q → x ^^^ 64 * q = x - 64 * q) := by
  decide +kernel

/-! ## Byte lanes -/

/-- `b` in every byte. -/
def bc (b : BitVec 8) : BitVec 128 := ofVBytes fun _ => b

theorem vbyte_ext {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true,
    Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

theorem vbyte_bc (b : BitVec 8) {e : Nat} (he : e < 16) : vbyte (bc b) e = b :=
  vbyte_ofVBytes _ he

theorem vbyte_xor (x y : BitVec 128) (e : Nat) : vbyte (x ^^^ y) e = vbyte x e ^^^ vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_or (x y : BitVec 128) (e : Nat) : vbyte (x ||| y) e = vbyte x e ||| vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem exec_vop' (s : State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- Only the vector registers `ds` change. -/
def VOnly (ds : List VReg) (s s' : State) : Prop :=
  s' = { s with v := s'.v } ∧ ∀ r, r ∉ ds → s'.v r = s.v r

theorem VOnly.refl (ds : List VReg) (s : State) : VOnly ds s s := ⟨rfl, fun _ _ => rfl⟩

theorem VOnly.trans {ds : List VReg} {a b c : State} (h₁ : VOnly ds a b) (h₂ : VOnly ds b c) :
    VOnly ds a c := by
  refine ⟨?_, fun r hr => (h₂.2 r hr).trans (h₁.2 r hr)⟩
  rw [h₂.1, h₁.1]

theorem VOnly.setV (s : State) {d : VReg} {ds : List VReg} (hd : d ∈ ds) (x : BitVec 128) :
    VOnly ds s (s.setV d x) := by
  refine ⟨rfl, fun r hr => ?_⟩
  have : r ≠ d := fun e => hr (e ▸ hd)
  exact v_setV_of_ne _ _ this

theorem VOnly.gpr {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.gpr = s.gpr := by
  rw [h.1]
theorem VOnly.mem {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.mem = s.mem := by
  rw [h.1]
theorem VOnly.rd {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.rd = s.rd := by
  rw [h.1]
theorem VOnly.wr {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.wr = s.wr := by
  rw [h.1]

/-- The table is outside `v0`–`v5`. -/
theorem tbyte_congr {v w : VReg → BitVec 128}
    (h : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → w r = v r)
    (k : Nat) (hk : k < 256) : tbyte w k = tbyte v k := by
  have hn := treg_ne (k / 16) (by omega)
  simp only [tbyte, h _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2]

/-- The table is in the table registers. -/
theorem tbyte_congr' {v w : VReg → BitVec 128} (h : ∀ a < 16, w (treg a) = v (treg a))
    (k : Nat) (hk : k < 256) : tbyte w k = tbyte v k := by
  simp only [tbyte, h _ (by omega : k / 16 < 16)]

/-- The table registers are `v16`–`v31`. -/
theorem treg_ne8 : ∀ a < 16, treg a ≠ .v0 ∧ treg a ≠ .v1 ∧ treg a ≠ .v2 ∧ treg a ≠ .v3 ∧
    treg a ≠ .v4 ∧ treg a ≠ .v5 ∧ treg a ≠ .v6 ∧ treg a ≠ .v7 := by decide

/-! ## Selection -/

/-- What a quarter's `tbl` leaves in a byte, at index `idx`. -/
def qbyte (T : Nat → BitVec 8) (q idx : Nat) : BitVec 8 :=
  if idx < 64 then T (64 * q + idx) else 0

theorem vbyte_tbl (v : VReg → BitVec 128) {q : Nat} (hq : q < 4) (m : BitVec 128) {e : Nat}
    (he : e < 16) :
    vbyte (ofVBytes fun i => if (vbyte m i).toNat < 16 * 4 then
        tableByte v (quarter q) (vbyte m i).toNat else 0) e =
      qbyte (tbyte v) q (vbyte m e).toNat := by
  rw [vbyte_ofVBytes _ he, qbyte]
  split
  · rename_i h; rw [tableByte_quarter _ hq (by omega)]
  · rfl

theorem or_zero8 (y : BitVec 8) : y ||| 0 = y := by simp
theorem zero_or8 (y : BitVec 8) : 0 ||| y = y := by simp

theorem toNat_xor_lit (X : BitVec 8) (k : Nat) (hk : k < 256) :
    (X ^^^ BitVec.ofNat 8 k).toNat = X.toNat ^^^ k := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- The four quarters' bytes, combined as `select true` combines them, are
the byte at the index. -/
theorem quarters_byte (T : Nat → BitVec 8) (X : BitVec 8) :
    (qbyte T 0 X.toNat ||| qbyte T 1 (X.toNat ^^^ 64)) |||
      (qbyte T 2 (X.toNat ^^^ 128) ||| qbyte T 3 (X.toNat ^^^ 192)) = T X.toNat := by
  have hX := X.isLt
  have q := xor_quarter X.toNat hX
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  obtain ⟨h2, e2⟩ := q 2 (by decide)
  obtain ⟨h3, e3⟩ := q 3 (by decide)
  simp only [Nat.mul_one, show 64 * 2 = 128 by rfl, show 64 * 3 = 192 by rfl] at h1 h2 h3 e1 e2 e3
  simp only [qbyte]
  have n1 : X.toNat / 64 ≠ 1 → ¬ (X.toNat ^^^ 64 < 64) := fun h h' => h (h1.mp h')
  have n2 : X.toNat / 64 ≠ 2 → ¬ (X.toNat ^^^ 128 < 64) := fun h h' => h (h2.mp h')
  have n3 : X.toNat / 64 ≠ 3 → ¬ (X.toNat ^^^ 192 < 64) := fun h h' => h (h3.mp h')
  rcases (by omega : X.toNat / 64 = 0 ∨ X.toNat / 64 = 1 ∨ X.toNat / 64 = 2 ∨ X.toNat / 64 = 3)
    with h | h | h | h
  · simp only [show X.toNat < 64 by omega, n1 (by omega), n2 (by omega), n3 (by omega), ite_true,
      ite_false, Nat.mul_zero, Nat.zero_add, or_zero8]
  · simp only [show ¬ X.toNat < 64 by omega, h1.mpr h, n2 (by omega), n3 (by omega), ite_true,
      ite_false, zero_or8, or_zero8]
    rw [e1 h]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), h2.mpr h, n3 (by omega), ite_true,
      ite_false, zero_or8, or_zero8]
    rw [e2 h]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), n2 (by omega), h3.mpr h, ite_true,
      ite_false, zero_or8]
    rw [e3 h]
    exact congrArg T (by omega)

/-- The two halves' bytes, for an index below 128. -/
theorem halves_byte (T : Nat → BitVec 8) (X : BitVec 8) (hX : X.toNat < 128) :
    qbyte T 0 X.toNat ||| qbyte T 1 (X.toNat ^^^ 64) = T X.toNat := by
  have q := xor_quarter X.toNat X.isLt
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  simp only [Nat.mul_one] at h1 e1
  simp only [qbyte]
  rcases (by omega : X.toNat / 64 = 0 ∨ X.toNat / 64 = 1) with h | h
  · have n1 : ¬ (X.toNat ^^^ 64 < 64) := fun h' => by have := h1.mp h'; omega
    simp only [show X.toNat < 64 by omega, n1, ite_true, ite_false, Nat.mul_zero, Nat.zero_add,
      or_zero8]
  · simp only [show ¬ X.toNat < 64 by omega, h1.mpr h, ite_true, ite_false, zero_or8]
    rw [e1 h]
    exact congrArg T (by omega)

/-- `select true`: the table byte at each lane's index. -/
theorem select_full_run {s : State} (I : Nat → BitVec 8)
    (h0 : ∀ e < 16, vbyte (s.v .v0) e = I e)
    (h1 : ∀ e < 16, vbyte (s.v .v1) e = I e ^^^ 64)
    (h2 : ∀ e < 16, vbyte (s.v .v2) e = I e ^^^ 128)
    (h3 : ∀ e < 16, vbyte (s.v .v3) e = I e ^^^ 192) :
    ∃ s', runBlock isa (select true) s = some s' ∧
      (∀ e < 16, vbyte (s'.v .v0) e = tbyte s.v (I e).toNat) ∧
      VOnly [.v0, .v1, .v2, .v3] s s' := by
  let T := tbyte s.v
  let f (q : Nat) (m : BitVec 128) (st : State) : BitVec 128 :=
    ofVBytes fun i => if (vbyte m i).toNat < 16 * 4 then
      tableByte st.v (quarter q) (vbyte m i).toNat else 0
  let s₁ := s.setV .v0 (f 0 (s.v .v0) s)
  let s₂ := s₁.setV .v1 (f 1 (s₁.v .v1) s₁)
  let s₃ := s₂.setV .v2 (f 2 (s₂.v .v2) s₂)
  let s₄ := s₃.setV .v3 (f 3 (s₃.v .v3) s₃)
  let s₅ := s₄.setV .v2 (s₄.v .v2 ||| s₄.v .v3)
  let s₆ := s₅.setV .v0 (s₅.v .v0 ||| s₅.v .v1)
  let s₇ := s₆.setV .v0 (s₆.v .v0 ||| s₆.v .v2)
  have o₁ : VOnly [.v0, .v1, .v2, .v3] s s₁ := VOnly.setV _ (by simp) _
  have o₂ : VOnly [.v0, .v1, .v2, .v3] s s₂ := o₁.trans (VOnly.setV _ (by simp) _)
  have o₃ : VOnly [.v0, .v1, .v2, .v3] s s₃ := o₂.trans (VOnly.setV _ (by simp) _)
  have o₄ : VOnly [.v0, .v1, .v2, .v3] s s₄ := o₃.trans (VOnly.setV _ (by simp) _)
  have o₅ : VOnly [.v0, .v1, .v2, .v3] s s₅ := o₄.trans (VOnly.setV _ (by simp) _)
  have o₆ : VOnly [.v0, .v1, .v2, .v3] s s₆ := o₅.trans (VOnly.setV _ (by simp) _)
  have o₇ : VOnly [.v0, .v1, .v2, .v3] s s₇ := o₆.trans (VOnly.setV _ (by simp) _)
  have tab : ∀ st, VOnly [.v0, .v1, .v2, .v3] s st → ∀ k < 256, tbyte st.v k = T k := by
    intro st h k hk
    exact tbyte_congr (fun r a b c d _ _ => h.2 r (by simp [a, b, c, d])) k hk
  have hf : ∀ q st, q < 4 → VOnly [.v0, .v1, .v2, .v3] s st → ∀ (X : BitVec 8) (m : BitVec 128),
      ∀ e < 16, vbyte m e = X ^^^ BitVec.ofNat 8 (64 * q) →
      vbyte (f q m st) e = qbyte T q (X.toNat ^^^ 64 * q) := by
    intro q st hq ho X m e he hm
    rw [vbyte_tbl st.v hq m he, hm, toNat_xor_lit _ _ (by omega)]
    simp only [qbyte]
    split
    · exact tab st ho _ (by omega)
    · rfl
  have y₁ : ∀ e < 16, vbyte (s₁.v .v0) e = qbyte T 0 (I e).toNat := by
    intro e he
    rw [show s₁.v .v0 = f 0 (s.v .v0) s from v_setV_self _ _ _]
    simpa using hf 0 s (by decide) (VOnly.refl _ _) (I e) _ e he (by rw [h0 e he]; simp)
  have y₂ : ∀ e < 16, vbyte (s₂.v .v1) e = qbyte T 1 ((I e).toNat ^^^ 64) := by
    intro e he
    rw [show s₂.v .v1 = f 1 (s₁.v .v1) s₁ from v_setV_self _ _ _]
    have := hf 1 s₁ (by decide) o₁ (I e) (s₁.v .v1) e he (by
      simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v0), h1 e he]; rfl)
    simpa using this
  have y₃ : ∀ e < 16, vbyte (s₃.v .v2) e = qbyte T 2 ((I e).toNat ^^^ 128) := by
    intro e he
    rw [show s₃.v .v2 = f 2 (s₂.v .v2) s₂ from v_setV_self _ _ _]
    have := hf 2 s₂ (by decide) o₂ (I e) (s₂.v .v2) e he (by
      simp only [s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v1),
        v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v0), h2 e he]; rfl)
    simpa using this
  have y₄ : ∀ e < 16, vbyte (s₄.v .v3) e = qbyte T 3 ((I e).toNat ^^^ 192) := by
    intro e he
    rw [show s₄.v .v3 = f 3 (s₃.v .v3) s₃ from v_setV_self _ _ _]
    have := hf 3 s₃ (by decide) o₃ (I e) (s₃.v .v3) e he (by
      simp only [s₃, s₂, s₁, v_setV_of_ne _ _ (by decide : VReg.v3 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v3 ≠ .v1),
        v_setV_of_ne _ _ (by decide : VReg.v3 ≠ .v0), h3 e he]; rfl)
    simpa using this
  refine ⟨s₇, ?_, ?_, o₇⟩
  · have e₁ : exec (.vop (.tblN false 4 .v0 (quarter 0) .v0)) s = some s₁ := rfl
    have e₂ : exec (.vop (.tblN false 4 .v1 (quarter 1) .v1)) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.tblN false 4 .v2 (quarter 2) .v2)) s₂ = some s₃ := rfl
    have e₄ : exec (.vop (.tblN false 4 .v3 (quarter 3) .v3)) s₃ = some s₄ := rfl
    have e₅ : exec (.vop (.logic .orr .v2 .v2 .v3)) s₄ = some s₅ := rfl
    have e₆ : exec (.vop (.logic .orr .v0 .v0 .v1)) s₅ = some s₆ := rfl
    have e₇ : exec (.vop (.logic .orr .v0 .v0 .v2)) s₆ = some s₇ := rfl
    simp only [select, ite_true, List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some,
      runBlock_cons, e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_nil]
  · intro e he
    have a₆ : s₆.v .v0 = s₄.v .v0 ||| s₄.v .v1 := by
      simp only [s₆, s₅, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2)]
    have b₆ : s₆.v .v2 = s₄.v .v2 ||| s₄.v .v3 := by
      simp only [s₆, s₅, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v0)]
    have a₄ : s₄.v .v0 = s₁.v .v0 := by
      simp only [s₄, s₃, s₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
    have b₄ : s₄.v .v1 = s₂.v .v1 := by
      simp only [s₄, s₃, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2)]
    have c₄ : s₄.v .v2 = s₃.v .v2 := by
      simp only [s₄, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)]
    have r₇ : s₇.v .v0 = s₆.v .v0 ||| s₆.v .v2 := v_setV_self _ _ _
    rw [r₇, a₆, b₆, a₄, b₄, c₄, vbyte_or, vbyte_or, vbyte_or, y₁ e he, y₂ e he, y₃ e he,
      y₄ e he]
    exact quarters_byte T (I e)

/-- `select false`: the table byte at each lane's index, for indices below 128. -/
theorem select_half_run {s : State} (I : Nat → BitVec 8) (hI : ∀ e < 16, (I e).toNat < 128)
    (h0 : ∀ e < 16, vbyte (s.v .v0) e = I e)
    (h1 : ∀ e < 16, vbyte (s.v .v1) e = I e ^^^ 64) :
    ∃ s', runBlock isa (select false) s = some s' ∧
      (∀ e < 16, vbyte (s'.v .v0) e = tbyte s.v (I e).toNat) ∧
      VOnly [.v0, .v1, .v2, .v3] s s' := by
  let T := tbyte s.v
  let f (q : Nat) (m : BitVec 128) (st : State) : BitVec 128 :=
    ofVBytes fun i => if (vbyte m i).toNat < 16 * 4 then
      tableByte st.v (quarter q) (vbyte m i).toNat else 0
  let s₁ := s.setV .v0 (f 0 (s.v .v0) s)
  let s₂ := s₁.setV .v1 (f 1 (s₁.v .v1) s₁)
  let s₃ := s₂.setV .v0 (s₂.v .v0 ||| s₂.v .v1)
  have o₁ : VOnly [.v0, .v1, .v2, .v3] s s₁ := VOnly.setV _ (by simp) _
  have o₂ : VOnly [.v0, .v1, .v2, .v3] s s₂ := o₁.trans (VOnly.setV _ (by simp) _)
  have o₃ : VOnly [.v0, .v1, .v2, .v3] s s₃ := o₂.trans (VOnly.setV _ (by simp) _)
  have tab : ∀ st, VOnly [.v0, .v1, .v2, .v3] s st → ∀ k < 256, tbyte st.v k = T k := by
    intro st h k hk
    exact tbyte_congr (fun r a b c d _ _ => h.2 r (by simp [a, b, c, d])) k hk
  have hf : ∀ q st, q < 4 → VOnly [.v0, .v1, .v2, .v3] s st → ∀ (X : BitVec 8) (m : BitVec 128),
      ∀ e < 16, vbyte m e = X ^^^ BitVec.ofNat 8 (64 * q) →
      vbyte (f q m st) e = qbyte T q (X.toNat ^^^ 64 * q) := by
    intro q st hq ho X m e he hm
    rw [vbyte_tbl st.v hq m he, hm, toNat_xor_lit _ _ (by omega)]
    simp only [qbyte]
    split
    · exact tab st ho _ (by omega)
    · rfl
  have y₁ : ∀ e < 16, vbyte (s₁.v .v0) e = qbyte T 0 (I e).toNat := by
    intro e he
    rw [show s₁.v .v0 = f 0 (s.v .v0) s from v_setV_self _ _ _]
    simpa using hf 0 s (by decide) (VOnly.refl _ _) (I e) _ e he (by rw [h0 e he]; simp)
  have y₂ : ∀ e < 16, vbyte (s₂.v .v1) e = qbyte T 1 ((I e).toNat ^^^ 64) := by
    intro e he
    rw [show s₂.v .v1 = f 1 (s₁.v .v1) s₁ from v_setV_self _ _ _]
    have := hf 1 s₁ (by decide) o₁ (I e) (s₁.v .v1) e he (by
      simp only [s₁, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v0), h1 e he]; rfl)
    simpa using this
  refine ⟨s₃, ?_, ?_, o₃⟩
  · have e₁ : exec (.vop (.tblN false 4 .v0 (quarter 0) .v0)) s = some s₁ := rfl
    have e₂ : exec (.vop (.tblN false 4 .v1 (quarter 1) .v1)) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.logic .orr .v0 .v0 .v1)) s₂ = some s₃ := rfl
    simp only [select, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.append_nil]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · intro e he
    have a₂ : s₂.v .v0 = s₁.v .v0 := by
      simp only [s₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
    have r₃ : s₃.v .v0 = s₂.v .v0 ||| s₂.v .v1 := v_setV_self _ _ _
    rw [r₃, a₂, vbyte_or, y₁ e he, y₂ e he]
    exact halves_byte T (I e) (hI e he)


/-! ## Blocks -/

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  induction a generalizing s with
  | nil => cases h₁; exact h₂
  | cons i is ih =>
    show (exec i s).bind (runBlock isa (is ++ b)) = some s₂
    cases he : exec i s with
    | none => rw [runBlock_cons, he] at h₁; cases h₁
    | some u =>
      rw [runBlock_cons, he, runStep_some] at h₁
      exact ih h₁

/-- A block that writes no vector register keeps them. -/
theorem runBlock_v {is : List Instr} {s s' : State}
    (h : is.all (fun i => vdstOf i == none) = true) (hr : runBlock isa is s = some s') :
    s'.v = s.v := by
  induction is generalizing s with
  | nil => cases hr; rfl
  | cons i is ih =>
    have hi := List.all_eq_true.mp h i (by simp)
    have his : is.all (fun i => vdstOf i == none) = true :=
      List.all_eq_true.mpr fun j hj => List.all_eq_true.mp h j (List.mem_cons_of_mem _ hj)
    cases he : exec i s with
    | none => rw [runBlock_cons, he] at hr; cases hr
    | some u =>
      rw [runBlock_cons, he, runStep_some] at hr
      rw [ih his hr]
      funext r
      exact exec_vec (by simp only [beq_iff_eq] at hi; rw [hi]; simp) he

/-! ## Constants and tables from immediates -/

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ (∀ g, g ≠ r → t.gpr g = s.gpr g) ∧
      t = { s with gpr := t.gpr } := by
  refine WP.of_runBlock ⟨_, rfl, ?_, fun g hg => ?_, rfl⟩
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, hg]

theorem ofVDwords_halves (x : BitVec 128) : ofVDwords (x.extractLsb' 0 64) (x.extractLsb' 64 64) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · simp only [h, ite_false, show i - 64 < 64 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem exec_eorv (s : State) (d n m : VReg) :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_dupb (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .b16 d n)) s = some (s.setV d (bc ((s.gpr n).setWidth 8))) := rfl

theorem exec_insd (s : State) (d : VReg) (i : Nat) (hi : i < 2) (n : Reg) :
    exec (.vop (.ins .d2 d i n)) s = some (s.setV d (setLane (s.v d) 64 i (s.gpr n))) := by
  simp [exec, VOp.eval, hi]

/-- A 128-bit constant into a vector register, through `x6` and `x7`. -/
theorem const128_ok (s : State) (d : VReg) (v : BitVec 128) :
    WP isa (.block (const128 d v)) s fun t => t.v d = v ∧ (∀ w, w ≠ d → t.v w = s.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold const128
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const64_ok s .x6 _) fun a ⟨a6, ag, ae⟩ => ?_
  refine WP.mono (const64_ok a .x7 _) fun b ⟨b7, bg, be⟩ => ?_
  have b6 : b.gpr .x6 = v.extractLsb' 0 64 := (bg .x6 (by decide)).trans a6
  let c := b.setV d (setLane (b.v d) 64 0 (b.gpr .x6))
  let e := c.setV d (setLane (c.v d) 64 1 (c.gpr .x7))
  have bv : b.v = s.v := by rw [be, ae]
  refine WP.of_runBlock ⟨e, ?_, ?_, fun w hw => ?_, fun g h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, exec_insd _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_insd _ _ _ (by decide), runStep_some, runBlock_nil]
  · simp only [e, c, v_setV_self, gpr_setV, b6, b7]
    rw [setLane_two, ofVDwords_halves]
  · simp only [e, c, v_setV_of_ne _ _ hw, bv]
  · simp only [e, c, gpr_setV, bg g h7, ag g h6]
  · simp only [e, c, mem_setV]; rw [be, ae]
  · simp only [e, c, rd_setV]; rw [be, ae]
  · simp only [e, c, wr_setV]; rw [be, ae]
  · simp only [e, c, sp_setV]; rw [be, ae]

/-- The table `t` into the table registers. -/
theorem loadTable_ok (s : State) (t : Nat → BitVec 8) :
    WP isa (.block (loadTable t)) s fun s' => (∀ k < 256, tbyte s'.v k = t k) ∧
      (∀ w, (∀ r < 16, w ≠ treg r) → s'.v w = s.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → s'.gpr g = s.gpr g) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  suffices h : ∀ n ≤ 16, WP isa (.block ((List.range n).flatMap fun r =>
      const128 (treg r) (ofVBytes fun e => t (16 * r + e)))) s fun s' =>
      (∀ r < n, s'.v (treg r) = ofVBytes fun e => t (16 * r + e)) ∧
      (∀ w, (∀ r < n, w ≠ treg r) → s'.v w = s.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → s'.gpr g = s.gpr g) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp by
    refine WP.mono (h 16 (Nat.le_refl _)) fun s' ⟨hr, hv, hg, hm, hrd, hwr, hsp⟩ =>
      ⟨fun k hk => ?_, hv, hg, hm, hrd, hwr, hsp⟩
    rw [tbyte, hr _ (by omega), vbyte_ofVBytes _ (by omega)]
    congr 1; omega
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun a ⟨arow, av, ag, am, ard, awr, asp⟩ => ?_
    refine WP.mono (const128_ok a (treg n) _) fun b ⟨brow, bv, bg, bm, brd, bwr, bsp⟩ =>
      ⟨fun r hr => ?_, fun w hw => ?_, fun g h6 h7 => (bg g h6 h7).trans (ag g h6 h7),
        bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp⟩
    · by_cases he : r = n
      · subst he; exact brow
      · rw [bv _ (fun e => he (treg_inj r (by omega) n (by omega) e)), arow r (by omega)]
    · rw [bv _ (hw n (by omega)), av w (fun r hr => hw r (by omega))]

end VG.AArch64.Tbl
