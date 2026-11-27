module

public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# `R² mod m` by word steps with ADX: a step

`R2Adx.fix` adds `m` back to `t` if its top word's sign bit is set, by a
branch, as `R2Words.addBack` does by a mask (`fix_ok`, the same statement);
`R2Adx.step` is `x := x 2^64 mod m` (`step_ok`, as `R2w.step_ok`), with the
accumulator holding `mc = R - m`: `q̂`, corrected by `R2Words.quot3` and
`fix3` twice (`refine3_ok`), is the 3-by-2 estimate, `q ≤ q̂ ≤ q + 1`
(`R2w.norm3`), so one `fix` suffices (`WordStep.wordStepQ1_val`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem top_cf (x : BitVec 64) : decide (2 ^ 64 ≤ x.toNat + x.toNat) = decide (2 ^ 63 ≤ x.toNat) :=
  decide_eq_decide.mpr (by omega_using [])

/-- `t := t + m` if `t` is negative (its top word's top bit set). -/
theorem fix_ok {s : State} {B : Addr} {Z w em et : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B em) (hbx : s.gpr .rbx = off B et) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa fix s fun t => ∃ c : Bool,
      wv t.mem B et (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat = wv s.mem B et (w + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat then wv s.mem B em w else 0) ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .r8, .r11, .rbp, .r14] s t := by
  have hn := hs.nowrap
  obtain hea : s.ea (ix .rbx .r12) = off B (et + 8 * w) := ea_ix0 s hbx h12
  unfold fix
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat)) ∧
      t.mem = s.mem) (by xrun [hea, hs.ld (show et + 8 * w + 8 ≤ Z by omega_using [hT]), top_cf]) rfl)
    fun t₁ ⟨⟨hc₁, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  refine WP.ite (decide (2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat)) (by simp only [eval, hc₁]) (fun hb => ?_)
    (fun hb => ?_)
  · refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B et ∧ t.mem = t₁.mem) (by
      xrun [(k₁.gpr (by decide)).trans hbx]) rfl) fun t₂ ⟨⟨h8, hm₂⟩, k₂⟩ => ?_)
    obtain k₁₂ := k₁.trans k₂
    refine WP.mono (R2w.addBack_ok (hs₁.congr k₂.2.2) ((k₁₂.gpr (by decide)).trans h10) h8
      ((k₁₂.gpr (by decide)).trans h12) hw hw' hM hT sM) fun t ⟨c, hv, ho, k⟩ => ⟨c, ?_, ?_, ?_⟩
    · rw [hv, hm₂, hm₁]
    · rw [← hm₁, ← hm₂]; exact ho
    · exact (k₁₂.trans k).mono (by decide)
  · refine WP.block_nil ⟨false, ?_, by rw [hm₁]; exact Outside.refl _ _ _ _, k₁.mono (by decide)⟩
    have : ¬ 2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat := by simpa using hb
    simp only [this, ↓reduceIte, hm₁, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- `fix3Body`: `q̂ := q̂ - 1` and `t := t + D` (`t` in `r15`, `r14`, `r13`), with
its carry `c`, for `m`'s top two words `D`. -/
theorem fix3Body_ok {t : State} {B : Addr} {Z w em : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hM : em + 8 * w ≤ Z) :
    WP isa (.block fix3Body) t fun t' => t'.gpr .rcx = t.gpr .rcx - 1 ∧
      (∃ c < 2, ((t'.gpr .r15).toNat * 2 ^ 128 + (t'.gpr .r14).toNat * 2 ^ 64 + (t'.gpr .r13).toNat) + 2 ^ 192 * c = ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) +
        ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat)) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .r13, .r14, .r15] t t' := by
  refine WP.mono (WP.keep [.rcx, .r13, .r14, .r15] (Q := fun t' => t'.gpr .rcx = t.gpr .rcx - 1 ∧
      (∃ c < 2, ((t'.gpr .r15).toNat * 2 ^ 128 + (t'.gpr .r14).toNat * 2 ^ 64 + (t'.gpr .r13).toNat) + 2 ^ 192 * c = ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) +
        ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat)) ∧
      t'.mem = t.mem) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold fix3Body
  xrun [State.ea, ix, addrm8 h10 h12 (by omega_using [hw]), R2w.addrm16 h10 h12 hw,
    hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hM]), hs.ld (show em + 8 * (w - 2) + 8 ≤ Z by omega_using [hw, hM]),
    sx0]
  dsimp only [word]
  generalize t.mem.readW (off B (em + 8 * (w - 1))) 64 = d1
  generalize t.mem.readW (off B (em + 8 * (w - 2))) 64 = d0
  obtain e1 := VG.Proof.Poly1305.Limbs64.addc0 (t.gpr .r13) d0
  generalize decide (2 ^ 64 ≤ (t.gpr .r13).toNat + d0.toNat) = c1 at *
  obtain e2 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r14) d1 c1
  generalize decide (2 ^ 64 ≤ (t.gpr .r14).toNat + d1.toNat + c1.toNat) = c2 at *
  obtain e3 := VG.Proof.Poly1305.Limbs64.addc1 (t.gpr .r15) 0 c2
  rw [show (0 : BitVec 64).toNat = 0 from rfl] at e3
  exact ⟨_, Bool.toNat_lt (decide (2 ^ 64 ≤ (t.gpr .r15).toNat + 0 + c2.toNat)), by omega_using [e1, e2, e3]⟩

/-- `fix3`: if the remainder `t` (`r15`, `r14`, `r13`) is negative, by a
branch: `q̂ := q̂ - 1` and `t := t + D`, with its carry `c`, for `m`'s top two
words `D`; as `R2w.fix3_ok`. -/
theorem fix3_ok {t : State} {B : Addr} {Z w em : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hM : em + 8 * w ≤ Z) :
    WP isa fix3 t fun t' =>
      (∀ n, (t.gpr .rcx).toNat = n + (if 2 ^ 192 / 2 ≤ ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) then 1 else 0) → (t'.gpr .rcx).toNat = n) ∧
      (∃ c < 2, ((t'.gpr .r15).toNat * 2 ^ 128 + (t'.gpr .r14).toNat * 2 ^ 64 + (t'.gpr .r13).toNat) + 2 ^ 192 * c = ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) + if 2 ^ 192 / 2 ≤ ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) then
        (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat else 0) ∧
      t'.mem = t.mem ∧ Keep [.rcx, .r11, .r13, .r14, .r15] t t' := by
  obtain l0 := (t.gpr .r13).isLt; have l1 := (t.gpr .r14).isLt; have l2 := (t.gpr .r15).isLt
  obtain lq := (t.gpr .rcx).isLt
  unfold fix3
  refine WP.seq (WP.mono (WP.keep [.r11] (Q := fun t₁ => t₁.cf = some (decide (2 ^ 63 ≤ (t.gpr .r15).toNat)) ∧
      t₁.mem = t.mem) (by xrun [top_cf]) rfl) fun t₁ ⟨⟨hc₁, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain e13 : t₁.gpr .r13 = t.gpr .r13 := k₁.gpr (by decide)
  obtain e14 : t₁.gpr .r14 = t.gpr .r14 := k₁.gpr (by decide)
  obtain e15 : t₁.gpr .r15 = t.gpr .r15 := k₁.gpr (by decide)
  obtain ecx : t₁.gpr .rcx = t.gpr .rcx := k₁.gpr (by decide)
  obtain t₁10 : t₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  refine WP.ite (decide (2 ^ 63 ≤ (t.gpr .r15).toNat)) (by simp only [eval, hc₁]) (fun hb => ?_) (fun hb => ?_)
  · have hn : 2 ^ 63 ≤ (t.gpr .r15).toNat := by simpa using hb
    obtain hc : 2 ^ 192 / 2 ≤ ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) := by omega_using [hn, l0, l1, l2]
    simp only [hc, ↓reduceIte]
    refine WP.mono (fix3Body_ok hs₁ t₁10 t₁12 hw hM) fun t' ⟨hcx, ⟨c, hc, hv⟩, hm, k⟩ =>
      ⟨fun n hq => ?_, ⟨c, hc, ?_⟩, hm.trans hm₁, (k₁.trans k).mono (by decide)⟩
    · rw [hcx, ecx, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [hq, lq]
    · rw [hv, e13, e14, e15, hm₁]
  · have hn : ¬ 2 ^ 63 ≤ (t.gpr .r15).toNat := by simpa using hb
    obtain hc : ¬ 2 ^ 192 / 2 ≤ ((t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat) := by omega_using [hn, l0, l1, l2]
    simp only [hc, ↓reduceIte]
    refine WP.block_nil ⟨fun n h => (by rw [ecx]; omega_using [h]), ⟨0, by decide, ?_⟩, hm₁, k₁.mono (by decide)⟩
    rw [e13, e14, e15]

/-- `quot3` and `fix3` twice: the 3-by-2 correction of the estimate `q̂` in
`rcx`, `Q ≤ q̂ ≤ Q + 2`, to `Q = min(⌊U / D⌋, 2^64 - 1)`, as `R2w.refine3_ok`. -/
theorem refine3_ok {t : State} {B : Addr} {Z w ex em U D : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 3 ≤ w) (hX : ex + 8 * w ≤ Z) (hM : em + 8 * w ≤ Z)
    (hU : U = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
      (word t.mem B (ex + 8 * (w - 3))).toNat)
    (hD : D = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat)
    (hD0 : 0 < D) (hUD : U < (2 ^ 64 + 1) * D)
    (hge : min (U / D) (2 ^ 64 - 1) ≤ (t.gpr .rcx).toNat) (hle : (t.gpr .rcx).toNat ≤ min (U / D) (2 ^ 64 - 1) + 2) :
    WP isa refine3 t fun t' =>
      (t'.gpr .rcx).toNat = min (U / D) (2 ^ 64 - 1) ∧ t'.mem = t.mem ∧
      Keep [.rax, .rcx, .rdx, .r9, .r11, .r13, .r14, .r15] t t' := by
  unfold refine3
  refine WP.seq (WP.mono (R2w.quot3_ok hs hbx h10 h12 hw hX hM) fun t₁ ⟨⟨b, hb, h1⟩, hm₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain t₁10 : t₁.gpr .r10 = off B em := (k₁.gpr (by decide)).trans h10
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  obtain t₁cx : t₁.gpr .rcx = t.gpr .rcx := k₁.gpr (by decide)
  refine WP.seq (WP.mono (fix3_ok hs₁ t₁10 t₁12 (by omega_using [hw]) hM) fun t₂ ⟨hq₂, ⟨c, hc, h2⟩, hm₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain t₂10 : t₂.gpr .r10 = off B em := (k₂.gpr (by decide)).trans t₁10
  obtain t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans t₁12
  refine WP.mono (fix3_ok hs₂ t₂10 t₂12 (by omega_using [hw]) hM) fun t₃ ⟨hq₃, _, hm₃, k₃⟩ => ?_
  refine ⟨?_, hm₃.trans (hm₂.trans hm₁), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm₁, ← hD] at h2
  rw [← hU, ← hD] at h1
  obtain hd1 := (word t.mem B (em + 8 * (w - 1))).isLt
  obtain hd0 := (word t.mem B (em + 8 * (w - 2))).isLt
  obtain hDW : 4 * D < 2 ^ 192 / 2 := by omega_using [hD, hd1, hd0]
  obtain hT1 : (t₁.gpr .r15).toNat * 2 ^ 128 + (t₁.gpr .r14).toNat * 2 ^ 64 + (t₁.gpr .r13).toNat < 2 ^ 192 := by
    have := (t₁.gpr .r15).isLt; have := (t₁.gpr .r14).isLt; have := (t₁.gpr .r13).isLt
    omega_using []
  obtain hT2 : (t₂.gpr .r15).toNat * 2 ^ 128 + (t₂.gpr .r14).toNat * 2 ^ 64 + (t₂.gpr .r13).toNat < 2 ^ 192 := by
    have := (t₂.gpr .r15).isLt; have := (t₂.gpr .r14).isLt; have := (t₂.gpr .r13).isLt
    omega_using []
  obtain hv := WordStep.quot3_val (W := 2 ^ 192) hD0 hDW hUD hge hle (t.gpr .rcx).isLt hT1 hb
    (by rw [← t₁cx] at h1 ⊢; exact h1) hT2 hc h2
  exact hq₃ _ (hq₂ _ (by rw [t₁cx, hv, Nat.add_right_comm]))

theorem mod_cancel {r D E W : Nat} (hr : r < W) (hD : D < W) (h : (r + E) % W = (D + E) % W) : r = D := by
  obtain h1 := Nat.div_add_mod (r + E) W
  obtain h2 := Nat.div_add_mod (D + E) W
  rcases Nat.lt_trichotomy ((r + E) / W) ((D + E) / W) with hl | he | hg
  · have := Nat.mul_le_mul_left W (show (r + E) / W + 1 ≤ (D + E) / W by omega_using [hl])
    rw [Nat.mul_add, Nat.mul_one] at this; omega_using [hD, h, h1, h2, this]
  · rw [he] at h1; omega_using [h, h1, h2]
  · have := Nat.mul_le_mul_left W (show (D + E) / W + 1 ≤ (r + E) / W by omega_using [hg])
    rw [Nat.mul_add, Nat.mul_one] at this; omega_using [hr, h, h1, h2, this]

/-- `t = x 2^64 - q̂ m` from the computed `t + q̂ R ≡ x 2^64 + q̂ (R - m)`: as
`R2w.mulSub_ok` states it, with a borrow `b`. -/
theorem sub_val {T q M X C R W : Nat} (hW : W = R * 2 ^ 64) (hC : C + M = R) (hT : T < W) (hq : q < 2 ^ 64)
    (hX : X < M) (h : (T + q * R) % W = (X * 2 ^ 64 + q * C) % W) :
    ∃ b : Bool, T + q * M = X * 2 ^ 64 + W * b.toNat := by
  obtain hXW : X * 2 ^ 64 < W := by rw [hW]; exact Nat.mul_lt_mul_of_pos_right (by omega_using [hC, hX]) (by decide)
  obtain hqM : q * M < W := by
    rw [hW, Nat.mul_comm R]; exact Nat.mul_lt_mul_of_lt_of_le hq (by omega_using [hC]) (by omega_using [hC, hX])
  obtain e : (T + q * M) % W = X * 2 ^ 64 := by
    obtain hA := Nat.div_add_mod (T + q * M) W
    obtain h' : ((T + q * M) % W + q * C) % W = (X * 2 ^ 64 + q * C) % W := by
      rw [← h, ← hC, Nat.mul_add, Nat.add_mod ((T + q * M) % W), Nat.mod_mod, ← Nat.add_mod,
        show T + (q * C + q * M) = T + q * M + q * C by omega_using []]
    exact mod_cancel (Nat.mod_lt _ (by omega_using [hqM])) hXW h'
  by_cases hb : T + q * M < W
  · exact ⟨false, by rw [Nat.mod_eq_of_lt hb] at e; simp [e]⟩
  · refine ⟨true, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega_using [hb]), Nat.mod_eq_of_lt (by omega_using [hT, hqM])] at e
    simp only [Bool.toNat_true, Nat.mul_one]; omega_using [e, hb]

/-- `x := x 2^64 mod m`, for `x < m` in `aR2`, `m` in `aN` (`w` a multiple of 4
words, its top word `d` at least `2^63`), `v` the first word of the
temporary and `R - m` in the accumulator; it changes only `x`. -/
theorem step_ok {L : Lay} {t : State} (hg : GoodL L t) (hw : 4 ≤ L.w) (hw4 : L.w % 4 = 0) (hw' : L.w < 2 ^ 30)
    (hd : 2 ^ 63 ≤ (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat)
    (hv : (word t.mem L.B (slot L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem L.B (slot L.w aR2) L.w < wv t.mem L.B (slot L.w aN) L.w)
    (hc : wv t.mem L.B (slot L.w aAcc) L.w + wv t.mem L.B (slot L.w aN) L.w = 2 ^ (64 * L.w)) :
    WP isa step t fun t' => GoodL L t' ∧
      wv t'.mem L.B (slot L.w aR2) L.w = wv t.mem L.B (slot L.w aR2) L.w * 2 ^ 64 % wv t.mem L.B (slot L.w aN) L.w ∧
      Arrays L.B L.w [aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨B, Z, w, minv⟩ := L
  dsimp only at hw hw4 hw' hd hv hx hc ⊢
  have hs : Scr t B Z := hg.1.scr
  have hZ : slot w 8 ≤ Z := hg.2
  have hn : B.toNat + Z ≤ 2 ^ 64 := hs.nowrap
  obtain hsx := slot_le (w := w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := w) (show aN < 8 by decide)
  obtain hst := slot_le (w := w) (show aAcc < 8 by decide)
  obtain sXT := slot_sep (w := w) (show aR2 ≠ aAcc by decide)
  obtain sXM := slot_sep (w := w) (show aR2 ≠ aN by decide)
  obtain hsv := slot_le (w := w) (show aTmp < 8 by decide)
  obtain hhd := hdr_lt_slot w 0 (show sArr aAcc < 32 by decide)
  obtain hs0 := slot_le (w := w) (show 0 < 8 by decide)
  rw [show step = .seq (.block R2Words.bases) (.seq (.block R2Words.quot) (.seq refine3 (.seq mulSub fix))) from rfl]
  refine WP.seq (WP.mono (R2w.stepBases_ok (L := ⟨B, Z, w, minv⟩) hg)
    fun t₁ ⟨h1bx, h110, _, h112, h1bp, hm₁, k₁⟩ => ?_)
  dsimp only at h1bx h110 h112 h1bp
  obtain hs₁ := hs.congr k₁.2.2
  generalize hX : wv t.mem B (slot w aR2) w = X at hx
  generalize hM : wv t.mem B (slot w aN) w = M at hx hc
  obtain hu := R2w.top_le (by omega_using [hw]) (hX ▸ hM ▸ hx)
  rw [← hm₁] at hu hd hv
  obtain e1 : slot w aR2 + 8 * w ≤ Z := by omega_using [hZ, hsx]
  obtain e2 : slot w aN + 8 * w ≤ Z := by omega_using [hZ, hsm]
  obtain e3 : slot w aTmp + 8 ≤ Z := by omega_using [hZ, hsv]
  obtain hw31 : w < 2 ^ 31 := by omega_using [hw']
  obtain hq := R2w.quot_ok hs₁ h1bx h110 h112 h1bp (by omega_using [hw]) e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  rw [hm₁] at h2cx hd
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain t₂bx : t₂.gpr .rbx = off B (slot w aR2) := (k₂.gpr (by decide)).trans h1bx
  obtain t₂10 : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h110
  obtain t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  -- The estimates.
  obtain hX' : X = (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) +
      (word t.mem B (slot w aR2 + 8 * (w - 3))).toNat * 2 ^ (64 * (w - 3)) + wv t.mem B (slot w aR2) (w - 3) := by
    rw [← hX, show w = (w - 3) + 1 + 1 + 1 by omega_using [hw], wv_succ, wv_succ, wv_succ,
      show w - 3 + 1 + 1 + 1 - 1 = w - 3 + 1 + 1 by omega_using [], show w - 3 + 1 + 1 + 1 - 2 = w - 3 + 1 by omega_using [],
      show w - 3 + 1 + 1 + 1 - 3 = w - 3 by omega_using []]
    grind
  obtain hM' : M = (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aN + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B (slot w aN) (w - 2) := by
    rw [← hM, show w = (w - 2) + 1 + 1 by omega_using [hw], wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega_using [],
      show w - 2 + 1 + 1 - 2 = w - 2 by omega_using []]
    grind
  obtain ⟨hUD, hq1, hq2, hge, hle⟩ :=
    R2w.norm3 (by omega_using [hw]) hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (BitVec.isLt _) (BitVec.isLt _) hd hx
  obtain h2cx' := congrArg BitVec.toNat h2cx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))] at h2cx'
  obtain hD0 : 0 < (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (slot w aN + 8 * (w - 2))).toNat := by
    omega_using [hd]
  obtain hr := refine3_ok hs₂ t₂bx t₂10 t₂12 (by omega_using [hw]) e1 e2 (by rw [hm₂, hm₁]) (by rw [hm₂, hm₁]) hD0 hUD
    (by rw [h2cx']; exact hq1) (by rw [h2cx']; exact hq2)
  refine WP.seq (WP.mono hr fun t₂b ⟨hrb, hmb, kb⟩ => ?_)
  rw [hm₂, hm₁] at hmb
  obtain hs₂b := hs₂.congr kb.2.2
  obtain k₁₂ := (k₁.trans k₂).trans kb
  obtain t₂bx' : t₂b.gpr .rbx = off B (slot w aR2) := (kb.gpr (by decide)).trans t₂bx
  obtain t₂12' : t₂b.gpr .r12 = BitVec.ofNat 64 w := (kb.gpr (by decide)).trans t₂12
  obtain t₂10' : t₂b.gpr .r10 = off B (slot w aN) := (kb.gpr (by decide)).trans t₂10
  obtain t₂di : t₂b.gpr .rdi = B := (k₁₂.gpr (by decide)).trans hg.1.rdi
  obtain hA : word t₂b.mem B (8 * sArr aAcc) = off B (slot w aAcc) := by
    rw [hmb]; exact hg.1.hdr.harr aAcc (by decide)
  obtain hms := mulSub_ok (N := w / 4) hs₂b t₂di hA (by omega_using [hZ, hhd, hs0]) t₂bx' t₂12' (by omega_using [hw4]) (by omega_using [hw]) (by omega_using [hw31]) (by omega_using [hZ, hsx])
    (by omega_using [hZ, hst]) (by omega_using [sXT])
  refine WP.seq (WP.mono hms fun t₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  obtain hQ' : min (((word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 128 +
      (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat * 2 ^ 64 + (word t.mem B (slot w aR2 + 8 * (w - 3))).toNat) /
      ((word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (slot w aN + 8 * (w - 2))).toNat))
      (2 ^ 64 - 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  rw [hrb, hmb, hX] at hv₃
  rw [hmb] at ho₃
  obtain hs₃ := hs₂b.congr k₃.2.2
  obtain k₁₃ := k₁₂.trans k₃
  obtain t₃10 : t₃.gpr .r10 = off B (slot w aN) := (k₃.gpr (by decide)).trans t₂10'
  obtain t₃bx : t₃.gpr .rbx = off B (slot w aR2) := (k₃.gpr (by decide)).trans t₂bx'
  obtain t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂12'
  obtain sM : slot w aR2 + 8 * (w + 1) ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aR2 := by omega_using [sXM]
  refine WP.mono (fix_ok hs₃ t₃10 t₃bx t₃12 (by omega_using [hw]) hw31 e2 (by omega_using [hZ, hsx]) sM) fun t' ⟨c1, hv₄, ho₄, k₄⟩ => ?_
  -- `m` is as on entry outside `x`.
  obtain em3 : ∀ {d n}, d + 8 * n ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => ho₃.wv (by omega_using [h]) (by omega_using [hn, h'])
  rw [em3 (n := w) (d := slot w aN) (by omega_using [sXM]) (by omega_using [e2]), hM] at hv₄
  simp only [← R2w.top_half] at hv₄
  -- `t`'s value with the borrow.
  have hC : wv t.mem B (slot w aAcc) w + M = 2 ^ (64 * w) := hc
  obtain ⟨b, hb⟩ := sub_val (T := wv t₃.mem B (slot w aR2) (w + 1)) (R := 2 ^ (64 * w))
    (W := 2 ^ (64 * (w + 1))) (by rw [show 64 * (w + 1) = 64 * w + 64 by omega_using [], Nat.pow_add]) hC (wv_lt _ _ _ _)
    hQ' hx hv₃
  obtain hMw : M < 2 ^ (64 * w) := by rw [← hM]; exact wv_lt _ _ _ _
  obtain hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [show 64 * (w + 1) = 64 * w + 64 by omega_using [], Nat.pow_add]
    omega_using [hMw]
  obtain hT3 := WordStep.wordStepQ1_val (by omega_using [hx]) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hb (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₄
  obtain hlow : wv t'.mem B (slot w aR2) w = wv t'.mem B (slot w aR2) (w + 1) := by
    obtain hlt : wv t'.mem B (slot w aR2) (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [hx])) (hM ▸ wv_lt _ _ _ _)
    rw [wv_succ] at hlt ⊢
    have : (word t'.mem B (slot w aR2 + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t'.mem B (slot w aR2 + 8 * w)).toNat by omega_using [h])
      omega_using [hlt, this]
    rw [this, Nat.mul_zero, Nat.add_zero]
  obtain ha : Arrays B w [aR2] t.mem t'.mem := by
    obtain e4 : slot w aR2 + 8 * (w + 1) ≤ slot w aR2 + 8 * (w + 2) := by omega_using []
    exact (Arrays.of_outside (j := aR2) (by simp) ho₃ (Nat.le_refl _) e4).trans
      (Arrays.of_outside (j := aR2) (by simp) ho₄ (Nat.le_refl _) e4)
  obtain k' := k₁₃.trans k₄
  refine ⟨⟨⟨hs₃.congr k₄.2.2, (k'.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, ?_, ha,
    k'.mono (by decide)⟩
  rw [hlow, hT3]

end VG.Proof.Bignum.X86_64.R2ax
