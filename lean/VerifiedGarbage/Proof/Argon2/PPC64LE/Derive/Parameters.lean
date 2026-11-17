module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Divide
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `Argon2.PPC64LE.Derive.Divide`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.Ops`, which this module and modules that import it used -/

section

/-! # Argon2 on PPC64LE: the derivation's arithmetic and logical instructions -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd WP.cons)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsrw {d n : Reg} {sh : Nat} (h : sh < 32)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 >>> sh).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .w d n sh :: is)) s Q :=
  WP.cons (exec_lsr_w h) (k _ (Upd.write _ _ _))

end

/-- `s'` is `s` with (at most) the registers `ds` changed. -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr, u.sp⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr, h.sp⟩

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Fixed-time division on PPC64LE

`code_ok`: `Impl.Argon2.PPC64LE.Divide.code` leaves `n / D` in `r6` and
`n mod D` in `r7`, for the numerator `n` in the low 32 bits of `r4` and the
divisor `D` in `r5`, `0 < D < 2³¹`. After `k` bits (`bits_ok`) the low 32
bits of `r4` hold the `32 - k` bits of `n` not yet consumed, shifted up by
`k`, and `r6`, `r7` the quotient and remainder of the `k` consumed ones: each
bit is one step of binary long division (`Proof.Argon2.divide_step`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive.Divide

open VG VG.PPC64LE
open VG.Impl.Argon2.PPC64LE.Divide (bit bits code)
open VG.Proof.MdStream.PPC64LE (Upd wp_add wp_sub wp_lsr wp_lsl wp_li)
open VG.Proof.Argon2.PPC64LE.Derive (wp_mul wp_lsrw)

/-- Only `r4`, `r6`, `r7` and `r8` change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c d => (h'.other r a b c d).trans (h.other r a b c d), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d = .r4 ∨ d = .r6 ∨ d = .r7 ∨ d = .r8) : Keep s t :=
  ⟨fun r a b c e => u.other r (by
    rcases hd with rfl | rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  ((s.gpr .r4).setWidth 32).toNat = (n % 2 ^ (32 - k)) * 2 ^ k ∧
    (s.gpr .r6).toNat = n / 2 ^ (32 - k) / D ∧
    (s.gpr .r7).toNat = n / 2 ^ (32 - k) % D

theorem toNat_lsl1 (x : BitVec 64) : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]

theorem toNat_lsr (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- One bit. -/
theorem bit_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .r5).toNat = D) (h9 : (s.gpr .r9).toNat = 1) {n k : Nat} (hn : n < 2 ^ 32)
    (hk : k < 32) (h : Stage n D k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, hq6, ha⟩ := h
  obtain hm : k + (31 - k) = 31 := by omega_arith
  obtain pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  obtain e32 : 32 - k = 31 - k + 1 := by omega_arith
  obtain p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  obtain hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  obtain hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  obtain hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    obtain h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [h', hRlt]))
  obtain hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  obtain hqlt : n / 2 ^ (32 - k) / D < 2 ^ 32 := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)
  obtain hrlt : n / 2 ^ (32 - k) % D < D := Nat.mod_lt _ hD
  generalize hN : n / 2 ^ (32 - k) = N at hq6 ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  obtain N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega_using [this]
  obtain R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  obtain step := Proof.Argon2.divide_step (n := N) (d := D) (q := N / D) (r := N % D)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  obtain res := Proof.Argon2.divide_result hD st₁ st₂
  obtain pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  obtain hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega_arith)
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  obtain hL : ((s.gpr .r4).setWidth 32).toNat = b * 2 ^ 31 + R' * 2 ^ k := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  obtain hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  generalize hPP : R' * 2 ^ k = P at hP hPb hL
  generalize hKK : 2 ^ k = K at hPb pk
  obtain hK : 0 < K := hKK ▸ pos k
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_lsrw (by decide) fun s₁ u₁ => ?_
  obtain v₁ : (s₁.gpr .r8).toNat = b := by
    rw [u₁.gpr, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hL,
      Nat.mod_eq_of_lt (by
        rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;>
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith))]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_lsl (by decide) fun s₂ u₂ => ?_
  obtain v₂ : ((s₂.gpr .r4).setWidth 32).toNat = 2 * P := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_setWidth, toNat_lsl1]
    obtain hx : (s.gpr .r4).toNat % 2 ^ 32 = b * 2 ^ 31 + P := by
      rw [← BitVec.toNat_setWidth, hL]
    rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mul_mod, hx]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_lsl (by decide) fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  obtain v₄ : (s₄.gpr .r7).toNat = 2 * (N % D) + b := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), BitVec.toNat_add, toNat_lsl1,
      u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha, v₁]
    omega_arith
  refine wp_sub fun s₅ u₅ => ?_
  obtain d₄ : (s₄.gpr .r5).toNat = D := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb]
  refine wp_lsr (by decide) fun s₆ u₆ => ?_
  generalize ht : (if 2 * (N % D) + b < D then 0 else 1) = t
  obtain ht1 : t ≤ 1 := by rw [← ht]; split <;> omega_arith
  obtain v₆ : (s₆.gpr .r8).toNat = 1 - t := by
    rw [u₆.gpr, toNat_lsr, u₅.gpr, BitVec.toNat_sub, v₄, d₄, ← ht]
    split
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = 2 ^ 64 - (D - (2 * (N % D) + b)) by omega_arith,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = (2 * (N % D) + b - D) + 2 ^ 64 by omega_arith,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
  refine wp_sub fun s₇ u₇ => ?_
  obtain v₇ : (s₇.gpr .r8).toNat = t := by
    obtain e9 : (s₆.gpr .r9).toNat = 1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
    rw [u₇.gpr, BitVec.toNat_sub, v₆, e9]
    rcases (by omega_arith : t = 0 ∨ t = 1) with rfl | rfl <;> decide
  refine wp_lsl (by decide) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  refine wp_mul fun s₁₀ u₁₀ => ?_
  refine wp_sub fun s₁₁ u₁₁ => hq s₁₁ ⟨?_, ?_, ?_⟩ ?_
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂, R'', hP]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, BitVec.toNat_add,
      u₈.gpr, u₈.other _ (by decide), toNat_lsl1, v₇, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hq6, N', ← res.1, ← ht]
    omega_arith
  · have d₉ : (s₉.gpr .r5).toNat = D := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), d₄]
    obtain r₉ : (s₉.gpr .r7).toNat = 2 * (N % D) + b := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), v₄]
    obtain e₉ : (s₉.gpr .r8).toNat = t := by rw [u₉.other _ (by decide), u₈.other _ (by decide), v₇]
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₁₀.gpr, BitVec.toNat_sub, BitVec.toNat_mul, e₉, d₉, r₉,
      N', ← res.2, ← ht]
    obtain sub : ∀ x v : Nat, x ≤ v → v < 2 ^ 64 → (2 ^ 64 - x % 2 ^ 64 + v) % 2 ^ 64 = v - x :=
      fun x v h₁ h₂ => by
        rw [Nat.mod_eq_of_lt (a := x) (by omega_arith), show 2 ^ 64 - x + v = (v - x) + 2 ^ 64 by omega_arith,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    split
    · rw [Nat.zero_mul, sub 0 _ (by omega_arith) (by omega_arith)]; rfl
    · rw [Nat.one_mul, sub D _ (by omega_arith) (by omega_arith)]
  · exact (((((((((((Keep.of_upd u₁ (by simp)).trans (Keep.of_upd u₂ (by simp))).trans (Keep.of_upd u₃ (by simp))).trans (Keep.of_upd u₄ (by simp))).trans (Keep.of_upd u₅ (by simp))).trans (Keep.of_upd u₆ (by simp))).trans (Keep.of_upd u₇ (by simp))).trans (Keep.of_upd u₈ (by simp))).trans (Keep.of_upd u₉ (by simp))).trans (Keep.of_upd u₁₀ (by simp))).trans (Keep.of_upd u₁₁ (by simp)))

theorem bits_ok {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, (s.gpr .r5).toNat = D → (s.gpr .r9).toNat = 1 → Stage n D 0 s →
      (∀ t, Stage n D k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h9, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega_arith) s hb h9 h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), hb])
      (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), h9]) hn (by omega_arith) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- Only `r4` and `r6`–`r9` change. -/
structure KeepD (s t : State) : Prop where
  other : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The division: `r6 := n / D`, `r7 := n mod D`, for `n` the low 32 bits of
`r4`. -/
theorem code_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .r5).toNat = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .r6).toNat = ((s.gpr .r4).setWidth 32).toNat / D →
      (t.gpr .r7).toNat = ((s.gpr .r4).setWidth 32).toNat % D → KeepD s t →
      WP isa (.block is) t Q) :
    WP isa (.block (code ++ is)) s Q := by
  obtain hn := ((s.gpr .r4).setWidth 32).isLt
  simp only [code, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => ?_
  obtain e4 : s₃.gpr .r4 = s.gpr .r4 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₃.gpr]; rfl) ⟨?_, ?_, ?_⟩ fun t ⟨hc, h6, h7⟩ kt => ?_
  · rw [e4, Nat.mod_eq_of_lt hn]; simp
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, show 32 - 0 = 32 from rfl,
      Nat.div_eq_of_lt hn, Nat.zero_div]; rfl
  · rw [u₃.other _ (by decide), u₂.gpr, show 32 - 0 = 32 from rfl, Nat.div_eq_of_lt hn,
      Nat.zero_mod]; rfl
  · refine hq t (by rw [h6]; simp) (by rw [h7]; simp) ⟨fun r a b c d e => ?_, ?_, ?_, ?_, ?_⟩
    · rw [kt.other r a b c d, u₃.other _ e, u₂.other _ c, u₁.other _ b]
    · rw [kt.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [kt.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [kt.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [kt.sp, u₃.sp, u₂.sp, u₁.sp]

end VG.Proof.Argon2.PPC64LE.Derive.Divide

end

end

/-!
# Argon2 on PPC64LE: the parameters

`parameters_ok`: the body's first computation stores the segment length (by
the fixed-time division of the memory cost by `4 · lanes`), the lane length
and its size in bytes in the frame (`Prm`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_lsl)
open VG.Impl.Argon2.PPC64LE.Derive (parameters segLenOff laneLenOff strideOff)

/-- The parameters in the frame. -/
structure Prm (s₀ s : State) : Prop where
  segLen : lw s₀ s segLenOff = BitVec.ofNat 64 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 64 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 64 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.divide {s₀ s t : State} (h : Inv s₀ s) (k : Divide.KeepD s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun r hr => k.other _ (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  ⟨by rw [lw_mem h]; exact pr.segLen, by rw [lw_mem h]; exact pr.laneLen,
    by rw [lw_mem h]; exact pr.stride⟩

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_ext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem ofNat_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {s : State} (h : Inv s₀ s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block (parameters ++ is)) s Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hb := hp.blocks_eq
  have hbl := hp.blocks_le
  have hm := mcost_lt s₀
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine wp_ldw hp h (i := Impl.Argon2.PPC64LE.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := h.upd u₂
  refine wp_lsl (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  have e₃ : (s₃.gpr .r5).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by rw [toNat_ext32]; show lanesN s₀ * 4 < _; omega_using [hL]), toNat_ext32]
    show lanesN s₀ * 4 = _
    omega_using []
  refine wp_ldw hp i₃ (i := Impl.Argon2.PPC64LE.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₃.upd u₅
  refine Divide.code_ok (D := 4 * lanesN s₀) (by omega_using [hL1]) (by omega_using [hL])
    (by rw [u₅.other _ (by decide), e₃]) fun s₆ c₆ _ k₆ => ?_
  have i₆ := i₅.divide k₆
  have c₆' : (s₆.gpr .r6).toNat = (prm s₀).segmentLen := by
    rw [c₆, u₅.gpr, hseg, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  refine wp_stloc i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  have hll : (prm s₀).laneLen ≤ mcostN s₀ :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)) hbl
  refine wp_lsl (by decide) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈
  have e₈ : (s₈.gpr .r6).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega_using [hm, hlane, hll]), c₆', hlane]; omega_using []
  refine wp_stloc i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_lsl (by decide) fun s₁₀ u₁₀ => ?_
  have i₁₀ := i₉.upd u₁₀
  have e₁₀ : (s₁₀.gpr .r6).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega_using [hm, hll]), e₈]
  refine wp_stloc i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ =>
    k s₁₁ i₁₁ ⟨?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide),
      lw_mem u₈.mem, v₇]
    exact ofNat_toNat c₆'
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact ofNat_toNat e₈
  · rw [v₁₁]
    exact ofNat_toNat e₁₀

end

end VG.Proof.Argon2.PPC64LE.Derive
