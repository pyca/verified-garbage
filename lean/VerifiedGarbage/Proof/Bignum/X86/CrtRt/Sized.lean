module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.Bool
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Coefficient
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Recombine
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate

/-! # Private CRT at a run-time width, from the arguments to the result

`sized_ok`: the components read, the key and input accepted or not, both
factors' powers, the coefficient, the recombination, and the result written
out (cleared unless accepted), with `eax` the acceptance. Every byte of the
working space may change but the saved registers' (`rtBody`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue)

/-- What private CRT at a run-time width writes: the working space but its saved registers, the
output and the zone below `sp` its calls write. -/
def rtBody (base out : Addr) (bytes len : Nat) (sp : BitVec 32) : List Region :=
  [⟨base, 32⟩, ⟨off base 48, bytes - 48⟩, ⟨out, len⟩, below sp 40]

/-- A range of the working space but its saved registers. -/
abbrev Body (bytes : Nat) (p : Nat × Nat) : Prop := p.1 + p.2 ≤ 32 ∨ (48 ≤ p.1 ∧ p.1 + p.2 ≤ bytes)

theorem toBody {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hw : ∀ p ∈ ws, Body bytes p) (fit : bytes ≤ 2 ^ 64) :
    Frame (rtBody base out bytes len sp) m m' :=
  F.sub fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, by simp [rtBody], fun _ h => h⟩
    · rcases hw p hp with w | ⟨w1, w2⟩
      · refine ⟨⟨base, 32⟩, by simp [rtBody], ?_⟩
        have := VG.Offset.sub base (d := p.1) (n := p.2) (e := 0) (k := 32) (Nat.zero_le _) (by omega)
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
      · exact ⟨⟨off base 48, bytes - 48⟩, by simp [rtBody], VG.Offset.sub base w1 (by omega)⟩

theorem body_of_outside {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {a n : Nat} {m m' : Mem}
    (O : Outside base a n m m') (w : Body bytes (a, n)) (fit : bytes ≤ 2 ^ 64) :
    Frame (rtBody base out bytes len sp) m m' :=
  toBody (ws := [(a, n)]) (frameR_of_outside O (by rcases w with w | w <;> dsimp only at w <;> omega) (by simp))
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact w) fit

/-- A component below `2^(8 l)` for its length `l`. -/
theorem comp_lt (m : Mem) (args : Nat → BitVec 32) (i : Nat) :
    componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  have B := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
  simpa only [componentValue, VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] using B

/-- An accepted key's recombination is the CRT's result, below the modulus. -/
theorem accepted_result {N p q dp dq qi x : Nat} (odd : N % 2 = 1) (pBound : p < N) (qBound : q < N)
    (product : p * q = N) :
    x ^ dq % safeM q + q * ((x ^ dp % safeM p + safeM p - x ^ dq % safeM q % safeM p) % safeM p * qi % safeM p) =
        VG.Proof.Bignum.crtResult p q dp dq qi x ∧
      x ^ dq % safeM q + q * ((x ^ dp % safeM p + safeM p - x ^ dq % safeM q % safeM p) % safeM p * qi % safeM p) <
        N := by
  obtain ⟨hq, hoq⟩ := VG.Proof.Bignum.factor_facts product pBound odd
  obtain ⟨hp, hop⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact product) qBound odd
  have sp : safeM p = p := ite_eq_left ⟨hp, hop⟩
  have sq : safeM q = q := ite_eq_left ⟨hq, hoq⟩
  rw [sp, sq]
  refine ⟨?_, ?_⟩
  · unfold VG.Proof.Bignum.crtResult
    rw [VG.Proof.Bignum.crt_coefficient_natural (by omega)]
  · rw [← product]; exact VG.Proof.Bignum.crt_recombine_bound (by omega) (Nat.mod_lt _ (by omega))

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The wide slots 9 to 17 hold the components (`n` of `2 B` bytes, the others of `B`) and `m_p` and
`m_q` (of `2 B` bytes). -/
structure Comps (base : Addr) (len : Nat) (args : Nat → BitVec 32) (m₀ m : Mem) : Prop where
  n : val32 m base (lo len (.slot .wide 9)) (2 * cwc len .wide) = componentValue m₀ args 2
  x : val32 m base (lo len (.slot .wide 15)) (cwc len .wide) = componentValue m₀ args 4
  p : val32 m base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue m₀ args 6
  q : val32 m base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue m₀ args 8
  dp : val32 m base (lo len (.slot .wide 12)) (cwc len .wide) = componentValue m₀ args 10
  dq : val32 m base (lo len (.slot .wide 13)) (cwc len .wide) = componentValue m₀ args 12
  qi : val32 m base (lo len (.slot .wide 14)) (cwc len .wide) = componentValue m₀ args 14

/-- The components kept by changes to the bytes below the wide slot 9 or from 16 on. -/
theorem Comps.keep {m₀ m m' : Mem} (c : Comps base len args m₀ m)
    (k : ∀ {j : Nat} {w : Nat}, 9 ≤ j → j ≤ 15 → w ≤ 2 * cwc len .wide →
      val32 m' base (lo len (.slot .wide j)) w = val32 m base (lo len (.slot .wide j)) w) :
    Comps base len args m₀ m' :=
  ⟨by rw [k (by decide) (by decide) (Nat.le_refl _)]; exact c.n,
    by rw [k (by decide) (by decide) (by omega)]; exact c.x, by rw [k (by decide) (by decide) (by omega)]; exact c.p,
    by rw [k (by decide) (by decide) (by omega)]; exact c.q, by rw [k (by decide) (by decide) (by omega)]; exact c.dp,
    by rw [k (by decide) (by decide) (by omega)]; exact c.dq, by rw [k (by decide) (by decide) (by omega)]; exact c.qi⟩

/-- The wide slots 9 to 17, within the working space. -/
theorem wide_hi (h : In base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hw : w ≤ 2 * cwc len .wide) :
    numBase ≤ lo len (.slot .wide j) ∧ lo len (.slot .wide j) + 4 * w ≤ lo len (.slot .wide 18) ∧
      lo len (.slot .wide 18) ≤ bytes := by
  have f := h.slot_fit .wide (j := 18) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega)
  rw [Nat.succ_mul] at this
  omega

/-- The components read and the key and input accepted or not. -/
theorem front_ok (h : In base bytes len args s) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, In base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args s.mem u.mem →
      u.mem.readW (off base accOff) 32 = cmask (decide (accepted s.mem args)) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq importComponents (.seq validate P)) s Q := by
  have bl := h.bytes_lt
  have f := h.slot_fit .wide (j := 18) (by decide)
  have pf := h.prod_fit
  have lb := len_le_bc len
  have bw := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁, K₁⟩ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  have nlt : componentValue s.mem args 2 < 2 ^ (32 * cwc len .wide) := by
    have := h.crt.modulus_bound
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  refine WP.seq (WP.mono (validate_ok h₁ N₁ nlt P₁ Q₁ QI₁ X₁) fun u₂ ⟨F₂, A₂, K₂⟩ => ?_)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have C₂ : Comps base len args s.mem u₂.mem :=
    Comps.keep ⟨N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁⟩ fun hj9 hj hw =>
      valR_keep h₁ F₂ (sp₁ ▸ h₁.crt.room) (wide_hi h hj9 (by omega) hw).1
        (by have := wide_hi h hj9 (by omega) hw; omega)
  refine k u₂ h₂ ?_ C₂ ?_ (K₁.trans K₂)
  · refine (body_of_outside O₁ (.inr ⟨by omega, by omega⟩) (by omega)).trans (toBody F₂ ?_ (by omega))
    intro p hp; simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact .inl (show 8 + 4 ≤ 32 by omega)
    · exact .inr ⟨by simp only [multOff]; omega, by simp only [multOff]; omega⟩
    · exact .inr ⟨by simp only [prodOff]; omega, by omega⟩
    · exact .inr ⟨by simp only [mulAOff]; omega, by omega⟩
  · apply BitVec.eq_of_toNat_eq
    rw [show (u₂.mem.readW (off base accOff) 32).toNat = w32 u₂.mem base accOff from rfl, A₂]
    rfl

/-- A power keeps the acceptance mask. -/
theorem stR_acc (h : In base bytes len args s) {sp : BitVec 32} {o : Nat} (ho : o ≤ 19) {m m' : Mem}
    (F : Frame (frameR base sp (stR len o)) m m') (R : CallRoom sp base bytes) :
    m'.readW (off base accOff) 32 = m.readW (off base accOff) 32 := by
  have f := h.slot_fit .wide (j := 8) (by decide)
  have W := h.wide_fit (j := o) ho
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  apply BitVec.eq_of_toNat_eq
  show w32 m' base accOff = w32 m base accOff
  rw [← w32_val32_one, ← w32_val32_one]
  refine frameR_val32 F R h.crt.scratch.nowrap (by simp only [accOff]; omega) ?_ (stR_fit h ho)
  intro q hq; simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp only [accOff] <;> omega

theorem stR_body (h : In base bytes len args s) {o : Nat} (ho : o ≤ 19) : ∀ q ∈ stR len o, Body bytes q := by
  have fit := stR_fit h ho
  have T := h.table_fit .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  intro q hq
  have := fit q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact .inl (show 0 + 8 ≤ 32 by omega)
  · exact .inr ⟨by dsimp only; omega, this⟩
  · exact .inr ⟨by dsimp only; omega, this⟩
  · exact .inr ⟨by dsimp only; omega, this⟩

/-- A factor fits half the width when its length does. -/
theorem fits_half {m : Mem} {i : Nat} (hl : (args (i + 1)).toNat ≤ bc len .half) :
    componentValue m args i < 2 ^ (32 * cwc len .half) := by
  have := comp_lt m args i
  have bh := bc_eq_cwc len .half
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

/-- A power keeps the components. -/
theorem Comps.stR (h : In base bytes len args s) {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17) {sp : BitVec 32}
    {m₀ m m' : Mem} (F : Frame (frameR base sp (stR len o)) m m') (R : CallRoom sp base bytes)
    (c : Comps base len args m₀ m) : Comps base len args m₀ m' :=
  Comps.keep c fun {j w} hj9 hj hw => by
    have W := wide_hi h hj9 (by omega) hw
    have a := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 16 by omega)
    have b := Nat.mul_le_mul_right (st len .wide) ho16
    rw [Nat.succ_mul] at a
    have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    have bw := bc_eq_cwc len .wide
    have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
    have := Nat.mul_le_mul_right (st len .wide) hj9
    exact stR_keep h ho16 ho F R (by omega) (by omega) (.inl (by omega))

/-- Both factors' powers: `x^dP mod p` into the wide slot 16, `x^dQ mod q` into 17. -/
theorem powers_ok (h : In base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem)
    (dpl : args 11 = args 7) (dql : args 13 = args 9) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, In base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args m₀ u.mem →
      u.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 →
      val32 u.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 10 % safeM (componentValue m₀ args 6) →
      val32 u.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 12 % safeM (componentValue m₀ args 8) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq (power 10 12 16 7) (.seq (power 11 13 17 9) P)) s Q := by
  have bl := h.bytes_lt
  have bw := bc_eq_cwc len .wide
  have e16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine WP.seq (WP.mono (power_ok h (f := 10) (e := 12) (o := 16) (l := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c.p c.dp c.x
    (fun hl => ⟨fits_half hl, fits_half (args := args) (len := len) (m := m₀) (i := 10) (show (args 11).toNat ≤ _ by rw [dpl]; exact hl)⟩))
    fun u₁ ⟨F₁, V₁, K₁⟩ => ?_)
  have h₁ := h.keepF K₁ (by decide) (by decide) F₁ (stR_fit h (by decide))
  have c₁ : Comps base len args m₀ u₁.mem := Comps.stR h (by decide) (by decide) F₁ h.crt.room c
  refine WP.seq (WP.mono (power_ok h₁ (f := 11) (e := 13) (o := 17) (l := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c₁.q c₁.dq c₁.x
    (fun hl => ⟨fits_half hl, fits_half (args := args) (len := len) (m := m₀) (i := 12) (show (args 13).toNat ≤ _ by rw [dql]; exact hl)⟩))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (stR_fit h (by decide))
  rw [sp₁] at F₂
  have c₂ : Comps base len args m₀ u₂.mem := Comps.stR h (by decide) (by decide) F₂ h.crt.room c₁
  have M16 : val32 u₂.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) =
      val32 u₁.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) :=
    stR_keep h (o := 17) (by decide) (by decide) F₂ h.crt.room (by omega) (by omega) (.inl (by omega))
  refine k u₂ h₂ ((toBody F₁ (stR_body h (by decide)) (by omega)).trans (toBody F₂ (stR_body h (by decide)) (by omega)))
    c₂ ?_ (by rw [M16, V₁]) V₂ (K₁.trans K₂)
  rw [stR_acc h (by decide) F₂ h.crt.room, stR_acc h (by decide) F₁ h.crt.room]

/-- Changes to ranges apart from the acceptance mask keep it. -/
theorem acc_keep (h : In base bytes len args s) {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes) (fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (hw : ∀ p ∈ ws, p.1 + p.2 ≤ accOff ∨ accOff + 4 ≤ p.1) :
    m'.readW (off base accOff) 32 = m.readW (off base accOff) 32 := by
  have f := h.slot_fit .wide (j := 0) (by decide)
  have z : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have nb : numBase = 3336 := rfl
  have ao : accOff = 8 := rfl
  apply BitVec.eq_of_toNat_eq
  show w32 m' base accOff = w32 m base accOff
  rw [← w32_val32_one, ← w32_val32_one]
  exact frameR_val32 F R h.crt.scratch.nowrap (by omega) (fun p hp => by have := hw p hp; omega) fit

/-- The coefficient, the recombination and the result written out. -/
theorem back_ok (h : In base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem) {mp mq : Nat}
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) = mp)
    (hmpl : mp < safeM (componentValue m₀ args 6)) (hmpb : mp < 2 ^ (32 * cwc len .wide))
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq) (hmqb : mq < 2 ^ (32 * cwc len .wide))
    {cb : Bool} (hacc : s.mem.readW (off base accOff) 32 = cmask cb) :
    let p := componentValue m₀ args 6
    let r := mq + componentValue m₀ args 8 *
      ((mp + safeM p - mq % safeM p) % safeM p * componentValue m₀ args 14 % safeM p)
    WP isa (.seq coefficient (.seq recombine exportResult)) s fun t =>
      ((cb = true → r < 2 ^ (8 * len)) → Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if cb then r else 0) len) ∧
      t.gpr .eax = BitVec.ofNat 32 cb.toNat ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  intro p r
  have bl := h.bytes_lt
  have bw := bc_eq_cwc len .wide
  have lb := len_le_bc len
  have f19 := h.slot_fit .wide (j := 19) (by decide)
  have pf := h.prod_fit
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e16 : lo len (.slot .wide 16) = numBase + 16 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have mo : maskOff = 12 := rfl
  have io : invOff = 0 := rfl
  have ao : accOff = 8 := rfl
  have mo' : multOff = 48 := rfl
  have po : prodOff = 256 := rfl
  have ma : mulAOff = 2312 := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have split : cwc len .wide + cwc len .wide = 2 * cwc len .wide := by omega
  -- The coefficient.
  refine WP.seq (WP.mono (coefficient_ok h c.p (val32_low (b := cwc len .wide) (by rw [split]; exact hmp) hmpb)
    hmpl (val32_low (b := cwc len .wide) (by rw [split]; exact hmq) hmqb) c.qi) fun u₁ ⟨F₁, V₁, K₁⟩ => ?_)
  have h₁ := h.keepF K₁ (by decide) (by decide) F₁ (coR_fit h)
  have k₁ : ∀ {d k : Nat}, lo len (.slot .wide 9) ≤ d → d + 4 * k ≤ bytes →
      val32 u₁.mem base d k = val32 s.mem base d k := fun hd hk => coR_keep h F₁ h.crt.room hd hk
  have a₁ := acc_keep h F₁ h.crt.room (coR_fit h) (by
    intro q hq; simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega)
  -- `m_q + q h`.
  refine WP.seq (WP.mono (recombine_ok h₁ (q := componentValue m₀ args 8) (hc := (mp + safeM p - mq % safeM p) %
      safeM p * componentValue m₀ args 14 % safeM p) (mq := mq)
    (by rw [k₁ (d := lo len (.slot .wide 11)) (k := cwc len .wide) (by omega) (by omega)]; exact c.q)
    (by simp only [sv] at V₁; exact V₁)
    (by rw [k₁ (d := lo len (.slot .wide 17)) (k := 2 * cwc len .wide) (by omega) (by omega)]; exact hmq)) fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
  rw [sp₁] at F₂
  have a₂ := acc_keep h F₂ h.crt.room (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [multOff, prodOff, mulAOff] <;> omega)
  -- The result cleared unless accepted, and written out.
  unfold exportResult
  refine maskResult_ok h₂ (c := cb) (by rw [a₂, a₁, hacc]) fun u₃ O₃ V₃ K₃ => ?_
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega))
  refine WP.mono (writeResult_ok h₃) fun t ⟨B, A, F, Kt⟩ => ⟨fun fits => ?_, ?_, ?_, ?_⟩
  · cases cb
    · rw [V₃] at B
      simp only [Bool.false_eq_true, ↓reduceIte] at B ⊢
      exact B (Nat.two_pow_pos _)
    · have fits := fits rfl
      have r64 : r < 2 ^ (32 * (2 * cwc len .wide)) :=
        Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (by omega))
      have R₂ : val32 u₂.mem base (lo len (.slot .wide 19)) (cwc len .wide) = r :=
        val32_low (b := cwc len .wide) (by rw [split]; exact V₂ r64)
          (Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [V₃, R₂] at B
      simp only [↓reduceIte] at B ⊢
      exact B fits
  · have a₃ : u₃.mem.readW (off base accOff) 32 = cmask cb := by
      rw [show u₃.mem.readW (off base accOff) 32 = u₂.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₃.w32 (d := accOff) (.inl (by omega)) (by omega)), a₂, a₁, hacc]
    rw [A, a₃]; cases cb <;> rfl
  · have F₃ : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₂.mem u₃.mem :=
      body_of_outside O₃ (.inr ⟨by omega, by omega⟩) (by omega)
    have Ft : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₃.mem t.mem :=
      F.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp [rtBody])
    refine ((((toBody F₁ ?_ (by omega)).trans (toBody F₂ ?_ (by omega))).trans F₃).trans Ft)
    · intro q hq; simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact .inl (show 0 + 4 ≤ 32 by omega)
      · exact .inl (show 12 + 4 ≤ 32 by omega)
      · exact .inr ⟨by dsimp only; omega, by have := coR_fit h _ (by simp : (numBase, 9 * st len .wide) ∈ coR len); exact this⟩
    · intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact .inr ⟨by simp only [multOff]; omega, by simp only [multOff]; omega⟩
      · exact .inr ⟨by simp only [prodOff]; omega, by dsimp only; omega⟩
      · exact .inr ⟨by simp only [mulAOff]; omega, by dsimp only; omega⟩
      · exact .inr ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact (((K₁.trans K₂).trans (K₃.mono (by decide))).trans (Kt.mono (by decide)))

/-- Private CRT at a run-time width: the result written out, cleared unless the key and the input are
accepted, and the acceptance in `eax`. -/
theorem sized_ok (h : In base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa sized s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accepted s.mem args then outputValue s.mem args else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (accepted s.mem args)).toNat ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lb := len_le_bc len
  have bw := bc_eq_cwc len .wide
  have nB := h.crt.modulus_bound
  have g := bc_ge h.lower' .wide
  have facts := h.crt.factor_bounds valid
  have pow : 2 ^ (8 * len) ≤ 2 ^ (32 * cwc len .wide) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold sized
  refine front_ok h fun u₁ h₁ F₁ c₁ A₁ K₁ => ?_
  refine powers_ok h₁ c₁ h.crt.dpLen h.crt.dqLen fun u₂ h₂ F₂ c₂ A₂ MP MQ K₂ => ?_
  have pl : (componentValue s.mem args 6) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.1 nB) pow
  have ql : (componentValue s.mem args 8) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.2 nB) pow
  have sp := safeM_lt pl (by omega)
  have sq := safeM_lt ql (by omega)
  have mpl : (componentValue s.mem args 4) ^ componentValue s.mem args 10 % safeM (componentValue s.mem args 6) < safeM (componentValue s.mem args 6) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 6); omega)
  have mql : (componentValue s.mem args 4) ^ componentValue s.mem args 12 % safeM (componentValue s.mem args 8) < safeM (componentValue s.mem args 8) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 8); omega)
  refine WP.mono (back_ok h₂ c₂ MP mpl (by omega) MQ (by omega) (cb := decide (accepted s.mem args))
    (by rw [A₂, A₁])) fun t ⟨B, E, F, K⟩ => ⟨?_, E, ?_, ?_⟩
  · by_cases acc : accepted s.mem args
    · obtain ⟨R, Rlt⟩ := accepted_result (dp := componentValue s.mem args 10)
        (dq := componentValue s.mem args 12) (qi := componentValue s.mem args 14) (x := (componentValue s.mem args 4)) facts.1 facts.2.1
        facts.2.2 acc.1
      have B' := B (fun _ => by omega)
      simp only [acc, decide_true, ↓reduceIte] at B' ⊢
      rw [B', R]; rfl
    · have B' := B (fun hc => absurd (of_decide_eq_true hc) acc)
      simp only [acc, decide_false, Bool.false_eq_true, ↓reduceIte] at B' ⊢
      exact B'
  · have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    rw [sp₁] at F₂
    rw [sp₂] at F
    exact (F₁.trans F₂).trans F
  · exact (K₁.trans K₂).trans K

end

end VG.Proof.Bignum.X86.CrtRt
