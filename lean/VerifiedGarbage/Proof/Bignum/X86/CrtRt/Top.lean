module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
public import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Bignum.X86.CrtRt.Sized`, which only this module used -/

section

/-! # Private CRT at a run-time width, from the arguments to the result

`sized_ok`: the components read, the key and input accepted or not, both
factors' powers, the coefficient, the recombination, and the result written
out (cleared unless accepted), with `eax` the acceptance. Every byte of the
working space may change but the saved registers' (`rtBody`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue)

/-- What private CRT at a run-time width writes: the working space but its saved registers, the
output and the zone below `sp` its calls write. -/
def rtBody (base out : Addr) (bytes len : Nat) (sp : BitVec 32) : List Region :=
  [⟨base, 32⟩, ⟨off base 48, bytes - 48⟩, ⟨out, len⟩, below sp 96]

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
  toBody (ws := [(a, n)]) (frameR_of_outside O (by rcases w with w | w <;> dsimp only at w <;> omega_arith) (by simp))
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact w) fit

/-- A component below `2^(8 l)` for its length `l`. -/
theorem comp_lt (m : Mem) (args : Nat → BitVec 32) (i : Nat) :
    componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  obtain B := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
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
  obtain sp : safeM p = p := ite_eq_left ⟨hp, hop⟩
  obtain sq : safeM q = q := ite_eq_left ⟨hq, hoq⟩
  rw [sp, sq]
  refine ⟨?_, ?_⟩
  · unfold VG.Proof.Bignum.crtResult
    rw [VG.Proof.Bignum.crt_coefficient_natural (by omega_using [hp])]
  · rw [← product]; exact VG.Proof.Bignum.crt_recombine_bound (by omega_using [hp]) (Nat.mod_lt _ (by omega_using [hq]))

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The wide slots 9 to 17 hold the components (`n` of `2 B` bytes, the others of `B`) and `m_p` and
`m_q` (of `2 B` bytes). -/
structure Comps (base : Addr) (len : Nat) (args : Nat → BitVec 32) (m₀ m : Mem) : Prop where
  n : val32 m base (lo len (.slot .wide 9)) (2 * cwc len .wide) = componentValue m₀ args 2
  x : val32 m base (lo len (.slot .wide 15)) (2 * cwc len .wide) = componentValue m₀ args 4
  p : val32 m base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue m₀ args 6
  q : val32 m base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue m₀ args 8
  dp : val32 m base (lo len (.slot .wide 12)) (cwc len .wide) = componentValue m₀ args 10
  dq : val32 m base (lo len (.slot .wide 13)) (cwc len .wide) = componentValue m₀ args 12
  qi : val32 m base (lo len (.slot .wide 14)) (2 * cwc len .wide) = componentValue m₀ args 14

/-- The components kept by changes to the bytes below the wide slot 9 or from 16 on. -/
theorem Comps.keep {m₀ m m' : Mem} (c : Comps base len args m₀ m)
    (k : ∀ {j : Nat} {w : Nat}, 9 ≤ j → j ≤ 15 → w ≤ 2 * cwc len .wide →
      val32 m' base (lo len (.slot .wide j)) w = val32 m base (lo len (.slot .wide j)) w) :
    Comps base len args m₀ m' :=
  ⟨by rw [k (by decide) (by decide) (Nat.le_refl _)]; exact c.n,
    by rw [k (by decide) (by decide) (Nat.le_refl _)]; exact c.x, by rw [k (by decide) (by decide) (by omega_using [])]; exact c.p,
    by rw [k (by decide) (by decide) (by omega_using [])]; exact c.q, by rw [k (by decide) (by decide) (by omega_using [])]; exact c.dp,
    by rw [k (by decide) (by decide) (by omega_using [])]; exact c.dq, by rw [k (by decide) (by decide) (Nat.le_refl _)]; exact c.qi⟩

/-- The wide slots 9 to 17, within the working space. -/
theorem wide_hi (h : RIn base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hw : w ≤ 2 * cwc len .wide) :
    numBase ≤ lo len (.slot .wide j) ∧ lo len (.slot .wide j) + 4 * w ≤ lo len (.slot .wide 18) ∧
      lo len (.slot .wide 18) ≤ bytes := by
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega)
  rw [Nat.succ_mul] at this
  omega_using [hw, f, bw, est, ej, e18, this]

/-- A component below `2^(32 W)` for the modulus's words `W` of 32 bits. -/
theorem comp_wide (h : RIn base bytes len args s) (m : Mem) {i : Nat} (hi : i ∈ componentArguments) :
    componentValue m args i < 2 ^ (32 * cwc len .wide) := by
  have := comp_lt m args i
  obtain b := h.crt.bounded i hi
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [b, lb, bw]))

/-- The components read and the key and input accepted or not. -/
theorem front_ok (h : RIn base bytes len args s) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, RIn base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args s.mem u.mem →
      u.mem.readW (off base accOff) 32 = cmask (decide (accepted s.mem args)) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq importComponents (.seq validate P)) s Q := by
  have bl := h.bytes_lt
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  have pf := h.prod_fit
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁, K₁⟩ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [f, e9, e18]))
  obtain nlt : componentValue s.mem args 2 < 2 ^ (32 * cwc len .wide) := by
    have := h.crt.modulus_bound
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [lb, bw]))
  obtain X₁' : val32 u₁.mem base (lo len (.slot .wide 15)) (cwc len .wide) = componentValue s.mem args 4 :=
    val32_low (b := cwc len .wide) (by rw [← Nat.two_mul]; exact X₁) (comp_wide h s.mem (by decide))
  obtain QI₁' : val32 u₁.mem base (lo len (.slot .wide 14)) (cwc len .wide) = componentValue s.mem args 14 :=
    val32_low (b := cwc len .wide) (by rw [← Nat.two_mul]; exact QI₁) (comp_wide h s.mem (by decide))
  refine WP.seq (WP.mono (validate_ok h₁ N₁ nlt P₁ Q₁ QI₁' X₁') fun u₂ ⟨F₂, A₂, K₂⟩ => ?_)
  obtain h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain C₂ : Comps base len args s.mem u₂.mem :=
    Comps.keep ⟨N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁⟩ fun hj9 hj hw =>
      valR_keep h₁ F₂ (sp₁ ▸ h₁.room) (wide_hi h hj9 (by omega_using [hj]) hw).1
        (by have := wide_hi h hj9 (by omega_using [hj]) hw; omega_using [this])
  refine k u₂ h₂ ?_ C₂ ?_ (K₁.trans K₂)
  · refine (body_of_outside O₁ (.inr ⟨by omega, by omega⟩) (by omega_using [bl])).trans (toBody F₂ ?_ (by omega_using [bl]))
    intro p hp; simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact .inl (show 8 + 4 ≤ 32 by omega_using [])
    · exact .inr ⟨by simp only [multOff]; omega_using [], by simp only [multOff]; omega_using [pf, nb]⟩
    · exact .inr ⟨by simp only [prodOff]; omega_using [], by omega_using [pf]⟩
    · exact .inr ⟨by simp only [mulAOff]; omega_using [], by omega_using [pf]⟩
  · apply BitVec.eq_of_toNat_eq
    rw [show (u₂.mem.readW (off base accOff) 32).toNat = w32 u₂.mem base accOff from rfl, A₂]
    rfl

theorem stR_body (h : RIn base bytes len args s) {o : Nat} (ho : o ≤ 19) : ∀ q ∈ stR len o, Body bytes q := by
  obtain fit := stR_fit h ho
  obtain T := h.table_fit .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  intro q hq
  have := fit q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact .inl (show 0 + 8 ≤ 32 by omega_using [])
  · exact .inr ⟨by dsimp only; omega_using [nb], this⟩
  · exact .inr ⟨by dsimp only; omega_using [e20, t0, nb], this⟩
  · exact .inr ⟨by dsimp only; omega_using [eo, nb], this⟩

/-- A factor fits half the width when its length does. -/
theorem fits_half {m : Mem} {i : Nat} (hl : (args (i + 1)).toNat ≤ bc len .half) :
    componentValue m args i < 2 ^ (32 * cwc len .half) := by
  have := comp_lt m args i
  obtain bh := bc_eq_cwc len .half
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [hl, bh]))

/-- The wide slots `a` and `b` exchanged through the wide slot 18, which only the wide slots 9 to 18
change. -/
theorem swap_ok (h : RIn base bytes len args s) {a b w : Nat} {n : Cnt} (N : CntOk n) (ha9 : 9 ≤ a)
    (hab : a < b) (hb : b ≤ 17) (hcb : cb len n = 4 * w) (hw : w ≤ 2 * cwc len .wide) :
    WP isa (swap a b n) s fun u =>
      Outside base (lo len (.slot .wide 9)) (10 * st len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide a)) w = val32 s.mem base (lo len (.slot .wide b)) w ∧
      val32 u.mem base (lo len (.slot .wide b)) w = val32 s.mem base (lo len (.slot .wide a)) w ∧
      (∀ j v, 9 ≤ j → j ≤ 17 → j ≠ a → j ≠ b → v ≤ 2 * cwc len .wide →
        val32 u.mem base (lo len (.slot .wide j)) v = val32 s.mem base (lo len (.slot .wide j)) v) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  have bl := h.bytes_lt
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  obtain ea := el a
  obtain eb := el b
  obtain e9 := el 9
  obtain e18 := el 18
  obtain s9 := Nat.mul_le_mul_right (st len .wide) ha9
  obtain sab := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ b by omega_arith)
  obtain sb := Nat.mul_le_mul_right (st len .wide) (show b + 1 ≤ 18 by omega_arith)
  rw [Nat.succ_mul] at sab sb
  obtain cwn : cw len n = w := by simp only [cw, hcb]; omega_arith
  -- Each number of a wide slot `j` from 9 to 17 apart from slots `a`, `b` and 18.
  obtain apart : ∀ j v, 9 ≤ j → j ≤ 17 → j ≠ a → j ≠ b → v ≤ 2 * cwc len .wide →
      (lo len (.slot .wide j) + 4 * v ≤ lo len (.slot .wide a) ∨ lo len (.slot .wide a) + cb len n ≤ lo len (.slot .wide j)) ∧
      (lo len (.slot .wide j) + 4 * v ≤ lo len (.slot .wide b) ∨ lo len (.slot .wide b) + cb len n ≤ lo len (.slot .wide j)) ∧
      lo len (.slot .wide j) + 4 * v ≤ lo len (.slot .wide 18) := fun j v hj9 hj ha hb' hv => by
    obtain ej := el j
    obtain sj := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega_arith)
    rw [Nat.succ_mul] at sj
    refine ⟨?_, ?_, by omega_arith⟩
    · rcases Nat.lt_or_gt_of_ne ha with l | l
      · have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ a by omega_arith)
        rw [Nat.succ_mul] at this; exact .inl (by omega_arith)
      · have := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ j by omega_arith)
        rw [Nat.succ_mul] at this; exact .inr (by omega_arith)
    · rcases Nat.lt_or_gt_of_ne hb' with l | l
      · have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ b by omega_arith)
        rw [Nat.succ_mul] at this; exact .inl (by omega_arith)
      · have := Nat.mul_le_mul_right (st len .wide) (show b + 1 ≤ j by omega_arith)
        rw [Nat.succ_mul] at this; exact .inr (by omega_arith)
  unfold swap
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide 18) N (by omega_arith) (by omega_arith)
    (.inr (by omega_arith))) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copy_ok h₁ (x := .slot .wide b) (d := .slot .wide a) N (by omega_arith) (by omega_arith)
    (.inl (by omega_arith))) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.mono (copy_ok h₂ (x := .slot .wide 18) (d := .slot .wide b) N (by omega_arith) (by omega_arith)
    (.inl (by omega_arith))) fun u ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_, fun j v hj9 hj ha hb' hv => ?_, (K₁.trans K₂).trans K₃⟩
  · exact ((O₁.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))).trans
      (O₃.mono (by omega_arith) (by omega_arith))
  · rw [cwn] at V₂ V₁
    rw [O₃.val32 (.inl (by omega_arith)) (by omega_arith), V₂, O₁.val32 (.inl (by omega_arith)) (by omega_arith)]
  · rw [cwn] at V₃ V₁
    rw [V₃, O₂.val32 (.inr (by omega_arith)) (by omega_arith), V₁]
  · obtain ⟨A, B, E⟩ := apart j v hj9 hj ha hb' hv
    rw [O₃.val32 B (by omega_arith), O₂.val32 A (by omega_arith), O₁.val32 (.inl E) (by omega_arith)]

/-- One factor's step: the power of the factor in the wide slot 10 into 16, and the factors, their
exponents, their powers and their lengths exchanged; one factor fewer left. -/
theorem factorStep_ok (h : RIn base bytes len args s) {A B dA dB x r LA LB k : Nat}
    (hA : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = A)
    (hB : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = B)
    (hdA : val32 s.mem base (lo len (.slot .wide 12)) (cwc len .wide) = dA)
    (hdB : val32 s.mem base (lo len (.slot .wide 13)) (cwc len .wide) = dB)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (2 * cwc len .wide) = x) (hxn : x < 2 ^ (32 * cwc len .wide))
    (hr : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = r)
    (hLA : w32 s.mem base lenOff = LA) (hLB : w32 s.mem base otherLenOff = LB)
    (hk : w32 s.mem base leftOff = k + 1)
    (fits : LA ≤ bc len .half → A < 2 ^ (32 * cwc len .half) ∧ dA < 2 ^ (32 * cwc len .half))
    {pc : Option Nat} (P : PreG s base bytes len args pc (safeM A))
    (pfit : FitG len args pc .wide ∧ (LA ≤ bc len .half → FitG len args pc .half)) :
    WP isa (factorStep pc) s fun u => RIn base bytes len args u ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem ∧
      (∀ j v, (j = 9 ∨ j = 14 ∨ j = 15) → v ≤ 2 * cwc len .wide →
        val32 u.mem base (lo len (.slot .wide j)) v = val32 s.mem base (lo len (.slot .wide j)) v) ∧
      u.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 ∧
      val32 u.mem base (lo len (.slot .wide 10)) (cwc len .wide) = B ∧
      val32 u.mem base (lo len (.slot .wide 11)) (cwc len .wide) = A ∧
      val32 u.mem base (lo len (.slot .wide 12)) (cwc len .wide) = dB ∧
      val32 u.mem base (lo len (.slot .wide 13)) (cwc len .wide) = dA ∧
      val32 u.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) = r ∧
      val32 u.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = x ^ dA % safeM A ∧
      w32 u.mem base lenOff = LB ∧ w32 u.mem base otherLenOff = LA ∧ w32 u.mem base leftOff = k ∧
      u.zf = some (decide (k = 0)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  obtain e9 := el 9
  obtain e18 := el 18
  have nb : numBase = 3336 := rfl
  obtain hw : ∀ {j : Nat}, 9 ≤ j → j ≤ 17 → lo len (.slot .wide j) + 4 * (2 * cwc len .wide) ≤ lo len (.slot .wide 18) ∧
      lo len (.slot .wide 9) ≤ lo len (.slot .wide j) := fun {j} hj9 hj => by
    obtain W := wide_hi h hj9 hj (Nat.le_refl _)
    obtain m9 := Nat.mul_le_mul_right (st len .wide) hj9
    exact ⟨W.2.1, by rw [el j]; omega_arith⟩
  obtain hdr : ∀ d, d + 4 ≤ 32 → d + 4 ≤ bytes := fun d hd => by omega_arith
  obtain wfit : ∀ d, d + 4 ≤ 32 → d + 4 ≤ 2 ^ 64 := fun d hd => by omega_arith
  obtain hout : ∀ d (m : Mem) (v : BitVec 32), d + 4 ≤ 32 → Outside base 0 bytes m (m.writeW (off base d) v) :=
    fun d m v hd => (writeW32_outside m base v (wfit d hd)).mono (Nat.zero_le _) (by have := hdr d hd; omega_arith)
  unfold factorStep
  -- The power.
  refine WP.seq (WP.mono (power_ok h (f := 10) (e := 12) (o := 16) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hA hdA hx hxn (by rw [hLA]; exact fits) P ⟨pfit.1, by rw [hLA]; exact pfit.2⟩)
    fun u₁ ⟨F₁, V₁, K₁⟩ => ?_)
  obtain h₁ := h.keepF K₁ (by decide) (by decide) F₁ (stR_fit h (by decide))
  obtain S₁ : ∀ {j v : Nat}, 9 ≤ j → j ≤ 17 → j ≠ 16 → v ≤ 2 * cwc len .wide →
      val32 u₁.mem base (lo len (.slot .wide j)) v = val32 s.mem base (lo len (.slot .wide j)) v := by
    intro j v hj9 hj h16 hv
    obtain W := hw hj9 hj
    obtain e16 := el 16
    obtain ej := el j
    rcases Nat.lt_or_gt_of_ne h16 with l | l
    · have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 16 by omega_arith)
      rw [Nat.succ_mul] at this
      exact stR_keep h (o := 16) (by decide) (by decide) F₁ h.room (by omega_arith) (by omega_arith) (.inl (by omega_arith))
    · have := Nat.mul_le_mul_right (st len .wide) (show 17 ≤ j by omega_arith)
      exact stR_keep h (o := 16) (by decide) (by decide) F₁ h.room (by omega_arith) (by omega_arith) (.inr (by omega_arith))
  obtain H₁ : ∀ d, d + 4 ≤ 32 → 8 ≤ d → w32 u₁.mem base d = w32 s.mem base d := fun d hd h8 => by
    rw [← w32_val32_one, ← w32_val32_one]
    refine frameR_val32 F₁ h.room nw (by omega_arith) ?_ (stR_fit h (by decide))
    obtain T := h.table_fit .wide
    obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
    obtain e20 := el 20
    obtain e16 := el 16
    intro q hq; simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
  -- The exchanges.
  obtain cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  obtain cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  refine WP.seq (WP.mono (swap_ok h₁ (a := 10) (b := 11) (w := cwc len .wide) (one_ok .wide) (by decide) (by decide)
    (by decide) (by omega_arith) (by omega_arith)) fun u₂ ⟨O₂, A₂, B₂, R₂, K₂⟩ => ?_)
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (swap_ok h₂ (a := 12) (b := 13) (w := cwc len .wide) (one_ok .wide) (by decide) (by decide)
    (by decide) (by omega_arith) (by omega_arith)) fun u₃ ⟨O₃, A₃, B₃, R₃, K₃⟩ => ?_)
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (swap_ok h₃ (a := 16) (b := 17) (w := 2 * cwc len .wide) (two_ok .wide) (by decide)
    (by decide) (by decide) (by omega_arith) (Nat.le_refl _)) fun u₄ ⟨O₄, A₄, B₄, R₄, K₄⟩ => ?_)
  obtain h₄ := h₃.keep K₄ (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega_arith))
  -- The header words through the exchanges.
  obtain O₂₄ : Outside base (lo len (.slot .wide 9)) (10 * st len .wide) u₁.mem u₄.mem := (O₂.trans O₃).trans O₄
  obtain H₄ : ∀ d, d + 4 ≤ 32 → w32 u₄.mem base d = w32 u₁.mem base d := fun d hd =>
    Outside.w32 O₂₄ (.inl (by omega_arith)) (by omega_arith)
  -- The lengths exchanged and the count down one.
  unfold factorNext
  refine wp_movS (readSrc_sc h₄.scratch (d := lenOff) (hdr lenOff (by decide))) fun v₁ a₁ _ => ?_
  obtain hv₁ := h₄.regs a₁.keeps a₁.mem
  refine wp_movS (readSrc_sc hv₁.scratch (d := otherLenOff) (hdr otherLenOff (by decide))) fun v₂ a₂ _ => ?_
  obtain K₅ : Keeps [.eax, .ecx] u₄ v₂ := (a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))
  obtain h₅ := h₄.regs K₅ (by rw [a₂.mem, a₁.mem])
  refine wp_storeS (h₅.scratch.ea (d := lenOff) (by simp only [lenOff]; omega_arith))
    (h₅.scratch.write (d := lenOff) (hdr lenOff (by decide))) fun v₃ s₃ => ?_
  obtain h₆ := h₅.keep (s₃.keeps []) (by decide) (by decide)
    (by rw [s₃.mem]; exact hout _ _ _ (by decide))
  refine wp_storeS (h₆.scratch.ea (d := otherLenOff) (by simp only [otherLenOff]; omega_arith))
    (h₆.scratch.write (d := otherLenOff) (hdr otherLenOff (by decide))) fun v₄ s₄ => ?_
  obtain h₇ := h₆.keep (s₄.keeps []) (by decide) (by decide)
    (by rw [s₄.mem]; exact hout _ _ _ (by decide))
  refine wp_movS (readSrc_sc h₇.scratch (d := leftOff) (hdr leftOff (by decide))) fun v₅ a₅ _ => ?_
  refine wp_subZ rfl fun v₆ a₆ z₆ => ?_
  obtain K₈ : Keeps [.eax] v₄ v₆ := (a₅.keeps.mono (by decide)).trans (a₆.keeps.mono (by decide))
  obtain h₈ := h₇.regs K₈ (by rw [a₆.mem, a₅.mem])
  refine wp_storeS (h₈.scratch.ea (d := leftOff) (by simp only [leftOff]; omega_arith))
    (h₈.scratch.write (d := leftOff) (hdr leftOff (by decide))) fun t s₉ => WP.block_nil ?_
  -- The memory of the block: three header words.
  obtain mv₂ : v₂.mem = u₄.mem := by rw [a₂.mem, a₁.mem]
  obtain mv₆ : v₆.mem = v₄.mem := by rw [a₆.mem, a₅.mem]
  obtain Lw : w32 v₂.mem base lenOff = LA := by rw [mv₂, H₄ _ (by decide), H₁ _ (by decide) (by decide), hLA]
  obtain Ow : w32 v₂.mem base otherLenOff = LB := by rw [mv₂, H₄ _ (by decide), H₁ _ (by decide) (by decide), hLB]
  obtain Kw : w32 v₄.mem base leftOff = k + 1 := by
    rw [s₄.mem, w32_write_ne nw (by simp only [otherLenOff]; omega_arith) (by simp only [leftOff]; omega_arith)
      (by decide), s₃.mem, w32_write_ne nw (by simp only [lenOff]; omega_arith) (by simp only [leftOff]; omega_arith)
      (by decide), mv₂, H₄ _ (by decide), H₁ _ (by decide) (by decide), hk]
  obtain k32 : k + 1 < 2 ^ 32 := by
    have := (v₄.mem.readW (off base leftOff) 32).isLt
    have Kw' : (v₄.mem.readW (off base leftOff) 32).toNat = k + 1 := Kw
    omega_arith
  obtain eax₆ : v₆.gpr .eax = BitVec.ofNat 32 k := by
    rw [a₆.gpr, a₅.gpr]
    apply BitVec.eq_of_toNat_eq
    have W' : (v₄.mem.readW (off base leftOff) 32).toNat = k + 1 := Kw
    have one : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, W', one, BitVec.toNat_ofNat]
    omega_arith
  obtain eaxv : v₂.gpr .eax = v₂.mem.readW (off base lenOff) 32 := by rw [a₂.other _ (by decide), a₁.gpr, ← mv₂]
  obtain ecxv : v₂.gpr .ecx = v₂.mem.readW (off base otherLenOff) 32 := by rw [a₂.gpr, a₂.mem]
  obtain mt : t.mem = ((v₂.mem.writeW (off base lenOff) (v₂.gpr .ecx)).writeW (off base otherLenOff) (v₂.gpr .eax)).writeW
      (off base leftOff) (BitVec.ofNat 32 k) := by
    rw [s₉.mem, mv₆, eax₆, s₄.mem, s₃.mem, s₃.gpr]
  obtain Oblk : Outside base lenOff 12 u₄.mem t.mem := by
    rw [mt, ← mv₂]
    refine (((writeW32_outside _ _ _ (by simp only [lenOff]; omega_arith)).mono (Nat.le_refl _) (by decide)).trans
      ((writeW32_outside _ _ _ (by simp only [otherLenOff]; omega_arith)).mono (by decide) (by decide))).trans
      ((writeW32_outside _ _ _ (by simp only [leftOff]; omega_arith)).mono (by decide) (by decide))
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (((K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
      ((K₅.mono (by decide)).trans ((s₃.keeps _).trans ((s₄.keeps _).trans ((K₈.mono (by decide)).trans (s₉.keeps _)))))
  obtain Wt : ∀ {j v : Nat}, 9 ≤ j → j ≤ 17 → v ≤ 2 * cwc len .wide →
      val32 t.mem base (lo len (.slot .wide j)) v = val32 u₄.mem base (lo len (.slot .wide j)) v := by
    intro j v hj9 hj hv
    obtain W := hw hj9 hj
    exact Outside.val32 Oblk (.inr (by simp only [lenOff]; omega_arith)) (by omega_arith)
  refine ⟨h₈.keep (s₉.keeps []) (by decide) (by decide)
      (by rw [s₉.mem]; exact hout _ _ _ (by decide)), ?_, fun j v hj hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Kall⟩
  · -- The frame.
    obtain b1 : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u₁.mem :=
      toBody F₁ (stR_body h (by decide)) (by omega_arith)
    obtain b2 : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₁.mem u₄.mem :=
      body_of_outside O₂₄ (.inr ⟨by omega_arith, by omega_arith⟩) (by omega_arith)
    obtain b3 : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₄.mem t.mem :=
      body_of_outside Oblk (.inl (by simp only [lenOff]; omega_arith)) (by omega_arith)
    exact (b1.trans b2).trans b3
  · rcases hj with rfl | rfl | rfl <;>
      rw [Wt (by decide) (by decide) hv, R₄ _ _ (by decide) (by decide) (by decide) (by decide) hv,
        R₃ _ _ (by decide) (by decide) (by decide) (by decide) hv, R₂ _ _ (by decide) (by decide) (by decide)
        (by decide) hv, S₁ (by decide) (by decide) (by decide) hv]
  · apply BitVec.eq_of_toNat_eq
    show w32 t.mem base accOff = w32 s.mem base accOff
    rw [Outside.w32 Oblk (.inl (by decide)) (by simp only [accOff]; omega_arith), H₄ _ (by decide), H₁ _ (by decide) (by decide)]
  · rw [Wt (by decide) (by decide) (by omega_arith), R₄ _ _ (by decide) (by decide) (by decide) (by decide)
      (by omega_arith), R₃ _ _ (by decide) (by decide) (by decide) (by decide) (by omega_arith), A₂,
      S₁ (by decide) (by decide) (by decide) (by omega_arith), hB]
  · rw [Wt (by decide) (by decide) (by omega_arith), R₄ _ _ (by decide) (by decide) (by decide) (by decide)
      (by omega_arith), R₃ _ _ (by decide) (by decide) (by decide) (by decide) (by omega_arith), B₂,
      S₁ (by decide) (by decide) (by decide) (by omega_arith), hA]
  · rw [Wt (by decide) (by decide) (by omega_arith), R₄ _ _ (by decide) (by decide) (by decide) (by decide)
      (by omega_arith), A₃, R₂ _ _ (by decide) (by decide) (by decide) (by decide) (by omega_arith),
      S₁ (by decide) (by decide) (by decide) (by omega_arith), hdB]
  · rw [Wt (by decide) (by decide) (by omega_arith), R₄ _ _ (by decide) (by decide) (by decide) (by decide)
      (by omega_arith), B₃, R₂ _ _ (by decide) (by decide) (by decide) (by decide) (by omega_arith),
      S₁ (by decide) (by decide) (by decide) (by omega_arith), hdA]
  · rw [Wt (by decide) (by decide) (Nat.le_refl _), A₄, R₃ _ _ (by decide) (by decide) (by decide) (by decide)
      (Nat.le_refl _), R₂ _ _ (by decide) (by decide) (by decide) (by decide) (Nat.le_refl _),
      S₁ (by decide) (by decide) (by decide) (Nat.le_refl _), hr]
  · rw [Wt (by decide) (by decide) (Nat.le_refl _), B₄, R₃ _ _ (by decide) (by decide) (by decide) (by decide)
      (Nat.le_refl _), R₂ _ _ (by decide) (by decide) (by decide) (by decide) (Nat.le_refl _), V₁]
  · rw [mt, w32_write_ne nw (by simp only [leftOff]; omega_arith) (by simp only [lenOff]; omega_arith) (by decide),
      w32_write_ne nw (by simp only [otherLenOff]; omega_arith) (by simp only [lenOff]; omega_arith) (by decide),
      w32_write_self, ecxv, ← Ow]
  · rw [mt, w32_write_ne nw (by simp only [leftOff]; omega_arith) (by simp only [otherLenOff]; omega_arith)
      (by decide), w32_write_self, eaxv, ← Lw]
  · rw [mt, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [s₉.zf, z₆, ← a₆.gpr, eax₆]
    congr 1
    by_cases e : k = 0
    · subst e; rfl
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hz
      have := congrArg BitVec.toNat hz
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact e (by simpa using this)

/-- The factors' loop after `j` steps: the factors (wide slots 10 and 11), their exponents (12 and
13) and their lengths exchanged when `j` is one, `2 - j` factors left, `m_p` in 17 after one step,
and in 16 with `m_q` in 17 after two; the components `n`, `x` and `qInv`, and the acceptance mask, as
they were. -/
structure FacInv (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (m₀ : Mem) (s : State) (j : Nat)
    (t : State) : Prop where
  inp : RIn base bytes len args t
  frame : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem
  comps : ∀ i v, (i = 9 ∨ i = 14 ∨ i = 15) → v ≤ 2 * cwc len .wide →
    val32 t.mem base (lo len (.slot .wide i)) v = val32 s.mem base (lo len (.slot .wide i)) v
  acc : t.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32
  f₁ : val32 t.mem base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue m₀ args (if j = 1 then 8 else 6)
  f₂ : val32 t.mem base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue m₀ args (if j = 1 then 6 else 8)
  e₁ : val32 t.mem base (lo len (.slot .wide 12)) (cwc len .wide) = componentValue m₀ args (if j = 1 then 12 else 10)
  e₂ : val32 t.mem base (lo len (.slot .wide 13)) (cwc len .wide) = componentValue m₀ args (if j = 1 then 10 else 12)
  l₁ : w32 t.mem base lenOff = (args (if j = 1 then 9 else 7)).toNat
  l₂ : w32 t.mem base otherLenOff = (args (if j = 1 then 7 else 9)).toNat
  left : w32 t.mem base leftOff = 2 - j
  one : j = 1 → val32 t.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) =
    componentValue m₀ args 4 ^ componentValue m₀ args 10 % safeM (componentValue m₀ args 6)
  two : j = 2 → val32 t.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) =
      componentValue m₀ args 4 ^ componentValue m₀ args 10 % safeM (componentValue m₀ args 6) ∧
    val32 t.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) =
      componentValue m₀ args 4 ^ componentValue m₀ args 12 % safeM (componentValue m₀ args 8)
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t

/-- The factors' lengths and their count into the header: the loop's state before its first step. -/
theorem factorsInit_ok (h : RIn base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem) :
    WP isa (.block factorsInit) s (FacInv base bytes len args m₀ s 0) := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  obtain hdr : ∀ d, d + 4 ≤ 32 → d + 4 ≤ bytes := fun d hd => by omega_arith
  obtain wfit : ∀ d, d + 4 ≤ 32 → d + 4 ≤ 2 ^ 64 := fun d hd => by omega_arith
  obtain hout : ∀ d (m : Mem) (v : BitVec 32), d + 4 ≤ 32 → Outside base 0 bytes m (m.writeW (off base d) v) :=
    fun d m v hd => (writeW32_outside m base v (wfit d hd)).mono (Nat.zero_le _) (by have := hdr d hd; omega_arith)
  -- The lengths and the count into the header.
  unfold factorsInit
  refine wp_movS (h.arg (i := 7) (by decide)) fun u₁ a₁ _ => ?_
  obtain h₁ := h.regs a₁.keeps a₁.mem
  refine wp_storeS (h₁.scratch.ea (d := lenOff) (by simp only [lenOff]; omega_arith))
    (h₁.scratch.write (d := lenOff) (hdr lenOff (by decide))) fun u₂ s₂ => ?_
  obtain h₂ := h₁.keep (s₂.keeps []) (by decide) (by decide)
    (by rw [s₂.mem]; exact hout _ _ _ (by decide))
  refine wp_movS (h₂.arg (i := 9) (by decide)) fun u₃ a₃ _ => ?_
  obtain h₃ := h₂.regs a₃.keeps a₃.mem
  refine wp_storeS (h₃.scratch.ea (d := otherLenOff) (by simp only [otherLenOff]; omega_arith))
    (h₃.scratch.write (d := otherLenOff) (hdr otherLenOff (by decide))) fun u₄ s₄ => ?_
  obtain h₄ := h₃.keep (s₄.keeps []) (by decide) (by decide)
    (by rw [s₄.mem]; exact hout _ _ _ (by decide))
  refine wp_movS rfl fun u₅ a₅ _ => ?_
  obtain h₅ := h₄.regs a₅.keeps a₅.mem
  refine wp_storeS (h₅.scratch.ea (d := leftOff) (by simp only [leftOff]; omega_arith))
    (h₅.scratch.write (d := leftOff) (hdr leftOff (by decide))) fun u₆ s₆ => WP.block_nil ?_
  obtain mt : u₆.mem = ((s.mem.writeW (off base lenOff) (args 7)).writeW (off base otherLenOff) (args 9)).writeW
      (off base leftOff) (BitVec.ofNat 32 2) := by
    rw [s₆.mem, a₅.mem, a₅.gpr, s₄.mem, a₃.mem, a₃.gpr, s₂.mem, a₁.mem, a₁.gpr]; rfl
  obtain O₆ : Outside base lenOff 12 s.mem u₆.mem := by
    rw [mt]
    refine (((writeW32_outside _ _ _ (by simp only [lenOff]; omega_arith)).mono (Nat.le_refl _) (by decide)).trans
      ((writeW32_outside _ _ _ (by simp only [otherLenOff]; omega_arith)).mono (by decide) (by decide))).trans
      ((writeW32_outside _ _ _ (by simp only [leftOff]; omega_arith)).mono (by decide) (by decide))
  obtain K₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₆ :=
    ((a₁.keeps.mono (by decide)).trans (s₂.keeps _)).trans (((a₃.keeps.mono (by decide)).trans (s₄.keeps _)).trans
      ((a₅.keeps.mono (by decide)).trans (s₆.keeps _)))
  obtain W₆ : ∀ {i v : Nat}, 9 ≤ i → i ≤ 17 → v ≤ 2 * cwc len .wide →
      val32 u₆.mem base (lo len (.slot .wide i)) v = val32 s.mem base (lo len (.slot .wide i)) v := by
    intro i v hi9 hi hv
    have := wide_hi h hi9 hi hv
    exact Outside.val32 O₆ (.inr (by simp only [lenOff]; omega_arith)) (by omega_arith)
  refine ⟨h₅.keep (s₆.keeps []) (by decide) (by decide)
      (by rw [s₆.mem]; exact hout _ _ _ (by decide)),
    body_of_outside O₆ (.inl (by simp only [lenOff]; omega_arith)) (by omega_arith),
    fun i v hi hv => W₆ (by omega_arith) (by omega_arith) hv, ?_,
    (W₆ (by decide) (by decide) (by omega_arith)).trans c.p, (W₆ (by decide) (by decide) (by omega_arith)).trans c.q,
    (W₆ (by decide) (by decide) (by omega_arith)).trans c.dp, (W₆ (by decide) (by decide) (by omega_arith)).trans c.dq,
    ?_, ?_, ?_, fun e => absurd e (by decide), fun e => absurd e (by decide), K₆⟩
  · apply BitVec.eq_of_toNat_eq
    show w32 u₆.mem base accOff = w32 s.mem base accOff
    exact Outside.w32 O₆ (.inl (by decide)) (by simp only [accOff]; omega_arith)
  · rw [mt, w32_write_ne nw (by simp only [leftOff]; omega_arith) (by simp only [lenOff]; omega_arith) (by decide),
      w32_write_ne nw (by simp only [otherLenOff]; omega_arith) (by simp only [lenOff]; omega_arith) (by decide),
      w32_write_self]; rfl
  · rw [mt, w32_write_ne nw (by simp only [leftOff]; omega_arith) (by simp only [otherLenOff]; omega_arith)
      (by decide), w32_write_self]; rfl
  · rw [mt, w32_write_self]; rfl

/-- A step of the factors' loop. -/
theorem facStep_ok {m₀ : Mem} (c : Comps base len args m₀ s.mem) (dpl : args 11 = args 7) (dql : args 13 = args 9)
    {j : Nat} {t : State} (hj : j < 2) (I : FacInv base bytes len args m₀ s j t) {pc : Option Nat}
    (P : PreG t base bytes len args pc (safeM (componentValue m₀ args (if j = 1 then 8 else 6))))
    (pfit : FitG len args pc .wide ∧ ((args (if j = 1 then 9 else 7)).toNat ≤ bc len .half → FitG len args pc .half)) :
    WP isa (factorStep pc) t fun u => FacInv base bytes len args m₀ s (j + 1) u ∧ u.zf = some (decide (j + 1 = 2)) := by
  obtain sp : t.gpr .esp = s.gpr .esp := I.keeps.1 _ (by decide)
  obtain hx : val32 t.mem base (lo len (.slot .wide 15)) (2 * cwc len .wide) = componentValue m₀ args 4 :=
    (I.comps 15 _ (.inr (.inr rfl)) (Nat.le_refl _)).trans c.x
  obtain hxn := comp_wide I.inp m₀ (i := 4) (by decide)
  obtain keepComps : ∀ {u : State}, (∀ i v, (i = 9 ∨ i = 14 ∨ i = 15) → v ≤ 2 * cwc len .wide →
      val32 u.mem base (lo len (.slot .wide i)) v = val32 t.mem base (lo len (.slot .wide i)) v) →
      ∀ i v, (i = 9 ∨ i = 14 ∨ i = 15) → v ≤ 2 * cwc len .wide →
      val32 u.mem base (lo len (.slot .wide i)) v = val32 s.mem base (lo len (.slot .wide i)) v :=
    fun C i v hi hv => (C i v hi hv).trans (I.comps i v hi hv)
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega_arith
  · refine WP.mono (factorStep_ok I.inp (A := componentValue m₀ args 6) (B := componentValue m₀ args 8)
      (dA := componentValue m₀ args 10) (dB := componentValue m₀ args 12) (k := 1) I.f₁ I.f₂ I.e₁ I.e₂ hx hxn rfl I.l₁
      I.l₂ I.left (fun hl => ⟨fits_half hl, fits_half (args := args) (len := len) (m := m₀) (i := 10)
        (show (args 11).toNat ≤ _ by rw [dpl]; exact hl)⟩) P pfit)
      fun u ⟨hu, Fu, Cu, Au, F1, F2, E1, E2, _, R17, L1, L2, Lk, Z, Ku⟩ => ⟨?_, Z⟩
    rw [sp] at Fu
    exact ⟨hu, I.frame.trans Fu, keepComps Cu, Au.trans I.acc, F1, F2, E1, E2, L1, L2, Lk, fun _ => R17,
      fun e => absurd e (by decide), I.keeps.trans Ku⟩
  · refine WP.mono (factorStep_ok I.inp (A := componentValue m₀ args 8) (B := componentValue m₀ args 6)
      (dA := componentValue m₀ args 12) (dB := componentValue m₀ args 10) (k := 0) I.f₁ I.f₂ I.e₁ I.e₂ hx hxn
      (I.one rfl) I.l₁ I.l₂ I.left (fun hl => ⟨fits_half hl, fits_half (args := args) (len := len) (m := m₀)
        (i := 12) (show (args 13).toNat ≤ _ by rw [dql]; exact hl)⟩) P pfit)
      fun u ⟨hu, Fu, Cu, Au, F1, F2, E1, E2, R16, R17, L1, L2, Lk, Z, Ku⟩ => ⟨?_, Z⟩
    rw [sp] at Fu
    exact ⟨hu, I.frame.trans Fu, keepComps Cu, Au.trans I.acc, F1, F2, E1, E2, L1, L2, Lk,
      fun e => absurd e (by decide), fun _ => ⟨R16, R17⟩, I.keeps.trans Ku⟩

/-- Both factors' powers: `x^dP mod p` into the wide slot 16, `x^dQ mod q` into 17. -/
theorem powers_ok (h : RIn base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem)
    (dpl : args 11 = args 7) (dql : args 13 = args 9) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, RIn base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args m₀ u.mem →
      u.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 →
      val32 u.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 10 % safeM (componentValue m₀ args 6) →
      val32 u.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 12 % safeM (componentValue m₀ args 8) →
      w32 u.mem base lenOff = (args 7).toNat →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq (.block factorsInit) (.seq (.loop factorStep .ne) P)) s Q := by
  refine WP.seq (WP.mono (factorsInit_ok h c) fun u₀ I₀ => ?_)
  refine WP.seq (WP.mono (PublicRt.countLoop (N := 2) (by decide) (fun j t => FacInv base bytes len args m₀ s j t)
    (fun j t hj I => facStep_ok c dpl dql hj I (pc := none) trivial ⟨trivial, fun _ => trivial⟩) I₀) fun u I => ?_)
  exact k u I.inp I.frame ⟨(I.comps 9 _ (.inl rfl) (Nat.le_refl _)).trans c.n,
    (I.comps 15 _ (.inr (.inr rfl)) (Nat.le_refl _)).trans c.x, I.f₁, I.f₂, I.e₁, I.e₂,
    (I.comps 14 _ (.inr (.inl rfl)) (Nat.le_refl _)).trans c.qi⟩ I.acc (I.two rfl).1 (I.two rfl).2 I.l₁ I.keeps

/-- Changes to ranges apart from the acceptance mask keep it. -/
theorem acc_keep (h : RIn base bytes len args s) {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes) (fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    (hw : ∀ p ∈ ws, p.1 + p.2 ≤ accOff ∨ accOff + 4 ≤ p.1) :
    m'.readW (off base accOff) 32 = m.readW (off base accOff) 32 := by
  obtain f := h.slot_fit .wide (j := 0) (by decide)
  obtain z : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have nb : numBase = 3336 := rfl
  have ao : accOff = 8 := rfl
  apply BitVec.eq_of_toNat_eq
  show w32 m' base accOff = w32 m base accOff
  rw [← w32_val32_one, ← w32_val32_one]
  exact frameR_val32 F R h.scratch.nowrap (by omega_using [f, z, nb, ao]) (fun p hp => by have := hw p hp; omega_using [this]) fit

/-- The coefficient, the recombination and the result written out. -/
theorem back_ok (h : RIn base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem) {mp mq : Nat}
    (hmp : val32 s.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) = mp)
    (hmpl : mp < safeM (componentValue m₀ args 6))
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq) (hmqb : mq < 2 ^ (32 * cwc len .wide))
    (hlen : w32 s.mem base lenOff = (args 7).toNat) {cb : Bool} (hacc : s.mem.readW (off base accOff) 32 = cmask cb)
    {pc : Option Nat} (P : PreG s base bytes len args pc (safeM (componentValue m₀ args 6)))
    (pfit : FitG len args pc .wide ∧ ((args 7).toNat ≤ bc len .half → FitG len args pc .half)) :
    let p := componentValue m₀ args 6
    let r := mq + componentValue m₀ args 8 *
      ((mp + safeM p - mq % safeM p) % safeM p * componentValue m₀ args 14 % safeM p)
    WP isa (.seq (coefficient pc) (.seq recombine exportResult)) s fun t =>
      ((cb = true → r < 2 ^ (8 * len)) → Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if cb then r else 0) len) ∧
      t.gpr .eax = BitVec.ofNat 32 cb.toNat ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  intro p r
  have bl := h.bytes_lt
  obtain bw := bc_eq_cwc len .wide
  obtain lb := len_le_bc len
  obtain f19 := h.slot_fit .wide (j := 19) (by decide)
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
  obtain split : cwc len .wide + cwc len .wide = 2 * cwc len .wide := by omega_arith
  -- The coefficient.
  refine WP.seq (WP.mono (coefficient_ok h c.p hmp hmpl hmq hmqb c.qi (comp_wide h m₀ (by decide))
    (comp_wide h m₀ (by decide)) (fun hl => fits_half (i := 6) (by rw [← hlen]; exact hl)) P
    ⟨pfit.1, fun hl => pfit.2 (by rw [← hlen]; exact hl)⟩) fun u₁ ⟨F₁, V₁, K₁⟩ => ?_)
  obtain h₁ := h.keepF K₁ (by decide) (by decide) F₁ (coR_fit h)
  obtain k₁ : ∀ {d k : Nat}, lo len (.slot .wide 9) ≤ d → d + 4 * k ≤ bytes →
      val32 u₁.mem base d k = val32 s.mem base d k := fun hd hk => coR_keep h F₁ h.room hd hk
  obtain a₁ := acc_keep h F₁ h.room (coR_fit h) (by
    intro q hq; simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega_arith)
  -- `m_q + q h`.
  refine WP.seq (WP.mono (recombine_ok h₁ (q := componentValue m₀ args 8) (hc := (mp + safeM p - mq % safeM p) %
      safeM p * componentValue m₀ args 14 % safeM p) (mq := mq)
    (by rw [k₁ (d := lo len (.slot .wide 11)) (k := cwc len .wide) (by omega_arith) (by omega_arith)]; exact c.q)
    (by simp only [sv] at V₁; exact V₁)
    (by rw [k₁ (d := lo len (.slot .wide 17)) (k := 2 * cwc len .wide) (by omega_arith) (by omega_arith)]; exact hmq)) fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  obtain h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith)
  rw [sp₁] at F₂
  obtain a₂ := acc_keep h F₂ h.room (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by
    intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [multOff, prodOff, mulAOff] <;> omega_arith)
  -- The result cleared unless accepted, and written out.
  unfold exportResult
  refine maskResult_ok h₂ (c := cb) (by rw [a₂, a₁, hacc]) fun u₃ O₃ V₃ K₃ => ?_
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by omega_arith))
  refine WP.mono (writeResult_ok h₃ h₃.crt.outFit h₃.crt.outWrite h₃.crt.outApart) fun t ⟨B, A, F, Kt⟩ => ⟨fun fits => ?_, ?_, ?_, ?_⟩
  · cases cb
    · rw [V₃] at B
      simp only [Bool.false_eq_true, ↓reduceIte] at B ⊢
      exact B (Nat.two_pow_pos _)
    · have fits := fits rfl
      obtain r64 : r < 2 ^ (32 * (2 * cwc len .wide)) :=
        Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (by omega_arith))
      obtain R₂ : val32 u₂.mem base (lo len (.slot .wide 19)) (cwc len .wide) = r :=
        val32_low (b := cwc len .wide) (by rw [split]; exact V₂ r64)
          (Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (by omega_arith)))
      rw [V₃, R₂] at B
      simp only [↓reduceIte] at B ⊢
      exact B fits
  · have a₃ : u₃.mem.readW (off base accOff) 32 = cmask cb := by
      rw [show u₃.mem.readW (off base accOff) 32 = u₂.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₃.w32 (d := accOff) (.inl (by omega_arith)) (by omega_arith)), a₂, a₁, hacc]
    rw [A, a₃]; cases cb <;> rfl
  · have F₃ : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₂.mem u₃.mem :=
      body_of_outside O₃ (.inr ⟨by omega_arith, by omega_arith⟩) (by omega_arith)
    obtain Ft : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) u₃.mem t.mem :=
      F.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp [rtBody])
    refine ((((toBody F₁ ?_ (by omega_arith)).trans (toBody F₂ ?_ (by omega_arith))).trans F₃).trans Ft)
    · intro q hq; simp only [coR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact .inl (show 0 + 4 ≤ 32 by omega_arith)
      · exact .inl (show 12 + 4 ≤ 32 by omega_arith)
      · exact .inr ⟨by dsimp only; omega_arith, by have := coR_fit h _ (by simp : (numBase, 9 * st len .wide) ∈ coR len); exact this⟩
    · intro q hq; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact .inr ⟨by simp only [multOff]; omega_arith, by simp only [multOff]; omega_arith⟩
      · exact .inr ⟨by simp only [prodOff]; omega_arith, by dsimp only; omega_arith⟩
      · exact .inr ⟨by simp only [mulAOff]; omega_arith, by dsimp only; omega_arith⟩
      · exact .inr ⟨by dsimp only; omega_arith, by dsimp only; omega_arith⟩
  · exact (((K₁.trans K₂).trans (K₃.mono (by decide))).trans (Kt.mono (by decide)))

/-- Private CRT at a run-time width: the result written out, cleared unless the key and the input are
accepted, and the acceptance in `eax`. -/
theorem sized_ok (h : RIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa sized s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accepted s.mem args then outputValue s.mem args else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (accepted s.mem args)).toNat ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  have nB := h.crt.modulus_bound
  obtain g := bc_ge h.lower' .wide
  obtain facts := h.crt.factor_bounds valid
  obtain pow : 2 ^ (8 * len) ≤ 2 ^ (32 * cwc len .wide) := Nat.pow_le_pow_right (by decide) (by omega_using [lb, bw])
  unfold sized
  refine front_ok h fun u₁ h₁ F₁ c₁ A₁ K₁ => ?_
  refine powers_ok h₁ c₁ h.crt.dpLen h.crt.dqLen fun u₂ h₂ F₂ c₂ A₂ MP MQ L₂ K₂ => ?_
  obtain pl : (componentValue s.mem args 6) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.1 nB) pow
  obtain ql : (componentValue s.mem args 8) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.2 nB) pow
  obtain sp := safeM_lt pl (by omega)
  obtain sq := safeM_lt ql (by omega)
  obtain mpl : (componentValue s.mem args 4) ^ componentValue s.mem args 10 % safeM (componentValue s.mem args 6) < safeM (componentValue s.mem args 6) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 6); omega_using [this])
  obtain mql : (componentValue s.mem args 4) ^ componentValue s.mem args 12 % safeM (componentValue s.mem args 8) < safeM (componentValue s.mem args 8) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 8); omega_using [this])
  refine WP.mono (back_ok h₂ c₂ MP mpl MQ (by omega_using [sq, mql]) L₂ (cb := decide (accepted s.mem args))
    (by rw [A₂, A₁]) (pc := none) trivial ⟨trivial, fun _ => trivial⟩) fun t ⟨B, E, F, K⟩ => ⟨?_, E, ?_, ?_⟩
  · by_cases acc : accepted s.mem args
    · obtain ⟨R, Rlt⟩ := accepted_result (dp := componentValue s.mem args 10)
        (dq := componentValue s.mem args 12) (qi := componentValue s.mem args 14) (x := (componentValue s.mem args 4)) facts.1 facts.2.1
        facts.2.2 acc.1
      obtain B' := B (fun _ => by omega_using [nB, Rlt])
      simp only [acc, decide_true, ↓reduceIte] at B' ⊢
      rw [B', R]; rfl
    · have B' := B (fun hc => absurd (of_decide_eq_true hc) acc)
      simp only [acc, decide_false, Bool.false_eq_true, ↓reduceIte] at B' ⊢
      exact B'
  · have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    obtain sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    rw [sp₁] at F₂
    rw [sp₂] at F
    exact (F₁.trans F₂).trans F
  · exact (K₁.trans K₂).trans K

/-! ## With `pre` -/

/-- With `pre`, the key and input accepted: the input below `n`, and `qInv` below `p`. -/
abbrev acceptedPre (m : Mem) (args : Nat → BitVec 32) : Prop :=
  componentValue m args 4 < componentValue m args 2 ∧ componentValue m args 14 < componentValue m args 6

/-- Argument 18 and factor `i`'s cached value, apart from the output. -/
structure PreOut (s : State) (args : Nat → BitVec 32) (len i : Nat) : Prop where
  arg : Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ ⟨byteAddr (args 0), len⟩
  val : Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ ⟨byteAddr (args 0), len⟩

theorem PreOut.keep {t : State} {i : Nat} (O : PreOut s args len i) {regs : List Reg} (K : Keeps regs s t)
    (sp : .esp ∉ regs) : PreOut t args len i :=
  ⟨by rw [show VG.Proof.Dsa.X86.stackAddress t preArg = VG.Proof.Dsa.X86.stackAddress s preArg by
      simp only [VG.Proof.Dsa.X86.stackAddress, K.1 _ sp]]; exact O.arg, O.val⟩

/-- The cached value holds after what private CRT writes (`rtBody`), apart from it. -/
theorem PreR2.keepBody {t : State} {i p : Nat} (h : RIn base bytes len args s) (P : PreR2 s base bytes len args i p)
    (O : PreOut s args len i) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    (F : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem) :
    PreR2 t base bytes len args i p := by
  obtain f := h.slot_fit .wide (j := 0) (by decide)
  obtain z : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have nb : numBase = 3336 := rfl
  obtain s0 : Region.Sub ⟨base, 32⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := 0) (n := 32) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [f, z, nb])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain s48 : Region.Sub ⟨off base 48, bytes - 48⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := 48) (n := bytes - 48) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [f, z, nb])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine P.keep K sp F (fun r hr => ?_) (fun r hr => ?_) <;>
    simp only [rtBody, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl | rfl
  · exact (P.apart_sub s0).1
  · exact (P.apart_sub s48).1
  · exact O.arg
  · exact P.argBelow h.room
  · exact (P.apart_sub s0).2
  · exact (P.apart_sub s48).2
  · exact O.val
  · exact P.apartSp

/-- With `pre`: the components read, and the input and `qInv` accepted or not. -/
theorem frontPre_ok (h : RIn base bytes len args s) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, RIn base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args s.mem u.mem →
      u.mem.readW (off base accOff) 32 = cmask (decide (acceptedPre s.mem args)) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq importComponents (.seq validatePre P)) s Q := by
  have bl := h.bytes_lt
  obtain f := h.slot_fit .wide (j := 18) (by decide)
  have pf := h.prod_fit
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁, K₁⟩ => ?_)
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [f, e9, e18]))
  obtain nlt : componentValue s.mem args 2 < 2 ^ (32 * cwc len .wide) := by
    have := h.crt.modulus_bound
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using [lb, bw]))
  obtain X₁' : val32 u₁.mem base (lo len (.slot .wide 15)) (cwc len .wide) = componentValue s.mem args 4 :=
    val32_low (b := cwc len .wide) (by rw [← Nat.two_mul]; exact X₁) (comp_wide h s.mem (by decide))
  obtain QI₁' : val32 u₁.mem base (lo len (.slot .wide 14)) (cwc len .wide) = componentValue s.mem args 14 :=
    val32_low (b := cwc len .wide) (by rw [← Nat.two_mul]; exact QI₁) (comp_wide h s.mem (by decide))
  refine WP.seq (WP.mono (validatePre_ok h₁ N₁ nlt P₁ QI₁' X₁') fun u₂ ⟨F₂, A₂, K₂⟩ => ?_)
  obtain h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain C₂ : Comps base len args s.mem u₂.mem :=
    Comps.keep ⟨N₁, X₁, P₁, Q₁, DP₁, DQ₁, QI₁⟩ fun hj9 hj hw =>
      valR_keep h₁ F₂ (sp₁ ▸ h₁.room) (wide_hi h hj9 (by omega_using [hj]) hw).1
        (by have := wide_hi h hj9 (by omega_using [hj]) hw; omega_using [this])
  refine k u₂ h₂ ?_ C₂ ?_ (K₁.trans K₂)
  · refine (body_of_outside O₁ (.inr ⟨by omega, by omega⟩) (by omega_using [bl])).trans (toBody F₂ ?_ (by omega_using [bl]))
    intro p hp; simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact .inl (show 8 + 4 ≤ 32 by omega_using [])
    · exact .inr ⟨by simp only [multOff]; omega_using [], by simp only [multOff]; omega_using [pf, nb]⟩
    · exact .inr ⟨by simp only [prodOff]; omega_using [], by omega_using [pf]⟩
    · exact .inr ⟨by simp only [mulAOff]; omega_using [], by omega_using [pf]⟩
  · apply BitVec.eq_of_toNat_eq
    rw [show (u₂.mem.readW (off base accOff) 32).toNat = w32 u₂.mem base accOff from rfl, A₂]

/-- With `pre`: both factors' powers, each from its cached value. -/
theorem powersPre_ok (h : RIn base bytes len args s) {m₀ : Mem} (c : Comps base len args m₀ s.mem)
    (dpl : args 11 = args 7) (dql : args 13 = args 9)
    (P0 : PreR2 s base bytes len args 0 (safeM (componentValue m₀ args 6))) (O0 : PreOut s args len 0)
    (P1 : PreR2 s base bytes len args 1 (safeM (componentValue m₀ args 8))) (O1 : PreOut s args len 1)
    {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, RIn base bytes len args u → Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem u.mem →
      Comps base len args m₀ u.mem →
      u.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 →
      val32 u.mem base (lo len (.slot .wide 16)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 10 % safeM (componentValue m₀ args 6) →
      val32 u.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) =
        componentValue m₀ args 4 ^ componentValue m₀ args 12 % safeM (componentValue m₀ args 8) →
      w32 u.mem base lenOff = (args 7).toNat →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u → WP isa P u Q) :
    WP isa (.seq (.block factorsInit) (.seq (powers true) P)) s Q := by
  obtain lb := len_le_bc len
  have p7 := h.crt.pShort
  have q9 := h.crt.qShort
  refine WP.seq (WP.mono (factorsInit_ok h c) fun u₀ I₀ => ?_)
  refine WP.seq (WP.seq (WP.mono (facStep_ok c dpl dql (j := 0) (by decide) I₀ (pc := some 0)
    (P0.keepBody h O0 I₀.keeps (by decide) I₀.frame)
    ⟨fitG_of h.lower (by show (args 7).toNat ≤ _; omega_using [lb, p7]), fun hl => fitG_of h.lower hl⟩) fun u₁ ⟨I₁, _⟩ => ?_))
  refine WP.mono (facStep_ok c dpl dql (j := 1) (by decide) I₁ (pc := some 1)
    (P1.keepBody h O1 I₁.keeps (by decide) I₁.frame)
    ⟨fitG_of h.lower (by show (args 9).toNat ≤ _; omega_using [lb, q9]), fun hl => fitG_of h.lower hl⟩) fun u I => ?_
  exact k u I.1.inp I.1.frame ⟨(I.1.comps 9 _ (.inl rfl) (Nat.le_refl _)).trans c.n,
    (I.1.comps 15 _ (.inr (.inr rfl)) (Nat.le_refl _)).trans c.x, I.1.f₁, I.1.f₂, I.1.e₁, I.1.e₂,
    (I.1.comps 14 _ (.inr (.inl rfl)) (Nat.le_refl _)).trans c.qi⟩ I.1.acc (I.1.two rfl).1 (I.1.two rfl).2 I.1.l₁
    I.1.keeps

/-- Private CRT at a run-time width with `pre`, which holds for `p q = n`: what `sized_ok` states. -/
theorem sizedPre_ok (h : RIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true)
    (pq : componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2)
    (P0 : PreR2 s base bytes len args 0 (safeM (componentValue s.mem args 6))) (O0 : PreOut s args len 0)
    (P1 : PreR2 s base bytes len args 1 (safeM (componentValue s.mem args 8))) (O1 : PreOut s args len 1) :
    WP isa (sized true) s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accepted s.mem args then outputValue s.mem args else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (accepted s.mem args)).toNat ∧
      Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  have nB := h.crt.modulus_bound
  obtain g := bc_ge h.lower' .wide
  obtain facts := h.crt.factor_bounds valid
  obtain pow : 2 ^ (8 * len) ≤ 2 ^ (32 * cwc len .wide) := Nat.pow_le_pow_right (by decide) (by omega_using [lb, bw])
  obtain accE : decide (acceptedPre s.mem args) = decide (accepted s.mem args) :=
    decide_eq_decide.mpr ⟨fun a => ⟨pq, a⟩, fun a => a.2⟩
  have p7 := h.crt.pShort
  show WP isa (.seq importComponents (.seq validatePre (.seq (.block factorsInit) (.seq (powers true)
    (.seq (coefficient (some 0)) (.seq recombine exportResult)))))) s _
  refine frontPre_ok h fun u₁ h₁ F₁ c₁ A₁ K₁ => ?_
  refine powersPre_ok h₁ c₁ h.crt.dpLen h.crt.dqLen (P0.keepBody h O0 K₁ (by decide) F₁) (O0.keep K₁ (by decide))
    (P1.keepBody h O1 K₁ (by decide) F₁) (O1.keep K₁ (by decide)) fun u₂ h₂ F₂ c₂ A₂ MP MQ L₂ K₂ => ?_
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  obtain pl : (componentValue s.mem args 6) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.1 nB) pow
  obtain ql : (componentValue s.mem args 8) < 2 ^ (32 * cwc len .wide) :=
    Nat.lt_of_lt_of_le (Nat.lt_trans facts.2.2 nB) pow
  obtain sp := safeM_lt pl (by omega)
  obtain sq := safeM_lt ql (by omega)
  obtain mpl : (componentValue s.mem args 4) ^ componentValue s.mem args 10 % safeM (componentValue s.mem args 6) < safeM (componentValue s.mem args 6) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 6); omega_using [this])
  obtain mql : (componentValue s.mem args 4) ^ componentValue s.mem args 12 % safeM (componentValue s.mem args 8) < safeM (componentValue s.mem args 8) := Nat.mod_lt _ (by have := safeM_gt (componentValue s.mem args 8); omega_using [this])
  refine WP.mono (back_ok h₂ c₂ MP mpl MQ (by omega_using [sq, mql]) L₂ (cb := decide (acceptedPre s.mem args))
    (by rw [A₂, A₁]) (pc := some 0) (P0.keepBody h O0 (K₁.trans K₂) (by decide) (F₁.trans F₂))
    ⟨fitG_of h.lower (by show (args 7).toNat ≤ _; omega_using [lb, p7]), fun hl => fitG_of h.lower hl⟩)
    fun t ⟨B, E, F, K⟩ => ⟨?_, by rw [E, accE], ?_, ?_⟩
  · rw [accE] at B
    by_cases acc : accepted s.mem args
    · obtain ⟨R, Rlt⟩ := accepted_result (dp := componentValue s.mem args 10)
        (dq := componentValue s.mem args 12) (qi := componentValue s.mem args 14) (x := (componentValue s.mem args 4)) facts.1 facts.2.1
        facts.2.2 acc.1
      obtain B' := B (fun _ => by omega_using [nB, Rlt])
      simp only [acc, decide_true, ↓reduceIte] at B' ⊢
      rw [B', R]; rfl
    · have B' := B (fun hc => absurd (of_decide_eq_true hc) acc)
      simp only [acc, decide_false, Bool.false_eq_true, ↓reduceIte] at B' ⊢
      exact B'
  · have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    rw [sp₂] at F
    exact (F₁.trans F₂).trans F
  · exact (K₁.trans K₂).trans K

end

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # Functional correctness and cdecl preservation of private CRT RSA at a run-time width

`body_ok`: the modulus checked, then `sized_ok` or the failure; `operation_ok`:
the registers saved and restored around it; `correct`: the contract.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue specResult specResult_eq)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem frameRt_saved {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame (rtBody base out bytes len sp) m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 48 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (Z : Region.Disjoint (VG.X86.below sp 96) ⟨base, bytes⟩)
    (S : Saved m (off base) g CrtRt.savedRegisters) : Saved m' (off base) g CrtRt.savedRegisters := by
  intro p hp
  obtain B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
    simp only [CrtRt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨off base 32, 16⟩)
    (Offset.contains base B.1 (by omega_using [B]) (by decide)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [rtBody, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base (by decide) (by decide)
  · exact Offset.disjoint base (.inl (by decide)) (by decide) (by omega_using [high])
  · exact A.sub_left (Offset.sub_base base (by omega_using [low]))
  · exact (Z.sub_right (Offset.sub_base base (by omega_using [low]))).symm

theorem frameRt_full {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame (rtBody base out bytes len sp) m m') (low : 48 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩, VG.X86.below sp 96] m m' := by
  apply F.sub
  intro r hr
  simp only [rtBody, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Region.sub_prefix (by omega_using [low])⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega_using [low])⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem restored_abi {s t u : State} (R : Restored t u s.gpr Crt.savedRegisters)
    (sp : t.gpr .esp = s.gpr .esp)
    (ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s u := by
  refine ⟨?_, by rw [R.mem]; exact ret⟩
  intro reg hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact (R.other _ (by decide)).trans sp

theorem ret_zone40 {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 96) := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]
  exact Offset.base_disjoint_below _ (by decide)

/-- The result and what may change. -/
def Post (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax) (specResult m args) ∧
    Frame (rtBody base (byteAddr (args 0)) bytes len sp) m t.mem

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem sized_post (h : RIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa CrtRt.sized s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (sized_ok h valid) fun t ⟨Y, B, F, K⟩ => ⟨⟨?_, F⟩, K⟩
  rw [specResult_eq, h.crt.modulus_length, valid]
  by_cases acc : accepted s.mem args
  · simp only [ite_true, acc, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_true]; rfl, by simpa only [acc, ite_true] using Y⟩
  · simp only [ite_true, acc, ite_false, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_false]; rfl,
      by simpa only [acc, ite_false, VG.Proof.Bignum.i2osp_zero'] using Y⟩

theorem failure_post (h : RIn base bytes len args s) (failed : specResult s.mem args = none) :
    WP isa PublicFn.failure s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lo := h.lower'
  have hi := h.upper'
  refine WP.mono (publicFailure_ok (by omega_using [lo]) (by omega_using [hi]) h.crt.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.crt.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [failed, Spec.Rsa.written]; exact ⟨B, Y⟩
  · have F := VG.Proof.Bignum.outside_frame O (by omega_using [hi] : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [rtBody, byteAddr])

theorem body_ok (h : RIn base bytes len args s) :
    WP isa CrtRt.body s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain nf := h.crt.fits 2 (by decide)
  obtain nr := h.crt.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [h.crt.modulus_length] at nf nr
  unfold CrtRt.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.crt.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower' h.upper' (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  obtain Msv : v.mem = s.mem := Mv.trans M
  obtain Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  obtain hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  obtain modulus : componentValue s.mem args 2 =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) := by
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat) = _
    rw [h.crt.modulus_length]
  rw [← modulus] at Z
  refine WP.ite (Spec.Rsa.modulusValid (componentValue s.mem args 2) len) Z ?_ ?_
  · intro valid
    refine WP.mono (sized_post hv (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩
  · intro invalid
    obtain failed : specResult v.mem args = none := by
      rw [specResult_eq, Msv, h.crt.modulus_length, invalid]
      rfl
    refine WP.mono (failure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩

end

theorem need_le {len words : Nat} (hl : 64 ≤ len) (hw : Spec.Rsa.scratchWords len ≤ words) :
    need len ≤ words * 8 := by
  simp only [need, st, bc, mw, Spec.Rsa.modulusWords, CrtRt.numBase, Spec.Rsa.scratchWords] at *
  omega_using [hl, hw]

theorem entry_eq : CrtRt.entry = Crt.entry := rfl
theorem restore_eq : CrtRt.restore = Crt.restore := rfl
theorem savedRegisters_eq : CrtRt.savedRegisters = Crt.savedRegisters := rfl

theorem operation_ok {s : State} (A : CrtABI s) :
    WP isa CrtRt.code s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (specResult s.mem (arg s)) ∧ abiPreserved s t := by
  obtain low : 48 ≤ (arg s 17).toNat * 8 := by have := A.used; omega_using [this]
  obtain high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega_using []
  unfold CrtRt.code
  rw [entry_eq]
  refine WP.seq (WP.mono (Crt.installed_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  obtain hI : RIn (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u :=
    In.ofInputs I (need_le A.lengths.1 A.scratchLength)
      (by simp only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))]) rfl
  refine WP.seq (WP.mono (body_ok hI) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  obtain Saved := frameRt_saved F I.outApart low high I.room.apart (savedRegisters_eq ▸ S)
  obtain espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  rw [espu] at F
  obtain Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    obtain Start := VG.Proof.Bignum.outside_frame O (by omega_using [])
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (frameRt_full F low)
  obtain Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact A.retScratch
    · rw [← A.outLength]; exact A.retOut
    · exact ret_zone40 A.stackLow
  rw [restore_eq]
  refine WP.mono (Crt.entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low
    (savedRegisters_eq ▸ Saved)) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega_using [])
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  obtain Specs : specResult u.mem (arg s) = specResult s.mem (arg s) := by
    unfold specResult
    rw [B 2 (by decide), B 4 (by decide), B 6 (by decide), B 8 (by decide),
      B 10 (by decide), B 12 (by decide), B 14 (by decide)]
  rw [Specs] at V
  exact V

theorem correct (s : State) (h : (Proof.Rsa.privateCrtContract abi 96).pre s) :
    ∃ trace t, Exec isa CrtRt.code s trace t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtContract abi 96).post s t := by
  obtain A := crtABI_of h
  obtain ⟨trace, t, E, V, P⟩ := operation_ok A
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold specResult at V
  rw [A.inLength, A.dpLength, A.dqLength, A.qiLength] at V
  exact V

end VG.Proof.Bignum.X86.CrtRt
