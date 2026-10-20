module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key's components read

`importComponents_ok`: `n` (wide slot 9, `2 B` bytes), the input (15), `p`
(10), `q` (11), `dP` (12), `dQ` (13) and `qInv` (14), each the number of its
argument's bytes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A wide slot's change keeps the other wide slots. -/
theorem wide_keep (h : In base bytes len args s) {a b n k : Nat} (hb : b ≤ 19) (hab : a ≠ b)
    (hn : n ≤ st len .wide) (hk : 4 * k ≤ st len .wide) {m m' : Mem}
    (O : VG.Proof.Mont.Outside base (lo len (.slot .wide a)) n m m') :
    val32 m' base (lo len (.slot .wide b)) k = val32 m base (lo len (.slot .wide b)) k := by
  have f := h.slot_fit .wide (j := 19) (by decide)
  have bl := h.bytes_lt
  have hb' := Nat.mul_le_mul_right (st len .wide) hb
  have ea : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have eb : lo len (.slot .wide b) = numBase + b * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  refine O.val32 ?_ (by omega)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ b by omega)
    rw [Nat.succ_mul] at this; exact .inr (by omega)
  · have := Nat.mul_le_mul_right (st len .wide) (show b + 1 ≤ a by omega)
    rw [Nat.succ_mul] at this; exact .inl (by omega)

/-- A component's bytes into the wide slot `j`. -/
theorem loadComp_ok (h : In base bytes len args s) {j : Nat} (hj : j ≤ 19) {n : Cnt} (N : CntOk n)
    (hn : cb len n ≤ st len .wide) (hlen : len ≤ cb len n) {i : Nat} (hi : i ∈ componentArguments) :
    WP isa (load (.slot .wide j) n i (i + 1)) s fun t =>
      val32 t.mem base (lo len (.slot .wide j)) (cw len n) = componentValue s.mem args i ∧
      VG.Proof.Mont.Outside base (lo len (.slot .wide j)) (cb len n) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have f := h.slot_fit .wide (j := j) (by omega)
  have hi18 : i + 1 < 18 := by
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  have pos := h.crt.positive i hi
  have bnd := h.crt.bounded i hi
  exact load_ok h N (by omega) (p := i) (l := i + 1) (L := (args (i + 1)).toNat) (by omega) hi18
    (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (args (i + 1)).isLt]))
    pos (by omega) (h.crt.fits i hi) (h.crt.readable i hi) (h.crt.apart i hi)

/-- The wide slots 9 to 15. -/
abbrev imR (len : Nat) : List (Nat × Nat) := [(lo len (.slot .wide 9), 7 * st len .wide)]

/-- The key's components read into the wide slots 9 to 15. -/
theorem importComponents_ok (h : In base bytes len args s) :
    WP isa importComponents s fun u =>
      VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = componentValue s.mem args 2 ∧
      val32 u.mem base (lo len (.slot .wide 15)) (cwc len .wide) = componentValue s.mem args 4 ∧
      val32 u.mem base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue s.mem args 6 ∧
      val32 u.mem base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue s.mem args 8 ∧
      val32 u.mem base (lo len (.slot .wide 12)) (cwc len .wide) = componentValue s.mem args 10 ∧
      val32 u.mem base (lo len (.slot .wide 13)) (cwc len .wide) = componentValue s.mem args 12 ∧
      val32 u.mem base (lo len (.slot .wide 14)) (cwc len .wide) = componentValue s.mem args 14 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have f := h.slot_fit .wide (j := 19) (by decide)
  have bl := h.bytes_lt
  have bw := bc_eq_cwc len .wide
  have lb := len_le_bc len
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega
  have n1 : cb len (one .wide) ≤ st len .wide := by rw [cb1]; omega
  have n2 : cb len (two .wide) ≤ st len .wide := by rw [cb2]; omega
  have l1 : len ≤ cb len (one .wide) := by rw [cb1]; omega
  have l2 : len ≤ cb len (two .wide) := by rw [cb2]; omega
  have k1 : 4 * cwc len .wide ≤ st len .wide := by omega
  have k2 : 4 * (2 * cwc len .wide) ≤ st len .wide := by omega
  -- An import's slot within the wide slots 9 to 15.
  have within : ∀ {j : Nat} {m m' : Mem}, 9 ≤ j → j ≤ 15 → ∀ {n : Nat}, n ≤ st len .wide →
      VG.Proof.Mont.Outside base (lo len (.slot .wide j)) n m m' → VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) m m' :=
    fun {j} {_ _} hj9 hj {_} hn O => O.mono
      (by have := Nat.mul_le_mul_right (st len .wide) hj9; show _ ≤ numBase + j * st len .wide; omega)
      (by have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 16 by omega); rw [Nat.succ_mul] at this
          show numBase + j * st len .wide + _ ≤ _; omega)
  -- The components' bytes, outside the working space.
  have cv : ∀ {m : Mem}, VG.Proof.Mont.Outside base 0 bytes s.mem m → ∀ {i}, i ∈ componentArguments →
      componentValue m args i = componentValue s.mem args i := fun O i hi => by
    unfold componentValue
    rw [VG.Proof.Bignum.scratch_bytes O (by have := (args (i + 1)).isLt; omega) (h.crt.apart i hi)]
  have wide : ∀ {t : State} {m m' : Mem}, VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) m m' →
      VG.Proof.Mont.Outside base 0 bytes m m' := fun O => O.mono (Nat.zero_le _) (by omega)
  unfold importComponents
  refine WP.seq (WP.mono (loadComp_ok h (j := 9) (by decide) (two_ok .wide) n2 l2 (i := 2) (by decide))
    fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  have O₁' := within (by decide) (by decide) n2 O₁
  have h₁ := h.keep K₁ (by decide) (by decide) (wide (t := s) O₁')
  refine WP.seq (WP.mono (loadComp_ok h₁ (j := 15) (by decide) (one_ok .wide) n1 l1 (i := 4) (by decide))
    fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  have O₂' := O₁'.trans (within (by decide) (by decide) n1 O₂)
  have h₂ := h.keep (K₁.trans K₂) (by decide) (by decide) (wide (t := s) O₂')
  refine WP.seq (WP.mono (loadComp_ok h₂ (j := 10) (by decide) (one_ok .wide) n1 l1 (i := 6) (by decide))
    fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  have O₃' := O₂'.trans (within (by decide) (by decide) n1 O₃)
  have h₃ := h.keep ((K₁.trans K₂).trans K₃) (by decide) (by decide) (wide (t := s) O₃')
  refine WP.seq (WP.mono (loadComp_ok h₃ (j := 11) (by decide) (one_ok .wide) n1 l1 (i := 8) (by decide))
    fun u₄ ⟨V₄, O₄, K₄⟩ => ?_)
  have O₄' := O₃'.trans (within (by decide) (by decide) n1 O₄)
  have h₄ := h.keep (((K₁.trans K₂).trans K₃).trans K₄) (by decide) (by decide) (wide (t := s) O₄')
  refine WP.seq (WP.mono (loadComp_ok h₄ (j := 12) (by decide) (one_ok .wide) n1 l1 (i := 10) (by decide))
    fun u₅ ⟨V₅, O₅, K₅⟩ => ?_)
  have O₅' := O₄'.trans (within (by decide) (by decide) n1 O₅)
  have h₅ := h.keep ((((K₁.trans K₂).trans K₃).trans K₄).trans K₅) (by decide) (by decide) (wide (t := s) O₅')
  refine WP.seq (WP.mono (loadComp_ok h₅ (j := 13) (by decide) (one_ok .wide) n1 l1 (i := 12) (by decide))
    fun u₆ ⟨V₆, O₆, K₆⟩ => ?_)
  have O₆' := O₅'.trans (within (by decide) (by decide) n1 O₆)
  have h₆ := h.keep (((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆) (by decide) (by decide)
    (wide (t := s) O₆')
  refine WP.mono (loadComp_ok h₆ (j := 14) (by decide) (one_ok .wide) n1 l1 (i := 14) (by decide))
    fun u ⟨V₇, O₇, K₇⟩ => ?_
  have O₇' := O₆'.trans (within (by decide) (by decide) n1 O₇)
  rw [cw2] at V₁
  rw [cw1] at V₂ V₃ V₄ V₅ V₆ V₇
  rw [cv (wide (t := s) O₁') (by decide)] at V₂
  rw [cv (wide (t := s) O₂') (by decide)] at V₃
  rw [cv (wide (t := s) O₃') (by decide)] at V₄
  rw [cv (wide (t := s) O₄') (by decide)] at V₅
  rw [cv (wide (t := s) O₅') (by decide)] at V₆
  rw [cv (wide (t := s) O₆') (by decide)] at V₇
  have kw : ∀ {a b k : Nat} {m m' : Mem}, a ≤ 19 → b ≤ 19 → a ≠ b → 4 * k ≤ st len .wide →
      VG.Proof.Mont.Outside base (lo len (.slot .wide a)) (cb len (one .wide)) m m' →
      val32 m' base (lo len (.slot .wide b)) k = val32 m base (lo len (.slot .wide b)) k :=
    fun _ hb hab hk O => wide_keep h hb hab n1 hk O
  refine ⟨O₇', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆).trans K₇)⟩
  · rw [kw (by decide) (by decide) (by decide) k2 O₇, kw (by decide) (by decide) (by decide) k2 O₆,
      kw (by decide) (by decide) (by decide) k2 O₅, kw (by decide) (by decide) (by decide) k2 O₄,
      kw (by decide) (by decide) (by decide) k2 O₃, kw (by decide) (by decide) (by decide) k2 O₂, V₁]
  · rw [kw (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆,
      kw (by decide) (by decide) (by decide) k1 O₅, kw (by decide) (by decide) (by decide) k1 O₄,
      kw (by decide) (by decide) (by decide) k1 O₃, V₂]
  · rw [kw (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆,
      kw (by decide) (by decide) (by decide) k1 O₅, kw (by decide) (by decide) (by decide) k1 O₄, V₃]
  · rw [kw (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆,
      kw (by decide) (by decide) (by decide) k1 O₅, V₄]
  · rw [kw (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆, V₅]
  · rw [kw (by decide) (by decide) (by decide) k1 O₇, V₆]
  · exact V₇

end

end VG.Proof.Bignum.X86.CrtRt
