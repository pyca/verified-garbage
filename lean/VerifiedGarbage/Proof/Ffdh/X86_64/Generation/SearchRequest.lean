module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState

/-! # The verified controller selects the exact next entropy request -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem request_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (ha : s.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used)) :
    WP isa (.block request) s fun t =>
      t.gpr .rax = 0 ∧
      t.mem = writeController s.mem p.control
        [(3, BitVec.ofNat 64 (Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)] ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv1 : s.mem.readW (p.control + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have hv2 : s.mem.readW (p.control + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have hk := h.input.width_bounds.2
  have ht := h.input.tape_bound
  have hc := h.input.entropy_bound
  have hmax : max (p.c.rand.length - used) (256 * p.c.k) ≤ 33555456 :=
    Nat.max_le.mpr ⟨by omega_using [ht, hc], by omega_using [hk]⟩
  have ha64 : p.c.rand.length - used < 2 ^ 64 := by omega_using [ht, hc]
  have hk64 : p.c.k < 2 ^ 64 := by omega_using [hk]
  have hc64 : Spec.Ffdh.parameterEntropy p.c.bits < 2 ^ 64 := by omega_using [hc]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
    t.gpr .rax = 0 ∧ t.mem = writeController s.mem p.control
      [(3, BitVec.ofNat 64 (Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)]) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  have hmaxeq : max (p.c.rand.length - used) (256 * p.c.k) =
      if p.c.rand.length - used < 256 * p.c.k then 256 * p.c.k else p.c.rand.length - used := by
    by_cases hb : p.c.rand.length - used < 256 * p.c.k
    · simp [hb, Nat.max_eq_right (Nat.le_of_lt hb)]
    · have hk : 256 * p.c.k ≤ p.c.rand.length - used := by omega_using [hb]
      simp [hb, Nat.max_eq_left hk]
  have hmin (a b : Nat) : min a b = if a < b then a else b := by
    by_cases hb : a < b
    · simp [hb, Nat.min_eq_left (Nat.le_of_lt hb)]
    · have hk : b ≤ a := by omega_using [hb]
      simp [hb, Nat.min_eq_right hk]
  have hreq : Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used) =
      if 2 * max (p.c.rand.length - used) (256 * p.c.k) < Spec.Ffdh.parameterEntropy p.c.bits
      then 2 * max (p.c.rand.length - used) (256 * p.c.k) else Spec.Ffdh.parameterEntropy p.c.bits := by
    rw [Spec.Ffdh.parameterRequest, ← h.input.width_bits, hmin]
  have ha2 : (p.c.rand.length - used) * 2 < 2 ^ 64 := by
    omega_using [hmax, Nat.le_max_left (p.c.rand.length - used) (256 * p.c.k)]
  have hk2 : p.c.k * 256 * 2 < 2 ^ 64 := by omega_using [hk]
  have han : (BitVec.ofNat 64 (p.c.rand.length - used)).toNat = p.c.rand.length - used :=
    toNat_ofNat_of_lt ha64
  have hkn : (BitVec.ofNat 64 (p.c.k * 256)).toNat = p.c.k * 256 :=
    toNat_ofNat_of_lt (by omega_using [hk])
  have hcn : (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)).toNat =
      Spec.Ffdh.parameterEntropy p.c.bits := toNat_ofNat_of_lt hc64
  have ha2n : (BitVec.ofNat 64 (2 * (p.c.rand.length - used))).toNat = 2 * (p.c.rand.length - used) :=
    toNat_ofNat_of_lt (by omega_using [ha2])
  have hk2n : (BitVec.ofNat 64 (2 * (p.c.k * 256))).toNat = 2 * (p.c.k * 256) :=
    toNat_ofNat_of_lt (by omega_using [hk2])
  have hshl : BitVec.ofNat 64 p.c.k <<< 8 = BitVec.ofNat 64 (p.c.k * 256) := by
    rw [shift_ofNat]
  have h256 : 256 * p.c.k = p.c.k * 256 := Nat.mul_comm _ _
  rw [h256] at hmaxeq hreq
  unfold request writeController
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hab : p.c.rand.length - used < p.c.k * 256
  all_goals
    by_cases hcut : 2 * max (p.c.rand.length - used) (p.c.k * 256) < Spec.Ffdh.parameterEntropy p.c.bits
    all_goals
      have hcut' := hcut
      rw [hmaxeq] at hcut'
      first | rw [ite_eq_left hab] at hcut' | rw [ite_eq_right hab] at hcut'
      try simp only [Nat.mul_comm] at hcut'
      xrun [State.ea, field, off, h.r12, ha, hv1, hv2, hshl, BitVec.ofInt_natCast, Nat.reduceMul,
        hl 8 (by decide), hl 16 (by decide), hs 24 (by decide), hs 112 (by decide), eval, execCmov,
        hreq, hmaxeq, hab, hcut, hcut', shift_ofNat, Nat.reducePow, Nat.mul_comm,
        han, hkn, hcn, ha2n, hk2n, decide_true, decide_false, Bool.not_true, Bool.not_false]
      rfl

end VG.Proof.Ffdh.X86_64.Generation
