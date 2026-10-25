module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Spec.Dsa

/-!
# The FFDH candidate on i686: a number halved in place

`halve` shifts a wide slot down a bit, a word at a time from the top, the
low bit of each word carried into the top of the next (`halve_ok`). After
`i` words, the top `i` words hold the top `i` words' value halved, and the
carry is that value's low bit.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

theorem ror_carry {c : Nat} (hc : c ≤ 1) : (BitVec.ofNat 32 c).rotateRight 1 = BitVec.ofNat 32 (c * 2 ^ 31) := by
  rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl <;> decide

theorem shr_or (w : BitVec 32) {c : Nat} (hc : c ≤ 1) :
    (w >>> 1 ||| BitVec.ofNat 32 (c * 2 ^ 31)).toNat = w.toNat / 2 + c * 2 ^ 31 := by
  have hw := w.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega_arith), Nat.pow_one, Nat.or_comm, Nat.mul_comm c,
    ← Nat.two_pow_add_eq_or_of_lt (show w.toNat / 2 < 2 ^ 31 by omega_arith)]
  omega_arith

/-- What `i` steps of the halving leave. -/
structure HalveAt (h : In Ex base bytes len args s) (j n i : Nat) (t : State) : Prop where
  ecx : t.gpr .ecx = BitVec.ofNat 32 (4 * (n - i))
  esi : PtrAt t base .esi (lo len (.slot .wide j) + 4 * (n - i))
  ebx : t.gpr .ebx = BitVec.ofNat 32 (val32 s.mem base (lo len (.slot .wide j) + 4 * (n - i)) i % 2)
  top : val32 t.mem base (lo len (.slot .wide j) + 4 * (n - i)) i =
    val32 s.mem base (lo len (.slot .wide j) + 4 * (n - i)) i / 2
  out : Outside base (lo len (.slot .wide j) + 4 * (n - i)) (4 * i) s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t

theorem halveStep_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {i : Nat}
    (hi : i < cwc len .wide) {t : State} (H : HalveAt h j (cwc len .wide) i t) :
    WP isa (.block halveStep) t fun u => HalveAt h j (cwc len .wide) (i + 1) u ∧
      isa.eval .ne u = some (decide (i + 1 ≠ cwc len .wide)) := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bw := bc_eq_cwc len .wide
  have hw : Ws t base bytes := h.ws.of_keeps H.keeps
  -- The word processed, at `o`.
  generalize ho : lo len (.slot .wide j) + 4 * (cwc len .wide - (i + 1)) = o
  have eo : lo len (.slot .wide j) + 4 * (cwc len .wide - i) = o + 4 := by omega_arith
  have hesi := H.esi
  rw [eo] at hesi
  unfold halveStep
  refine wp_subi fun t₁ U₁ _ _ => ?_
  have p₁ : PtrAt t₁ base .esi o := by
    rw [PtrAt, U₁.gpr, ptr_sub hesi 4 (by show 4 ≤ o + 4; omega_arith)]
    show (base.toNat + (o + 4 - 4)) % 2 ^ 32 = _
    rw [Nat.add_sub_cancel]
  have hw₁ := hw.of_keeps U₁.keeps
  refine wp_movS (readSrc_ptr hw₁ p₁ (d := 0) (by omega_arith)) fun t₂ U₂ _ => ?_
  refine wp_mov fun t₃ U₃ => wp_andi fun t₄ U₄ => wp_shr (by decide) fun t₅ U₅ _ => ?_
  refine wp_ror (by decide) fun t₆ U₆ => wp_or fun t₇ U₇ => ?_
  have p₇ : PtrAt t₇ base .esi o := by
    rw [PtrAt, U₇.other _ (by decide), U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide)]; exact p₁
  have hw₇ : Ws t₇ base bytes :=
    (((((hw₁.of_wr U₂.wr).of_wr U₃.wr).of_wr U₄.wr).of_wr U₅.wr).of_wr U₆.wr).of_wr U₇.wr
  refine wp_storeS (ea_ptr hw₇ p₇ (d := 0) (by omega_arith)) (ws_write hw₇ (y := o + 0) (n := 4) (by omega_arith))
    fun t₈ M₈ => wp_mov fun t₉ U₉ => wp_subi fun u U₁₀ _ z => WP.block_nil ?_
  -- The values.
  have mt : t₇.mem = t.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have w : t₂.gpr .eax = t.mem.readW (off base o) 32 := by rw [U₂.gpr, U₁.mem, Nat.add_zero]
  have wo : t.mem.readW (off base o) 32 = s.mem.readW (off base o) 32 :=
    Mem.readW_congr fun x hx => H.out _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
  have carry : val32 s.mem base (o + 4) i % 2 ≤ 1 := by omega_arith
  have e₇ : (t₇.gpr .eax).toNat = (s.mem.readW (off base o) 32).toNat / 2 +
      val32 s.mem base (o + 4) i % 2 * 2 ^ 31 := by
    rw [U₇.gpr, U₆.other _ (by decide), U₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), w, wo, U₆.gpr,
      U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.other _ (by decide), H.ebx, eo, ror_carry carry, shr_or _ carry]
  have e₉ : u.gpr .ebx = BitVec.ofNat 32 ((s.mem.readW (off base o) 32).toNat % 2) := by
    rw [U₁₀.other _ (by decide), U₉.gpr, M₈.keeps [] |>.1 .edx (by simp), U₇.other _ (by decide),
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.gpr, U₃.gpr, w, wo]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (s.mem.readW (off base o) 32).toNat % 2) (by omega_arith)]
  have mu : u.mem = t.mem.writeW (off base o) (t₇.gpr .eax) := by
    rw [U₁₀.mem, U₉.mem, M₈.mem, mt, Nat.add_zero]
  have Ow : Outside base o 4 t.mem u.mem := by rw [mu]; exact writeW32_outside _ _ _ (by omega_arith)
  have sp : i + 1 ≤ cwc len .wide := hi
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [U₁₀.gpr, U₉.other _ (by decide), M₈.keeps [] |>.1 .ecx (by simp), U₇.other _ (by decide),
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide), U₁.other _ (by decide), H.ecx]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  · rw [ho, PtrAt, U₁₀.other _ (by decide), U₉.other _ (by decide), M₈.keeps [] |>.1 .esi (by simp)]
    exact p₇
  · rw [ho, e₉, val32]
    congr 1
    simp only [w32]
    omega_arith
  · rw [ho, val32, val32, mu, w32_write_self, e₇]
    have rest : val32 (t.mem.writeW (off base o) (t₇.gpr .eax)) base (o + 4) i = val32 t.mem base (o + 4) i :=
      (writeW32_outside t.mem base _ (by omega_arith)).val32 (by omega_arith) (by omega_arith)
    have top := H.top
    rw [eo] at top
    rw [rest, top]
    simp only [w32]
    omega_arith
  · rw [ho]
    intro x hx
    by_cases hin : ofs base x < o ∨ o + 4 ≤ ofs base x
    · rw [Ow x hin]
      exact H.out x (by rw [eo]; omega_arith)
    · omega_arith
  · have K₉ : Keeps [.eax, .ebx, .ecx, .edx, .esi] t u :=
      (U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans
        ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans
          ((U₇.keeps.mono (by decide)).trans ((M₈.keeps _).trans ((U₉.keeps.mono (by decide)).trans
            (U₁₀.keeps.mono (by decide))))))))))
    exact H.keeps.trans K₉
  · show u.zf.map (!·) = _
    rw [z, U₉.other _ (by decide), M₈.keeps [] |>.1 .ecx (by simp), U₇.other _ (by decide),
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide), U₁.other _ (by decide), H.ecx, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      sub_beq (by omega_arith) (by decide)]
    simp only [Option.map_some, Option.some.injEq]
    by_cases e : i + 1 = cwc len .wide
    · simp [e, show 4 * (cwc len .wide - i) = 4 by omega_arith]
    · simp [e, show 4 * (cwc len .wide - i) ≠ 4 by omega_arith]

/-- A wide slot halved in place. -/
theorem halve_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) :
    WP isa (halve (.slot .wide j)) s fun t => In Ex base bytes len args t ∧
      Outside base (lo len (.slot .wide j)) (bc len .wide) s.mem t.mem ∧
      sv t.mem base len .wide j = sv s.mem base len .wide j / 2 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bw := bc_eq_cwc len .wide
  have cp := cwc_pos h
  unfold halve
  rw [show ptrTo (.slot .wide j) .esi .edx ++ cntTo (one .wide) .ecx ++ [.alu .add .esi (.reg .ecx), .mov .ebx (.imm 0)] =
    ptrTo (.slot .wide j) .esi .edx ++ (cntTo (one .wide) .ecx ++ [.alu .add .esi (.reg .ecx), .mov .ebx (.imm 0)])
    from List.append_assoc _ _ _]
  refine WP.seq (ptrTo_ok (r := .esi) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u Ku mu pu => ?_)
  have hu : In Ex base bytes len args u := h.regs (Ku.mono (by decide) : Keeps [.edx, .esi] s u) mu
  refine cntTo_ok (n := one .wide) hu.width h.upper' (by decide) fun u₁ K₁ m₁ c₁ => ?_
  refine wp_addS rfl fun u₂ U₂ _ => wp_movi fun u₃ U₃ => WP.block_nil ?_
  have c₁' : u₁.gpr .ecx = BitVec.ofNat 32 (4 * cwc len .wide) := by rw [c₁, cb1, bw]
  have H₀ : HalveAt h j (cwc len .wide) 0 u₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [U₃.other _ (by decide), U₂.other _ (by decide), c₁', Nat.sub_zero]
    · rw [PtrAt, U₃.other _ (by decide), U₂.gpr, ptr_add (by rw [PtrAt, K₁.1 _ (by decide)]; exact pu), c₁',
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * cwc len .wide) (by omega_arith), Nat.sub_zero]
    · rw [U₃.gpr]; rfl
    · simp only [val32]
    · rw [U₃.mem, U₂.mem, m₁, mu]; exact Outside.refl _ _ _ _
    · exact (Ku.mono (by decide)).trans ((K₁.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
        (U₃.keeps.mono (by decide))))
  refine WP.loop (M := isa) (fun m t => ∃ i, m = cwc len .wide - i ∧ i < cwc len .wide ∧ HalveAt h j (cwc len .wide) i t)
    ?_ (cwc len .wide) u₃ ⟨0, by omega_arith, cp, H₀⟩
  rintro m t ⟨i, rfl, hi, H⟩
  refine WP.mono (halveStep_ok h hj hi H) fun u ⟨Hu, ne⟩ => ?_
  by_cases last : i + 1 = cwc len .wide
  · refine .inl ⟨by rw [ne]; simp [last], ?_⟩
    rw [last] at Hu
    have O := Hu.out
    have T := Hu.top
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at O T
    exact ⟨h.keep Hu.keeps (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O.mono (Nat.le_refl _)
      (by omega_arith), T, Hu.keeps⟩
  · exact .inr ⟨by rw [ne]; simp [last], cwc len .wide - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, Hu⟩

end VG.Proof.Ffdh.X86.Cand
