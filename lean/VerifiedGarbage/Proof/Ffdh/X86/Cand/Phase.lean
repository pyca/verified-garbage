module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WitnessStreamStep
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.TwosMath
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Spec.Dsa

/-! ### `Ffdh.X86.Cand.Draw`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.Round`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.Prep`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.Halve`, which this module and modules that import it used -/

section

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
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  obtain bw := bc_eq_cwc len .wide
  obtain hw : Ws t base bytes := h.ws.of_keeps H.keeps
  -- The word processed, at `o`.
  generalize ho : lo len (.slot .wide j) + 4 * (cwc len .wide - (i + 1)) = o
  obtain eo : lo len (.slot .wide j) + 4 * (cwc len .wide - i) = o + 4 := by omega_arith
  have hesi := H.esi
  rw [eo] at hesi
  unfold halveStep
  refine wp_subi fun t₁ U₁ _ _ => ?_
  obtain p₁ : PtrAt t₁ base .esi o := by
    rw [PtrAt, U₁.gpr, ptr_sub hesi 4 (by show 4 ≤ o + 4; omega_arith)]
    show (base.toNat + (o + 4 - 4)) % 2 ^ 32 = _
    rw [Nat.add_sub_cancel]
  obtain hw₁ := hw.of_keeps U₁.keeps
  refine wp_movS (readSrc_ptr hw₁ p₁ (d := 0) (by omega_arith)) fun t₂ U₂ _ => ?_
  refine wp_mov fun t₃ U₃ => wp_andi fun t₄ U₄ => wp_shr (by decide) fun t₅ U₅ _ => ?_
  refine wp_ror (by decide) fun t₆ U₆ => wp_or fun t₇ U₇ => ?_
  obtain p₇ : PtrAt t₇ base .esi o := by
    rw [PtrAt, U₇.other _ (by decide), U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide)]; exact p₁
  obtain hw₇ : Ws t₇ base bytes :=
    (((((hw₁.of_wr U₂.wr).of_wr U₃.wr).of_wr U₄.wr).of_wr U₅.wr).of_wr U₆.wr).of_wr U₇.wr
  refine wp_storeS (ea_ptr hw₇ p₇ (d := 0) (by omega_arith)) (ws_write hw₇ (y := o + 0) (n := 4) (by omega_arith))
    fun t₈ M₈ => wp_mov fun t₉ U₉ => wp_subi fun u U₁₀ _ z => WP.block_nil ?_
  -- The values.
  obtain mt : t₇.mem = t.mem := by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  obtain w : t₂.gpr .eax = t.mem.readW (off base o) 32 := by rw [U₂.gpr, U₁.mem, Nat.add_zero]
  obtain wo : t.mem.readW (off base o) 32 = s.mem.readW (off base o) 32 :=
    Mem.readW_congr fun x hx => H.out _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
  obtain carry : val32 s.mem base (o + 4) i % 2 ≤ 1 := by omega_arith
  obtain e₇ : (t₇.gpr .eax).toNat = (s.mem.readW (off base o) 32).toNat / 2 +
      val32 s.mem base (o + 4) i % 2 * 2 ^ 31 := by
    rw [U₇.gpr, U₆.other _ (by decide), U₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide), w, wo, U₆.gpr,
      U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.other _ (by decide), H.ebx, eo, ror_carry carry, shr_or _ carry]
  obtain e₉ : u.gpr .ebx = BitVec.ofNat 32 ((s.mem.readW (off base o) 32).toNat % 2) := by
    rw [U₁₀.other _ (by decide), U₉.gpr, M₈.keeps [] |>.1 .edx (by simp), U₇.other _ (by decide),
      U₆.other _ (by decide), U₅.other _ (by decide), U₄.gpr, U₃.gpr, w, wo]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (s.mem.readW (off base o) 32).toNat % 2) (by omega_arith)]
  obtain mu : u.mem = t.mem.writeW (off base o) (t₇.gpr .eax) := by
    rw [U₁₀.mem, U₉.mem, M₈.mem, mt, Nat.add_zero]
  obtain Ow : Outside base o 4 t.mem u.mem := by rw [mu]; exact writeW32_outside _ _ _ (by omega_arith)
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
    obtain rest : val32 (t.mem.writeW (off base o) (t₇.gpr .eax)) base (o + 4) i = val32 t.mem base (o + 4) i :=
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
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  obtain bw := bc_eq_cwc len .wide
  obtain cp := cwc_pos h
  unfold halve
  rw [show ptrTo (.slot .wide j) .esi .edx ++ cntTo (one .wide) .ecx ++ [.alu .add .esi (.reg .ecx), .mov .ebx (.imm 0)] =
    ptrTo (.slot .wide j) .esi .edx ++ (cntTo (one .wide) .ecx ++ [.alu .add .esi (.reg .ecx), .mov .ebx (.imm 0)])
    from List.append_assoc _ _ _]
  refine WP.seq (ptrTo_ok (r := .esi) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u Ku mu pu => ?_)
  obtain hu : In Ex base bytes len args u := h.regs (Ku.mono (by decide) : Keeps [.edx, .esi] s u) mu
  refine cntTo_ok (n := one .wide) hu.width h.upper' (by decide) fun u₁ K₁ m₁ c₁ => ?_
  refine wp_addS rfl fun u₂ U₂ _ => wp_movi fun u₃ U₃ => WP.block_nil ?_
  obtain c₁' : u₁.gpr .ecx = BitVec.ofNat 32 (4 * cwc len .wide) := by rw [c₁, cb1, bw]
  obtain H₀ : HalveAt h j (cwc len .wide) 0 u₃ := by
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

end

end

/-!
# The FFDH candidate on i686: a phase's preparation

`prepPhase j`: the context of the modulus `w` in wide slot `j` (its
Montgomery inverse and `R² mod w`), one in slot 14, `w − 1` in slot 15,
and `w − 1 = 2^s d` with `d` odd: `d` in slot 11 and `s` in the header,
by halving `w − 1` while it is even (`prepPhase_ok`, `splitTwos_of`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- Halvings while even find the split of `m`. -/
theorem splitTwos_of : ∀ (k m : Nat), 0 < m → (∀ i < k, (m / 2 ^ i) % 2 = 0) → (m / 2 ^ k) % 2 = 1 →
    Spec.Rsa.splitTwos m = (k, m / 2 ^ k)
  | 0, m, _, _, hodd => by
    simp only [Nat.pow_zero, Nat.div_one] at hodd ⊢
    exact VG.Proof.Rsa.splitTwos_odd hodd
  | k + 1, m, hm, heven, hodd => by
    obtain h0 := heven 0 (by omega_arith)
    simp only [Nat.pow_zero, Nat.div_one] at h0
    rw [VG.Proof.Rsa.splitTwos_even (by omega_arith) h0]
    obtain ih := splitTwos_of k (m / 2) (by omega_arith) (fun i hi => by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact heven (i + 1) (by omega_arith))
      (by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact hodd)
    rw [ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- `o = a − b` for wide slots, with `b ≤ a`. -/
theorem subW_ok (h : In Ex base bytes len args s) {o a b : Nat} (ho : o ≤ 19) (ha : a ≤ 19) (hb : b ≤ 19)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : sv s.mem base len .wide b ≤ sv s.mem base len .wide a) :
    WP isa (chain .sbb (.slot .wide o) (.slot .wide a) (.slot .wide b) (one .wide)) s fun u =>
      Step Ex base bytes len args s u ∧
      sv u.mem base len .wide o = sv s.mem base len .wide a - sv s.mem base len .wide b ∧
      Kept base len [o] [] s.mem u.mem ∧ Outside base (lo len (.slot .wide o)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine WP.mono (chainSub_ok h (one_ok .wide) (slot_fit1 h (by omega_arith)) (slot_fit1 h (by omega_arith))
    (slot_fit1 h (by omega_arith)) (apart1 len hoa) (apart1 len hob)) fun u ⟨O, _, ⟨c, _, V⟩, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  refine ⟨Step.slot h (by omega_arith) O K, ?_, kept_slot h O, O, K⟩
  change sv u.mem base len .wide o + sv s.mem base len .wide b = sv s.mem base len .wide a +
    2 ^ (32 * cwc len .wide) * c.toNat at V
  obtain lt := val32_lt u.mem base (lo len (.slot .wide o)) (cwc len .wide)
  obtain lta := val32_lt s.mem base (lo len (.slot .wide a)) (cwc len .wide)
  change sv u.mem base len .wide o < _ at lt
  change sv s.mem base len .wide a < _ at lta
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at V <;> omega_arith

/-- The wide slot `a` copied into `b`, with the bytes it changes. -/
theorem copyO_ok (h : In Ex base bytes len args s) {a b : Nat} (ha : a ≤ 19) (hb : b ≤ 19) (hab : a ≠ b) :
    WP isa (copy (.slot .wide a) (.slot .wide b) (one .wide)) s fun u => Step Ex base bytes len args s u ∧
      sv u.mem base len .wide b = sv s.mem base len .wide a ∧ Kept base len [b] [] s.mem u.mem ∧
      Outside base (lo len (.slot .wide b)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  refine WP.mono (copy_ok h (x := .slot .wide a) (d := .slot .wide b) (one_ok .wide)
    (slot_fit1 h (by omega_arith)) (slot_fit1 h (by omega_arith)) (apart1 len (Ne.symm hab))) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨Step.slot h (by omega_arith) O K, V, kept_slot h O, O, K⟩

/-- A modulus's context, ready for its powers: the context, one in slot 3 and `R² mod w` in slot 4. -/
structure Ready (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (w : Nat) (t : State) : Prop where
  ctx : CtxOk Ex base bytes len args .wide w t
  one : sv t.mem base len .wide 3 = 1
  r2 : sv t.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % w

/-- A write into a wide slot from 5 to 27 keeps a context ready. -/
theorem Ready.slot {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {a : Nat} (ha9 : 5 ≤ a)
    (ha : a ≤ 27) {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  obtain f := slot_fit1 h ha
  rw [cb1] at f
  obtain ea := lo_wide len a
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have := Nat.mul_le_mul_right (st len .wide) ha9
  refine ⟨R.ctx.keepF K di sp (ws := [(lo len (.slot .wide a), bc len .wide)])
    (frameR_of_outside O (by omega_arith) (List.mem_singleton_self _)) (by simp; omega_arith) (by simp; omega_arith), ?_, ?_⟩
  · rw [← R.one]; exact slotKeep h (by decide) (by omega_arith) O
  · rw [← R.r2]; exact slotKeep h (by decide) (by omega_arith) O

/-- A write into a header word keeps a context ready. -/
theorem Ready.hdr {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {d : Nat} (hd : Hdr d)
    {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base d 4 s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  obtain hf := hdr_fit h hd
  have nb : numBase = 3336 := rfl
  obtain e3 := lo_wide len 3
  obtain e4 := lo_wide len 4
  obtain f4 := slot_fit1 h (j := 4) (by decide)
  rw [cb1] at f4
  obtain bw := bc_eq_cwc len .wide
  refine ⟨R.ctx.keepF2 K di sp (ws := [(d, 4)]) (frameR_of_outside O (by omega_arith) (List.mem_singleton_self _))
    (by simp; omega_arith) (by simp; rcases hd.1 with e | e <;> omega_arith), ?_, ?_⟩
  · rw [← R.one]; exact O.val32 (.inr (by omega)) (by omega)
  · rw [← R.r2]; exact O.val32 (.inr (by omega)) (by omega_using [bl, f4, bw])

theorem Ready.regs {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {rs : List Reg}
    (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs) (m : t.mem = s.mem) : Ready Ex base bytes len args w t :=
  ⟨R.ctx.keepF K di sp (ws := []) (by rw [m]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
    by rw [m]; exact R.one, by rw [m]; exact R.r2⟩

/-- The context of the modulus in wide slot `j`, ready. -/
theorem ready_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19)
    (hw : sv s.mem base len .wide j = w) (hw1 : 1 < w) (hodd : w % 2 = 1) :
    WP isa (.seq (copy (.slot .wide j) (.slot .wide 0) (one .wide)) (prepare .wide)) s fun t =>
      Step Ex base bytes len args s t ∧ Ready Ex base bytes len args w t ∧ Kept base len [] [] s.mem t.mem := by
  have bl := h.bytes_lt
  obtain f0 := h.slot_fit .wide (j := 0) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine WP.seq (WP.mono (copyIn_ok h (j := j) (d := 0) hj9 hj (by decide)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain F₁ : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u₁.mem :=
    stR_of_outside h (by decide) O₁ ⟨_, by simp, slot_in h .wide (j := 0) (by decide)⟩
  obtain S₁ : Step Ex base bytes len args s u₁ := Step.ops h F₁ K₁
  refine WP.mono (prepCtx_ok S₁.inp .wide) fun u ⟨C, one, R2, F, K⟩ => ?_
  rw [V₁, hw, safeM_of hw1 hodd] at C R2
  obtain F₂ := stR_widen F (prepR_in S₁.inp .wide 0)
  rw [S₁.esp] at F₂
  exact ⟨S₁.trans (Step.ops S₁.inp (by rw [S₁.esp]; exact F₂) K), ⟨C, one, R2⟩,
    (kept_ops h F₁ h.room).trans (kept_ops h F₂ h.room)⟩

/-- What a phase's preparation leaves for the modulus `w`: its context ready, one in slot 14,
`w − 1` in slot 15, and its split `w − 1 = 2^s d`: `d` in slot 11, `s` in the header. -/
structure Prepped (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (w : Nat) (t : State) : Prop extends Ready Ex base bytes len args w t where
  one14 : sv t.mem base len .wide 14 = 1
  m1 : sv t.mem base len .wide 15 = w - 1
  exp : sv t.mem base len .wide 11 = (Spec.Rsa.splitTwos (w - 1)).2
  two : w32 t.mem base twoOff = (Spec.Rsa.splitTwos (w - 1)).1

/-- The halvings so far: slot 11 holds `(w − 1) / 2^k`, even and positive, and the header `k`. -/
structure Halving (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) (w k : Nat) (t : State) : Prop where
  step : Step Ex base bytes len args s t
  ready : Ready Ex base bytes len args w t
  one14 : sv t.mem base len .wide 14 = 1
  m1 : sv t.mem base len .wide 15 = w - 1
  exp : sv t.mem base len .wide 11 = (w - 1) / 2 ^ k
  two : w32 t.mem base twoOff = k
  even : ∀ i < k, ((w - 1) / 2 ^ i) % 2 = 0
  kept : Kept base len [11, 14, 15] [twoOff] s.mem t.mem

theorem hdr_two : Hdr twoOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- One halving of the split. -/
theorem halveIter_ok {w k : Nat} {t : State} (H : Halving Ex base bytes len args s w k t)
    (hx : ((w - 1) / 2 ^ k) % 2 = 0) (hp : 0 < (w - 1) / 2 ^ k) (hwl : w < 2 ^ (32 * cwc len .wide)) :
    WP isa (.seq (halve (.slot .wide 11)) (.block (([.mov .eax (.mem (sc twoOff)), .alu .add .eax (.imm 1),
      .store (sc twoOff) .eax] : List Instr) ++ lowWord (.slot .wide 11) ++ ([.alu .and .eax (.imm 1)] : List Instr)))) t fun u =>
      Halving Ex base bytes len args s w (k + 1) u ∧
        isa.eval .e u = some (decide (((w - 1) / 2 ^ (k + 1)) % 2 = 0)) := by
  have ht := H.step.inp
  have bl := ht.bytes_lt
  have nb : numBase = 3336 := rfl
  obtain kl : k + 1 < 2 ^ 32 := by
    obtain p1 : 2 ^ k ≤ w - 1 := (Nat.div_pos_iff.mp hp).2
    obtain p2 : 2 ^ k < 2 ^ (32 * cwc len .wide) := by omega_arith
    obtain p3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp p2
    have := bc_le ht.upper' .wide
    simp only [cwc] at p3
    omega_arith
  obtain half : (w - 1) / 2 ^ (k + 1) = (w - 1) / 2 ^ k / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  refine WP.seq (WP.mono (halve_ok ht (j := 11) (by decide)) fun u₁ ⟨h₁, O₁, V₁, K₁⟩ => ?_)
  rw [H.exp] at V₁
  obtain two₁ : w32 u₁.mem base twoOff = k := by
    rw [← H.two]
    have := lo_wide len 11
    exact O₁.w32 (.inl (by simp only [twoOff]; omega_arith)) (by simp only [twoOff]; omega_arith)
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS (hdr_read h₁ hdr_two) fun u₂ U₂ _ => wp_addi fun u₃ U₃ => ?_
  refine hdr_store (h₁.regs ((U₂.keeps.trans U₃.keeps).mono (by decide) : Keeps [.eax] u₁ u₃)
    (by rw [U₃.mem, U₂.mem])) hdr_two fun u₄ S₄ W₄ k₄ O₄ G₄ _ _ => ?_
  refine lowWord_ok S₄.inp (j := 11) (by decide) fun u₅ m₅ K₅ e₅ => wp_andZ fun u U z => WP.block_nil ?_
  obtain S₃ : Step Ex base bytes len args u₁ u₃ := Step.regs h₁ (by rw [U₃.mem, U₂.mem]) (U₂.keeps.trans U₃.keeps)
  obtain S₅ : Step Ex base bytes len args u₄ u := Step.regs S₄.inp (by rw [U.mem, m₅]) (K₅.trans (U.keeps.mono (by decide)))
  obtain S₁ : Step Ex base bytes len args t u₁ := Step.slot ht (by decide) O₁ K₁
  obtain sv₄ : sv u₄.mem base len .wide 11 = (w - 1) / 2 ^ k / 2 := by
    rw [k₄.slot_eq, U₃.mem, U₂.mem, V₁]
  refine ⟨⟨H.step.trans (S₁.trans (S₃.trans (S₄.trans S₅))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have R₁ := H.ready.slot (a := 11) (by decide) (by decide) K₁ (by decide) (by decide) O₁
    obtain R₃ := R₁.regs (U₂.keeps.trans U₃.keeps) (by decide) (by decide) (by rw [U₃.mem, U₂.mem])
    exact (R₃.hdr hdr_two S₄.keeps (by decide) (by decide) O₄).regs (K₅.trans (U.keeps.mono (by decide))) (by decide) (by decide)
      (by rw [U.mem, m₅])
  · rw [U.mem, m₅, k₄.slot_eq, U₃.mem, U₂.mem, slotKeep ht (by decide) (by decide) O₁, H.one14]
  · rw [U.mem, m₅, k₄.slot_eq, U₃.mem, U₂.mem, slotKeep ht (by decide) (by decide) O₁, H.m1]
  · rw [U.mem, m₅, sv₄, half]
  · rw [U.mem, m₅, W₄, U₃.gpr, U₂.gpr, two₁, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt kl]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact H.even i hi
    · exact hx
  · have k₁ : Kept base len [11, 14, 15] [twoOff] t.mem u₁.mem := (kept_slot ht (a := 11) O₁).mono
    obtain k₃ : Kept base len [11, 14, 15] [twoOff] u₁.mem u₃.mem := by
      rw [U₃.mem, U₂.mem]; exact Kept.refl _ |>.mono
    obtain k₅ : Kept base len [11, 14, 15] [twoOff] u₄.mem u.mem := by
      rw [U.mem, m₅]; exact Kept.refl _ |>.mono
    exact H.kept.trans (k₁.trans (k₃.trans (k₄.mono.trans k₅)))
  · show u.zf = _
    rw [z, e₅, sv₄, and_one_zero _ (by omega_arith), half, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]


/-- The context of `w`, one, `w − 1` and its copy, and the count of halvings zero. -/
theorem prepHead_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa (prepHead j) s (Halving Ex base bytes len args s w 0) := by
  have bl := h.bytes_lt
  obtain bw := bc_eq_cwc len .wide
  unfold prepHead
  refine WP.assoc (WP.seq (WP.mono (ready_ok h hj9 (by omega_arith) hw (by omega_arith) hodd) fun u₁ ⟨S₁, R₁, k₁⟩ => ?_))
  have h₁ := S₁.inp
  refine WP.seq (WP.mono (setW_ok h₁ (a := 14) (v := 1) (by decide) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  obtain S₂ : Step Ex base bytes len args s u₂ := S₁.trans (Step.slot h₁ (by decide) O₂ K₂)
  obtain R₂ := R₁.slot (a := 14) (by decide) (by decide) K₂ (by decide) (by decide) O₂
  obtain k₂ : Kept base len [11, 14, 15] [twoOff] s.mem u₂.mem := k₁.mono.trans (kept_slot h₁ (a := 14) O₂).mono
  obtain wj₂ : sv u₂.mem base len .wide j = w := by
    rw [slotKeep h₁ (by omega_arith) (by omega_arith) O₂, k₁.slot_eq ⟨hj9, by omega_arith, by simp⟩, hw]
  refine WP.seq (WP.mono (subW_ok S₂.inp (o := 15) (a := j) (b := 14) (by decide) (by omega_arith) (by decide) (by omega_arith)
    (by decide) (by rw [V₂, wj₂]; omega_arith)) fun u₃ ⟨S₃, V₃, k₃, O₃, K₃⟩ => ?_)
  rw [V₂, wj₂] at V₃
  obtain R₃ := R₂.slot (a := 15) (by decide) (by decide) K₃ (by decide) (by decide) O₃
  refine WP.seq (WP.mono (copyO_ok S₃.inp (a := 15) (b := 11) (by decide) (by decide) (by decide))
    fun u₄ ⟨S₄, V₄, k₄, O₄, K₄⟩ => ?_)
  obtain R₄ := R₃.slot (a := 11) (by decide) (by decide) K₄ (by decide) (by decide) O₄
  refine wp_movi fun u₅ U₅ => hdr_store (S₄.inp.regs U₅.keeps U₅.mem) hdr_two fun u₆ S₆ W₆ k₆ O₆ G₆ _ _ =>
    WP.block_nil ?_
  obtain S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S₄.inp U₅.mem U₅.keeps
  refine ⟨S₂.trans (S₃.trans (S₄.trans (S₅.trans S₆))), ((R₄.regs U₅.keeps (by decide) (by decide) U₅.mem).hdr hdr_two
    S₆.keeps (by decide) (by decide) O₆), ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
  · rw [k₆.slot_eq, U₅.mem, k₄.slot_eq, k₃.slot_eq, V₂]
  · rw [k₆.slot_eq, U₅.mem, k₄.slot_eq, V₃]
  · rw [k₆.slot_eq, U₅.mem, V₄, V₃, Nat.pow_zero, Nat.div_one]
  · rw [W₆, U₅.gpr]; rfl
  · exact k₂.trans (k₃.mono.trans (k₄.mono.trans ((by rw [U₅.mem]; exact Kept.refl _ : Kept base len [] [] u₄.mem u₅.mem).mono.trans
      k₆.mono)))

/-- The halving loop's invariant: `k` halvings done, `(w − 1) / 2^k` still even. -/
abbrev Halved (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s : State) (w x : Nat) (t : State) : Prop :=
  ∃ k, x = (w - 1) / 2 ^ k ∧ x % 2 = 0 ∧ 0 < x ∧ Halving Ex base bytes len args s w k t

/-- A halving, and whether to halve again. -/
theorem halveRound_ok {w x : Nat} {t : State} (hw3 : 3 ≤ w) (hodd : w % 2 = 1) (hwl : w < 2 ^ (32 * cwc len .wide))
    (H : Halved Ex base bytes len args s w x t) :
    WP isa (.seq (halve (.slot .wide 11)) (.block (([.mov .eax (.mem (sc twoOff)), .alu .add .eax (.imm 1),
      .store (sc twoOff) .eax] : List Instr) ++ lowWord (.slot .wide 11) ++ ([.alu .and .eax (.imm 1)] : List Instr)))) t fun u =>
      (isa.eval .e u = some false ∧ Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
        Kept base len [11, 14, 15] [twoOff] s.mem u.mem) ∨
      (isa.eval .e u = some true ∧ ∃ x' < x, Halved Ex base bytes len args s w x' u) := by
  obtain ⟨k, rfl, hx, hp, H⟩ := H
  refine WP.mono (halveIter_ok H hx hp hwl) fun u ⟨Hu, z⟩ => ?_
  obtain half : (w - 1) / 2 ^ (k + 1) = (w - 1) / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  by_cases ev : ((w - 1) / 2 ^ (k + 1)) % 2 = 0
  · refine .inr ⟨by rw [z]; simp [ev], (w - 1) / 2 ^ (k + 1), by omega_arith, k + 1, rfl, ev, by omega_arith, Hu⟩
  · have od : ((w - 1) / 2 ^ (k + 1)) % 2 = 1 := by omega_arith
    obtain sp := splitTwos_of (k + 1) (w - 1) (by omega_arith) Hu.even od
    refine .inl ⟨by rw [z]; simp [ev], Hu.step, ⟨Hu.ready, Hu.one14, Hu.m1, by rw [Hu.exp, sp], by rw [Hu.two, sp]⟩,
      Hu.kept⟩

/-- The context of the modulus `w` in wide slot `j`, and the split `w − 1 = 2^s d`. -/
theorem prepPhase_ok (h : In Ex base bytes len args s) {j w : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa (prepPhase j) s fun t => Step Ex base bytes len args s t ∧ Prepped Ex base bytes len args w t ∧
      Kept base len [11, 14, 15] [twoOff] s.mem t.mem := by
  obtain hwl : w < 2 ^ (32 * cwc len .wide) := by rw [← hw]; exact val32_lt _ _ _ _
  unfold prepPhase
  refine WP.seq (WP.mono (prepHead_ok h hj9 hj hw hw3 hodd) fun u₆ H₀ => ?_)
  refine WP.loop (M := isa) (Halved Ex base bytes len args s w) ?_ (w - 1) u₆ ⟨0, by simp, by omega_arith, by omega_arith, H₀⟩
  intro x t H
  refine WP.mono (halveRound_ok hw3 hodd hwl H) fun u o => ?_
  rcases o with ⟨e, r⟩ | ⟨e, r⟩
  · exact .inl ⟨e, r⟩
  · exact .inr ⟨e, r⟩

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: a Miller–Rabin round

`round`: for the witness `a` in wide slot 13 and the prepared modulus `w`
(`w − 1 = 2^s d`), `z = a^d mod w` by the window power, then its `s − 1`
squarings, the header's hit mask or'ing `z = 1` and each `z^(2^j) = w − 1`:
`mrRound w a` (`round_ok`, through `hits`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

/-- A round's hits after `i` squarings of `z`: `z = 1`, or `z^(2^j) = w − 1` for a `j ≤ i`. -/
def hits (w z i : Nat) : Bool :=
  decide (z % w = 1) || (List.range (i + 1)).any fun j => decide (z ^ 2 ^ j % w = w - 1)

theorem hits_zero {w z : Nat} (hz : z < w) : hits w z 0 = (decide (z = 1) || decide (z = w - 1)) := by
  simp [hits, Nat.mod_eq_of_lt hz]

theorem hits_succ (w z i : Nat) : hits w z (i + 1) = (hits w z i || decide (z ^ 2 ^ (i + 1) % w = w - 1)) := by
  simp only [hits, List.range_succ (n := i + 1), List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_assoc]

theorem sq_pow (z w i : Nat) : (z ^ 2 ^ i % w) * (z ^ 2 ^ i % w) % w = z ^ 2 ^ (i + 1) % w := by
  rw [← Nat.mul_mod, Nat.pow_succ, Nat.pow_mul, Nat.pow_two]

/-- The round is its hits after `s − 1` squarings of `a^d`. -/
theorem mrRound_hits {w a : Nat} (h1 : 1 ≤ (Spec.Rsa.splitTwos (w - 1)).1) :
    Spec.Ffdh.mrRound w a =
      hits w (a ^ (Spec.Rsa.splitTwos (w - 1)).2 % w) ((Spec.Rsa.splitTwos (w - 1)).1 - 1) := by
  unfold Spec.Ffdh.mrRound hits
  generalize Spec.Rsa.splitTwos (w - 1) = p at *
  obtain ⟨s, d⟩ := p
  dsimp only at h1 ⊢
  rw [Nat.sub_add_cancel h1]
  simp only [VG.Proof.Bignum.powMod_eq, Nat.mod_mod]
  rfl

theorem splitTwos_pos {w : Nat} (hw3 : 3 ≤ w) (hodd : w % 2 = 1) : 1 ≤ (Spec.Rsa.splitTwos (w - 1)).1 := by
  rw [VG.Proof.Rsa.splitTwos_even (by omega_arith) (by omega_arith)]
  omega_arith

theorem hdr_hit : Hdr hitOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩
theorem hdr_j : Hdr jOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A prepared modulus stays prepared through a ready context and kept slots and words. -/
theorem Prepped.keep {w : Nat} (P : Prepped Ex base bytes len args w s) {t : State}
    (R : Ready Ex base bytes len args w t) {js ds : List Nat} (k : Kept base len js ds s.mem t.mem)
    (hd : twoOff ∉ ds) (hj : 11 ∉ js ∧ 14 ∉ js ∧ 15 ∉ js := by decide) : Prepped Ex base bytes len args w t :=
  ⟨R, by rw [k.slot_eq ⟨by decide, by decide, hj.2.1⟩]; exact P.one14,
    by rw [k.slot_eq ⟨by decide, by decide, hj.2.2⟩]; exact P.m1,
    by rw [k.slot_eq ⟨by decide, by decide, hj.1⟩]; exact P.exp,
    by rw [k.word_eq ⟨by decide, by decide, by decide, hd⟩]; exact P.two⟩

/-- An exponentiation keeps slot 4. -/
theorem pwR_sv4 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (pwR len .wide)) m m') (R : CallRoom sp base bytes) :
    sv m' base len .wide 4 = sv m base len .wide 4 := by
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  obtain bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain T := h.table_fit .wide
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  obtain e20 := lo_wide len 20
  obtain e1 := lo_wide len 1
  obtain e4 := lo_wide len 4
  obtain e5 := lo_wide len 5
  obtain e6 := lo_wide len 6
  obtain e7 := lo_wide len 7
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega_arith) ?_ (pwR_fit h .wide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [winOff] <;> omega_arith

/-- `a^d mod w` into slot 6, for the witness in slot 13 and the exponent in slot 11. -/
theorem pw_ok {w : Nat} (P : Prepped Ex base bytes len args w s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Step Ex base bytes len args s u → Prepped Ex base bytes len args w u →
      sv u.mem base len .wide 6 = sv s.mem base len .wide 13 ^ sv s.mem base len .wide 11 % w →
      Kept base len [] [] s.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (copy (.slot .wide 13) (.slot .wide 5) (one .wide))
      (.seq (copy (.slot .wide 11) (.slot .wide 8) (one .wide)) (.seq (windowPower .wide) rest))) s Q := by
  have C₀ := P.ctx
  have h := C₀.inp
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain e5 := lo_wide len 5
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (copyIn_ok h (j := 13) (d := 5) (by decide) (by decide) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  obtain h₂ := h.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyIn_ok h₂ (j := 11) (d := 8) (by decide) (by decide) (by decide)) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := K₂.1 _ (by decide)
  obtain sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  obtain G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  obtain G₃ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₂.mem u₃.mem :=
    stR_of_outside h (by decide) O₃ ⟨_, by simp, slot_in h .wide (j := 8) (by decide)⟩
  obtain C₃ : CtxOk Ex base bytes len args .wide w u₃ := by
    refine C₀.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) (K₂.trans K₃) (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide), (lo len (.slot .wide 8), bc len .wide)])
      ((frameR_of_outside O₂ (by omega_arith) (by simp)).trans (frameR_of_outside O₃ (by omega_arith) (by simp))) ?_ ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain B₃ : sv u₃.mem base len .wide 5 = sv s.mem base len .wide 13 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, V₂]
  obtain E₃ : sv u₃.mem base len .wide 8 = sv s.mem base len .wide 11 := by
    rw [V₃, slotKeep h (by decide) (by decide) O₂]
  obtain one₃ : sv u₃.mem base len .wide 3 = 1 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h (by decide) (by decide) O₂, P.one]
  obtain R₃ : sv u₃.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % w := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h (by decide) (by decide) O₂, P.r2]
  refine WP.seq (WP.mono (windowPower_ok C₃ one₃ R₃) fun u ⟨C, F, K, Y⟩ => ?_)
  rw [B₃, E₃] at Y
  have room : CallRoom (u₃.gpr .esp) base bytes := C₃.inp.room
  rw [sp₃] at F room
  obtain G := stR_widen F (pwR_in C₃.inp .wide 0)
  obtain kt : Kept base len [] [] s.mem u.mem :=
    ((kept_ops h G₂ h.room).trans (kept_ops h G₃ h.room)).trans (kept_ops h G h.room)
  obtain R : Ready Ex base bytes len args w u :=
    ⟨C, by rw [pwR_sv3 C₃.inp F room, one₃], by rw [pwR_sv4 C₃.inp F room, R₃]⟩
  refine k u (Step.ops h ((G₂.trans G₃).trans G)
    (((K₂.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂).trans (K₃.mono (by decide))).trans K))
    (P.keep R kt (by decide)) Y kt

/-- A square of slot 6 modulo the ready modulus, through `R² mod w` in slot 4. -/
theorem sqr_ok {w : Nat} (R : Ready Ex base bytes len args w s) {z : Nat} (hz : sv s.mem base len .wide 6 = z)
    (hzw : z < w) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Step Ex base bytes len args s u → Ready Ex base bytes len args w u →
      sv u.mem base len .wide 6 = z * z % w → Kept base len [] [] s.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (mul .wide 6 6 6) (.seq (mul .wide 6 6 4) rest)) s Q := by
  have C := R.ctx
  have h := C.inp
  have hM := C.gt
  obtain RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hz]; exact hzw)) fun u₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  obtain sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  obtain s3₁ : sv u₁.mem base len .wide 3 = sv s.mem base len .wide 3 :=
    mulR_sv h F₁ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain s4₁ : sv u₁.mem base len .wide 4 = sv s.mem base len .wide 4 :=
    mulR_sv h F₁ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [s4₁, R.r2]; exact Nat.mod_lt _ (by omega_arith))) fun u ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  rw [sp₁] at F₂
  obtain s3 : sv u.mem base len .wide 3 = sv u₁.mem base len .wide 3 :=
    mulR_sv h F₂ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain s4 : sv u.mem base len .wide 4 = sv u₁.mem base len .wide 4 :=
    mulR_sv h F₂ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain G₁ := stR_widen F₁ (mulR_in h .wide (by decide) 0)
  obtain G₂ := stR_widen F₂ (mulR_in h .wide (by decide) 0)
  rw [hz] at V₁
  rw [s4₁, R.r2, RR] at V₂
  obtain e : sv u.mem base len .wide 6 * 2 ^ (8 * bc len .wide) % w = z * z * 2 ^ (8 * bc len .wide) % w := by
    rw [V₂, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, V₁, Nat.mod_mul_mod]
  obtain v := VG.Proof.Bignum.mont_cancel C.coprime e
  rw [Nat.mod_eq_of_lt L₂] at v
  exact k u (Step.ops h (G₁.trans G₂) (K₁.trans K₂))
    ⟨C₂, by rw [s3, s3₁, R.one], by rw [s4, s4₁, R.r2]⟩ v
    ((kept_ops h G₁ h.room).trans (kept_ops h G₂ h.room))

theorem cmask_or_hit (a b : Bool) : cmask b ||| cmask a = cmask (a || b) := by
  cases a <;> cases b <;> decide

/-- The hit mask or'ed with `c` (in `ecx`), and the count in word `d`, less one, into the
squarings' count. -/
theorem tally_ok {w : Nat} (P : Prepped Ex base bytes len args w s) {d : Nat} (hd : Hdr d) (hdh : d ≠ hitOff)
    {n : Nat} (hn : w32 s.mem base d = n) (hn1 : 1 ≤ n) {c old : Bool}
    (hold : w32 s.mem base hitOff = (cmask old).toNat) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx, .mov .eax (.mem (sc d)),
      .alu .sub .eax (.imm 1), .store (sc jOff) .eax]) s fun u =>
      Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (old || c)).toNat ∧ w32 u.mem base jOff = n - 1 ∧
      u.zf = some (decide (n = 1)) ∧ Kept base len [] [hitOff, jOff] s.mem u.mem ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide 6 := by
  have h := P.ctx.inp
  obtain nl : n < 2 ^ 32 := by rw [← hn]; exact BitVec.isLt _
  refine wp_orS (hdr_read h hdr_hit) fun v₁ U₁ => ?_
  refine hdr_store (h.regs U₁.keeps U₁.mem) hdr_hit fun v₂ S₂ W₂ k₂ O₂ _ _ _ => ?_
  refine wp_movS (hdr_read S₂.inp hd) fun v₃ U₃ _ => wp_subi fun v₄ U₄ _ z₄ => ?_
  refine hdr_store (S₂.inp.regs (U₃.keeps.trans U₄.keeps) (by rw [U₄.mem, U₃.mem])) hdr_j
    fun v₅ S₅ W₅ k₅ O₅ _ _ z₅ => WP.block_nil ?_
  obtain dn : w32 v₂.mem base d = n := by
    rw [← hn, k₂.word_eq ⟨by rcases hd.1 with e | e <;> omega_arith, by rcases hd.1 with e | e <;> simp only [numBase] <;> omega_arith,
      hd.2, by simp only [List.mem_singleton]; exact hdh⟩, U₁.mem]
  obtain e₄ : v₄.gpr .eax = BitVec.ofNat 32 n - 1 := by rw [U₄.gpr, U₃.gpr, dn]
  obtain S₁ : Step Ex base bytes len args s v₁ := Step.regs h U₁.mem U₁.keeps
  obtain S₄ : Step Ex base bytes len args v₂ v₄ :=
    Step.regs S₂.inp (by rw [U₄.mem, U₃.mem]) (U₃.keeps.trans U₄.keeps)
  obtain kt : Kept base len [] [hitOff, jOff] s.mem v₅.mem :=
    ((by rw [U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] s.mem v₁.mem).trans
      (k₂.mono.trans ((by rw [U₄.mem, U₃.mem]; exact (Kept.refl _).mono :
        Kept base len [] [hitOff, jOff] v₂.mem v₄.mem).trans k₅.mono)))
  obtain R : Ready Ex base bytes len args w v₅ :=
    ((((P.toReady.regs U₁.keeps (by decide) (by decide) U₁.mem).hdr hdr_hit S₂.keeps (by decide) (by decide) O₂).regs
      (U₃.keeps.trans U₄.keeps) (by decide) (by decide) (by rw [U₄.mem, U₃.mem])).hdr hdr_j S₅.keeps (by decide)
      (by decide) O₅)
  obtain e6 := lo_wide len 6
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  obtain f6 := slot_fit1 h (j := 6) (by decide)
  rw [cb1] at f6
  obtain bw := bc_eq_cwc len .wide
  obtain s6 : sv v₅.mem base len .wide 6 = sv s.mem base len .wide 6 := by
    show val32 _ _ _ _ = val32 _ _ _ _
    rw [O₅.val32 (.inr (by simp only [jOff]; omega_arith)) (by omega_arith), U₄.mem, U₃.mem,
      O₂.val32 (.inr (by simp only [hitOff]; omega_arith)) (by omega_arith), U₁.mem]
  refine ⟨S₁.trans (S₂.trans (S₄.trans S₅)), P.keep R kt (by decide), ?_, ?_, ?_, kt, s6⟩
  · rw [k₅.word_eq, U₄.mem, U₃.mem, W₂, U₁.gpr, hc, hold, BitVec.ofNat_toNat, BitVec.setWidth_eq, cmask_or_hit]
  · rw [W₅, e₄]
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
    omega_arith
  · have e₃ : v₃.gpr .eax = BitVec.ofNat 32 n := by rw [U₃.gpr, dn]
    rw [z₅, z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq nl (by decide)]

/-- A round after `i` squarings of `z`: slot 6 `z^(2^i) mod w`, the hit mask its hits. -/
structure RoundAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) (w z i : Nat) (t : State) : Prop where
  step : Step Ex base bytes len args s t
  prep : Prepped Ex base bytes len args w t
  z6 : sv t.mem base len .wide 6 = z ^ 2 ^ i % w
  hit : w32 t.mem base hitOff = (cmask (hits w z i)).toNat
  kept : Kept base len [] [hitOff, jOff] s.mem t.mem

/-- One squaring of the round, the squarings' count `n` down one. -/
theorem squareStep_ok {w z i n : Nat} {t : State} (A : RoundAt Ex base bytes len args s w z i t)
    (hj : w32 t.mem base jOff = n) (hn1 : 1 ≤ n) :
    WP isa squareStep t fun u => RoundAt Ex base bytes len args s w z (i + 1) u ∧
      w32 u.mem base jOff = n - 1 ∧ u.zf = some (decide (n = 1)) := by
  have hM := A.prep.ctx.gt
  unfold squareStep
  refine sqr_ok A.prep.toReady A.z6 (Nat.mod_lt _ (by omega_arith)) fun u₁ S₁ R₁ Z₁ k₁ => ?_
  rw [sq_pow] at Z₁
  obtain P₁ := A.prep.keep R₁ k₁ (by decide)
  refine WP.seq (WP.mono (eqW_ok S₁.inp (a := 6) (b := 15) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [Z₁, P₁.m1] at e₂
  obtain P₂ := P₁.keep (P₁.toReady.regs K₂ (by decide) (by decide) m₂) (ds := []) (by rw [m₂]; exact Kept.refl _)
    (by decide)
  refine WP.mono (tally_ok P₂ hdr_j (by decide) (n := n) (by rw [m₂, k₁.word_eq, hj]) hn1
    (old := hits w z i) (by rw [m₂, k₁.word_eq, A.hit]) e₂) fun u ⟨S, P, H, J, Z, k, s6⟩ => ?_
  refine ⟨⟨A.step.trans (S₁.trans ((Step.regs S₁.inp m₂ K₂).trans S)), P, by rw [s6, m₂, Z₁], ?_, ?_⟩, J, Z⟩
  · rw [H, hits_succ]
  · exact A.kept.trans (k₁.mono.trans ((by rw [m₂]; exact (Kept.refl _).mono :
      Kept base len [] [hitOff, jOff] u₁.mem u₂.mem).trans k))

/-- A Miller–Rabin round of the witness `a` in slot 13 for the prepared modulus `w`: its hit mask
in the header. -/
theorem round_ok {w a : Nat} (P : Prepped Ex base bytes len args w s) (ha : sv s.mem base len .wide 13 = a)
    (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa round s fun u => Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (Spec.Ffdh.mrRound w a)).toNat ∧
      Kept base len [] [hitOff, jOff] s.mem u.mem := by
  obtain s1 := splitTwos_pos hw3 hodd
  rw [mrRound_hits s1]
  generalize hz : a ^ (Spec.Rsa.splitTwos (w - 1)).2 % w = z
  obtain zw : z < w := by rw [← hz]; exact Nat.mod_lt _ (by omega_arith)
  unfold round
  refine pw_ok P fun u₁ S₁ P₁ Z₁ k₁ => ?_
  rw [ha, P.exp, hz] at Z₁
  refine WP.seq (WP.mono (eqW_ok S₁.inp (a := 6) (b := 3) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [Z₁, P₁.one] at e₂
  obtain S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs S₁.inp m₂ K₂
  refine WP.seq (hdr_store (S₂.inp) hdr_hit fun u₃ S₃ W₃ k₃ O₃ _ _ _ => WP.block_nil ?_)
  obtain P₃ : Prepped Ex base bytes len args w u₃ :=
    P₁.keep (((P₁.toReady.regs K₂ (by decide) (by decide) m₂).hdr hdr_hit S₃.keeps (by decide) (by decide) O₃))
      ((by rw [m₂]; exact (Kept.refl _).mono : Kept base len [] [hitOff] u₁.mem u₂.mem).trans k₃)
      (by decide)
  have h₂ := S₂.inp
  have bl := h₂.bytes_lt
  obtain e6 := lo_wide len 6
  have nb : numBase = 3336 := rfl
  obtain f6 := slot_fit1 h₂ (j := 6) (by decide)
  rw [cb1] at f6
  obtain bw := bc_eq_cwc len .wide
  obtain z₃ : sv u₃.mem base len .wide 6 = z := by
    show val32 _ _ _ _ = _
    rw [O₃.val32 (.inr (by simp only [hitOff]; omega_arith)) (by omega_arith), m₂]; exact Z₁
  refine WP.seq (WP.mono (eqW_ok S₃.inp (a := 6) (b := 15) (by decide) (by decide)) fun u₄ ⟨m₄, e₄, K₄⟩ => ?_)
  rw [z₃, P₃.m1] at e₄
  obtain P₄ := P₃.keep (P₃.toReady.regs K₄ (by decide) (by decide) m₄) (ds := []) (by rw [m₄]; exact Kept.refl _)
    (by decide)
  refine WP.seq (WP.mono (tally_ok P₄ hdr_two (by decide) (n := (Spec.Rsa.splitTwos (w - 1)).1)
    (by rw [m₄]; exact P₃.two) s1 (old := decide (z = 1)) (by rw [m₄, W₃, e₂]) e₄)
    fun u₅ ⟨S₅, P₅, H₅, J₅, Z₅, k₅, s6₅⟩ => ?_)
  obtain A : RoundAt Ex base bytes len args s w z 0 u₅ := by
    refine ⟨S₁.trans (S₂.trans (S₃.trans ((Step.regs S₃.inp m₄ K₄).trans S₅))), P₅, ?_, ?_, ?_⟩
    · rw [s6₅, m₄, z₃, Nat.pow_zero, Nat.pow_one, Nat.mod_eq_of_lt zw]
    · rw [H₅, hits_zero zw]
    · exact k₁.mono.trans ((by rw [m₂]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] u₁.mem u₂.mem).trans
        (k₃.mono.trans ((by rw [m₄]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] u₃.mem u₄.mem).trans
          k₅)))
  generalize (Spec.Rsa.splitTwos (w - 1)).1 = sn at s1 J₅ Z₅ ⊢
  obtain fin : ∀ u, RoundAt Ex base bytes len args s w z (sn - 1) u →
      Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (hits w z (sn - 1))).toNat ∧
      Kept base len [] [hitOff, jOff] s.mem u.mem := fun u A => ⟨A.step, A.prep, A.hit, A.kept⟩
  refine WP.ite (decide (sn = 1)) Z₅ (fun e => WP.block_nil (fin _ ?_)) fun e => ?_
  · rw [show sn = 1 by simpa using e]; exact A
  obtain sn2 : 2 ≤ sn := by simp at e; omega_arith
  refine WP.loop (M := isa) (fun n t => ∃ i, n = sn - 1 - i ∧ i < sn - 1 ∧ RoundAt Ex base bytes len args s w z i t ∧
    w32 t.mem base jOff = sn - 1 - i) ?_ (sn - 1) u₅ ⟨0, by omega_arith, by omega_arith, A, by rw [J₅, Nat.sub_zero]⟩
  rintro n t ⟨i, rfl, hi, At, Jt⟩
  refine WP.mono (squareStep_ok At Jt (by omega_arith)) fun u ⟨Au, Ju, Zu⟩ => ?_
  by_cases last : i + 1 = sn - 1
  · refine .inl ⟨by show u.zf.map (!·) = _; rw [Zu]; simp; omega_arith, fin u (last ▸ Au)⟩
  · refine .inr ⟨by show u.zf.map (!·) = _; rw [Zu]; simp; omega_arith, sn - 1 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
      Au, by rw [Ju]; omega_arith⟩

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: a witness's draw

The tape (synthetic argument 2, `rand_len` octets in argument 12) keeps its
bytes through every stage (`Tape.step`). `drawLoad` reads the witness's
octets at the cursor (`drawLoad_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The bytes at `p + a` are those at `p` from the `a`-th on. -/
theorem bytesAt_offset (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b = ((Spec.Rsa.bytesAt m p n).drop a).take b := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith)
  intro k h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Rsa.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

/-- Where the tape lies: `n` octets at synthetic argument 2, `n` in argument 12, readable, apart
from the working space and the 96 bytes below `sp`. -/
structure TapeGeo (Ex : List Region → List Region → Prop) (args : Nat → BitVec 32) (base : Addr) (bytes : Nat)
    (sp : BitVec 32) (n : Nat) : Prop where
  len : args 12 = BitVec.ofNat 32 n
  small : n < 2 ^ 32
  fit : (args 2).toNat + n ≤ 2 ^ 32
  rd : ∀ rd wr, Ex rd wr → InRegions (rd ++ wr) (byteAddr (args 2)) n
  apart : Region.Disjoint ⟨byteAddr (args 2), n⟩ ⟨base, bytes⟩
  far : Region.Disjoint ⟨byteAddr (args 2), n⟩ (below sp 96)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The tape's bytes after a stage. -/
theorem tape_keep {n : Nat} (G : TapeGeo Ex args base bytes (s.gpr .esp) n) {t : State}
    (S : Step Ex base bytes len args s t) :
    Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) n = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) n := by
  have h := S.inp
  obtain fit := fR_fit h
  have bl := h.bytes_lt
  refine frame_bytes S.frame (fun r hr => ?_) (by have := G.fit; omega_arith)
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact G.far
  · have := fit p hp
    exact G.apart.sub_right (Offset.sub_base _ (by omega_arith))

/-- Slot 13 zeroed, and the pointers `reverseBytes` reads from the cursor `c` and the count `o`. -/
theorem drawSetup_ok (h : In Ex base bytes len args s) {c o : Nat}
    (hc : w32 s.mem base curOff = c) (ho : w32 s.mem base octOff = o) (ho1 : 1 ≤ o) :
    WP isa (.seq (zero (.slot .wide 13) (one .wide)) (.block drawSetup)) s fun v => In Ex base bytes len args v ∧
      Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem v.mem ∧
      val32 v.mem base (lo len (.slot .wide 13)) (cw len (one .wide)) = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v ∧ v.gpr .ecx = BitVec.ofNat 32 o ∧
      v.gpr .esi = (args 2 + BitVec.ofNat 32 c) + BitVec.ofNat 32 (o - 1) ∧
      PtrAt v base .ebx (lo len (.slot .wide 13)) := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f13 := slot_fit1 h (j := 13) (by decide)
  rw [cb1] at f13
  obtain e13 := lo_wide len 13
  have nb : numBase = 3336 := rfl
  obtain ce := cb_eq (len := len) (one_ok .wide)
  rw [cb1] at ce
  unfold drawSetup
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide 13) (one_ok .wide) (by rw [cb1]; omega_arith)) fun u ⟨O, Z, K⟩ => ?_)
  rw [cb1] at O
  obtain Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega_arith)
  obtain hu := h.keep K (by decide) (by decide) Ou
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_
  obtain hv := hu.regs Kv mv
  refine wp_movS (hv.arg (i := 2) (by decide)) fun v₁ U₁ _ => ?_
  obtain hv₁ := hv.regs U₁.keeps U₁.mem
  refine wp_addS (hdr_read hv₁ hdr_cur) fun v₂ U₂ _ => ?_
  obtain hv₂ := hv₁.regs U₂.keeps U₂.mem
  refine wp_movS (hdr_read hv₂ hdr_oct) fun v₃ U₃ _ => wp_addS rfl fun v₄ U₄ _ => wp_subS rfl fun v₅ U₅ _ =>
    WP.block_nil ?_
  obtain m₅ : v₅.mem = u.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, mv]
  obtain K₅ : Keeps [.ebx, .ecx, .esi] v v₅ :=
    ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))).trans
      (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))
  obtain hv₅ : In Ex base bytes len args v₅ := hv.regs K₅ (by rw [m₅, mv])
  obtain cu : w32 u.mem base curOff = c := by
    rw [← hc]; exact O.w32 (.inl (by simp only [curOff]; omega_arith)) (by simp only [curOff]; omega_arith)
  obtain ou : w32 u.mem base octOff = o := by
    rw [← ho]; exact O.w32 (.inl (by simp only [octOff]; omega_arith)) (by simp only [octOff]; omega_arith)
  obtain ebx₅ : v₅.gpr .ebx = v.gpr .ebx := by
    rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.other _ (by decide)]
  refine ⟨hv₅, by rw [m₅]; exact O, by rw [m₅]; exact Z,
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₅.mono (by decide))), ?_, ?_,
    by rw [PtrAt, ebx₅]; exact pv⟩
  · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, U₂.mem, U₁.mem, mv, ou]
  · rw [U₅.gpr, U₄.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr, U₃.gpr, U₂.mem, U₁.mem, mv, cu, ou]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]

/-- The `o` octets of the tape `T` at the cursor `c` into slot 13, and the cursor past them. -/
theorem drawLoad_ok {w n : Nat} (P : Prepped Ex base bytes len args w s) (G : TapeGeo Ex args base bytes (s.gpr .esp) n)
    {T : List Byte} (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) n = T) {c o : Nat}
    (hc : w32 s.mem base curOff = c) (ho : w32 s.mem base octOff = o) (ho1 : 1 ≤ o) (hco : c + o ≤ n)
    (hob : o ≤ bc len .wide) :
    WP isa drawLoad s fun u => Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      sv u.mem base len .wide 13 = Spec.Rsa.os2ip ((T.drop c).take o) ∧ w32 u.mem base curOff = c + o ∧
      Kept base len [13] [curOff] s.mem u.mem := by
  have h := P.ctx.inp
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f13 := slot_fit1 h (j := 13) (by decide)
  rw [cb1] at f13
  obtain e13 := lo_wide len 13
  have nb : numBase = 3336 := rfl
  have fit := G.fit
  have small := G.small
  obtain ce := cb_eq (len := len) (one_ok .wide)
  rw [cb1] at ce
  unfold drawLoad
  refine WP.assoc (WP.seq (WP.mono (drawSetup_ok h hc ho ho1) fun v₅ ⟨hv₅, O, Z, keep, ecx₅, esi₅, pv⟩ => ?_))
  obtain Ou : Outside base 0 bytes s.mem v₅.mem := O.mono (Nat.zero_le _) (by omega_arith)
  obtain Pn : (args 2 + BitVec.ofNat 32 c).toNat = (args 2).toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain Pa : byteAddr (args 2 + BitVec.ofNat 32 c) = byteAddr (args 2) + BitVec.ofNat 64 c := byteAddr_add (by omega_arith)
  obtain sub : Region.Sub ⟨byteAddr (args 2 + BitVec.ofNat 32 c), o⟩ ⟨byteAddr (args 2), n⟩ := by
    rw [Pa]; exact Offset.sub_base _ hco
  obtain rd : InRegions (v₅.rd ++ v₅.wr) (byteAddr (args 2 + BitVec.ofNat 32 c)) o := by
    rw [Pa]; exact VG.CallLay.inRegions_sub (G.rd _ _ hv₅.extra) hco (by omega_arith)
  have Ov := O
  obtain input : Spec.Rsa.bytesAt v₅.mem (byteAddr (args 2 + BitVec.ofNat 32 c)) o = (T.drop c).take o := by
    rw [VG.Proof.Bignum.scratch_bytes Ou (by omega_arith)
      (G.apart.sub_left sub), Pa, bytesAt_offset _ _ hco, hT]
  refine WP.seq (WP.mono (reverseInto_ok hv₅ (x := .slot .wide 13) (one_ok .wide) (by rw [cb1]; omega_arith)
    Z (by omega_arith) (by rw [cb1]; omega_arith) (by omega_arith) rd (G.apart.sub_left sub) pv ecx₅ esi₅) fun t ⟨V, Ot, Kt⟩ => ?_)
  rw [cb1] at Ot
  rw [cw1, input] at V
  obtain Ost : Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem t.mem := Ov.trans Ot
  obtain Kst : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keep.trans Kt
  obtain ht : In Ex base bytes len args t := h.keep Kst (by decide) (by decide) (Ost.mono (Nat.zero_le _) (by omega_arith))
  obtain St : Step Ex base bytes len args s t := Step.slot h (by decide) Ost Kst
  obtain ct : w32 t.mem base curOff = c := by
    rw [← hc]; exact Ost.w32 (.inl (by simp only [curOff]; omega_arith)) (by simp only [curOff]; omega_arith)
  obtain ot : w32 t.mem base octOff = o := by
    rw [← ho]; exact Ost.w32 (.inl (by simp only [octOff]; omega_arith)) (by simp only [octOff]; omega_arith)
  refine wp_movS (hdr_read ht hdr_oct) fun t₁ T₁ _ => wp_addS (hdr_read (ht.regs T₁.keeps T₁.mem) hdr_cur)
    fun t₂ T₂ _ => ?_
  refine hdr_store (ht.regs (T₁.keeps.trans T₂.keeps) (by rw [T₂.mem, T₁.mem])) hdr_cur
    fun u' S' W' k' O' _ _ _ => WP.block_nil ?_
  obtain S₂ : Step Ex base bytes len args t t₂ := Step.regs ht (by rw [T₂.mem, T₁.mem]) (T₁.keeps.trans T₂.keeps)
  obtain Rt : Ready Ex base bytes len args w t :=
    P.toReady.slot (a := 13) (by decide) (by decide) Kst (by decide) (by decide) Ost
  obtain R' : Ready Ex base bytes len args w u' :=
    ((Rt.regs (T₁.keeps.trans T₂.keeps) (by decide) (by decide) (by rw [T₂.mem, T₁.mem])).hdr hdr_cur S'.keeps
      (by decide) (by decide) O')
  obtain kt : Kept base len [13] [curOff] s.mem u'.mem :=
    (kept_slot h Ost).mono.trans (((by rw [T₂.mem, T₁.mem]; exact (Kept.refl _).mono :
      Kept base len [13] [curOff] t.mem t₂.mem)).trans k'.mono)
  refine ⟨St.trans (S₂.trans S'), P.keep R' kt (by decide), ?_, ?_, kt⟩
  · rw [k'.slot_eq, T₂.mem, T₁.mem]; exact V
  · rw [W', T₂.gpr, T₁.gpr, T₁.mem, ct, ot, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (a := c) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
      Nat.add_comm]

/-- `cmp d, src`, and the borrow. -/
theorem wp_cmpC {is : List Instr} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

/-- A write into a header word past the inverse's keeps a context ready. -/
theorem Ready.word {w : Nat} (R : Ready Ex base bytes len args w s) {t : State} {d : Nat} (hd4 : 4 ≤ d)
    (hd : d + 4 ≤ numBase) {rs : List Reg} (K : Keeps rs s t) (di : .edi ∉ rs) (sp : .esp ∉ rs)
    (O : Outside base d 4 s.mem t.mem) : Ready Ex base bytes len args w t := by
  have h := R.ctx.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  obtain e3 := lo_wide len 3
  obtain e4 := lo_wide len 4
  obtain f4 := slot_fit1 h (j := 4) (by decide)
  rw [cb1] at f4
  obtain bw := bc_eq_cwc len .wide
  refine ⟨R.ctx.keepF2 K di sp (ws := [(d, 4)]) (frameR_of_outside O (by omega_arith) (List.mem_singleton_self _))
    (by simp; omega_arith) (by simp; omega_arith), ?_, ?_⟩
  · rw [← R.one]; exact O.val32 (.inr (by omega_arith)) (by omega_arith)
  · rw [← R.r2]; exact O.val32 (.inr (by omega_arith)) (by omega_arith)

/-- The header words the draws change. -/
abbrev drawDs : List Nat := [curOff, cntOff, stOff, hitOff, jOff, maskOff]

/-- A state of a phase's draws from `s₀`: a stage, the modulus prepared, the tape `T` as it was,
and only the witness and the draws' words changed. -/
structure Mid (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (t : State) : Prop where
  step : Step Ex base bytes len args s₀ t
  prep : Prepped Ex base bytes len args w t
  tape : Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) T.length = T
  kept : Kept base len [13] drawDs s₀.mem t.mem

theorem Mid.next {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {u : State} (S : Step Ex base bytes len args t u)
    (P : Prepped Ex base bytes len args w u) {js ds : List Nat} (k : Kept base len js ds t.mem u.mem)
    (hj : ∀ j ∈ js, j ∈ [13] := by decide) (hd : ∀ d ∈ ds, d ∈ drawDs := by decide) :
    Mid Ex base bytes len args s₀ w T u :=
  ⟨M.step.trans S, P, by rw [tape_keep (by rw [M.step.esp]; exact G) S, M.tape], M.kept.trans (k.mono hj hd)⟩

theorem Mid.regs {s₀ t : State} {w : Nat} {T : List Byte} (M : Mid Ex base bytes len args s₀ w T t) {u : State}
    {rs : List Reg} (K : Keeps rs t u) (m : u.mem = t.mem)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) : Mid Ex base bytes len args s₀ w T u :=
  ⟨M.step.trans (Step.regs M.step.inp m K hrs),
    M.prep.keep (M.prep.toReady.regs K (by intro hm; have := hrs _ hm; simp at this)
      (by intro hm; have := hrs _ hm; simp at this) m) (ds := []) (js := []) (by rw [m]; exact Kept.refl _) (by decide),
    by rw [m]; exact M.tape, by rw [m]; exact M.kept⟩

/-- A register stored into one of the draws' header words. -/
theorem Mid.store {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {d : Nat} (hd : Hdr d) (hdd : d ∈ drawDs) (hdt : d ≠ twoOff)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Mid Ex base bytes len args s₀ w T u → w32 u.mem base d = (t.gpr r).toNat →
      Kept base len [] [d] t.mem u.mem → (∀ q, u.gpr q = t.gpr q) → u.cf = t.cf → u.zf = t.zf →
      WP isa (.block is) u Q) :
    WP isa (.block (.store (sc d) r :: is)) t Q :=
  hdr_store M.step.inp hd fun u S W k' O g cf zf =>
    k u (M.next G S (M.prep.keep (M.prep.toReady.hdr hd S.keeps (by decide) (by decide) O) k'
      (by simp only [List.mem_singleton]; exact Ne.symm hdt)) k' (by simp) (by simpa using hdd)) W k' g cf zf

/-- A draw's state: the octets and bits of `w − 1`, the cursor `c`, `n` witnesses to go and the
status 0. -/
structure DrawAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (t : State) : Prop
    extends Mid Ex base bytes len args s₀ w T t where
  oct : w32 t.mem base octOff = Spec.Ffdh.witnessOctets w
  bits : w32 t.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1)
  cur : w32 t.mem base curOff = c
  cnt : w32 t.mem base cntOff = n
  st : w32 t.mem base stOff = 0

/-- A phase's status: 3 for too few octets, 1 for a pass, 2 for a failed round. -/
def drawStatus : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 3
  | some (true, _) => 1
  | some (false, _) => 2

/-- The end of a phase's draws, with the result `D`: its status, and the cursor where it left the
tape. -/
structure DrawEnd (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (D : Option (Bool × Spec.RsaKeyGen.Rand)) (t : State) : Prop
    extends Mid Ex base bytes len args s₀ w T t where
  status : w32 t.mem base stOff = drawStatus D
  used : ∀ b r, D = some (b, r) → ∃ c, w32 t.mem base curOff = c ∧ c ≤ T.length ∧ T.drop c = r

theorem DrawAt.regs {s₀ t : State} {w : Nat} {T : List Byte} {n c : Nat}
    (A : DrawAt Ex base bytes len args s₀ w T n c t) {u : State} {rs : List Reg} (K : Keeps rs t u) (m : u.mem = t.mem)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    DrawAt Ex base bytes len args s₀ w T n c u :=
  ⟨A.toMid.regs K m hrs, by rw [m]; exact A.oct, by rw [m]; exact A.bits, by rw [m]; exact A.cur,
    by rw [m]; exact A.cnt, by rw [m]; exact A.st⟩

theorem DrawEnd.regs {s₀ t : State} {w : Nat} {T : List Byte} {D : Option (Bool × Spec.RsaKeyGen.Rand)}
    (E : DrawEnd Ex base bytes len args s₀ w T D t) {u : State} {rs : List Reg} (K : Keeps rs t u)
    (m : u.mem = t.mem) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    DrawEnd Ex base bytes len args s₀ w T D u :=
  ⟨E.toMid.regs K m hrs, by rw [m]; exact E.status, by rw [m]; exact E.used⟩

/-- A draw's witness for `w` from the tape `T` at `c`, whether it is in range, whether the draws go
on after it with `n` to go, and how many are then left: functions of the public values alone. -/
def drawA (w : Nat) (T : List Byte) (c : Nat) : Nat :=
  Spec.Rsa.os2ip ((T.drop c).take (Spec.Ffdh.witnessOctets w)) % 2 ^ Spec.RsaKeyGen.bitLength (w - 1)

def drawRange (w : Nat) (T : List Byte) (c : Nat) : Bool := decide (2 ≤ drawA w T c ∧ drawA w T c < w - 1)

def drawCont (w n : Nat) (T : List Byte) (c : Nat) : Bool :=
  decide (Spec.Ffdh.witnessOctets w ≤ T.length - c) &&
    (!drawRange w T c || (Spec.Ffdh.mrRound w (drawA w T c) && decide (n ≠ 1)))

def drawN (w n : Nat) (T : List Byte) (c : Nat) : Nat := if drawRange w T c then n - 1 else n

/-- Where a draw leaves the phase: on to the next draw with as good a result, or its end. -/
abbrev DrawOut (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (u : State) : Prop :=
  (∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' u ∧ 1 ≤ n' ∧ c < c' ∧ c' ≤ T.length ∧
      ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
      n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
    (DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) u ∧
      drawStatus (ParameterCandidate.checkWitnesses w n (T.drop c)) ≠ 0 ∧ drawCont w n T c = false)

/-- The status tested: ZF while the draws go on. -/
theorem drawFin_ok {s₀ u : State} {w n c : Nat} {T : List Byte} (O : DrawOut Ex base bytes len args s₀ w T n c u) :
    WP isa (.block [.mov .eax (.mem (sc stOff)), .alu .cmp .eax (.imm 0)]) u fun v =>
      (isa.eval .e v = some true ∧ ∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' v ∧ 1 ≤ n' ∧ c < c' ∧
        c' ≤ T.length ∧
        ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
        n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
      (isa.eval .e v = some false ∧
        DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) v ∧
        drawCont w n T c = false) := by
  obtain hst : ∃ M : Mid Ex base bytes len args s₀ w T u, True := by
    rcases O with ⟨_, _, A, _⟩ | ⟨E, _⟩
    · exact ⟨A.toMid, trivial⟩
    · exact ⟨E.toMid, trivial⟩
  obtain ⟨M, -⟩ := hst
  have hu := M.step.inp
  refine wp_movS (hdr_read hu (d := stOff) ⟨.inr ⟨by decide, by decide⟩, by decide⟩) fun v₁ U₁ _ =>
    wp_cmpS rfl fun v F z => WP.block_nil ?_
  obtain K : Keeps [.eax] u v := U₁.keeps.trans (F.keeps [.eax])
  obtain m : v.mem = u.mem := by rw [F.mem, U₁.mem]
  obtain zv : isa.eval .e v = some (decide (w32 u.mem base stOff = 0)) := by
    show v.zf = _
    rw [z, U₁.gpr, show ∀ x : BitVec 32, x - 0 = x from fun x => by simp, ofNat_beq_zero (BitVec.isLt _)]
  rcases O with ⟨n', c', A, h1, h2, h3, h4, h5, h6, h7⟩ | ⟨E, ne, h7⟩
  · exact .inl ⟨by rw [zv, A.st]; rfl, n', c', A.regs K m, h1, h2, h3, h4, h5, h6, h7⟩
  · exact .inr ⟨by rw [zv, E.status]; simp [ne], E.regs K m, h7⟩

theorem hdr_st : Hdr stOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩
theorem hdr_cnt : Hdr cntOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- The status `r` into its word. -/
theorem setSt_ok {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {r : Nat} (hr : r < 2 ^ 32) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 r)), .store (sc stOff) .eax]) t fun u =>
      Mid Ex base bytes len args s₀ w T u ∧ w32 u.mem base stOff = r ∧ Kept base len [] [stOff] t.mem u.mem := by
  refine wp_movS rfl fun t₁ U₁ _ => ?_
  refine (M.regs U₁.keeps U₁.mem).store G hdr_st (by decide) (by decide) fun u Mu W k _ _ _ => WP.block_nil ?_
  refine ⟨Mu, by rw [W, U₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr], ?_⟩
  exact (by rw [U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [stOff] t.mem t₁.mem).trans k

/-- A witness passed: the count down one, the status 1 if it reaches zero. -/
theorem passed_ok {s₀ t : State} {w : Nat} {T : List Byte} (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length)
    (M : Mid Ex base bytes len args s₀ w T t) {n : Nat} (hn : w32 t.mem base cntOff = n + 1) :
    WP isa (.block passed) t fun u =>
      Mid Ex base bytes len args s₀ w T u ∧ w32 u.mem base cntOff = n ∧
      w32 u.mem base stOff = (if n = 0 then 1 else 0) ∧ Kept base len [] [cntOff, stOff] t.mem u.mem := by
  have ht := M.step.inp
  obtain nl : n + 1 < 2 ^ 32 := by rw [← hn]; exact BitVec.isLt _
  unfold passed
  refine wp_movS (hdr_read ht hdr_cnt) fun t₁ U₁ _ => wp_subi fun t₂ U₂ _ _ => ?_
  obtain e₂ : t₂.gpr .eax = BitVec.ofNat 32 n := by
    rw [U₂.gpr, U₁.gpr, hn]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
    omega_arith
  refine (M.regs (U₁.keeps.trans U₂.keeps) (by rw [U₂.mem, U₁.mem])).store G hdr_cnt (by decide) (by decide)
    fun t₃ M₃ W₃ k₃ g₃ _ _ => ?_
  refine wp_cmpC rfl fun t₄ F₄ c₄ => wp_movS rfl fun t₅ U₅ cf₅ => wp_adcS rfl (c := decide (n < 1))
    (by rw [cf₅, c₄, g₃, e₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; rfl) fun t₆ U₆ _ => ?_
  obtain K₆ : Keeps [.eax] t₃ t₆ := ((F₄.keeps [.eax]).trans U₅.keeps).trans U₆.keeps
  obtain m₆ : t₆.mem = t₃.mem := by rw [U₆.mem, U₅.mem, F₄.mem]
  refine (M₃.regs K₆ m₆).store G hdr_st (by decide) (by decide) fun u Mu W k _ _ _ => WP.block_nil ?_
  obtain cnt₆ : w32 t₆.mem base cntOff = n := by
    rw [m₆, W₃, U₂.gpr, U₁.gpr, hn, BitVec.toNat_sub, BitVec.toNat_ofNat]
    show (2 ^ 32 - 1 + (n + 1) % 2 ^ 32) % 2 ^ 32 = n
    omega_arith
  refine ⟨Mu, by rw [k.word_eq, cnt₆], ?_, ?_⟩
  · rw [W, U₆.gpr, U₅.gpr]
    by_cases n0 : n = 0
    · subst n0; rfl
    · simp only [n0, ↓reduceIte, show decide (n < 1) = false by simp; omega_arith]; rfl
  · exact (by rw [U₂.mem, U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [cntOff, stOff] t.mem t₂.mem).trans
      (k₃.mono.trans ((by rw [m₆]; exact (Kept.refl _).mono : Kept base len [] [cntOff, stOff] t₃.mem t₆.mem).trans
        k.mono))

/-- A draw's step of the specification, with its witness `a` and octets `o`. -/
theorem checkWitnesses_draw {w n c o k : Nat} {T : List Byte} (ho : Spec.Ffdh.witnessOctets w = o) (ho1 : 1 ≤ o)
    (hk : Spec.RsaKeyGen.bitLength (w - 1) = k) (hco : c + o ≤ T.length) :
    ParameterCandidate.checkWitnesses w (n + 1) (T.drop c) =
      let a := Spec.Rsa.os2ip ((T.drop c).take o) % 2 ^ k
      if 2 ≤ a ∧ a < w - 1 then
        if Spec.Ffdh.mrRound w a then ParameterCandidate.checkWitnesses w n (T.drop (c + o))
        else some (false, T.drop (c + o))
      else ParameterCandidate.checkWitnesses w (n + 1) (T.drop (c + o)) := by
  rw [ParameterCandidate.checkWitnesses_step (by omega_arith), ho, hk, List.length_drop, List.drop_drop,
    ite_eq_left (by omega_arith)]

theorem checkWitnesses_short {w n c o : Nat} {T : List Byte} (ho : Spec.Ffdh.witnessOctets w = o) (ho1 : 1 ≤ o)
    (hs : T.length - c < o) : ParameterCandidate.checkWitnesses w (n + 1) (T.drop c) = none := by
  rw [ParameterCandidate.checkWitnesses_step (by omega_arith), ho, List.length_drop, ite_eq_right (by omega_arith)]

/-- The tape's octets left compared with a witness's. -/
theorem drawHead_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (ol : Spec.Ffdh.witnessOctets w < 2 ^ 32)
    (A : DrawAt Ex base bytes len args s₀ w T n c t) (hc : c ≤ T.length) :
    WP isa (.block [.mov .eax (.mem (argAt 0 12)), .alu .sub .eax (.mem (sc curOff)), .alu .cmp .eax (.mem (sc octOff))])
      t fun t₃ => DrawAt Ex base bytes len args s₀ w T n c t₃ ∧
        t₃.cf = some (decide (T.length - c < Spec.Ffdh.witnessOctets w)) := by
  have ht := A.step.inp
  have small := G.small
  refine wp_movS (ht.arg (i := 12) (by decide)) fun t₁ U₁ _ => ?_
  obtain h₁ := ht.regs U₁.keeps U₁.mem
  refine wp_subS (hdr_read h₁ hdr_cur) fun t₂ U₂ _ => ?_
  obtain h₂ := h₁.regs U₂.keeps U₂.mem
  refine wp_cmpC (hdr_read h₂ hdr_oct) fun t₃ F₃ c₃ => WP.block_nil ⟨A.regs ((U₁.keeps.trans U₂.keeps).trans
    (F₃.keeps [.eax])) (by rw [F₃.mem, U₂.mem, U₁.mem]), ?_⟩
  obtain cu : w32 t₁.mem base curOff = c := by rw [U₁.mem, A.cur]
  obtain ou : w32 t₂.mem base octOff = Spec.Ffdh.witnessOctets w := by rw [U₂.mem, U₁.mem, A.oct]
  obtain e1 : (BitVec.ofNat 32 T.length - BitVec.ofNat 32 c).toNat = T.length - c := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_arith
  rw [c₃, U₂.gpr, U₁.gpr, G.len, cu, ou, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ol]

/-- A witness drawn and tested for its range: its value `drawA` in slot 13, the cursor past it. -/
structure Picked (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (s₀ : State) (w : Nat) (T : List Byte) (n c : Nat) (u : State) : Prop
    extends Mid Ex base bytes len args s₀ w T u where
  wit : sv u.mem base len .wide 13 = drawA w T c
  oct : w32 u.mem base octOff = Spec.Ffdh.witnessOctets w
  bits : w32 u.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1)
  cur : w32 u.mem base curOff = c + Spec.Ffdh.witnessOctets w
  cnt : w32 u.mem base cntOff = n
  st : w32 u.mem base stOff = 0

theorem witness_bits {w : Nat} (hw3 : 3 ≤ w) (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) :
    2 ≤ Spec.RsaKeyGen.bitLength (w - 1) ∧ Spec.RsaKeyGen.bitLength (w - 1) ≤ 32 * cwc len .wide ∧
      Spec.Ffdh.witnessOctets w = (Spec.RsaKeyGen.bitLength (w - 1) + 7) / 8 := by
  obtain wb := VG.Proof.Ffdh.KeyScalar.bitLength_bounds (x := w - 1) (by omega_arith)
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at wb
  refine ⟨?_, ?_, by rw [Spec.Ffdh.witnessOctets, hk]⟩
  · by_contra hk2
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  · have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt wb.1 hwl)
    omega_arith

/-- The witness at the cursor loaded, cut to the bits of `w − 1` and tested for `1 < a < w − 1`. -/
theorem drawPick_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w)
    (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) (A : DrawAt Ex base bytes len args s₀ w T n c t)
    (co : c + Spec.Ffdh.witnessOctets w ≤ T.length) :
    WP isa (.seq drawLoad (.seq (cut (.slot .wide 13) false) (.seq (Impl.Ffdh.X86.rangeMask 13) Impl.Ffdh.X86.testMask))) t fun u =>
      Picked Ex base bytes len args s₀ w T n c u ∧ isa.eval .e u = some (!drawRange w T c) := by
  have ht := A.step.inp
  obtain bw := bc_eq_cwc len .wide
  obtain ⟨k2, kw, ho⟩ := witness_bits hw3 hwl
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at k2 kw ho
  obtain ⟨o, hoo⟩ : ∃ o, Spec.Ffdh.witnessOctets w = o := ⟨_, rfl⟩
  rw [hoo] at ho co
  generalize hx : Spec.Rsa.os2ip ((T.drop c).take o) = x
  generalize ha : x % 2 ^ k = a
  obtain dA : drawA w T c = a := by rw [drawA, hoo, hk, hx, ha]
  obtain dR : drawRange w T c = decide (2 ≤ a ∧ a < w - 1) := by rw [drawRange, dA]
  obtain ob : o ≤ bc len .wide := by omega_arith
  obtain G₃ : TapeGeo Ex args base bytes (t.gpr .esp) T.length := by rw [A.step.esp]; exact G
  refine WP.seq (WP.mono (drawLoad_ok A.prep G₃ A.tape A.cur (by rw [A.oct, hoo]) (by omega_arith) co ob)
    fun u₁ ⟨S₁, P₁, V₁, C₁, k₁⟩ => ?_)
  obtain M₁ := A.toMid.next G S₁ P₁ k₁
  rw [hx] at V₁
  obtain xl : x < 2 ^ (32 * ((k - 1) / 32 + 1)) := by
    obtain l := VG.Proof.Bignum.os2ip_lt ((T.drop c).take o)
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega_arith), VG.Proof.Bignum.pow256_eq, hx] at l
    exact Nat.lt_of_lt_of_le l (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.seq (WP.mono (cut_ok S₁.inp (j := 13) (by decide) false (k := k)
    (by rw [k₁.word_eq, A.bits, hk]) (by omega_arith) kw (by rw [V₁]; exact xl)) fun u₂ ⟨h₂, O₂, V₂, K₂⟩ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero, V₁, ha] at V₂
  obtain S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
  obtain k₂ := kept_slot S₁.inp O₂
  obtain M₂ := M₁.next G S₂ (P₁.keep (P₁.toReady.slot (a := 13) (by decide) (by decide) K₂ (by decide) (by decide) O₂)
    k₂ (by decide)) k₂
  refine WP.seq (WP.mono (rangeMask_ok h₂ (a := 13) (by decide)) fun u₃ ⟨_, e₃, O₃, K₃⟩ => ?_)
  obtain S₃ : Step Ex base bytes len args u₂ u₃ := Step.word h₂ (d := maskOff) (by decide) O₃ K₃
  obtain k₃ := kept_word h₂ (d := maskOff) (by decide) (by decide) O₃
  obtain M₃ := M₂.next G S₃ (M₂.prep.keep (M₂.prep.toReady.word (d := maskOff) (by decide) (by decide) K₃ (by decide)
    (by decide) O₃) k₃ (by decide)) k₃
  rw [V₂, M₂.prep.m1, M₂.prep.one14] at e₃
  obtain a₃ : sv u₃.mem base len .wide 13 = a := by rw [k₃.slot_eq, V₂]
  refine WP.mono (testMask_ok e₃) fun u₄ ⟨E₄, m₄, K₄⟩ => ?_
  obtain kx : Kept base len [13] [maskOff] u₁.mem u₄.mem :=
    k₂.mono.trans (k₃.mono.trans (by rw [m₄]; exact (Kept.refl _).mono))
  refine ⟨⟨M₃.regs K₄ m₄, by rw [m₄, a₃, dA], by rw [kx.word_eq, k₁.word_eq, A.oct],
    by rw [kx.word_eq, k₁.word_eq, A.bits], by rw [kx.word_eq, C₁, hoo], by rw [kx.word_eq, k₁.word_eq, A.cnt],
    by rw [kx.word_eq, k₁.word_eq, A.st]⟩, ?_⟩
  rw [E₄, dR]
  congr 2
  simp only [Bool.decide_and]
  rw [Bool.and_comm]
  rfl

/-- A drawn witness's round, and its result tested: ZF if it failed. -/
theorem drawRound_ok {s₀ u : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (Pk : Picked Ex base bytes len args s₀ w T n c u) :
    WP isa (.seq round (.block [.mov .ecx (.mem (sc hitOff)), .alu .test .ecx (.reg .ecx)])) u fun v =>
      Picked Ex base bytes len args s₀ w T n c v ∧
        isa.eval .e v = some (!Spec.Ffdh.mrRound w (drawA w T c)) := by
  refine WP.seq (WP.mono (round_ok Pk.prep Pk.wit hw3 hodd) fun u₅ ⟨S₅, P₅, H₅, k₅⟩ => ?_)
  obtain M₅ := Pk.toMid.next G S₅ P₅ k₅
  refine wp_movS (hdr_read S₅.inp hdr_hit) fun u₆ U₆ _ => wp_testS rfl fun u₇ F₇ z₇ => WP.block_nil ?_
  obtain e₆ : u₆.gpr .ecx = cmask (Spec.Ffdh.mrRound w (drawA w T c)) := by
    rw [U₆.gpr, H₅, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain m₇ : u₇.mem = u₅.mem := by rw [F₇.mem, U₆.mem]
  obtain k₇ : Kept base len [] [hitOff, jOff] u.mem u₇.mem := by rw [m₇]; exact k₅
  exact ⟨⟨M₅.regs (U₆.keeps.trans (F₇.keeps [.ecx])) m₇, by rw [k₇.slot_eq, Pk.wit], by rw [k₇.word_eq, Pk.oct],
    by rw [k₇.word_eq, Pk.bits], by rw [k₇.word_eq, Pk.cur], by rw [k₇.word_eq, Pk.cnt], by rw [k₇.word_eq, Pk.st]⟩,
    by show u₇.zf = _; rw [z₇, e₆, cmask_test]⟩

/-- One draw: the status 3 for too few octets; else the witness, drawn again if out of range, and
its round: the status 2 if it fails, else one fewer to go. -/
theorem draw_ok {s₀ t : State} {w n c : Nat} {T : List Byte}
    (G : TapeGeo Ex args base bytes (s₀.gpr .esp) T.length) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (hwl : w - 1 < 2 ^ (32 * cwc len .wide)) (A : DrawAt Ex base bytes len args s₀ w T n c t) (hn : 1 ≤ n)
    (hc : c ≤ T.length) :
    WP isa draw t fun u =>
      (isa.eval .e u = some true ∧ ∃ n' c', DrawAt Ex base bytes len args s₀ w T n' c' u ∧ 1 ≤ n' ∧ c < c' ∧
        c' ≤ T.length ∧
        ParameterCandidate.checkWitnesses w n' (T.drop c') = ParameterCandidate.checkWitnesses w n (T.drop c) ∧
        n' = drawN w n T c ∧ c' = c + Spec.Ffdh.witnessOctets w ∧ drawCont w n T c = true) ∨
      (isa.eval .e u = some false ∧
        DrawEnd Ex base bytes len args s₀ w T (ParameterCandidate.checkWitnesses w n (T.drop c)) u ∧
        drawCont w n T c = false) := by
  have ht := A.step.inp
  obtain bw := bc_eq_cwc len .wide
  obtain ⟨n₁, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_arith⟩
  obtain ⟨k2, kw, ho⟩ := witness_bits hw3 hwl
  generalize hk : Spec.RsaKeyGen.bitLength (w - 1) = k at k2 kw ho
  obtain ⟨o, hoo⟩ : ∃ o, Spec.Ffdh.witnessOctets w = o := ⟨_, rfl⟩
  rw [hoo] at ho
  obtain ol : o < 2 ^ 32 := by
    have := bc_le ht.upper' .wide
    omega_arith
  unfold draw
  refine WP.seq (WP.mono (drawHead_ok G (by rw [hoo]; exact ol) A hc) fun t₃ ⟨A₃, cf₃⟩ => ?_)
  rw [hoo] at cf₃
  refine WP.seq (WP.mono (?_ : WP isa (.ite .b _ _) t₃ (DrawOut Ex base bytes len args s₀ w T (n₁ + 1) c))
    fun u O => drawFin_ok O)
  refine WP.ite (decide (T.length - c < o)) cf₃ (fun e => ?_) fun e => ?_
  · -- Too few octets.
    obtain sh : T.length - c < o := by simpa using e
    obtain D := checkWitnesses_short (n := n₁) hoo (by omega_arith) sh
    refine WP.mono (setSt_ok G A₃.toMid (r := 3) (by decide)) fun u ⟨Mu, Wu, _⟩ => .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Wu, D]; rfl
    · intro b r e; rw [D] at e; cases e
    · rw [D]; decide
    · simp only [drawCont, hoo, show ¬ o ≤ T.length - c by omega_arith, decide_false, Bool.false_and]
  obtain co : c + o ≤ T.length := by simp at e; omega_arith
  obtain D := checkWitnesses_draw (n := n₁) hoo (by omega_arith) hk co
  generalize hx : Spec.Rsa.os2ip ((T.drop c).take o) = x at D
  generalize ha : x % 2 ^ k = a at D
  obtain dA : drawA w T c = a := by rw [drawA, hoo, hk, hx, ha]
  obtain dR : drawRange w T c = decide (2 ≤ a ∧ a < w - 1) := by rw [drawRange, dA]
  -- The witness, cut and tested for its range.
  refine WP.seq (WP.mono (WP.seq_iff.mp (drawPick_ok G hw3 hwl A₃ (by rw [hoo]; exact co))) fun u₁ h₁ =>
    WP.seq (WP.mono (WP.seq_iff.mp h₁) fun u₂ h₂ => WP.seq (WP.mono (WP.seq_iff.mp h₂) fun u₃ h₃ =>
      WP.seq (WP.mono h₃ fun u₄ ⟨Pk, E₄⟩ => ?_))))
  rw [dR] at E₄
  refine WP.ite _ E₄ (fun e => WP.block_nil ?_) fun e => ?_
  · -- Out of range: drawn again.
    obtain nr : ¬ (2 ≤ a ∧ a < w - 1) := by simp at e; omega_arith
    refine .inl ⟨n₁ + 1, c + o, ⟨Pk.toMid, Pk.oct, Pk.bits, by rw [Pk.cur, hoo], Pk.cnt, Pk.st⟩, by omega_arith, by omega_arith, co,
      ?_, by rw [drawN, dR, decide_eq_false nr]; rfl, by rw [hoo], ?_⟩
    · rw [D, ite_eq_right nr]
    · rw [drawCont, dR, decide_eq_false nr, hoo, decide_eq_true (by omega_arith : o ≤ T.length - c)]; rfl
  obtain r : 2 ≤ a ∧ a < w - 1 := by simp at e; omega_arith
  refine WP.seq (WP.mono (WP.seq_iff.mp (drawRound_ok G hw3 hodd Pk)) fun u₅ h₅ =>
    WP.seq (WP.mono h₅ fun u₇ ⟨P₇, E₇⟩ => ?_))
  rw [dA] at E₇
  have M₇ := P₇.toMid
  obtain cur₇ : w32 u₇.mem base curOff = c + o := by rw [P₇.cur, hoo]
  refine WP.ite (!Spec.Ffdh.mrRound w a) E₇ (fun e => ?_) fun e => ?_
  · -- The round failed.
    obtain mf : Spec.Ffdh.mrRound w a = false := by simpa using e
    obtain D' : ParameterCandidate.checkWitnesses w (n₁ + 1) (T.drop c) = some (false, T.drop (c + o)) := by
      rw [D, ite_eq_left r, mf]; rfl
    refine WP.mono (setSt_ok G M₇ (r := 2) (by decide)) fun u ⟨Mu, Wu, ku⟩ => .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Wu, D']; rfl
    · intro b r' e'
      rw [D'] at e'
      cases e'
      exact ⟨c + o, by rw [ku.word_eq, cur₇], co, rfl⟩
    · rw [D']; simp [drawStatus]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega_arith : o ≤ T.length - c), dA, mf]; rfl
  -- The round passed.
  obtain mt : Spec.Ffdh.mrRound w a = true := by simpa using e
  obtain D' : ParameterCandidate.checkWitnesses w (n₁ + 1) (T.drop c) =
      ParameterCandidate.checkWitnesses w n₁ (T.drop (c + o)) := by
    rw [D, ite_eq_left r, mt]; rfl
  refine WP.mono (passed_ok G M₇ P₇.cnt) fun u ⟨Mu, Cu, Su, ku⟩ => ?_
  obtain curu : w32 u.mem base curOff = c + o := by rw [ku.word_eq, cur₇]
  by_cases n0 : n₁ = 0
  · subst n0
    obtain D'' : ParameterCandidate.checkWitnesses w (0 + 1) (T.drop c) = some (true, T.drop (c + o)) := by
      rw [D']; rfl
    refine .inr ⟨⟨Mu, ?_, ?_⟩, ?_, ?_⟩
    · rw [Su, D'']; rfl
    · intro b r' e'
      rw [D''] at e'
      cases e'
      exact ⟨c + o, curu, co, rfl⟩
    · rw [D'']; simp [drawStatus]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega_arith : o ≤ T.length - c), dA, mt]; rfl
  · refine .inl ⟨n₁, c + o, ⟨Mu, ?_, ?_, curu, Cu, by rw [Su]; simp [n0]⟩, by omega_arith, by omega_arith, co, D'.symm,
      by rw [drawN, dR, decide_eq_true r]; rfl, by rw [hoo], ?_⟩
    · rw [ku.word_eq, P₇.oct]
    · rw [ku.word_eq, P₇.bits]
    · rw [drawCont, dR, decide_eq_true r, hoo, decide_eq_true (by omega_arith : o ≤ T.length - c), dA, mt,
        decide_eq_true (by omega_arith : n₁ + 1 ≠ 1)]; rfl

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: a phase of Miller–Rabin

`phase j`: the modulus `w` in wide slot `j` prepared, then draws from the
tape at the cursor until `n` witnesses pass, one fails or the tape runs
out: the status `drawStatus` of `checkWitnesses w n` (`phase_ok`), and the
cursor where it left the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A phase's start: the modulus `w` in wide slot `j` prepared and the status 0, the first draw's
state. -/
theorem phaseStart_ok {j w n c : Nat} {T : List Byte} (h : In Ex base bytes len args s)
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T) (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (ho : w32 s.mem base octOff = Spec.Ffdh.witnessOctets w)
    (hk : w32 s.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1))
    (hn : w32 s.mem base cntOff = n) (hc : w32 s.mem base curOff = c) :
    WP isa (.seq (prepPhase j) (.block [.mov .eax (.imm 0), .store (sc stOff) .eax])) s fun u =>
      Step Ex base bytes len args s u ∧ DrawAt Ex base bytes len args u w T n c u ∧
      Kept base len [11, 14, 15] [twoOff, stOff] s.mem u.mem := by
  refine WP.seq (WP.mono (prepPhase_ok h hj9 hj hw hw3 hodd) fun u₁ ⟨S₁, P₁, k₁⟩ => ?_)
  refine wp_movi fun u₂ U₂ => hdr_store (S₁.inp.regs U₂.keeps U₂.mem) hdr_st
    fun u₃ S₃ W₃ k₃ O₃ _ _ _ => WP.block_nil ?_
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs S₁.inp U₂.mem U₂.keeps
  have S₀ : Step Ex base bytes len args s u₃ := S₁.trans (S₂.trans S₃)
  have k₀ : Kept base len [11, 14, 15] [twoOff, stOff] s.mem u₃.mem :=
    k₁.mono.trans ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [11, 14, 15] [twoOff, stOff] u₁.mem u₂.mem).trans
      k₃.mono)
  have P₀ : Prepped Ex base bytes len args w u₃ :=
    P₁.keep ((P₁.toReady.regs U₂.keeps (by decide) (by decide) U₂.mem).hdr hdr_st S₃.keeps (by decide) (by decide) O₃)
      ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [stOff] u₁.mem u₂.mem).trans k₃) (by decide)
  refine ⟨S₀, ⟨⟨Step.regs S₀.inp rfl (rs := []) ⟨fun _ _ => rfl, rfl, rfl⟩, P₀, by rw [tape_keep G S₀, hT],
    (Kept.refl _).mono⟩, ?_, ?_, ?_, ?_, ?_⟩, k₀⟩
  · rw [k₀.word_eq, ho]
  · rw [k₀.word_eq, hk]
  · rw [k₀.word_eq, hc]
  · rw [k₀.word_eq, hn]
  · rw [W₃, U₂.gpr]; rfl

/-- A phase for the modulus `w` in wide slot `j`, with `n` witnesses to go and the tape `T` read
from `c`: its status, the cursor where its result leaves the tape, and the words it changes. -/
theorem phase_ok {j w n c : Nat} {T : List Byte} (h : In Ex base bytes len args s)
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T) (hj9 : 9 ≤ j) (hj : j ≤ 10)
    (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w) (hodd : w % 2 = 1)
    (ho : w32 s.mem base octOff = Spec.Ffdh.witnessOctets w)
    (hk : w32 s.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1))
    (hn : w32 s.mem base cntOff = n) (hn1 : 1 ≤ n) (hc : w32 s.mem base curOff = c) (hcT : c ≤ T.length) :
    WP isa (phase j) s fun u => Step Ex base bytes len args s u ∧
      u.gpr .eax = BitVec.ofNat 32 (drawStatus (ParameterCandidate.checkWitnesses w n (T.drop c))) ∧
      (∀ b r, ParameterCandidate.checkWitnesses w n (T.drop c) = some (b, r) →
        ∃ c', w32 u.mem base curOff = c' ∧ c' ≤ T.length ∧ T.drop c' = r) ∧
      Kept base len [11, 13, 14, 15] (twoOff :: drawDs) s.mem u.mem := by
  have hwl : w - 1 < 2 ^ (32 * cwc len .wide) := by
    have := val32_lt s.mem base (lo len (.slot .wide j)) (cwc len .wide)
    change sv s.mem base len .wide j < _ at this
    omega_using [hw, this]
  unfold phase
  refine WP.assoc (WP.seq (WP.mono (phaseStart_ok h G hT hj9 hj hw hw3 hodd ho hk hn hc) fun u₃ ⟨S₀, A₀, k₀⟩ => ?_))
  have G₀ : TapeGeo Ex args base bytes (u₃.gpr .esp) T.length := by rw [S₀.esp]; exact G
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := DrawEnd Ex base bytes len args u₃ w T
      (ParameterCandidate.checkWitnesses w n (T.drop c)))
    (fun m t => ∃ n' c', m = T.length - c' ∧ DrawAt Ex base bytes len args u₃ w T n' c' t ∧ 1 ≤ n' ∧
      c' ≤ T.length ∧ ParameterCandidate.checkWitnesses w n' (T.drop c') =
        ParameterCandidate.checkWitnesses w n (T.drop c)) ?_ (T.length - c) u₃ ⟨n, c, rfl, A₀, hn1, hcT, rfl⟩)
    fun u E => ?_)
  · rintro m t ⟨n', c', rfl, A, hn', hc', hD⟩
    refine WP.mono (draw_ok G₀ hw3 hodd hwl A hn' hc') fun u o => ?_
    rcases o with ⟨ev, n'', c'', A', h1, h2, h3, h4, -⟩ | ⟨ev, E, -⟩
    · exact .inr ⟨ev, T.length - c'', by omega_using [h2, h3], n'', c'', rfl, A', h1, h3, by rw [h4, hD]⟩
    · exact .inl ⟨ev, by rw [hD] at E; exact E⟩
  refine wp_movS (hdr_read E.step.inp hdr_st) fun v U _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact S₀.trans (E.step.trans (Step.regs E.step.inp U.mem U.keeps))
  · rw [U.gpr, E.status]
  · intro b r e
    obtain ⟨c', hc', hl, hr⟩ := E.used b r e
    exact ⟨c', by rw [U.mem, hc'], hl, hr⟩
  · exact k₀.mono.trans (E.kept.mono.trans (by rw [U.mem]; exact (Kept.refl _).mono))

end VG.Proof.Ffdh.X86.Cand
