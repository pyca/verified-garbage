import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Loop
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce

/-!
# Poly1305 on AArch64 in AdvSIMD: the last group and the end

Untrusted: everything here is checked by Lean. The lanes are added
(`sumLanes`), the limbs put back into three words (`pack`), the third reduced
to at most 4 (`fold6`), and `v8`–`v14` restored.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Proof.Poly1305.Limbs64 (add3_toNat)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305.AArch64.Radix64 (hval Keeps ofNat_bool zero_nat)

/-! ## The lanes added -/

theorem sumLanes_ok (s : State) :
    WP isa (.block sumLanes) s fun t =>
      (∀ i < 5, (t.gpr (X i)).toNat = (ln (s.v (hV i)) 0 + ln (s.v (hV i)) 1) % 2 ^ 64) ∧
      (∀ r ∉ limbRegs, t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  simp only [sumLanes, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil]
  iterate 15
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
    gstep
  refine WP.block_nil_iff.mpr ⟨fun i hi => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      gstep <;> simp only [BitVec.toNat_add, ln] <;> rfl
  · simp only [limbRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13, h14⟩ := hr
    simp (disch := assumption) only [show X 0 = Reg.x9 from rfl, show X 1 = Reg.x10 from rfl,
      show X 2 = Reg.x11 from rfl, show X 3 = Reg.x12 from rfl, show X 4 = Reg.x13 from rfl,
      RegUpd.gpr_write_of_ne]

/-! ## Three words -/

/-- Reads of the general-purpose registers and the carry through the writes so far. -/
macro "cstep" : tactic =>
  `(tactic| simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    State.read, Size.bits, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Bool.toNat_false, Nat.add_zero,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
    ofNat_bool])

theorem pack_ok (s : State) :
    WP isa (.block pack) s fun t =>
      ((∀ i < 5, (s.gpr (X i)).toNat < 2 ^ 28) →
        hval t = val fun i => (s.gpr (X i)).toNat) ∧ Keeps [.x4, .x5, .x6, .x14, .x15] s t := by
  simp only [pack]
  iterate 12
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [hval]
  cstep
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h0 : (s.gpr .x9).toNat < 2 ^ 28 := h 0 (by decide)
    have h1 : (s.gpr .x10).toNat < 2 ^ 28 := h 1 (by decide)
    have h2 : (s.gpr .x11).toNat < 2 ^ 28 := h 2 (by decide)
    have h3 : (s.gpr .x12).toNat < 2 ^ 28 := h 3 (by decide)
    have h4 : (s.gpr .x13).toNat < 2 ^ 28 := h 4 (by decide)
    have ea : (s.gpr .x9 + s.gpr .x10 <<< 26).toNat = (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ 26 := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have eb : (s.gpr .x11 <<< 52).toNat = (s.gpr .x11).toNat * 2 ^ 52 % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have ec : (s.gpr .x11 >>> 12 + s.gpr .x12 <<< 14).toNat =
        (s.gpr .x11).toNat / 2 ^ 12 + (s.gpr .x12).toNat * 2 ^ 14 := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]; omega
    have ed : (s.gpr .x13 <<< 40).toNat = (s.gpr .x13).toNat * 2 ^ 40 % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have ee : (s.gpr .x13 >>> 24).toNat = (s.gpr .x13).toNat / 2 ^ 24 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have e := add3_toNat (s.gpr .x9 + s.gpr .x10 <<< 26) (s.gpr .x11 <<< 52)
      (s.gpr .x11 >>> 12 + s.gpr .x12 <<< 14) (s.gpr .x13 <<< 40) (s.gpr .x13 >>> 24) 0#64
      (by rw [ea, eb, ec, ed, ee, show (0#64).toNat = 0 from rfl]; omega)
    simp only [BitVec.add_zero] at e
    rw [e, ea, eb, ec, ed, ee, show (0#64).toNat = 0 from rfl]
    simp only [val, show X 0 = Reg.x9 from rfl, show X 1 = Reg.x10 from rfl, show X 2 = Reg.x11 from rfl,
      show X 3 = Reg.x12 from rfl, show X 4 = Reg.x13 from rfl]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The third word reduced -/

theorem fold6_ok (s : State) :
    WP isa (.block fold6) s fun t =>
      ((s.gpr .x6).toNat < 2 ^ 20 → hval t + P * ((s.gpr .x6).toNat / 4) = hval s ∧ (t.gpr .x6).toNat ≤ 4) ∧
        Keeps [.x4, .x5, .x6, .x14, .x15] s t := by
  simp only [fold6]
  iterate 9
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [hval]
  cstep
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have w4 := (s.gpr .x4).isLt; have w5 := (s.gpr .x5).isLt
    have eT : (s.gpr .x6 >>> 2 + s.gpr .x6 >>> 2 <<< 2).toNat = 5 * ((s.gpr .x6).toNat / 4) := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]; omega
    have eE : (s.gpr .x6 &&& BitVec.setWidth 64 3#16).toNat = (s.gpr .x6).toNat % 4 := by
      rw [BitVec.toNat_and, show (BitVec.setWidth 64 3#16).toNat = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have e := add3_toNat (s.gpr .x4) (s.gpr .x6 >>> 2 + s.gpr .x6 >>> 2 <<< 2) (s.gpr .x5) 0#64
      (s.gpr .x6 &&& BitVec.setWidth 64 3#16) 0#64
      (by rw [eT, eE, show (0#64).toNat = 0 from rfl]; omega)
    simp only [BitVec.add_zero] at e
    have z : (0#64).toNat = 0 := rfl
    refine ⟨?_, ?_⟩
    · rw [e, Limbs26.P_eq]; omega
    · omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The end of `vec` -/

theorem finish_eq : finish = times5 fV sV ++ (group fV sV ++
    (([.addImm .x .x2 .x2 64, .movz .x .x9 63 0, .logic .and .x .x3 .x3 .x9] : List Instr) ++
    (sumLanes ++ (pack ++ (fold6 ++ restore))))) := by
  simp only [finish, List.append_assoc]

theorem adv_ok (s : State) :
    WP isa (.block ([.addImm .x .x2 .x2 64, .movz .x .x9 63 0, .logic .and .x .x3 .x3 .x9] : List Instr)) s
      fun t => t.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 64 ∧ (t.gpr .x3).toNat = (s.gpr .x3).toNat % 64 ∧
        (∀ r ∉ [Reg.x2, .x3, .x9], t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · allstep
  · allstep
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 (63 : BitVec 16) <<< (16 * 0)).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h9⟩ := hr
    allstep

theorem nmem_of {r : Reg} {l l' : List Reg} (hr : r ∉ l) (hs : ∀ x ∈ l', x ∈ l := by decide) : r ∉ l' :=
  fun h => hr (hs r h)

theorem fV_sV : ∀ i < 5, ∀ j < 5, 1 ≤ j → fV i ≠ sV j := by decide

/-- What `vec` leaves: the registers and memory it keeps, `v8`–`v15`, and the accumulator. -/
structure VEnd (s₀ : State) (R : Nat) (M : Mem) (t : State) : Prop where
  x0 : t.gpr .x0 = s₀.gpr .x0
  x2 : t.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * nq s₀)
  x3 : (t.gpr .x3).toNat = (s₀.gpr .x3).toNat % 64
  x7 : t.gpr .x7 = s₀.gpr .x7
  x8 : t.gpr .x8 = s₀.gpr .x8
  x17 : t.gpr .x17 = s₀.gpr .x17
  mem : t.mem = M
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  vlow : ∀ k < 7, vdword (t.v (V (8 + k))) 0 = vdword (s₀.v (V (8 + k))) 0
  v15 : t.v .v15 = s₀.v .v15
  acc : (s₀.gpr .x6).toNat ≤ 4 →
    hval t % P = absorbAll R (hval s₀) (bytesAt M (s₀.gpr .x2) (64 * nq s₀)) % P ∧ (t.gpr .x6).toNat ≤ 4

theorem finish_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} (hY : Ys R yL yF)
    (hS : Saved s₀ M) (hL : LInv s₀ R M yL yF (nq s₀ - 1) s) (hq : 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16)
    (hw : ∀ k < 7, InRegions (s₀.rd ++ s₀.wr) (svA (s₀.gpr .x0) k) 8) :
    WP isa (.block finish) s (VEnd s₀ R M) := by
  have hn := (s₀.gpr .x3).isLt
  rw [finish_eq]
  -- `5 F`
  refine WP.block_append (WP.mono (times5_ok fV sV (fun i hi _ j hj h1 => fV_sV i hi j hj h1) sV_inj s
      fun j hj _ c hc => by rw [hL.fw j hj c hc]; exact Nat.lt_trans (hY.ltF c hc j hj) (by decide))
    fun s1 ⟨t1, v1, g1, m1, rd1, wr1, _⟩ => ?_)
  have fV1 : ∀ i < 5, s1.v (fV i) = s.v (fV i) := fun i hi => v1 _ fun j hj h1 => fV_sV i hi j hj h1
  have nS : ∀ r, (∀ j < 5, 1 ≤ j → r ≠ sV j) → s1.v r = s.v r := v1
  have mul1 : Mults s1 fV sV yF :=
    { r := fun i hi c hc => by rw [fV1 i hi]; exact hL.fw i hi c hc
      s5 := fun j hj h1 c hc => by rw [t1 j hj h1 c hc, hL.fw j hj c hc]
      lt := hY.ltF
      regR := by decide
      regS := by decide }
  have x2s1 : s1.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * (nq s₀ - 1)) := by rw [g1, hL.x2]
  -- the last group
  refine WP.block_append (WP.mono (group_ok mul1 (fun e he => by rw [nS _ (by decide)]; exact hL.mask e he)
      (fun e he => by rw [nS _ (by decide)]; exact hL.pad e he) fun j' hj' => by
        rw [gAddr, x2s1, rd1, wr1, hL.rd, hL.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact hd _ (by simp only [nq] at hq ⊢; omega)) fun s2 ⟨hg, gk⟩ => ?_)
  -- `x2`, `x3`
  refine WP.block_append (WP.mono (adv_ok s2) fun s3 ⟨a2, a3, ag, av, am, ard, awr, _⟩ => ?_)
  refine WP.block_append (WP.mono (sumLanes_ok s3) fun s4 ⟨l4, g4, v4, m4, rd4, wr4, _⟩ => ?_)
  refine WP.block_append (WP.mono (WP.keepV (pack_ok s4)) fun s5 ⟨⟨p5, k5⟩, v5⟩ => ?_)
  refine WP.block_append (WP.mono (WP.keepV (fold6_ok s5)) fun s6 ⟨⟨f6, k6⟩, v6⟩ => ?_)
  -- the state pointer and the slots, at `s6`
  have gpr26 : ∀ r ∉ [Reg.x2, .x3, .x9, .x4, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15],
      s6.gpr r = s2.gpr r := fun r hr => by
    rw [k6.1 r (nmem_of hr), k5.1 r (nmem_of hr), g4 r (nmem_of hr), ag r (nmem_of hr)]
  have gpr0 : ∀ r ∈ [Reg.x0, .x7, .x8, .x17], s6.gpr r = s₀.gpr r := fun r hr => by
    rw [gpr26 r (by revert hr; decide +revert), congrFun gk.gpr r, g1]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x0
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x7
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x8
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x17
    · exact absurd hr List.not_mem_nil
  have mem6 : s6.mem = M := by rw [k6.2.1, k5.2.1, m4, am, gk.mem, m1, hL.mem]
  have rd6 : s6.rd = s₀.rd := by rw [k6.2.2.1, k5.2.2.1, rd4, ard, gk.rd, rd1, hL.rd]
  have wr6 : s6.wr = s₀.wr := by rw [k6.2.2.2, k5.2.2.2, wr4, awr, gk.wr, wr1, hL.wr]
  have v26 : s6.v = s2.v := by rw [v6, v5, v4, av]
  refine WP.mono (restore_ok s6 fun k hk => by rw [rd6, wr6, gpr0 .x0 (by decide)]; exact hw k hk)
    fun t ⟨rv, ro, rg, rm, rrd, rwr, _⟩ => ?_
  have gt : ∀ r, r ≠ .x9 → t.gpr r = s6.gpr r := rg
  refine ⟨by rw [gt _ (by decide)]; exact gpr0 .x0 (by decide), ?_, ?_, by rw [gt _ (by decide)]; exact gpr0 .x7 (by decide),
    by rw [gt _ (by decide)]; exact gpr0 .x8 (by decide), by rw [gt _ (by decide)]; exact gpr0 .x17 (by decide),
    by rw [rm, mem6], by rw [rrd, rd6], by rw [rwr, wr6], fun k hk => ?_, ?_, fun h6 => ?_⟩
  · rw [gt _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), g4 _ (by decide), a2, congrFun gk.gpr .x2, x2s1,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  · rw [gt _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), g4 _ (by decide), a3, congrFun gk.gpr .x3, g1,
      hL.x3]
  · rw [rv k hk, mem6, gpr0 .x0 (by decide)]; exact hS.slots k hk
  · rw [ro _ (by decide), v26, gk.v _ (by decide), nS _ (by decide)]; exact hL.v15
  · obtain ⟨hb, hSc⟩ := hL.acc h6
    have hl1 : ∀ e < 2, ∀ i < 5, hl s1 e i = hl s e i := fun e _ i hi => by
      show ln (s1.v (hV i)) e = ln (s.v (hV i)) e; rw [nS _ (by revert i; decide +revert)]
    have hg' := hg fun e he i hi => by rw [hl1 e he i hi]; exact hb e he i hi
    -- the lanes after the last group
    have l0 := group_lane (s := s1) (t := s2) (y := yF) (e := 0) fun i hi => (hg' 0 (by decide) i hi).1
    have l1 := group_lane (s := s1) (t := s2) (y := yF) (e := 1) fun i hi => (hg' 1 (by decide) i hi).1
    rw [val_congr (hl1 0 (by decide))] at l0
    rw [val_congr (hl1 1 (by decide))] at l1
    have y0 : val (yF 0) ≡ R ^ 4 [MOD P] := hY.valF 0 (by decide)
    have y1 : val (yF 1) ≡ R ^ 3 [MOD P] := hY.valF 1 (by decide)
    have y2 : val (yF 2) ≡ R ^ 2 [MOD P] := hY.valF 2 (by decide)
    have y3 : val (yF 3) ≡ R [MOD P] := (hY.valF 3 (by decide)).trans (by rw [Nat.pow_one])
    have len : ∀ j' : Nat, (gbytes s1 j').length = 16 := fun _ => Poly1305.length_bytesAt _ _ _
    have eA := l0.trans ((y2.mul_left _).add (y0.mul_left _))
    have eB := l1.trans ((y3.mul_left _).add (y1.mul_left _))
    have hlast := Poly1305.pair_last (len 0) (len 1) (len 2) (len 3) hSc
      (eA.trans (by rw [Nat.add_comm])) (eB.trans (by rw [Nat.add_comm]))
    -- the lanes added, packed and reduced
    have lt2 : ∀ e < 2, ∀ i < 5, hl s2 e i < 2 ^ 27 := fun e he i hi => (hg' e he i hi).2
    have x4v : ∀ i < 5, (s4.gpr (X i)).toNat = hl s2 0 i + hl s2 1 i := fun i hi => by
      rw [l4 i hi, av]
      have := lt2 0 (by decide) i hi; have := lt2 1 (by decide) i hi
      exact Nat.mod_eq_of_lt (by simp only [hl] at *; omega)
    have hv5 : hval s5 = val (hl s2 0) + val (hl s2 1) := by
      rw [p5 fun i hi => by
        rw [x4v i hi]; have := lt2 0 (by decide) i hi; have := lt2 1 (by decide) i hi; omega,
        ← val_add]
      exact val_congr x4v
    have b5 : (s5.gpr .x6).toNat < 2 ^ 20 := by
      have := (s5.gpr .x4).isLt; have := (s5.gpr .x5).isLt
      have h0 := lt2 0 (by decide); have h1 := lt2 1 (by decide)
      have a := h0 0 (by decide); have := h0 1 (by decide); have := h0 2 (by decide)
      have := h0 3 (by decide); have := h0 4 (by decide)
      have := h1 0 (by decide); have := h1 1 (by decide); have := h1 2 (by decide)
      have := h1 3 (by decide); have := h1 4 (by decide)
      simp only [hval, val] at hv5
      omega
    obtain ⟨ef, bf⟩ := f6 b5
    have ht : hval t = hval s6 := by
      simp only [hval, gt .x4 (by decide), gt .x5 (by decide), gt .x6 (by decide)]
    refine ⟨?_, by rw [gt _ (by decide)]; exact bf⟩
    have e1 : hval t % P = hval s5 % P := by
      rw [ht, ← ef, Nat.add_mul_mod_self_left]
    rw [e1, hv5]
    refine hlast.trans ?_
    rw [← Poly1305.absorbAll_append (by rw [Poly1305.length_bytesAt]; omega),
      show 64 * nq s₀ = 64 * (nq s₀ - 1 + 1) from by omega, group_bytes]
    simp only [gbytes, gAddr, x2s1, m1, hL.mem, List.append_assoc]
    rfl

end VG.Proof.Poly1305.AArch64.Vector
