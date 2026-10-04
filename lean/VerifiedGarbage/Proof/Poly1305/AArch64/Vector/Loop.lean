import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Buffer
import VerifiedGarbage.Proof.Poly1305.Stream

/-!
# Poly1305 on AArch64 in AdvSIMD: the setup and the loop

Untrusted: everything here is checked by Lean. After `setup` and each group of
the loop, `LInv` holds: the registers and the memory `vec` keeps, the
multipliers (`[r⁴, r⁴, r², r²]` in `R`, `[r⁴, r³, r², r]` in the last group's),
the constants, and (if the accumulator on entry is below `2¹³⁰ + 2¹²⁹`, as
`Radix64` keeps it) the lanes `A`, `B` with `A r + B ≡ r a` for the
accumulator `a` of the blocks so far.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305.AArch64.Radix64 (hval)

/-- The multipliers' limbs: `yL c` is `r⁴` (words 0, 1) or `r²` (words 2, 3), `yF c` is `r^(4-c)`. -/
structure Ys (R : Nat) (yL yF : Nat → Nat → Nat) : Prop where
  ltL : ∀ c < 4, ∀ i < 5, yL c i < 2 ^ 27
  ltF : ∀ c < 4, ∀ i < 5, yF c i < 2 ^ 27
  valL : ∀ c < 4, val (yL c) % P = R ^ (if c < 2 then 4 else 2) % P
  valF : ∀ c < 4, val (yF c) % P = R ^ (4 - c) % P

/-- The slots of the low halves of `v8`–`v14` in `M`, which is `m` elsewhere. -/
structure Saved (s₀ : State) (M : Mem) : Prop where
  slots : ∀ k < 7, M.readW (svA (s₀.gpr .x0) k) 64 = vdword (s₀.v (V (8 + k))) 0
  frame : Frame [svR (s₀.gpr .x0)] s₀.mem M

/-- The number of groups. -/
abbrev nq (s₀ : State) : Nat := (s₀.gpr .x3).toNat / 64

/-- After `j` groups. -/
structure LInv (s₀ : State) (R : Nat) (M : Mem) (yL yF : Nat → Nat → Nat) (j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x2 : s.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * j)
  x3 : s.gpr .x3 = s₀.gpr .x3
  x9 : s.gpr .x9 = BitVec.ofNat 64 (nq s₀ - 1 - j)
  x7 : s.gpr .x7 = s₀.gpr .x7
  x8 : s.gpr .x8 = s₀.gpr .x8
  x17 : s.gpr .x17 = s₀.gpr .x17
  mem : s.mem = M
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mul : Mults s rV sV yL
  fw : ∀ i < 5, ∀ c < 4, wd (s.v (fV i)) c = yF c i
  mask : ∀ e < 2, ln (s.v maskV) e = 2 ^ 26 - 1
  pad : ∀ e < 2, ln (s.v padV) e = 2 ^ 24
  v15 : s.v .v15 = s₀.v .v15
  acc : (s₀.gpr .x6).toNat ≤ 4 → (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) ∧
    val (hl s 0) * R + val (hl s 1) ≡ R * absorbAll R (hval s₀) (bytesAt M (s₀.gpr .x2) (64 * j)) [MOD P]

/-! ## The setup -/

theorem mask_ok (s : State) :
    WP isa (.block Impl.Poly1305.AArch64.Vector.mask) s fun t =>
      (t.gpr .x16).toNat = 2 ^ 26 - 1 ∧ (∀ r, r ≠ .x16 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [Impl.Poly1305.AArch64.Vector.mask]
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · allstep; rfl
  · allstep

theorem setup_eq : setup = Impl.Poly1305.AArch64.Vector.mask ++ (save ++ (loadH ++ (powers ++
    (times5 rV sV ++ tail)))) := by
  simp only [setup, tail, List.append_assoc]

theorem rV_sV : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → rV i ≠ sV j := by decide
theorem sV_inj : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → sV i ≠ sV j := by
  intro i hi h1 j hj h2 hij
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hij | decide

theorem setup_ok {s₀ : State} {R : Nat} (hk : Radix64.Keys R s₀) (hn : 128 ≤ (s₀.gpr .x3).toNat)
    (hw : ∀ k < 7, InRegions s₀.wr (svA (s₀.gpr .x0) k) 8) :
    WP isa (.block setup) s₀ fun t => ∃ yL yF M, Ys R yL yF ∧ Saved s₀ M ∧ LInv s₀ R M yL yF 0 t := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (mask_ok s₀) fun s1 ⟨m1, g1, v1, mm1, rd1, wr1, _⟩ => ?_)
  refine WP.block_append (WP.mono (save_ok s1 fun k hk => by
      rw [g1 .x0 (by decide), wr1]; exact hw k hk) fun s2 ⟨sl2, f2, g2, v2, rd2, wr2, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadH_ok s2 (by rw [g2 .x16 (by decide)]; exact m1))
    fun s3 ⟨h3, z3, v3, g3, m3, rd3, wr3, _⟩ => ?_)
  refine WP.block_append (WP.mono (powers_ok (s := s3) (R := R) ?keys (by
      rw [g3 .x16 (by decide), g2 .x16 (by decide)]; exact m1))
    fun s4 ⟨L1, L2, L3, L4, p1, p2, p3, p4, w4r, w4f, g4, m4, rd4, wr4, v4⟩ => ?_)
  case keys =>
    obtain ⟨q, a, b, c, d, e⟩ := hk
    have e7 : s3.gpr .x7 = s₀.gpr .x7 := by rw [g3 .x7 (by decide), g2 .x7 (by decide), g1 .x7 (by decide)]
    have e8 : s3.gpr .x8 = s₀.gpr .x8 := by rw [g3 .x8 (by decide), g2 .x8 (by decide), g1 .x8 (by decide)]
    have e17 : s3.gpr .x17 = s₀.gpr .x17 := by
      rw [g3 .x17 (by decide), g2 .x17 (by decide), g1 .x17 (by decide)]
    exact ⟨q, by rw [e7]; exact a, by rw [e8]; exact b, c, by rw [e17]; exact d, by rw [e7, e8]; exact e⟩
  refine WP.block_append (WP.mono (times5_ok rV sV rV_sV sV_inj s4 fun j hj _ c hc => by
      rw [w4r j hj c hc]; split
      · exact Nat.lt_trans (p4.lt j hj) (by decide)
      · exact Nat.lt_trans (p2.lt j hj) (by decide))
    fun s5 ⟨t5, v5, g5, m5, rd5, wr5, _⟩ => ?_)
  refine WP.mono (tail_ok s5) fun t ⟨tm, tp, t9, tg, tv, tmm, trd, twr, _⟩ => ?_
  -- the general-purpose registers
  have gs : ∀ r ∈ [Reg.x0, .x2, .x3, .x7, .x8, .x17, .x4, .x5, .x6], s3.gpr r = s₀.gpr r := fun r hr => by
    rw [g3 r (by revert hr; decide +revert), g2 r (by revert hr; decide +revert),
      g1 r (by revert hr; decide +revert)]
  have gt : ∀ r ∈ [Reg.x0, .x2, .x3, .x7, .x8, .x17], t.gpr r = s₀.gpr r := fun r hr => by
    rw [tg r (by revert hr; decide +revert), congrFun g5 r, g4 r (by revert hr; decide +revert),
      gs r (by revert hr; decide +revert)]
  -- the vectors kept since `s3` (all but the multipliers, `5 R` and the constants)
  have vt : ∀ r, (∀ i < 5, r ≠ rV i ∧ r ≠ fV i) → (∀ j < 5, 1 ≤ j → r ≠ sV j) → r ≠ maskV → r ≠ padV →
      t.v r = s3.v r := fun r h1 h2 h3 h4 => by rw [tv r h3 h4, v5 r h2, v4 r h1]
  have hvt : ∀ i < 5, t.v (hV i) = s3.v (hV i) := fun i hi => vt _
    (fun j hj => (show ∀ i < 5, ∀ j < 5, hV i ≠ rV j ∧ hV i ≠ fV j by decide) i hi j hj)
    (fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → hV i ≠ sV j by decide) i hi j hj h1)
    ((show ∀ i < 5, hV i ≠ maskV by decide) i hi) ((show ∀ i < 5, hV i ≠ padV by decide) i hi)
  have hrt : ∀ i < 5, t.v (rV i) = s4.v (rV i) := fun i hi => by
    rw [tv _ ((show ∀ i < 5, rV i ≠ maskV by decide) i hi) ((show ∀ i < 5, rV i ≠ padV by decide) i hi),
      v5 _ fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → rV i ≠ sV j by decide) i hi j hj h1]
  have hft : ∀ i < 5, t.v (fV i) = s4.v (fV i) := fun i hi => by
    rw [tv _ ((show ∀ i < 5, fV i ≠ maskV by decide) i hi) ((show ∀ i < 5, fV i ≠ padV by decide) i hi),
      v5 _ fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → fV i ≠ sV j by decide) i hi j hj h1]
  have hst : ∀ j < 5, 1 ≤ j → t.v (sV j) = s5.v (sV j) := fun j hj h1 =>
    tv _ ((show ∀ j < 5, 1 ≤ j → sV j ≠ maskV by decide) j hj h1)
      ((show ∀ j < 5, 1 ≤ j → sV j ≠ padV by decide) j hj h1)
  have yL_def : ∀ c < 4, ∀ i < 5, (fun c i => (if c < 2 then L4 else L2) i) c i < 2 ^ 27 := fun c _ i hi => by
    simp only; split
    · exact p4.lt i hi
    · exact p2.lt i hi
  refine ⟨fun c i => (if c < 2 then L4 else L2) i,
    fun c i => (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) i, s2.mem,
    ⟨yL_def, fun c _ i hi => ?_, fun c _ => ?_, fun c hc => ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) i < 2 ^ 27
    split
    · exact p4.lt i hi
    · split
      · exact p3.lt i hi
      · split
        · exact p2.lt i hi
        · exact p1.lt i hi
  · show val (if c < 2 then L4 else L2) % P = _
    split
    · rw [p4.val]
    · rw [p2.val]
  · show val (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) % P = _
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · exact p4.val
    · exact p3.val
    · exact p2.val
    · exact p1.val
  · intro k hk
    have := sl2 k hk
    rw [g1 .x0 (by decide), v1] at this
    exact this
  · rw [g1 .x0 (by decide), mm1] at f2; exact f2
  have x16 : (s5.gpr .x16).toNat = 2 ^ 26 - 1 := by
    rw [congrFun g5 .x16, g4 .x16 (by decide), g3 .x16 (by decide), g2 .x16 (by decide)]; exact m1
  have x3t : s5.gpr .x3 = s₀.gpr .x3 := by rw [congrFun g5 .x3, g4 .x3 (by decide), gs .x3 (by decide)]
  have hv2 : ∀ r, s2.v r = s₀.v r := fun r => by rw [v2, v1]
  have g20 : ∀ r ∈ [Reg.x4, .x5, .x6], s2.gpr r = s₀.gpr r := fun r hr => by
    rw [g2 r (by revert hr; decide +revert), g1 r (by revert hr; decide +revert)]
  refine ⟨gt .x0 (by decide), ?_, gt .x3 (by decide), ?_, gt .x7 (by decide), gt .x8 (by decide),
    gt .x17 (by decide), by rw [tmm, m5, m4, m3], by rw [trd, rd5, rd4, rd3, rd2, rd1],
    by rw [twr, wr5, wr4, wr3, wr2, wr1], ⟨fun i hi c hc => ?_, fun j hj h1 c hc => ?_, yL_def,
      by decide, fun i hi h1 j hj => by revert i; decide +revert⟩, fun i hi c hc => ?_,
    fun e he => by rw [tm e he, x16], tp, ?_, fun h6 => ?_⟩
  · rw [gt .x2 (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [t9, x3t]
    apply BitVec.eq_of_toNat_eq
    have h64 : ((s₀.gpr .x3) >>> 6).toNat = nq s₀ := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [BitVec.toNat_sub, h64, show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
    have := (s₀.gpr .x3).isLt
    simp only [nq] at *
    omega
  · rw [hrt i hi, w4r i hi c hc]
  · rw [hst j hj h1, t5 j hj h1 c hc, w4r j hj c hc]
  · rw [hft i hi, w4f i hi c hc]
  · rw [vt _ (by decide) (by decide) (by decide) (by decide), v3 _ (by decide), hv2]
  · have h62 : (s2.gpr .x6).toNat ≤ 4 := by rw [g20 .x6 (by decide)]; exact h6
    have hl0 : ∀ i < 5, hl t 0 i = limOf s2 i := fun i hi => by
      show ln (t.v (hV i)) 0 = _; rw [hvt i hi]; exact h3 h62 i hi
    have hl1 : ∀ i < 5, hl t 1 i = 0 := fun i hi => by
      show ln (t.v (hV i)) 1 = _; rw [hvt i hi]; exact z3 i hi
    refine ⟨fun e he i hi => ?_, ?_⟩
    · rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · rw [hl0 i hi]; exact lim_lt (s2.gpr .x4).isLt (s2.gpr .x5).isLt h62 i hi
      · rw [hl1 i hi]; decide
    · have v0 : val (hl t 0) = hval s₀ := by
        rw [val_congr hl0, lim_val (s2.gpr .x4).isLt (s2.gpr .x5).isLt]
        simp only [hval, g20 .x4 (by decide), g20 .x5 (by decide), g20 .x6 (by decide)]
      have v1' : val (hl t 1) = 0 := by rw [val_congr hl1]; rfl
      rw [v0, v1', Nat.mul_zero, show bytesAt s2.mem (s₀.gpr .x2) 0 = [] from rfl, Poly1305.absorbAll_nil]
      exact Poly1305.pair_init R (hval s₀)

/-! ## A group of the loop -/

/-- The bytes of a group, in four blocks. -/
theorem group_bytes (m : Mem) (p : Addr) (j : Nat) :
    bytesAt m p (64 * (j + 1)) = bytesAt m p (64 * j) ++
      (bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 0)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 1)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 2)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 3)) 16) := by
  rw [show 64 * (j + 1) = 64 * j + 64 from by omega, Poly1305.bytesAt_add]
  generalize p + BitVec.ofNat 64 (64 * j) = q
  rw [show bytesAt m q 64 = bytesAt m q (16 + (16 + (16 + 16))) from rfl, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.mul_zero, Nat.mul_one,
    BitVec.add_zero]

theorem step_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} {j : Nat} (hY : Ys R yL yF)
    (hL : LInv s₀ R M yL yF j s) (hj : j + 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa (.block (group rV sV ++ ([.addImm .x .x2 .x2 64, .subImm .x .x9 .x9 1] : List Instr))) s
      (LInv s₀ R M yL yF (j + 1)) := by
  have hn := (s₀.gpr .x3).isLt
  have ga : ∀ j' < 4, gAddr s j' = s₀.gpr .x2 + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * j') :=
    fun j' _ => by rw [gAddr, hL.x2]
  refine WP.block_append (WP.mono (group_ok hL.mul hL.mask hL.pad fun j' hj' => by
      rw [ga j' hj', hL.rd, hL.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hd _ (by simp only [nq] at hj; omega)) fun t ⟨hg, gk⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  have tv : ∀ r, (∀ i < 5, r ≠ hV i ∧ r ≠ dV i ∧ r ≠ iV i) → t.v r = s.v r := gk.v
  have gt : ∀ r, t.gpr r = s.gpr r := fun r => congrFun gk.gpr r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi c hc => ?_, fun e he => ?_, fun e he => ?_, ?_,
    fun h6 => ?_⟩
  · allstep; rw [gt, hL.x0]
  · allstep; rw [gt, hL.x2, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · allstep; rw [gt, hL.x3]
  · allstep; rw [gt, hL.x9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nq] at *; omega
  · allstep; rw [gt, hL.x7]
  · allstep; rw [gt, hL.x8]
  · allstep; rw [gt, hL.x17]
  · simp only [RegUpd.mem_write]; rw [gk.mem, hL.mem]
  · simp only [RegUpd.rd_write]; rw [gk.rd, hL.rd]
  · simp only [RegUpd.wr_write]; rw [gk.wr, hL.wr]
  · exact hL.mul.of_v fun r h => tv r fun i hi => ⟨(h i hi).2.2, (h i hi).2.1, (h i hi).1⟩
  · show wd (t.v (fV i)) c = _
    rw [tv _ fun i' hi' => (show ∀ i < 5, ∀ i' < 5, fV i ≠ hV i' ∧ fV i ≠ dV i' ∧ fV i ≠ iV i' by decide) i hi i' hi']
    exact hL.fw i hi c hc
  · show ln (t.v maskV) e = _; rw [tv _ (by decide)]; exact hL.mask e he
  · show ln (t.v padV) e = _; rw [tv _ (by decide)]; exact hL.pad e he
  · show t.v .v15 = _; rw [tv _ (by decide)]; exact hL.v15
  · obtain ⟨hb, hS⟩ := hL.acc h6
    have hg' := hg hb
    have hlt : ∀ e < 2, ∀ i < 5, hl t e i < 2 ^ 27 := fun e he i hi => (hg' e he i hi).2
    -- the lanes after the group
    have l0 := group_lane (s := s) (t := t) (y := yL) (e := 0) fun i hi => (hg' 0 (by decide) i hi).1
    have l1 := group_lane (s := s) (t := t) (y := yL) (e := 1) fun i hi => (hg' 1 (by decide) i hi).1
    have y0 : val (yL 0) ≡ R ^ 4 [MOD P] := hY.valL 0 (by decide)
    have y1 : val (yL 1) ≡ R ^ 4 [MOD P] := hY.valL 1 (by decide)
    have y2 : val (yL 2) ≡ R ^ 2 [MOD P] := hY.valL 2 (by decide)
    have y3 : val (yL 3) ≡ R ^ 2 [MOD P] := hY.valL 3 (by decide)
    have len : ∀ j' : Nat, (gbytes s j').length = 16 := fun _ => Poly1305.length_bytesAt _ _ _
    have eA := l0.trans ((y2.mul_left _).add (y0.mul_left _))
    have eB := l1.trans ((y3.mul_left _).add (y1.mul_left _))
    have hstep := Poly1305.pair_step (len 0) (len 1) (len 2) (len 3) hS
      (eA.trans (by rw [Nat.add_comm]))
      (eB.trans (by rw [Nat.add_comm]))
    refine ⟨fun e he i hi => ?_, ?_⟩
    · exact hlt e he i hi
    · show val (hl t 0) * R + val (hl t 1) ≡ _ [MOD P]
      refine hstep.trans ?_
      rw [← Poly1305.absorbAll_append (by rw [Poly1305.length_bytesAt]; omega), group_bytes]
      simp only [gbytes, ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide), hL.mem,
        List.append_assoc]
      exact Nat.ModEq.refl _

/-! ## The loop -/

theorem loop_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} (hY : Ys R yL yF)
    (hL : LInv s₀ R M yL yF 0 s) (hq : 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa (.loop (.block (group rV sV ++ ([.addImm .x .x2 .x2 64, .subImm .x .x9 .x9 1] : List Instr)))
      (.nonzero .x .x9)) s (LInv s₀ R M yL yF (nq s₀ - 1)) := by
  have hn := (s₀.gpr .x3).isLt
  refine WP.loop (M := isa) (fun k s => ∃ j, k = nq s₀ - 1 - j ∧ LInv s₀ R M yL yF j s ∧ j + 2 ≤ nq s₀) ?_ _ s
    ⟨0, rfl, hL, hq⟩
  rintro k s ⟨j, rfl, h, hj⟩
  refine WP.mono (step_ok hY h hj hd) fun s' h' => ?_
  have hev : isa.eval (.nonzero .x .x9) s' = some (!decide (nq s₀ - 1 - (j + 1) = 0)) := by
    rw [AArch64.eval_nonzero, h'.x9, show (BitVec.ofNat 64 (nq s₀ - 1 - (j + 1)) != 0) =
      !(BitVec.ofNat 64 (nq s₀ - 1 - (j + 1)) == 0) from rfl, Poly1305.ofNat_beq_zero (by simp only [nq] at *; omega)]
  by_cases hl : nq s₀ - 1 - (j + 1) = 0
  · refine .inl ⟨by rw [hev, hl]; rfl, ?_⟩
    rw [show nq s₀ - 1 = j + 1 by omega]; exact h'
  · exact .inr ⟨by rw [hev]; simp only [hl, decide_false, Bool.not_false], _, by omega, j + 1, rfl, h',
      by omega⟩

end VG.Proof.Poly1305.AArch64.Vector
