module
-- separate module: the proof of the division by words is split in a chain of modules (`KdNorm`, `KdTop`, `KdEst`, `KdStep`, `KdDiv`), so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.Arm.KdTop
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Bignum.WordTop32

/-! # A step's estimate of the key checks' division on ARMv7 (`KeyDiv.estimate`)

With the pieces it is made of: the 2-by-1 estimate (`KeyDiv.quot`) and the 3-by-2
refinement (`KeyDiv.refine3`).
-/

@[expose] public section

/-! ## The 2-by-1 estimate of the key checks' division on ARMv7 (`KeyDiv.quot`) -/

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem readW_slot_ne (m : Mem) (A : Addr) (o d : Nat) (v : BitVec 32) (hsep : d + 4 ≤ o ∨ o + 4 ≤ d)
    (ho : o < 2 ^ 32) (hd : d < 2 ^ 32) :
    (m.writeW (off A o) v).readW (off A d) 32 = m.readW (off A d) 32 :=
  VG.Mem.readW_writeW_sep (VG.Offset.sep A hsep (by omega_using [hd]) (by omega_using [ho])) (by decide)

/-- The mask of `u₂ = d`, from `d - u₂ ≥ 1`'s carry. -/
abbrev eqMask (u2 d : Nat) : BitVec 32 := if u2 = d then -1 else 0

theorem eqMask_eq {u2 d : Nat} (hu : u2 ≤ d) (hd : d < 2 ^ 32) :
    (0 + 0 + bif decide ((1 : BitVec 32).toNat ≤ (BitVec.ofNat 32 d - BitVec.ofNat 32 u2).toNat) then 1 else 0) -
      1 = eqMask u2 d := by
  have e : (BitVec.ofNat 32 d - BitVec.ofNat 32 u2).toNat = d - u2 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hu, hd]
  rw [e, show (1 : BitVec 32).toNat = 1 from rfl]
  by_cases h : u2 = d
  · subst h; simp only [Nat.sub_self, eqMask, ite_true]; decide
  · have : 1 ≤ d - u2 := by omega_using [hu, h]
    simp only [eqMask, h, ite_false, this, decide_true, Bool.cond_true]; decide

theorem bic_eqMask {u2 d : Nat} :
    BitVec.ofNat 32 u2 &&& ~~~(eqMask u2 d) = BitVec.ofNat 32 (if u2 = d then 0 else u2) := by
  by_cases h : u2 = d
  · simp only [eqMask, h, ite_true]; rw [show ~~~(-1 : BitVec 32) = 0 by decide]; simp
  · simp only [eqMask, h, ite_false]; rw [show ~~~(0 : BitVec 32) = -1 by decide]
    rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem bit_toNat (b : Bool) : (bif b then (1 : BitVec 32) else 0).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem bitMask_eq (b : Bool) : (0 + 0 + bif b then (1 : BitVec 32) else 0) - 1 = bif b then 0 else -1 := by
  cases b <;> decide

/-- `quot`'s arithmetic after its product `(hi, lo) = v u₂`, for `u₂ < d`: Möller
and Granlund's quotient (`WordStep32.mg_quot`). -/
theorem quot_expr {lo hi : BitVec 32} {u2 u1 d : Nat} (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) (hu : u2 < d)
    (hu1 : u1 < 2 ^ 32) (hP : lo.toNat + hi.toNat * 2 ^ 32 = u2 * ((2 ^ 64 - 1) / d - 2 ^ 32)) :
    (hi + BitVec.ofNat 32 u2 + bif decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 u1).toNat) then 1 else 0) + 1 +
        ((0 + 0 + bif decide ((BitVec.ofNat 32 u1 - ((hi + BitVec.ofNat 32 u2 +
          bif decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 u1).toNat) then 1 else 0) + 1) *
            BitVec.ofNat 32 d).toNat ≤ (lo + BitVec.ofNat 32 u1).toNat) then 1 else 0) - 1) + 0 +
      (bif decide ((BitVec.ofNat 32 d).toNat ≤ (BitVec.ofNat 32 u1 - ((hi + BitVec.ofNat 32 u2 +
          bif decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 u1).toNat) then 1 else 0) + 1) *
            BitVec.ofNat 32 d + ((0 + 0 + bif decide ((BitVec.ofNat 32 u1 - ((hi + BitVec.ofNat 32 u2 +
              bif decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 u1).toNat) then 1 else 0) + 1) *
                BitVec.ofNat 32 d).toNat ≤ (lo + BitVec.ofNat 32 u1).toNat) then 1 else 0) - 1 &&&
                  BitVec.ofNat 32 d)).toNat) then 1 else 0) =
      BitVec.ofNat 32 ((u2 * 2 ^ 32 + u1) / d) := by
  have hd0 : 0 < d := by omega_using [hd1]
  have hV : (2 ^ 64 - 1) / d = (2 ^ 64 - 1) / d - 2 ^ 32 + 2 ^ 32 := by
    have : 2 ^ 32 ≤ (2 ^ 64 - 1) / d := by rw [Nat.le_div_iff_mul_le hd0]; omega_using [hd2]
    omega_using [this]
  generalize eV : (2 ^ 64 - 1) / d = V at hV hP
  generalize ePP : V * u2 + u1 = PP
  have ePP' : PP = lo.toNat + hi.toNat * 2 ^ 32 + u2 * 2 ^ 32 + u1 := by
    have e : V * u2 = (V - 2 ^ 32) * u2 + 2 ^ 32 * u2 := by rw [← Nat.add_mul, ← hV]
    rw [← ePP, e, hP]; rw [Nat.mul_comm u2 (V - 2 ^ 32), Nat.mul_comm (2 ^ 32) u2]
  have eu2 : (BitVec.ofNat 32 u2).toNat = u2 := by rw [BitVec.toNat_ofNat]; omega_using [hd2, hu]
  have eu1 : (BitVec.ofNat 32 u1).toNat = u1 := by rw [BitVec.toNat_ofNat]; omega_using [hu1]
  have ed : (BitVec.ofNat 32 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega_using [hd2]
  have hlo := lo.isLt
  have hhi := hi.isLt
  rw [eu1, ed]
  generalize eQ : (hi + BitVec.ofNat 32 u2 + bif decide (2 ^ 32 ≤ lo.toNat + u1) then 1 else 0) + 1 = Q
  have hQ : Q.toNat = (PP / 2 ^ 32 + 1) % 2 ^ 32 := by
    rw [← eQ, ePP']
    simp only [BitVec.toNat_add, bit_toNat, eu2, show (1 : BitVec 32).toNat = 1 from rfl]
    split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega_arith
  have hq0 : (lo + BitVec.ofNat 32 u1).toNat = PP % 2 ^ 32 := by
    rw [BitVec.toNat_add, eu1, ePP']; omega_using []
  generalize er : BitVec.ofNat 32 u1 - Q * BitVec.ofNat 32 d = r
  have hr : r.toNat = (u1 + (2 ^ 32 - Q.toNat * d % 2 ^ 32)) % 2 ^ 32 := by
    rw [← er, BitVec.toNat_sub, BitVec.toNat_mul, eu1, ed]; omega_using []
  rw [hq0, bitMask_eq]
  generalize ec : decide (r.toNat ≤ PP % 2 ^ 32) = c
  have neg1 : (-1 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide
  have hm : ∀ x : BitVec 32, (x + bif c then 0 else -1).toNat =
      (x.toNat + if PP % 2 ^ 32 < r.toNat then 2 ^ 32 - 1 else 0) % 2 ^ 32 := fun x => by
    cases c
    · have hc : PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_false_iff_not] at ec; omega_using [ec]
      simp only [hc, ↓reduceIte, Bool.cond_false]; rw [BitVec.toNat_add, neg1]
    · have hc : ¬ PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_true_eq] at ec; omega_using [ec]
      simp only [hc, ↓reduceIte, Bool.cond_true]
      rw [BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]
  have hm2 : (r + ((bif c then (0 : BitVec 32) else -1) &&& BitVec.ofNat 32 d)).toNat =
      (r.toNat + if PP % 2 ^ 32 < r.toNat then d else 0) % 2 ^ 32 := by
    cases c
    · have hc : PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_false_iff_not] at ec; omega_using [ec]
      simp only [hc, ↓reduceIte, Bool.cond_false]
      rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.toNat_add, ed]
    · have hc : ¬ PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_true_eq] at ec; omega_using [ec]
      simp only [hc, ↓reduceIte, Bool.cond_true]
      rw [BitVec.toNat_add, BitVec.toNat_and, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_and]
  have key := VG.Proof.Bignum.WordStep32.mg_quot (d := d) (u := u2) (a := u1) (V := V) (P := PP)
    (Q := Q.toNat) (r := r.toNat) (Q1 := (Q + bif c then 0 else -1).toNat)
    (r1 := (r + ((bif c then (0 : BitVec 32) else -1) &&& BitVec.ofNat 32 d)).toNat) hd2 hd1 hu hu1 eV.symm
    (by rw [← ePP, Nat.mul_comm]) hQ hr (hm Q) hm2
  apply BitVec.eq_of_toNat_eq
  have : (u2 * 2 ^ 32 + u1) / d < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hd0]; omega_using [hd1, hd2, hu, hu1, hd0, eV, hP, ePP, eu2, eu1, ed, eQ, hq0, er, hr, key]
  have hq1 := (Q + bif c then 0 else -1).isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, bit_toNat,
    BitVec.toNat_ofNat]
  revert key
  generalize (Q + bif c then 0 else -1).toNat = q1
  generalize (r + ((bif c then (0 : BitVec 32) else -1) &&& BitVec.ofNat 32 d)).toNat = r1
  intro key
  simp only [decide_eq_true_eq]
  rw [Nat.mod_eq_of_lt this, ← key]
  by_cases hr : d ≤ r1
  · have h2 : d - 1 < r1 := by omega_using [hd1, hr]
    simp only [hr, h2, ↓reduceIte]; omega_using []
  · have h2 : ¬ d - 1 < r1 := by omega_using [hr]
    simp only [hr, h2, ↓reduceIte]; omega_using []

theorem or_zero32 (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero

/-- The registers `quot` changes. -/
abbrev quotRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- `quot`: `q̂` (156), `min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)` for `u₂ ≤ d`,
from `u₂` (68), `u₁` (`r11`), `d` (140) and `v` (144). -/
theorem quot_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (h12 : s.gpr .r12 = B)
    {u2 u1 d : Nat} (hu1 : s.gpr .r11 = BitVec.ofNat 32 u1) (hD : slot s.mem B sD = d)
    (hU2 : slot s.mem B sU2 = u2) (hV : slot s.mem B sV = (2 ^ 64 - 1) / d - 2 ^ 32)
    (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) (hu2 : u2 ≤ d) (hu1' : u1 < 2 ^ 32) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, slot t.mem B sQ = (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) →
      Keep B w [] [sMk, sQ] s.mem t.mem → t.gpr .r11 = s.gpr .r11 → t.gpr .r12 = B → Rest quotRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (quot ++ rest)) s Q := by
  have hz := h.hdr_le
  have sl : ∀ {o : Nat}, o + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → State.addr (B + BitVec.ofNat 32 o) = off (State.addr B) o ∧
      InRegions (s.rd ++ s.wr) (off (State.addr B) o) 4 ∧ InRegions s.wr (off (State.addr B) o) 4 := fun ho =>
    ⟨h.addr (by omega_using [hz, ho]), h.read (by omega_using [hz, ho]), h.write (by omega_using [hz, ho])⟩
  obtain ⟨aD, rD, -⟩ := sl (o := sD) (by decide)
  obtain ⟨aU2, rU2, -⟩ := sl (o := sU2) (by decide)
  obtain ⟨aV, rV, -⟩ := sl (o := sV) (by decide)
  obtain ⟨aMk, rMk, wMk⟩ := sl (o := sMk) (by decide)
  obtain ⟨aQ, -, wQ⟩ := sl (o := sQ) (by decide)
  have tv : ∀ {o v : Nat}, slot s.mem B o = v → s.mem.readW (off (State.addr B) o) 32 = BitVec.ofNat 32 v :=
    fun e => by rw [← e]; exact (ofNat_toNat32 _).symm
  generalize ev : (2 ^ 64 - 1) / d - 2 ^ 32 = v at hV
  simp only [quot, List.append_assoc]
  have hu2' : u2 < 2 ^ 32 := by omega_using [hd2, hu2]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r10, .r2] (Q := fun t =>
      t.gpr .r1 = BitVec.ofNat 32 (if u2 = d then 0 else u2) ∧
      t.gpr .r10 = BitVec.ofNat 32 (if u2 = d then 0 else u2) ∧ t.gpr .r2 = BitVec.ofNat 32 v ∧
      t.mem = s.mem.writeW (off (State.addr B) sMk) (eqMask u2 d)) (by
    krun [h12, aD, aU2, aV, aMk, rD, rU2, rV, wMk, tv hD, tv hU2, readW_slot_ne, tv hV, eqMask_eq hu2 hd2,
      bic_eqMask]) (by decide)) fun v1 ⟨⟨i1, t1, p1, m1⟩, k1⟩ => ?_)
  refine wp_wide fun v2 e2 P2 => ?_
  have q11 : v2.gpr .r11 = BitVec.ofNat 32 u1 := (P2.regs _ (by decide)).trans ((k1.gpr _ (by decide)).trans hu1)
  have q10 : v2.gpr .r10 = BitVec.ofNat 32 (if u2 = d then 0 else u2) := (P2.regs _ (by decide)).trans t1
  have q12 : v2.gpr .r12 = B := (P2.regs _ (by decide)).trans ((k1.gpr _ (by decide)).trans h12)
  have qm : v2.mem = s.mem.writeW (off (State.addr B) sMk) (eqMask u2 d) := P2.mem.trans m1
  have rD2 : InRegions (v2.rd ++ v2.wr) (off (State.addr B) sD) 4 := by rw [P2.rd, P2.wr, k1.rd, k1.wr]; exact rD
  have rMk2 : InRegions (v2.rd ++ v2.wr) (off (State.addr B) sMk) 4 := by rw [P2.rd, P2.wr, k1.rd, k1.wr]; exact rMk
  have wQ2 : InRegions v2.wr (off (State.addr B) sQ) 4 := by rw [P2.wr, k1.wr]; exact wQ
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10] (Q := fun t =>
      t.mem = v2.mem.writeW (off (State.addr B) sQ)
        (BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d))) (by
    krun [q11, q10, q12, qm, aD, aMk, aQ, rD2, rMk2, wQ2, readW_slot_ne, tv hD, VG.Mem.readW_writeW_self32]
    refine congrArg (Mem.writeW _ _) ?_
    by_cases e : u2 = d
    · simp only [e, ite_true, eqMask]
      rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.or_allOnes]; decide
    · have e2' : (v2.gpr .r3).toNat + (v2.gpr .r4).toNat * 2 ^ 32 = u2 * v := by
        rw [e2, i1, p1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        simp only [e, ite_false]
        rw [Nat.mod_eq_of_lt (by omega_using [hu2']), Nat.mod_eq_of_lt (show v < 2 ^ 32 from hV ▸ BitVec.isLt _)]
      simp only [e, ite_false, eqMask]
      rw [or_zero32]
      rw [← ev] at e2'
      exact quot_expr hd1 hd2 (by omega_using [hu2, e]) hu1' e2') (by decide)) fun v3 ⟨m3, k3⟩ => ?_)
  have ht : (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) < 2 ^ 32 := by
    split
    · omega_using []
    · rw [Nat.div_lt_iff_lt_mul (by omega_using [hd1])]; omega_arith
  refine k v3 ?_ ?_ ?_ ?_ ?_
  · simp only [slot]; rw [m3, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  · rw [m3, qm]
    exact (keep_write _ _ (by simp) (by simp only [sMk]; omega_using [])).trans (keep_write _ _ (by simp) (by simp only [sQ]; omega_using []))
  · rw [k3.gpr _ (by decide), P2.regs _ (by decide), k1.gpr _ (by decide)]
  · rw [k3.gpr _ (by decide), q12]
  · exact ((k1.mono (by decide)).trans ((Preserves.toRest P2).mono (by decide))).trans (k3.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv

/-! ## The 3-by-2 refinement of the key checks' division on ARMv7 (`KeyDiv.refine3`) -/

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The part of `refine3` after its two products, up to the store. -/
def refineTail : List Instr :=
  [.adds .r1 .r3 (.reg .r10), .adc .r2 .r4 (.imm 0),
    .ldr .r10 .r12 sU0, .subs .r10 .r10 (.reg .r0), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .dp .eor .r3 .r3 (.imm 1),
    .subs .r11 .r11 (.reg .r1), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0), .subs .r11 .r11 (.reg .r3),
    .adc .r4 .r4 (.imm 0), .dp .eor .r3 .r4 (.imm 3),
    .ldr .lr .r12 sU2, .dp .sub .lr .lr (.reg .r2), .dp .sub .lr .lr (.reg .r3), .ldr .r1 .r12 sQ] ++ fix3 ++ fix3

theorem negMask (t : BitVec 32) : (0 : BitVec 32) - t >>> 31 = if 2 ^ 31 ≤ t.toNat then -1 else 0 := by
  have e : (t >>> 31).toNat = t.toNat / 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := t.isLt
  by_cases h : 2 ^ 31 ≤ t.toNat
  · simp only [h, ↓reduceIte]
    have : t >>> 31 = 1 := BitVec.eq_of_toNat_eq (by rw [e]; show _ = 1; omega_using [h])
    rw [this]; decide
  · simp only [h, ↓reduceIte]
    have : t >>> 31 = 0 := BitVec.eq_of_toNat_eq (by rw [e]; show _ = 0; omega_using [h])
    rw [this]; decide

theorem and_negMask (x : BitVec 32) (c : Prop) [Decidable c] :
    (x &&& if c then (-1 : BitVec 32) else 0) = if c then x else 0 := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
  · simp only [h, ↓reduceIte]; exact BitVec.and_zero

theorem carry_toNat (a b : BitVec 32) :
    ((0 : BitVec 32) + 0 + bif decide (2 ^ 32 ≤ a.toNat + b.toNat) then 1 else 0).toNat =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp [h]

theorem carry_div (n : Nat) : (bif decide (2 ^ 32 ≤ n) then (1 : BitVec 32) else 0).toNat = min (n / 2 ^ 32) 1 := by
  by_cases h : 2 ^ 32 ≤ n
  · simp only [h, decide_true, Bool.cond_true]; show 1 = _; omega_using [h]
  · simp only [h, decide_false, Bool.cond_false]; show 0 = _; omega_using [h]

/-- `fix3`: for `t = (t₂, t₁, t₀)` negative (its top bit set), `q̂ - 1` and
`t + D` modulo `2^96`. -/
theorem fix3_ok {s : State} {B : BitVec 32} (h12 : s.gpr .r12 = B)
    {d d1 : BitVec 32} (hD : s.mem.readW (off (State.addr B) sD) 32 = d)
    (hD1 : s.mem.readW (off (State.addr B) sD1) 32 = d1)
    (aD : State.addr (B + BitVec.ofNat 32 sD) = off (State.addr B) sD)
    (aD1 : State.addr (B + BitVec.ofNat 32 sD1) = off (State.addr B) sD1)
    (rD : InRegions (s.rd ++ s.wr) (off (State.addr B) sD) 4)
    (rD1 : InRegions (s.rd ++ s.wr) (off (State.addr B) sD1) 4) :
    WP isa (.block fix3) s fun t =>
      t.gpr .r1 = s.gpr .r1 + (if 2 ^ 31 ≤ (s.gpr .lr).toNat then -1 else 0) ∧
      (t.gpr .r10).toNat + (t.gpr .r11).toNat * 2 ^ 32 + (t.gpr .lr).toNat * 2 ^ 64 =
        ((s.gpr .r10).toNat + (s.gpr .r11).toNat * 2 ^ 32 + (s.gpr .lr).toNat * 2 ^ 64 +
          if 2 ^ 31 ≤ (s.gpr .lr).toNat then d.toNat * 2 ^ 32 + d1.toNat else 0) % 2 ^ 96 ∧
      t.mem = s.mem ∧ t.gpr .r12 = s.gpr .r12 := by
  krun [fix3, h12, hD, hD1, aD, aD1, rD, rD1]
  simp only [negMask, and_negMask]
  by_cases hn : 2 ^ 31 ≤ (s.gpr .lr).toNat
  · simp only [hn, ↓reduceIte, true_and]
    simp only [BitVec.toNat_add]
    simp only [carry_div, show BitVec.toNat (0 : BitVec 32) = 0 from rfl, Nat.zero_add, Nat.zero_mod,
      Nat.add_zero]
    omega_using []
  · simp only [hn, ↓reduceIte, true_and]
    have z0 : BitVec.toNat (0 : BitVec 32) = 0 := rfl
    have nc : ∀ x : BitVec 32, decide (2 ^ 32 ≤ x.toNat + 0) = false := fun x => by
      have := x.isLt; simp only [decide_eq_false_iff_not]; omega_using []
    rw [z0, nc, nc]
    have e0 : (0 + 0 + bif false then (1 : BitVec 32) else 0) = 0 := by decide
    have a0 : ∀ x : BitVec 32, x + 0 = x := fun x => BitVec.add_zero x
    rw [e0, a0, a0, z0, nc, e0, a0, e0, a0]
    have h0 := (s.gpr .r10).isLt
    have h1 := (s.gpr .r11).isLt
    have h2 := (s.gpr .lr).isLt
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [])]

theorem geBit (a b : Nat) : (bif decide (a ≤ b) then (1 : BitVec 32) else 0).toNat = min (b + 1 - a) 1 := by
  by_cases h : a ≤ b
  · simp only [h, decide_true, Bool.cond_true]; show 1 = _; omega_using [h]
  · simp only [h, decide_false, Bool.cond_false]; show 0 = _; omega_using [h]

theorem geBit_xor1 (a b : Nat) :
    ((0 + 0 + bif decide (a ≤ b) then (1 : BitVec 32) else 0) ^^^ 1).toNat = 1 - min (b + 1 - a) 1 := by
  by_cases h : a ≤ b
  · simp only [h, decide_true, Bool.cond_true]; show 0 = _; omega_using [h]
  · simp only [h, decide_false, Bool.cond_false]; show 1 = _; omega_using [h]

theorem geBits_xor3 (a b c d : Nat) :
    (((1 + 0 + bif decide (a ≤ b) then (1 : BitVec 32) else 0) + 0 + bif decide (c ≤ d) then 1 else 0) ^^^
      3).toNat = 2 - min (b + 1 - a) 1 - min (d + 1 - c) 1 := by
  by_cases h : a ≤ b <;> by_cases h' : c ≤ d <;>
    simp only [h, h', decide_true, decide_false, Bool.cond_true, Bool.cond_false] <;>
    first | (show 0 = _; omega_using [h, h']) | (show 1 = _; omega_using [h, h']) | (show 2 = _; omega_using [h, h'])

/-- `sub96`'s arithmetic: `U - q̂ D` modulo `2^96`, by words with their borrows. -/
theorem sub96_nat {r0 r3 r4 r10 r11 u0 u2 : Nat} (h0 : r0 < 2 ^ 32) (h3 : r3 < 2 ^ 32) (h4 : r4 < 2 ^ 32)
    (h10 : r10 < 2 ^ 32) (h11 : r11 < 2 ^ 32) (hu0 : u0 < 2 ^ 32) (hu2 : u2 < 2 ^ 32)
    (hq : r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64 < 2 ^ 96) :
    (2 ^ 32 - r0 + u0) % 2 ^ 32 +
        (2 ^ 32 - (1 - min (u0 + 1 - r0) 1) + (2 ^ 32 - (r3 + r10) % 2 ^ 32 + r11) % 2 ^ 32) % 2 ^ 32 * 2 ^ 32 +
      (2 ^ 32 - (2 - min (r11 + 1 - (r3 + r10) % 2 ^ 32) 1 -
            min ((2 ^ 32 - (r3 + r10) % 2 ^ 32 + r11) % 2 ^ 32 + 1 - (1 - min (u0 + 1 - r0) 1)) 1) +
          (2 ^ 32 - (r4 % 2 ^ 32 + min (r3 + r10 + 1 - 2 ^ 32) 1) % 2 ^ 32 + u2) % 2 ^ 32) % 2 ^ 32 * 2 ^ 64 =
      (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) % 2 ^ 96 := by
  have e1 := Nat.div_add_mod (r3 + r10) (2 ^ 32)
  have b1 : (r3 + r10) / 2 ^ 32 < 2 := by omega_using [h3, h10]
  have b2 := Nat.mod_lt (r3 + r10) (Nat.two_pow_pos 32)
  have e2 : min (r3 + r10 + 1 - 2 ^ 32) 1 = (r3 + r10) / 2 ^ 32 := by omega_using [h3, h10]
  rw [e2, Nat.mod_eq_of_lt h4]
  generalize (r3 + r10) % 2 ^ 32 = m at *
  generalize (r3 + r10) / 2 ^ 32 = c at *
  have e3 : (r4 + c) % 2 ^ 32 = r4 + c := Nat.mod_eq_of_lt (by omega_using [hq, e2])
  rw [e3]
  have b0 : 1 - min (u0 + 1 - r0) 1 = if r0 ≤ u0 then 0 else 1 := by split <;> omega_arith
  have bm : 2 - min (r11 + 1 - m) 1 - min ((2 ^ 32 - m + r11) % 2 ^ 32 + 1 - (if r0 ≤ u0 then 0 else 1)) 1 =
      (if m ≤ r11 then 0 else 1) + (if (if r0 ≤ u0 then 0 else 1) ≤ (2 ^ 32 - m + r11) % 2 ^ 32 then 0 else 1) := by
    repeat' split
    all_goals omega_arith
  rw [b0, bm]
  -- t0
  have f0 : u0 + (if r0 ≤ u0 then 0 else 1) * 2 ^ 32 = r0 + (2 ^ 32 - r0 + u0) % 2 ^ 32 := by split <;> omega_arith
  have g0 := Nat.mod_lt (2 ^ 32 - r0 + u0) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - r0 + u0) % 2 ^ 32 = t0 at *
  generalize (if r0 ≤ u0 then 0 else 1) = x0 at *
  have hx0 : x0 < 2 := by omega_using [b0]
  -- a
  have fa : r11 + (if m ≤ r11 then 0 else 1) * 2 ^ 32 = m + (2 ^ 32 - m + r11) % 2 ^ 32 := by split <;> omega_arith
  have ga := Nat.mod_lt (2 ^ 32 - m + r11) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - m + r11) % 2 ^ 32 = a at *
  generalize (if m ≤ r11 then 0 else 1) = xa at *
  have hxa : xa < 2 := by omega_using [b2, ga, fa]
  -- t1
  have f1 : a + (if x0 ≤ a then 0 else 1) * 2 ^ 32 = x0 + (2 ^ 32 - x0 + a) % 2 ^ 32 := by split <;> omega_arith
  have g1 := Nat.mod_lt (2 ^ 32 - x0 + a) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - x0 + a) % 2 ^ 32 = t1 at *
  generalize (if x0 ≤ a then 0 else 1) = xb at *
  have hxb : xb < 2 := by omega_using [fa, bm]
  -- t2
  have f2 := Nat.div_add_mod (2 ^ 32 - (r4 + c) + u2) (2 ^ 32)
  have g2 := Nat.mod_lt (2 ^ 32 - (r4 + c) + u2) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - (r4 + c) + u2) % 2 ^ 32 = y at *
  have f3 := Nat.div_add_mod (2 ^ 32 - (xa + xb) + y) (2 ^ 32)
  have g3 := Nat.mod_lt (2 ^ 32 - (xa + xb) + y) (Nat.two_pow_pos 32)
  generalize (2 ^ 32 - (xa + xb) + y) % 2 ^ 32 = t2 at *
  have f4 := Nat.div_add_mod (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) (2 ^ 96)
  have g4 := Nat.mod_lt (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64))
    (Nat.two_pow_pos 96)
  generalize (u0 + r11 * 2 ^ 32 + u2 * 2 ^ 64 + 2 ^ 96 - (r0 + (r3 + r10) * 2 ^ 32 + r4 * 2 ^ 64)) % 2 ^ 96 = z at *
  omega_using [h0, h3, h4, h10, h11, hu0, hu2, hq, e2, e1, e3, g0, b0, f0, hx0, ga, fa, hxa, g1, bm, f1, hxb, f2, g2, f3, g3, f4, g4]

/-- The subtraction of `quot3`, after its two products. -/
def sub96 : List Instr :=
  [.adds .r1 .r3 (.reg .r10), .adc .r2 .r4 (.imm 0),
    .ldr .r10 .r12 sU0, .subs .r10 .r10 (.reg .r0), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
    .dp .eor .r3 .r3 (.imm 1),
    .subs .r11 .r11 (.reg .r1), .mov .r4 (.imm 1), .adc .r4 .r4 (.imm 0), .subs .r11 .r11 (.reg .r3),
    .adc .r4 .r4 (.imm 0), .dp .eor .r3 .r4 (.imm 3),
    .ldr .lr .r12 sU2, .dp .sub .lr .lr (.reg .r2), .dp .sub .lr .lr (.reg .r3)]

theorem sub96_ok {s : State} {B : BitVec 32} (h12 : s.gpr .r12 = B) {u0 u2 : BitVec 32}
    (hU0 : s.mem.readW (off (State.addr B) sU0) 32 = u0) (hU2 : s.mem.readW (off (State.addr B) sU2) 32 = u2)
    (aU0 : State.addr (B + BitVec.ofNat 32 sU0) = off (State.addr B) sU0)
    (aU2 : State.addr (B + BitVec.ofNat 32 sU2) = off (State.addr B) sU2)
    (rU0 : InRegions (s.rd ++ s.wr) (off (State.addr B) sU0) 4)
    (rU2 : InRegions (s.rd ++ s.wr) (off (State.addr B) sU2) 4)
    (hq : (s.gpr .r0).toNat + ((s.gpr .r3).toNat + (s.gpr .r10).toNat) * 2 ^ 32 + (s.gpr .r4).toNat * 2 ^ 64 <
      2 ^ 96) :
    WP isa (.block sub96) s fun t =>
      (t.gpr .r10).toNat + (t.gpr .r11).toNat * 2 ^ 32 + (t.gpr .lr).toNat * 2 ^ 64 =
        (u0.toNat + (s.gpr .r11).toNat * 2 ^ 32 + u2.toNat * 2 ^ 64 + 2 ^ 96 -
          ((s.gpr .r0).toNat + ((s.gpr .r3).toNat + (s.gpr .r10).toNat) * 2 ^ 32 + (s.gpr .r4).toNat * 2 ^ 64)) %
          2 ^ 96 ∧ t.mem = s.mem ∧ t.gpr .r12 = s.gpr .r12 := by
  krun [sub96, h12, hU0, hU2, aU0, aU2, rU0, rU2]
  simp only [geBits_xor3, geBit_xor1, BitVec.toNat_add, BitVec.toNat_sub, geBit,
    show BitVec.toNat (0 : BitVec 32) = 0 from rfl, Nat.add_zero]
  exact sub96_nat (s.gpr .r0).isLt (s.gpr .r3).isLt (s.gpr .r4).isLt (s.gpr .r10).isLt (s.gpr .r11).isLt
    u0.isLt u2.isLt hq

/-- `refine3`'s arithmetic: the two corrections take `q̂` to `Q` (`WordStep32.quot3_val`). -/
theorem refine3_math {U D q0 T1 T2 : Nat} (hD0 : 0 < D) (hDW : 4 * D < 2 ^ 96 / 2) (hUD : U < (2 ^ 32 + 1) * D)
    (hge : min (U / D) (2 ^ 32 - 1) ≤ q0) (hle : q0 ≤ min (U / D) (2 ^ 32 - 1) + 2) (hq0 : q0 < 2 ^ 32)
    (hU : U < 2 ^ 96) (hqD : q0 * D < 2 ^ 96)
    (hT1 : T1 = (U + 2 ^ 96 - q0 * D) % 2 ^ 96)
    (hT2 : T2 = (T1 + if 2 ^ 95 ≤ T1 then D else 0) % 2 ^ 96) :
    (q0 + (if 2 ^ 95 ≤ T1 then 2 ^ 32 - 1 else 0) + (if 2 ^ 95 ≤ T2 then 2 ^ 32 - 1 else 0)) % 2 ^ 32 =
      min (U / D) (2 ^ 32 - 1) := by
  have hT1' : T1 < 2 ^ 96 := hT1 ▸ Nat.mod_lt _ (Nat.two_pow_pos 96)
  have hT2' : T2 < 2 ^ 96 := hT2 ▸ Nat.mod_lt _ (Nat.two_pow_pos 96)
  have e1 : T1 + q0 * D = U + 2 ^ 96 * (if q0 * D ≤ U then 0 else 1) := by
    rw [hT1]; split <;> omega_arith
  have e2 : T2 + 2 ^ 96 * ((T1 + if 2 ^ 95 ≤ T1 then D else 0) / 2 ^ 96) = T1 + if 2 ^ 96 / 2 ≤ T1 then D else 0 := by
    rw [hT2, show (2 : Nat) ^ 96 / 2 = 2 ^ 95 by decide]; omega_using []
  have hv := VG.Proof.Bignum.WordStep32.quot3_val (W := 2 ^ 96) (T1 := T1) (T2 := T2) hD0 hDW hUD hge hle hq0
    hT1' (by split <;> decide) e1 hT2' (by split <;> omega_arith) e2
  rw [show (2 : Nat) ^ 96 / 2 = 2 ^ 95 by decide] at hv
  have hQ : min (U / D) (2 ^ 32 - 1) < 2 ^ 32 := by omega_using []
  rw [hv]
  generalize min (U / D) (2 ^ 32 - 1) = Q at hQ ⊢
  by_cases a1 : 2 ^ 95 ≤ T1 <;> by_cases a2 : 2 ^ 95 ≤ T2 <;> simp only [a1, a2, ↓reduceIte] <;> omega_using [hQ]

theorem quot3_split : quot3 = ([.ldr .r1 .r12 sQ, .ldr .r2 .r12 sD1] : List Instr) ++
    (VG.Impl.Bignum.Arm.wideMul ++ (([.mov .r0 (.reg .r3), .mov .r10 (.reg .r4), .ldr .r1 .r12 sQ,
      .ldr .r2 .r12 sD] : List Instr) ++ (VG.Impl.Bignum.Arm.wideMul ++ sub96))) := by
  simp only [quot3, sub96, List.append_assoc]

theorem top_bit_iff {a b c : BitVec 32} :
    2 ^ 31 ≤ c.toNat ↔ 2 ^ 95 ≤ a.toNat + b.toNat * 2 ^ 32 + c.toNat * 2 ^ 64 := by
  have := a.isLt; have := b.isLt; have := c.isLt; omega_using []

theorem negOne_toNat (q : BitVec 32) (c : Prop) [Decidable c] :
    (q + if c then (-1 : BitVec 32) else 0).toNat = (q.toNat + if c then 2 ^ 32 - 1 else 0) % 2 ^ 32 := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; rw [BitVec.toNat_add, show (-1 : BitVec 32).toNat = 2 ^ 32 - 1 by decide]
  · simp only [h, ↓reduceIte]; rw [BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]

/-- The registers `refine3` changes. -/
abbrev refineRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- `refine3`: `q̂` (156), within `Q ≤ q̂ ≤ Q + 2` of `Q = min(⌊U / D⌋, 2^32 - 1)`, refined to
`Q`, for `U = (u₂, u₁, u₀)` (68, `r11`, 64) and `D = (d, d₁)` (140, 148), `U < (2^32 + 1) D`. -/
theorem refine3_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (h12 : s.gpr .r12 = B)
    {q0 u1 : Nat} (hu1 : s.gpr .r11 = BitVec.ofNat 32 u1) (hu1' : u1 < 2 ^ 32) (hQ0 : slot s.mem B sQ = q0)
    {U D : Nat} (hU : U = slot s.mem B sU2 * 2 ^ 64 + u1 * 2 ^ 32 + slot s.mem B sU0)
    (hD : D = slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1) (hD0 : 0 < D) (hUD : U < (2 ^ 32 + 1) * D)
    (hge : min (U / D) (2 ^ 32 - 1) ≤ q0) (hle : q0 ≤ min (U / D) (2 ^ 32 - 1) + 2) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, slot t.mem B sQ = min (U / D) (2 ^ 32 - 1) → Keep B w [] [sQ] s.mem t.mem → t.gpr .r12 = B →
      Rest refineRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (refine3 ++ rest)) s Q := by
  have hz := h.hdr_le
  have sl : ∀ {o : Nat}, o + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → State.addr (B + BitVec.ofNat 32 o) = off (State.addr B) o ∧
      InRegions (s.rd ++ s.wr) (off (State.addr B) o) 4 ∧ InRegions s.wr (off (State.addr B) o) 4 := fun ho =>
    ⟨h.addr (by omega_using [hz, ho]), h.read (by omega_using [hz, ho]), h.write (by omega_using [hz, ho])⟩
  obtain ⟨aQ, rQ, wQ⟩ := sl (o := sQ) (by decide)
  obtain ⟨aD, rD, -⟩ := sl (o := sD) (by decide)
  obtain ⟨aD1, rD1, -⟩ := sl (o := sD1) (by decide)
  obtain ⟨aU0, rU0, -⟩ := sl (o := sU0) (by decide)
  obtain ⟨aU2, rU2, -⟩ := sl (o := sU2) (by decide)
  have tv : ∀ {o v : Nat}, slot s.mem B o = v → s.mem.readW (off (State.addr B) o) 32 = BitVec.ofNat 32 v :=
    fun e => by rw [← e]; exact (ofNat_toNat32 _).symm
  generalize ed : slot s.mem B sD = d at hD
  generalize ed1 : slot s.mem B sD1 = d1 at hD
  have hq0 : q0 < 2 ^ 32 := hQ0 ▸ BitVec.isLt _
  have hd : d < 2 ^ 32 := ed ▸ BitVec.isLt _
  have hd1 : d1 < 2 ^ 32 := ed1 ▸ BitVec.isLt _
  have tn : ∀ {a : Nat}, a < 2 ^ 32 → (BitVec.ofNat 32 a).toNat = a := fun h => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  simp only [refine3, quot3_split, List.append_assoc]
  -- `q̂ d₁`.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r1, .r2] (Q := fun v =>
      v.gpr .r1 = BitVec.ofNat 32 q0 ∧ v.gpr .r2 = BitVec.ofNat 32 d1 ∧ v.mem = s.mem) (by
    krun [h12, aQ, aD1, rQ, rD1, tv hQ0, tv ed1]) (by decide)) fun v1 ⟨⟨i1, p1, m1⟩, k1⟩ => ?_)
  refine wp_wide fun v2 e2 P2 => ?_
  rw [i1, p1, tn hq0, tn hd1] at e2
  -- `q̂ d`.
  have q12 : v2.gpr .r12 = B := (P2.regs _ (by decide)).trans ((k1.gpr _ (by decide)).trans h12)
  have m2 : v2.mem = s.mem := P2.mem.trans m1
  have rd2 : v2.rd = s.rd := P2.rd.trans k1.rd
  have wr2 : v2.wr = s.wr := P2.wr.trans k1.wr
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r10, .r1, .r2] (Q := fun v =>
      v.gpr .r0 = v2.gpr .r3 ∧ v.gpr .r10 = v2.gpr .r4 ∧ v.gpr .r1 = BitVec.ofNat 32 q0 ∧
      v.gpr .r2 = BitVec.ofNat 32 d ∧ v.mem = s.mem) (by
    krun [q12, m2, rd2, wr2, aQ, aD, rQ, rD, tv hQ0, tv ed]) (by decide)) fun v3 ⟨⟨x3, t3, i3, p3, m3⟩, k3⟩ => ?_)
  refine wp_wide fun v4 e4 P4 => ?_
  rw [i3, p3, tn hq0, tn hd] at e4
  -- `U - q̂ D`.
  have q12' : v4.gpr .r12 = B := (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans q12)
  have m4 : v4.mem = s.mem := P4.mem.trans m3
  have rd4 : v4.rd = s.rd := P4.rd.trans (k3.rd.trans rd2)
  have wr4 : v4.wr = s.wr := P4.wr.trans (k3.wr.trans wr2)
  have x4 : v4.gpr .r0 = v2.gpr .r3 := (P4.regs _ (by decide)).trans x3
  have t4 : v4.gpr .r10 = v2.gpr .r4 := (P4.regs _ (by decide)).trans t3
  have u4 : v4.gpr .r11 = BitVec.ofNat 32 u1 :=
    (P4.regs _ (by decide)).trans ((k3.gpr _ (by decide)).trans ((P2.regs _ (by decide)).trans
      ((k1.gpr _ (by decide)).trans hu1)))
  have hqD : (v4.gpr .r0).toNat + ((v4.gpr .r3).toNat + (v4.gpr .r10).toNat) * 2 ^ 32 +
      (v4.gpr .r4).toNat * 2 ^ 64 = q0 * D := by
    rw [x4, t4, hD, Nat.mul_add, ← Nat.mul_assoc]; omega_using [e2, e4]
  have hDlt : D < 2 ^ 64 := by rw [hD]; omega_using [hd, hd1]
  have hqD' : q0 * D < 2 ^ 96 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hq0 (Nat.le_of_lt hDlt) (by omega_using [])) (by decide)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (sub96_ok q12' (u0 := BitVec.ofNat 32 (slot s.mem B sU0)) (u2 := BitVec.ofNat 32 (slot s.mem B sU2))
      (by rw [m4]; exact tv rfl) (by rw [m4]; exact tv rfl) aU0 aU2 (by rw [rd4, wr4]; exact rU0)
      (by rw [rd4, wr4]; exact rU2) (by rw [hqD]; exact hqD')) (by decide)) fun v5 ⟨⟨T5, m5, b5⟩, k5⟩ => ?_)
  rw [hqD, u4, tn hu1'] at T5
  have q12'' : v5.gpr .r12 = B := b5.trans q12'
  have m5' : v5.mem = s.mem := m5.trans m4
  have rd5 : v5.rd = s.rd := k5.rd.trans rd4
  have wr5 : v5.wr = s.wr := k5.wr.trans wr4
  -- `q̂` again, and the two corrections.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r1] (Q := fun v =>
      v.gpr .r1 = BitVec.ofNat 32 q0 ∧ v.mem = s.mem) (by
    krun [q12'', m5', rd5, wr5, aQ, rQ, tv hQ0]) (by decide)) fun v6 ⟨⟨i6, m6⟩, k6⟩ => ?_)
  have b6 : v6.gpr .r12 = B := (k6.gpr _ (by decide)).trans q12''
  have rd6 : v6.rd = s.rd := k6.rd.trans rd5
  have wr6 : v6.wr = s.wr := k6.wr.trans wr5
  have T6 : (v6.gpr .r10).toNat + (v6.gpr .r11).toNat * 2 ^ 32 + (v6.gpr .lr).toNat * 2 ^ 64 =
      (U + 2 ^ 96 - q0 * D) % 2 ^ 96 := by
    rw [k6.gpr .r10 (by decide), k6.gpr .r11 (by decide), k6.gpr .lr (by decide), T5, hU]
    congr 2
    simp only [BitVec.toNat_ofNat, slot]
    have := (s.mem.readW (off (State.addr B) sU0) 32).isLt
    have := (s.mem.readW (off (State.addr B) sU2) 32).isLt
    simp only [w32] at *
    omega_using []
  have vD : v6.mem.readW (off (State.addr B) sD) 32 = BitVec.ofNat 32 d := by rw [m6]; exact tv ed
  have vD1 : v6.mem.readW (off (State.addr B) sD1) 32 = BitVec.ofNat 32 d1 := by rw [m6]; exact tv ed1
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (fix3_ok b6 vD vD1 aD aD1 (by rw [rd6, wr6]; exact rD) (by rw [rd6, wr6]; exact rD1)) (by decide))
    fun v7 ⟨⟨i7, T7, m7, b7⟩, k7⟩ => ?_)
  have rd7 : v7.rd = s.rd := k7.rd.trans rd6
  have wr7 : v7.wr = s.wr := k7.wr.trans wr6
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r10, .r11, .lr]
    (fix3_ok (b7.trans b6) (d := BitVec.ofNat 32 d) (d1 := BitVec.ofNat 32 d1) (by rw [m7]; exact vD) (by rw [m7]; exact vD1) aD aD1 (by rw [rd7, wr7]; exact rD)
      (by rw [rd7, wr7]; exact rD1)) (by decide)) fun v8 ⟨⟨i8, T8, m8, b8⟩, k8⟩ => ?_)
  have b8' : v8.gpr .r12 = B := b8.trans (b7.trans b6)
  have wr8 : v8.wr = s.wr := k8.wr.trans wr7
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [] (Q := fun v =>
      v.mem = v8.mem.writeW (off (State.addr B) sQ) (v8.gpr .r1)) (by
    krun [b8', wr8, aQ, wQ]) (by decide)) fun v9 ⟨m9, k9⟩ => ?_)
  have hDv : (BitVec.ofNat 32 d).toNat * 2 ^ 32 + (BitVec.ofNat 32 d1).toNat = D := by rw [tn hd, tn hd1, hD]
  rw [hDv] at T7 T8
  generalize eT1 : (v6.gpr .r10).toNat + (v6.gpr .r11).toNat * 2 ^ 32 + (v6.gpr .lr).toNat * 2 ^ 64 = T1 at T6 T7
  generalize eT2 : (v7.gpr .r10).toNat + (v7.gpr .r11).toNat * 2 ^ 32 + (v7.gpr .lr).toNat * 2 ^ 64 = T2 at T7 T8
  have c1 : (2 ^ 31 ≤ (v6.gpr .lr).toNat) ↔ 2 ^ 95 ≤ T1 := by rw [← eT1]; exact top_bit_iff
  have c2 : (2 ^ 31 ≤ (v7.gpr .lr).toNat) ↔ 2 ^ 95 ≤ T2 := by rw [← eT2]; exact top_bit_iff
  have hUlt : U < 2 ^ 96 := by
    rw [hU]; have := (s.mem.readW (off (State.addr B) sU0) 32).isLt
    have := (s.mem.readW (off (State.addr B) sU2) 32).isLt; simp only [slot, w32]; omega_using [hu1']
  have key := refine3_math (T1 := T1) (T2 := T2) hD0 (by omega_using [hDlt]) hUD hge hle hq0 hUlt hqD' T6
    (by rw [T7]; simp only [c1])
  refine k v9 ?_ ?_ (by rw [k9.gpr _ (by decide), b8']) ?_
  · simp only [slot]
    rw [m9, w32_write_self, i8, i7, i6, negOne_toNat, negOne_toNat, tn hq0]
    simp only [c1, c2]
    rw [← key]; omega_using []
  · rw [m9, m8, m7, m6]; exact keep_write _ _ (by simp) (by simp only [sQ]; omega_using [])
  · exact ((((k1.mono (by decide)).trans ((Preserves.toRest P2).mono (by decide))).trans
      ((k3.mono (by decide)).trans ((Preserves.toRest P4).mono (by decide)))).trans
      (((k5.mono (by decide)).trans (k6.mono (by decide))).trans
        ((k7.mono (by decide)).trans (k8.mono (by decide))))).trans (k9.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

open VG.Proof.Bignum.WordStep32 VG.Proof.Bignum.WordTop32 in
/-- The estimate's arithmetic: for a window `Y < 2^32 M` whose top four words
are `a₁ a₂ a₃ a` (`k` words `L` below), `u₂ u₁ u₀` the top three words of
`Y 2^z` and `D = Dh 2^32 + Dl` the top two of `M 2^z`, `M 2^z < 2^(32 (k + 3))`
normalized: `u₂ ≤ Dh`, `U < (2^32 + 1) D`, the 2-by-1 estimate within 2 above
`Q = min(⌊U / D⌋, 2^32 - 1)`, and `⌊Y / M⌋ ≤ Q ≤ ⌊Y / M⌋ + 1`. -/
theorem est_math {Y M z k L a a1 a2 a3 Dh Dl u2 u1 u0 : Nat} (hz : z ≤ 31)
    (hY' : Y = (L + 2 ^ (32 * k) * a) + 2 ^ (32 * (k + 1)) * a3 +
      2 ^ (32 * (k + 1)) * 2 ^ 32 * (a2 + 2 ^ 32 * a1))
    (hL : L < 2 ^ (32 * k)) (ha : a < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hYM : Y < M * 2 ^ 32) (hMP : M * 2 ^ z < 2 ^ (32 * (k + 3)))
    (hD : Dh * 2 ^ 32 + Dl = M * 2 ^ z / 2 ^ (32 * (k + 1))) (hDn : 2 ^ 31 ≤ Dh) (hDl : Dl < 2 ^ 32)
    (hu2 : u2 = wordP a1 a2 (2 ^ z)) (hu1 : u1 = wordP a2 a3 (2 ^ z)) (hu0 : u0 = wordP a3 a (2 ^ z)) :
    u2 ≤ Dh ∧ u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 < (2 ^ 32 + 1) * (Dh * 2 ^ 32 + Dl) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) + 2 ∧
    Y / M ≤ min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤ Y / M + 1 := by
  have hP := Nat.two_pow_pos z
  have eK : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by
    rw [show 32 * (k + 1) = 32 * k + 32 by omega_using [], Nat.pow_add]
  have hL' : L + 2 ^ (32 * k) * a < 2 ^ (32 * (k + 1)) := by
    rw [eK]
    have := Nat.mul_le_mul_left (2 ^ (32 * k)) (show a + 1 ≤ 2 ^ 32 by omega_using [ha])
    rw [Nat.mul_add, Nat.mul_one] at this; omega_using [hL, this]
  -- `Y 2^z < 2^32 M 2^z < 2^(32 (k + 4))`.
  have hYP : Y * 2 ^ z < M * 2 ^ z * 2 ^ 32 := by
    rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right hYM hP
  have hY : Y = L + 2 ^ (32 * k) * a + 2 ^ (32 * k) * 2 ^ 32 * (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1) := by
    rw [hY', eK]; grind
  have hsm : a1 * 2 ^ z < 2 ^ 32 := by
    refine top_small (L := L + 2 ^ (32 * k) * a) (k := k + 1) (a2 := a2) (a3 := a3) ?_
    rw [← hY', show 32 * (k + 1 + 3) = 32 * (k + 3) + 32 by omega_using [], Nat.pow_add]
    exact Nat.lt_of_lt_of_le hYP (Nat.mul_le_mul_right _ (Nat.le_of_lt hMP))
  have e2 : u2 = a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32 := by
    rw [hu2]; exact Nat.mod_eq_of_lt (lohi_lt (by omega_using [hz]) ha2)
  have e1 : u1 = a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32 := by
    rw [hu1]; exact Nat.mod_eq_of_lt (lohi_lt (by omega_using [hz]) ha3)
  have e0 : u0 = a3 * 2 ^ z % 2 ^ 32 + a * 2 ^ z / 2 ^ 32 := by
    rw [hu0]; exact Nat.mod_eq_of_lt (lohi_lt (by omega_using [hz]) ha)
  have hU : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = Y * 2 ^ z / 2 ^ (32 * k + 32) := by
    rw [e2, e1, e0, top3_math hz hL hsm, ← hY]
    exact congrArg (Y * 2 ^ z / ·) (Nat.pow_add 2 (32 * k) 32).symm
  have hu0' : u0 < 2 ^ 32 := hu0 ▸ Nat.mod_lt _ (by decide)
  have hu1' : u1 < 2 ^ 32 := hu1 ▸ Nat.mod_lt _ (by decide)
  have hDD : M * 2 ^ z / 2 ^ (32 * k + 32) = Dh * 2 ^ 32 + Dl := by
    rw [hD, show 32 * (k + 1) = 32 * k + 32 by omega_using []]
  have hDh : (Dh * 2 ^ 32 + Dl) / 2 ^ 32 = Dh := by omega_using [hDl]
  have hUh : (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 32 = u2 * 2 ^ 32 + u1 := by omega_using [hu0']
  have q := qhat3_div (Y := Y) (M := M) (P := 2 ^ z) (K := 32 * k) hP hYM (by rw [hDD, hDh]; exact hDn)
  rw [hDD, ← hU, hDh, hUh] at q
  refine ⟨?_, q⟩
  -- `u₂ = ⌊Y 2^z / 2^(32 (k + 3))⌋ ≤ ⌊2^32 M 2^z / 2^(32 (k + 3))⌋ = Dh`.
  have h2 : u2 = (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 64 := by omega_using [hu0', hu1']
  have hd2 : Dh = M * 2 ^ z * 2 ^ 32 / 2 ^ (32 * k + 32) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * k + 32 + 64 = (32 * k + 64) + 32 by omega_using [],
      Nat.pow_add 2 (32 * k + 64) 32, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 32),
      show 32 * k + 64 = (32 * k + 32) + 32 by omega_using [], Nat.pow_add 2 (32 * k + 32) 32, ← Nat.div_div_eq_div_mul,
      hDD, hDh]
  rw [h2, hU, hd2]
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt hYP))

/-- `ctx`: `w` (16) into `r9` and its stride into `r7`, with `r8 = B`. -/
theorem kctx_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (h8 : s.gpr .r8 = B)
    (h16 : slot s.mem B 16 = w) (hw0 : 0 < w) (hw : w ≤ 1024) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Rest [.r9, .r7] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ctx ++ rest)) s Q := by
  have hz := h.hdr_le
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r9, .r7] (Q := fun v =>
      v.gpr .r9 = BitVec.ofNat 32 w ∧ v.gpr .r7 = (BitVec.ofNat 32 w + 2) <<< 2 ∧ v.mem = s.mem) (by
    krun [ctx, VG.Impl.Rsa.Arm.Keys.stride, h8, h.addr (d := 16) (by omega_using [hz]), h.read (d := 16) (by omega_using [hz]),
      show s.mem.readW (off (State.addr B) 16) 32 = BitVec.ofNat 32 w by rw [← h16]; exact (ofNat_toNat32 _).symm])
    (by decide)) fun t ⟨⟨n9, n7, mt⟩, kt⟩ => ?_)
  refine k t ⟨h.nowrap, by rw [kt.wr]; exact h.writable, h.fits, hw0, hw, ?_, by rw [kt.gpr _ (by decide)]; exact h8,
    n9⟩ kt mt
  rw [n7, stride_val hw]

/-- The registers `estimate` changes. -/
abbrev estRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

open VG.Proof.Bignum.WordTop32 in
/-- `estimate r`: `q̂` (156) with `⌊Y / M⌋ ≤ q̂ ≤ ⌊Y / M⌋ + 1`, for the window `Y < 2^32 M`
of `w / 2 + 1` words at word `j` (72, `4 j`) of `[r]`, `P = 2^z` (136), the top two words
`(d, d₁)` (140, 148) of `M 2^z`, normalized, and `v` (144) `d`'s reciprocal. -/
theorem estimate_ok {s : State} {B : BitVec 32} {Z w N r j z : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 256) (h16 : slot s.mem B 16 = w) (hdw : 3 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j)
    (hj : j + w / 2 ≤ w) {Y M : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y)
    (hYM : Y < M * 2 ^ 32) (hz : z ≤ 31) (hP : slot s.mem B sP = 2 ^ z) (hMP : M * 2 ^ z < 2 ^ (32 * (w / 2)))
    (hD : slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2)))
    (hDn : 2 ^ 31 ≤ slot s.mem B sD) (hV : slot s.mem B sV = (2 ^ 64 - 1) / slot s.mem B sD - 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t q, slot t.mem B sQ = q → Y / M ≤ q → q ≤ Y / M + 1 → q < 2 ^ 32 →
      Keep B w [] [sMk, sQ, sU0, sU2] s.mem t.mem → Ws t B Z w N → Rest estRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (estimate r ++ rest)) s Q := by
  have := h.wle
  have nw := h.nowrap
  have fr := h.arr_fit hr
  have hz' := h.hdr_le
  simp only [S] at fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain ⟨kk, hk⟩ : ∃ kk, w / 2 = kk + 3 := ⟨w / 2 - 3, by omega_using [hdw]⟩
  simp only [estimate, List.append_assoc]
  refine topPtr_ok h (r := .r10) (t := .r0) (by decide) (by decide) (by decide) (j := r) (i := 3) (by omega_using [hr, hN])
    (by omega_using [hdw]) (by decide) (by omega_using [fr]) fun u1 p1 r1 m1 h1 => ?_
  have aJ := h.addr (d := sJ) (by simp only [sJ]; omega_using [hz'])
  have rJ : InRegions (u1.rd ++ u1.wr) (off (State.addr B) sJ) 4 := h1.read (by simp only [sJ]; omega_using [hz'])
  have vJ : u1.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) := by
    rw [m1, ← hJ]; exact (ofNat_toNat32 _).symm
  generalize eX : arr w r + 4 * j + 4 * kk = X
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r10] (Q := fun v =>
      v.gpr .r10 = B + BitVec.ofNat 32 X ∧ v.mem = u1.mem) (by
    krun [h1.r8, aJ, rJ, vJ, p1]
    rw [add_ofNat_assoc, ← eX]; congr 2; omega_using [hk]) (by decide)) fun u2 ⟨⟨p2, m2⟩, k2⟩ => ?_)
  have h2 : Ws u2 B Z w N := h1.rest k2
  have mu2 : u2.mem = s.mem := m2.trans m1
  have wr2 : u2.wr = s.wr := k2.wr.trans r1.wr
  have hXZ : X + 16 ≤ Z := by omega_using [hj, fr, hk, eX]
  refine topWords_ok h2 hXZ p2 fun t3 m3 q11 q12 R3 => ?_
  rw [mu2] at m3 q11
  simp only [hP] at m3 q11
  generalize ea : w32 s.mem (State.addr B) X = a at m3 q11
  generalize ea3 : w32 s.mem (State.addr B) (X + 4) = a3 at m3 q11
  generalize ea2 : w32 s.mem (State.addr B) (X + 8) = a2 at m3 q11
  generalize ea1 : w32 s.mem (State.addr B) (X + 12) = a1 at m3
  have ha : a < 2 ^ 32 := ea ▸ BitVec.isLt _
  have ha3 : a3 < 2 ^ 32 := ea3 ▸ BitVec.isLt _
  have ha2 : a2 < 2 ^ 32 := ea2 ▸ BitVec.isLt _
  have hYe : Y = (val32 s.mem (State.addr B) (arr w r + 4 * j) kk + 2 ^ (32 * kk) * a) +
      2 ^ (32 * (kk + 1)) * a3 + 2 ^ (32 * (kk + 1)) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
    rw [← hY, hk, show kk + 3 + 1 = (kk + 1) + 3 from rfl, val32_top3, val32_succ, ← ea, ← ea3, ← ea2, ← ea1,
      show arr w r + 4 * j + 4 * kk = X from eX, show arr w r + 4 * j + 4 * (kk + 1) = X + 4 by omega_using [eX],
      show arr w r + 4 * j + 4 * (kk + 1 + 1) = X + 8 by omega_using [eX],
      show arr w r + 4 * j + 4 * (kk + 1 + 2) = X + 12 by omega_using [eX]]
  have E := est_math (u2 := wordP a1 a2 (2 ^ z)) (u1 := wordP a2 a3 (2 ^ z)) (u0 := wordP a3 a (2 ^ z)) hz hYe
    (val32_lt _ _ _ _) ha ha2 ha3 hYM (hk ▸ hMP) (by rw [hD, hk, show kk + 3 - 2 = kk + 1 by omega_using []]) hDn (BitVec.isLt _) rfl rfl rfl
  obtain ⟨Eu, EUD, Ege, Ele, Elo, Ehi⟩ := E
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega_using [nw]
  -- Header words other than `u₀` and `u₂` after `topWords`.
  have s3 : ∀ {o : Nat}, o + 4 ≤ 160 → (o + 4 ≤ sU0 ∨ sU0 + 4 ≤ o) → (o + 4 ≤ sU2 ∨ sU2 + 4 ≤ o) →
      slot t3.mem B o = slot s.mem B o := fun ho h0 h2 => by
    simp only [slot]
    rw [m3, w32_write_ne hA (by simp only [sU2]; omega_using [hz']) (by omega_using [hz', ho]) h2,
      w32_write_ne hA (by simp only [sU0]; omega_using [hz']) (by omega_using [hz', ho]) h0]
  have tw : ∀ {x : Nat}, (BitVec.ofNat 32 (x % 2 ^ 32)).toNat = x % 2 ^ 32 := fun {x} => by
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
  have sU2v : slot t3.mem B sU2 = wordP a1 a2 (2 ^ z) := by simp only [slot]; rw [m3, w32_write_self, tw]
  have sU0v : slot t3.mem B sU0 = wordP a3 a (2 ^ z) := by
    simp only [slot]; rw [m3, w32_write_ne hA (by simp only [sU2]; omega_using [hz']) (by simp only [sU0]; omega_using [hz']) (by decide),
      w32_write_self, tw]
  have wr3 : t3.wr = s.wr := R3.wr.trans wr2
  have hDl : slot s.mem B sD < 2 ^ 32 := BitVec.isLt _
  refine quot_ok (h.m.of wr3) q12 q11 (s3 (by decide) (by decide) (by decide)) sU2v
    (by rw [s3 (by decide) (by decide) (by decide)]; exact hV) hDn hDl Eu (Nat.mod_lt _ (by decide))
    fun t4 hq4 K4 q11' q12' R4 => ?_
  rw [qhat_min Eu (Nat.mod_lt _ (by decide)) (by omega_using [hDn])] at hq4
  have s4 : ∀ {o : Nat}, o + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → (∀ d ∈ [sMk, sQ], o + 4 ≤ d ∨ d + 4 ≤ o) →
      slot t4.mem B o = slot t3.mem B o := fun ho hd => K4.slot ho hd
  have wr4 : t4.wr = s.wr := R4.wr.trans wr3
  refine refine3_ok (h.m.of wr4) q12' (u1 := wordP a2 a3 (2 ^ z)) (q11'.trans q11) (Nat.mod_lt _ (by decide)) hq4
    (U := wordP a1 a2 (2 ^ z) * 2 ^ 64 + wordP a2 a3 (2 ^ z) * 2 ^ 32 + wordP a3 a (2 ^ z))
    (D := slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1)
    (by rw [s4 (by decide) (by decide), s4 (by decide) (by decide), sU2v, sU0v])
    (by rw [s4 (by decide) (by decide), s4 (by decide) (by decide), s3 (by decide) (by decide) (by decide),
      s3 (by decide) (by decide) (by decide)])
    (by omega_using [hDn]) EUD Ege Ele fun t5 hq5 K5 q12'' R5 => ?_
  have K45 : Keep B w [] [sMk, sQ, sU0, sU2] s.mem t5.mem := by
    have K3 : Keep B w [] [sMk, sQ, sU0, sU2] s.mem t3.mem := by
      rw [m3]
      exact (keep_write _ _ (by simp) (by simp only [sU0]; omega_using [])).trans
        (keep_write _ _ (by simp) (by simp only [sU2]; omega_using []))
    exact (K3.trans K4.mono).trans K5.mono
  rw [List.singleton_append]
  refine wp_mov (op2_reg _ _) fun t6 u6 => ?_
  have h86 : t6.gpr .r8 = B := by rw [u6.gpr, q12'']
  have wr6 : t6.wr = s.wr := u6.wr.trans (R5.wr.trans wr4)
  have h166 : slot t6.mem B 16 = w := by
    rw [u6.mem, K45.slot (by decide) (by decide), h16]
  refine kctx_ok (h.m.of wr6) h86 h166 h.wpos this fun t7 h7 R7 m7 => ?_
  refine k t7 _ (by rw [m7, u6.mem, hq5]) Elo Ehi (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))
    (by rw [m7, u6.mem]; exact K45) h7 ?_
  have K : Rest (estRegs ++ [.r7, .r8, .r9]) s t7 :=
    ((((r1.mono (by decide)).trans (k2.mono (by decide))).trans ((R3.mono (by decide)).trans (R4.mono (by decide)))).trans
      (((R5.mono (by decide)).trans (u6.rest (by decide))).trans (R7.mono (by decide))))
  refine ⟨fun r hr => ?_, K.rd, K.wr, K.sp⟩
  by_cases e : r ∈ [Reg.r7, .r8, .r9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with rfl | rfl | rfl
    · rw [h7.r7, h.r7]
    · rw [h7.r8, h.r8]
    · rw [h7.r9, h.r9]
  · exact K.gpr r fun hm => (List.mem_append.mp hm).elim hr e

end VG.Proof.Rsa.Arm.KeyDiv
