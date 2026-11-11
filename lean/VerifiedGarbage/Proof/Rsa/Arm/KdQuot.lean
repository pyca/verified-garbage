module

public import VerifiedGarbage.Proof.Rsa.Arm.KdTop
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Framework.Offset

/-! # The 2-by-1 estimate of the key checks' division on ARMv7 (`KeyDiv.quot`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem readW_slot_ne (m : Mem) (A : Addr) (o d : Nat) (v : BitVec 32) (hsep : d + 4 ≤ o ∨ o + 4 ≤ d)
    (ho : o < 2 ^ 32) (hd : d < 2 ^ 32) :
    (m.writeW (off A o) v).readW (off A d) 32 = m.readW (off A d) 32 :=
  VG.Mem.readW_writeW_sep (VG.Offset.sep A hsep (by omega) (by omega)) (by decide)

/-- The mask of `u₂ = d`, from `d - u₂ ≥ 1`'s carry. -/
abbrev eqMask (u2 d : Nat) : BitVec 32 := if u2 = d then -1 else 0

theorem eqMask_eq {u2 d : Nat} (hu : u2 ≤ d) (hd : d < 2 ^ 32) :
    (0 + 0 + bif decide ((1 : BitVec 32).toNat ≤ (BitVec.ofNat 32 d - BitVec.ofNat 32 u2).toNat) then 1 else 0) -
      1 = eqMask u2 d := by
  have e : (BitVec.ofNat 32 d - BitVec.ofNat 32 u2).toNat = d - u2 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e, show (1 : BitVec 32).toNat = 1 from rfl]
  by_cases h : u2 = d
  · subst h; simp only [Nat.sub_self, eqMask, ite_true]; decide
  · have : 1 ≤ d - u2 := by omega
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
  have hd0 : 0 < d := by omega
  have hV : (2 ^ 64 - 1) / d = (2 ^ 64 - 1) / d - 2 ^ 32 + 2 ^ 32 := by
    have : 2 ^ 32 ≤ (2 ^ 64 - 1) / d := by rw [Nat.le_div_iff_mul_le hd0]; omega
    omega
  generalize eV : (2 ^ 64 - 1) / d = V at hV hP
  generalize ePP : V * u2 + u1 = PP
  have ePP' : PP = lo.toNat + hi.toNat * 2 ^ 32 + u2 * 2 ^ 32 + u1 := by
    have e : V * u2 = (V - 2 ^ 32) * u2 + 2 ^ 32 * u2 := by rw [← Nat.add_mul, ← hV]
    rw [← ePP, e, hP]; rw [Nat.mul_comm u2 (V - 2 ^ 32), Nat.mul_comm (2 ^ 32) u2]
  have eu2 : (BitVec.ofNat 32 u2).toNat = u2 := by rw [BitVec.toNat_ofNat]; omega
  have eu1 : (BitVec.ofNat 32 u1).toNat = u1 := by rw [BitVec.toNat_ofNat]; omega
  have ed : (BitVec.ofNat 32 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega
  have hlo := lo.isLt
  have hhi := hi.isLt
  rw [eu1, ed]
  generalize eQ : (hi + BitVec.ofNat 32 u2 + bif decide (2 ^ 32 ≤ lo.toNat + u1) then 1 else 0) + 1 = Q
  have hQ : Q.toNat = (PP / 2 ^ 32 + 1) % 2 ^ 32 := by
    rw [← eQ, ePP']
    simp only [BitVec.toNat_add, bit_toNat, eu2, show (1 : BitVec 32).toNat = 1 from rfl]
    split <;> rename_i hc <;> simp only [decide_eq_true_eq] at hc <;> omega
  have hq0 : (lo + BitVec.ofNat 32 u1).toNat = PP % 2 ^ 32 := by
    rw [BitVec.toNat_add, eu1, ePP']; omega
  generalize er : BitVec.ofNat 32 u1 - Q * BitVec.ofNat 32 d = r
  have hr : r.toNat = (u1 + (2 ^ 32 - Q.toNat * d % 2 ^ 32)) % 2 ^ 32 := by
    rw [← er, BitVec.toNat_sub, BitVec.toNat_mul, eu1, ed]; omega
  rw [hq0, bitMask_eq]
  generalize ec : decide (r.toNat ≤ PP % 2 ^ 32) = c
  have neg1 : (-1 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide
  have hm : ∀ x : BitVec 32, (x + bif c then 0 else -1).toNat =
      (x.toNat + if PP % 2 ^ 32 < r.toNat then 2 ^ 32 - 1 else 0) % 2 ^ 32 := fun x => by
    cases c
    · have hc : PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_false_iff_not] at ec; omega
      simp only [hc, ↓reduceIte, Bool.cond_false]; rw [BitVec.toNat_add, neg1]
    · have hc : ¬ PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_true_eq] at ec; omega
      simp only [hc, ↓reduceIte, Bool.cond_true]
      rw [BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]
  have hm2 : (r + ((bif c then (0 : BitVec 32) else -1) &&& BitVec.ofNat 32 d)).toNat =
      (r.toNat + if PP % 2 ^ 32 < r.toNat then d else 0) % 2 ^ 32 := by
    cases c
    · have hc : PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_false_iff_not] at ec; omega
      simp only [hc, ↓reduceIte, Bool.cond_false]
      rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.toNat_add, ed]
    · have hc : ¬ PP % 2 ^ 32 < r.toNat := by
        simp only [decide_eq_true_eq] at ec; omega
      simp only [hc, ↓reduceIte, Bool.cond_true]
      rw [BitVec.toNat_add, BitVec.toNat_and, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_and]
  have key := VG.Proof.Bignum.WordStep32.mg_quot (d := d) (u := u2) (a := u1) (V := V) (P := PP)
    (Q := Q.toNat) (r := r.toNat) (Q1 := (Q + bif c then 0 else -1).toNat)
    (r1 := (r + ((bif c then (0 : BitVec 32) else -1) &&& BitVec.ofNat 32 d)).toNat) hd2 hd1 hu hu1 eV.symm
    (by rw [← ePP, Nat.mul_comm]) hQ hr (hm Q) hm2
  apply BitVec.eq_of_toNat_eq
  have : (u2 * 2 ^ 32 + u1) / d < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hd0]; omega
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
  · have h2 : d - 1 < r1 := by omega
    simp only [hr, h2, ↓reduceIte]; omega
  · have h2 : ¬ d - 1 < r1 := by omega
    simp only [hr, h2, ↓reduceIte]; omega

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
    ⟨h.addr (by omega), h.read (by omega), h.write (by omega)⟩
  obtain ⟨aD, rD, -⟩ := sl (o := sD) (by decide)
  obtain ⟨aU2, rU2, -⟩ := sl (o := sU2) (by decide)
  obtain ⟨aV, rV, -⟩ := sl (o := sV) (by decide)
  obtain ⟨aMk, rMk, wMk⟩ := sl (o := sMk) (by decide)
  obtain ⟨aQ, -, wQ⟩ := sl (o := sQ) (by decide)
  have tv : ∀ {o v : Nat}, slot s.mem B o = v → s.mem.readW (off (State.addr B) o) 32 = BitVec.ofNat 32 v :=
    fun e => by rw [← e]; exact (ofNat_toNat32 _).symm
  generalize ev : (2 ^ 64 - 1) / d - 2 ^ 32 = v at hV
  simp only [quot, List.append_assoc]
  have hu2' : u2 < 2 ^ 32 := by omega
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
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (show v < 2 ^ 32 from hV ▸ BitVec.isLt _)]
      simp only [e, ite_false, eqMask]
      rw [or_zero32]
      rw [← ev] at e2'
      exact quot_expr hd1 hd2 (by omega) hu1' e2') (by decide)) fun v3 ⟨m3, k3⟩ => ?_)
  have ht : (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) < 2 ^ 32 := by
    split
    · omega
    · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  refine k v3 ?_ ?_ ?_ ?_ ?_
  · simp only [slot]; rw [m3, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  · rw [m3, qm]
    exact (keep_write _ _ (by simp) (by simp only [sMk]; omega)).trans (keep_write _ _ (by simp) (by simp only [sQ]; omega))
  · rw [k3.gpr _ (by decide), P2.regs _ (by decide), k1.gpr _ (by decide)]
  · rw [k3.gpr _ (by decide), q12]
  · exact ((k1.mono (by decide)).trans ((Preserves.toRest P2).mono (by decide))).trans (k3.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv
