module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Prep
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNafWide
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Impl.Weierstrass.AArch64.PubNafWide
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 PubNaf
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
theorem word_toNat (k j : Nat) :
 (BitVec.ofInt 64 (FastNaf7.digit k j)).toNat =
 if FastNaf7.negative k j then 2^64-FastNaf7.magnitude k j else FastNaf7.magnitude k j := by
 simpa only [FastNaf.digit,FastNaf.negative,FastNaf.magnitude,ite_true] using fastWord_toNat 7 k j

theorem sign_toNat (k j : Nat) :
 (0#64-(BitVec.ofInt 64 (FastNaf7.digit k j)>>>63)).toNat =
 if FastNaf7.negative k j then 2^64-1 else 0 := by
 simpa only [FastNaf.digit,FastNaf.negative,ite_true] using fastSign_toNat 7 k j

/-- The digit of the scalar's low word `x5`, into `x2`. -/
theorem chooseDigit_ok {n : Nat} (hR : Regs n) (s : State) (h0 : s.gpr (cst n 0) = 127)
    (h1 : s.gpr (cst n 1) = 64) (h3 : s.gpr (cst n 3) = 1) :
    WP isa (chooseDigit n) s fun t => t.gpr .x2 = fastRaw7 (s.gpr .x5) ∧ Keeps [.x1, .x2, .x3] s t := by
  obtain ⟨a1, a2, a3, -, -⟩ := hR.cst_ne (i := 1) (by decide)
  rw [chooseDigit]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, h3, Option.some.injEq,
    exists_eq_left']
  by_cases h : s.gpr .x5 &&& 1 = 0
  · refine WP.ite false ?_ (by intro h; cases h) (fun _ => ?_)
    · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, Size.bits]
      simpa only [Option.some.injEq, bne_eq_false_iff_eq] using h
    refine WP.mono (movz0_ok _ .x2) fun t ⟨ht, kt⟩ => ?_
    refine ⟨by rw [ht, fastRaw7, ite_eq_left h], ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩
    intro r hr
    have hr' : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by simpa using hr
    rw [kt.gpr r (by simpa using hr'.2.1)]
    simp only [RegUpd.gpr_write, hr'.1, ite_false]
  · refine WP.ite true ?_ (fun _ => ?_) (by intro h; cases h)
    · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, Size.bits]
      simpa only [Option.some.injEq, bne_iff_ne] using h
    obtain ⟨b1, -, -, -, -⟩ := hR.cst_ne (i := 0) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', fastRaw7, h, ite_false,
      reduceCtorEq, ite_true, b1, a1, a2, h0, h1, show 1 < Size.x.bits from by decide]
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The scalar less the digit, shifted right by one bit: the next residual. -/
theorem subtractShift_ok {n : Nat} (hR : Regs n) (s : State) (k j : Nat)
    (hz : s.gpr (cst n 2) = 0) (h2 : s.gpr .x2 = BitVec.ofInt 64 (FastNaf7.digit k j))
    (hv : regsVal s (limbs n) = FastNaf7.residual k j) (hb : FastNaf7.residual k j ≤ 2 ^ (64 * n)) :
    WP isa (.block (subtractShift n)) s fun t =>
      regsVal t (limbs n) = FastNaf7.residual k (j + 1) ∧ Keeps (.x3 :: limbs n) s t := by
  have hl := limbs_eq hR
  have hlen := limbs_length hR
  generalize hrest : (limbs n).drop 1 = rest at hl
  have hnd : (limbs n).Nodup := (List.nodup_append.mp hR.nodup).1
  have hav : ∀ r ∈ limbs n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x16, .x17, .x19, .x20] :=
    fun r hr => hR.avoid r (List.mem_append_left _ hr)
  rw [hl] at hnd hav hv hlen
  have hrl : rest.length = n := by simp only [List.length_cons] at hlen; omega_arith
  have h5 : Reg.x5 ∉ rest := (List.nodup_cons.mp hnd).1
  have h3 : Reg.x3 ∉ rest := fun h => hav .x3 (List.mem_cons_of_mem _ h) (by simp)
  have h2r : Reg.x2 ∉ rest := fun h => hav .x2 (List.mem_cons_of_mem _ h) (by simp)
  obtain ⟨-, -, z3, -, -⟩ := hR.cst_ne (i := 2) (by decide)
  rw [subtractShift, hl, List.drop_one, List.tail_cons,
    show ([.lsr .x .x3 .x2 63, .sub .x .x3 (cst n 2) .x3, .subs .x .x5 .x5 .x2] : List Instr) ++
      rest.map (fun r => .sbcs .x r r .x3) ++ shrChain (.x5 :: rest) =
      [.lsr .x .x3 .x2 63] ++ ([.sub .x .x3 (cst n 2) .x3] ++ ([if true then .subs .x .x5 .x5 .x2 else
        .sbcs .x .x5 .x5 .x2] ++ (rest.map (fun r => .sbcs .x r r .x3) ++ shrChain (.x5 :: rest)))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (lsr_ok s (d := .x3) (n := .x2) (by decide : 63 < 64)) fun a ⟨da, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subR_ok a .x3 (cst n 2) .x3) fun b ⟨db, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok b .x5 .x5 .x2 true (c := true) rfl) fun c ⟨dc, cc, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sbcs_ok rest c (List.nodup_cons.mp hnd).2 h3) fun d ⟨ed, kd⟩ => ?_
  refine WP.mono (shr_ok (.x5 :: rest) d hnd) fun t ⟨et, kt⟩ => ⟨?_, ?_⟩
  · -- The values.
    have b2 : b.gpr .x2 = s.gpr .x2 := by rw [kb.gpr _ (by decide), ka.gpr _ (by decide)]
    have b5 : b.gpr .x5 = s.gpr .x5 := by rw [kb.gpr _ (by decide), ka.gpr _ (by decide)]
    have b3 : b.gpr .x3 = 0#64 - (BitVec.ofInt 64 (FastNaf7.digit k j) >>> 63) := by
      rw [db, ka.gpr _ (Ne.symm z3 |> fun h => by simpa using h.symm), hz, da, h2]
      rfl
    have c3 : c.gpr .x3 = b.gpr .x3 := kc.gpr _ (by decide)
    have cr : regsVal c rest = regsVal s rest := regsVal_congr fun q hq => by
      rw [kc.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h5 hq),
        kb.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h3 hq),
        ka.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h3 hq)]
    have d5 : d.gpr .x5 = c.gpr .x5 := kd.gpr _ h5
    have hbor := sub_borrow (b.gpr .x5) (b.gpr .x2) true
    rw [← dc, ← cc, b2, b5, h2, word_toNat] at hbor
    rw [c3, b3, cr, hrl, sign_toNat] at ed
    have hlt := regsVal_lt d (.x5 :: rest)
    rw [List.length_cons, hrl, show 64 * (n + 1) = 64 * n + 64 by omega_arith, Nat.pow_add] at hlt
    simp only [regsVal] at hv hlt et ⊢
    rw [et, d5]
    rw [d5] at hlt
    have hr := FastNaf7.recurrence k j
    have hm := FastNaf7.magnitude_le k j
    have hnext := FastNaf7.residual_boundB (B := 64 * n) (k := FastNaf7.residual k j) (j := 1) hb (by
      have := hR.pos; omega_arith)
    rw [show FastNaf7.residual (FastNaf7.residual k j) 1 = FastNaf7.residual k (j + 1) from rfl] at hnext
    have hP : 2 ^ (64 * n - 1) * 2 = 2 ^ (64 * n) := by
      rw [← Nat.pow_succ]; congr 1; have := hR.pos; omega_arith
    have ho := rep_ones n
    -- Name the numbers.
    generalize (c.gpr .x5).toNat = A at hbor hlt ⊢
    generalize (s.gpr .x5).toNat = X at hbor hv
    generalize regsVal s rest = Rs at ed hv
    generalize regsVal d rest = Rd at ed hlt ⊢
    generalize FastNaf7.residual k j = r at hr hv hb
    generalize FastNaf7.residual k (j + 1) = r' at hr hnext ⊢
    generalize FastNaf7.magnitude k j = mag at hr hm hbor ed
    generalize 2 ^ (64 * n - 1) = P' at hnext hP
    generalize 2 ^ (64 * n) = P at ed hlt hb hP ho
    revert hbor ed hr ho
    cases FastNaf7.negative k j <;> cases c.c <;> cases d.c <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, rep_zero, Bool.not_true, Bool.not_false,
        Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega_arith
  · exact ((((ka.mono (by sub_regs)).trans (kb.mono (by sub_regs))).trans (kc.mono (by sub_regs))).trans
      (kd.mono (by sub_regs))).trans (kt.mono (by sub_regs))


end VG.Proof.Weierstrass.AArch64.PubNafWide
