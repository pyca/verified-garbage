module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# The public NAF's recoding, for any word count

`PubNaf.prep` writes the `64 n + 1` signed digits `Naf5.byte k j` of the
scalar `k` of `n` words (`prep_ok`): the scalar in the registers `limbs n`
(`n` words and a top word), less each digit and shifted right by one bit,
through the borrow chain `sbcs_ok` and the shift `shr_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The constants' registers. -/
def csts (n : Nat) : List Reg := [cst n 0, cst n 1, cst n 2, cst n 3]

/-- What the recoding needs of its registers, for `1 ≤ n ≤ 9` (`regs_ok9`). -/
structure Regs (n : Nat) : Prop where
  nodup : (limbs n ++ csts n).Nodup
  head : low n = .x5 :: (low n).tail
  avoid : ∀ r ∈ limbs n ++ csts n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x16, .x17, .x19, .x20]
  len : (low n).length = n
  pos : 1 ≤ n
  le : n ≤ 9

theorem regs_ok9 : ∀ n, 1 ≤ n → n ≤ 9 → Regs n := by
  have h : ∀ n < 10, 1 ≤ n → ((limbs n ++ csts n).Nodup ∧ low n = .x5 :: (low n).tail ∧
      (∀ r ∈ limbs n ++ csts n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x16, .x17, .x19, .x20]) ∧
      (low n).length = n) := by decide
  intro n h1 h6
  obtain ⟨a, b, c, d⟩ := h n (by omega_arith) h1
  exact ⟨a, b, c, d, h1, h6⟩

/-- The original six-word interface, retained for existing callers. -/
theorem regs_ok (n : Nat) (h1 : 1 ≤ n) (h6 : n ≤ 6) : Regs n :=
  regs_ok9 n h1 (by omega_arith)

/-- Registers the recoding writes. -/
def clobs (n : Nat) : List Reg := [.x1, .x2, .x3, .x19, .x20] ++ limbs n ++ csts n

/-! ## Single instructions -/

theorem movzW_ok (s : State) (d : Reg) (v : BitVec 16) :
    WP isa (.block [.movz .x d v 0]) s fun t => t.gpr d = v.setWidth 64 ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [Nat.mul_zero, BitVec.shiftLeft_zero, Size.bits, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem subR_ok (s : State) (d a b : Reg) :
    WP isa (.block [.sub .x d a b]) s fun t => t.gpr d = s.gpr a - s.gpr b ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-! ## The borrow chain and the shift -/

/-- The word `w` repeated `L` times, as a number. -/
def rep (w : Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => w + 2 ^ 64 * rep w L

theorem rep_zero : ∀ L, rep 0 L = 0
  | 0 => rfl
  | L + 1 => by rw [rep, rep_zero L]

theorem rep_ones : ∀ L, rep (2 ^ 64 - 1) L + 1 = 2 ^ (64 * L)
  | 0 => rfl
  | L + 1 => by
    rw [rep, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (64 * L)), ← rep_ones L]
    omega_arith

/-- `rs -= x3 + !c`, word by word with `sbcs`. -/
theorem sbcs_ok : ∀ (rs : List Reg) (s : State), rs.Nodup → .x3 ∉ rs →
    WP isa (.block (rs.map fun r => .sbcs .x r r .x3)) s fun t =>
      regsVal t rs + rep (s.gpr .x3).toNat rs.length + (!s.c).toNat =
        regsVal s rs + 2 ^ (64 * rs.length) * (!t.c).toNat ∧ Keeps rs s t
  | [], s, _, _ => WP.block_nil ⟨by simp [regsVal, rep], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | r :: rs, s, hd, h3 => by
    have hr3 : r ≠ .x3 := fun h => h3 (h ▸ List.mem_cons_self ..)
    have hrs : r ∉ rs := (List.nodup_cons.mp hd).1
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (subc_ok s r r .x3 false (c := s.c) rfl) fun a ⟨da, ca, ka⟩ => ?_
    refine WP.mono (sbcs_ok rs a (List.nodup_cons.mp hd).2 (fun h => h3 (List.mem_cons_of_mem _ h)))
      fun t ⟨et, kt⟩ => ?_
    have a3 : a.gpr .x3 = s.gpr .x3 := ka.gpr _ (by simpa using hr3.symm)
    have tr : t.gpr r = a.gpr r := kt.gpr r hrs
    have ar : regsVal a rs = regsVal s rs :=
      regsVal_congr fun q hq => ka.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact hrs hq)
    have hb := sub_borrow (s.gpr r) (s.gpr .x3) s.c
    rw [← da, ← ca] at hb
    rw [a3, ar] at et
    refine ⟨?_, (ka.mono (by sub_regs)).trans (kt.mono (by sub_regs))⟩
    rw [regsVal, regsVal, List.length_cons, rep, tr, show 64 * (rs.length + 1) = 64 * rs.length + 64 by omega_arith,
      Nat.pow_add]
    generalize 2 ^ (64 * rs.length) = P at et ⊢
    cases ht : t.c <;> simp only [ht, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
      Nat.mul_one, Nat.mul_zero, Nat.add_zero] at et ⊢ <;> omega_arith

/-- `rs >>= 1`. -/
theorem shr_ok : ∀ (rs : List Reg) (s : State), rs.Nodup →
    WP isa (.block (shrChain rs)) s fun t => regsVal t rs = regsVal s rs / 2 ∧ Keeps rs s t
  | [], s, _ => WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [r], s, _ => by
    refine WP.mono (lsr_ok s (d := r) (n := r) (by decide : 1 < 64)) fun t ⟨dt, kt⟩ => ⟨?_, kt⟩
    simp only [regsVal, dt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega_arith
  | r :: r' :: rs, s, hd => by
    have hrr : r ∉ r' :: rs := (List.nodup_cons.mp hd).1
    rw [shrChain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (extr_ok s (d := r) (hi := r') (lo := r) (by decide : 1 < 64)) fun a ⟨da, ka⟩ => ?_
    refine WP.mono (shr_ok (r' :: rs) a (List.nodup_cons.mp hd).2) fun t ⟨et, kt⟩ => ?_
    have tr : t.gpr r = a.gpr r := kt.gpr r hrr
    have ar : regsVal a (r' :: rs) = regsVal s (r' :: rs) :=
      regsVal_congr fun q hq => ka.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact hrr hq)
    rw [ar] at et
    refine ⟨?_, (ka.mono (by sub_regs)).trans (kt.mono (by sub_regs))⟩
    have extr (hi lo : BitVec 64) : ((hi ++ lo).extractLsb' 1 64).toNat = lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
      rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
        Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      have := hi.isLt; have := lo.isLt
      omega_arith
    have e2 : regsVal t (r :: r' :: rs) = (a.gpr r).toNat + 2 ^ 64 * regsVal t (r' :: rs) := by
      rw [regsVal, tr]
    rw [e2, et, da, extr]
    simp only [regsVal] at ⊢
    omega_arith

/-! ## One digit -/

theorem Regs.cst_ne {n : Nat} (hR : Regs n) {i : Nat} (hi : i < 4) :
    cst n i ≠ .x1 ∧ cst n i ≠ .x2 ∧ cst n i ≠ .x3 ∧ cst n i ≠ .x19 ∧ cst n i ≠ .x20 := by
  have h := hR.avoid (cst n i) (List.mem_append_right _ (by
    simp only [csts, List.mem_cons, List.not_mem_nil, or_false]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp))
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- The digit of the scalar's low word `x5`, into `x2`. -/
theorem chooseDigit_ok {n : Nat} (hR : Regs n) (s : State) (h0 : s.gpr (cst n 0) = 31)
    (h1 : s.gpr (cst n 1) = 16) (h3 : s.gpr (cst n 3) = 1) :
    WP isa (chooseDigit n) s fun t => t.gpr .x2 = nafRaw (s.gpr .x5) ∧ Keeps [.x1, .x2, .x3] s t := by
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
    refine ⟨by rw [ht, nafRaw, ite_eq_left h], ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩
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
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', nafRaw, h, ite_false,
      reduceCtorEq, ite_true, b1, a1, a2, h0, h1, show 1 < Size.x.bits from by decide]
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem limbs_eq {n : Nat} (hR : Regs n) : limbs n = .x5 :: (limbs n).drop 1 := by
  rw [limbs, hR.head]; rfl

theorem limbs_length {n : Nat} (hR : Regs n) : (limbs n).length = n + 1 := by
  rw [limbs, List.length_append, hR.len]; rfl

/-- The scalar less the digit, shifted right by one bit: the next residual. -/
theorem subtractShift_ok {n : Nat} (hR : Regs n) (s : State) (k j : Nat)
    (hz : s.gpr (cst n 2) = 0) (h2 : s.gpr .x2 = BitVec.ofInt 64 (Naf5.digit k j))
    (hv : regsVal s (limbs n) = Naf5.residual k j) (hb : Naf5.residual k j ≤ 2 ^ (64 * n)) :
    WP isa (.block (subtractShift n)) s fun t =>
      regsVal t (limbs n) = Naf5.residual k (j + 1) ∧ Keeps (.x3 :: limbs n) s t := by
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
    have b3 : b.gpr .x3 = 0#64 - (BitVec.ofInt 64 (Naf5.digit k j) >>> 63) := by
      rw [db, ka.gpr _ (Ne.symm z3 |> fun h => by simpa using h.symm), hz, da, h2]
      rfl
    have c3 : c.gpr .x3 = b.gpr .x3 := kc.gpr _ (by decide)
    have cr : regsVal c rest = regsVal s rest := regsVal_congr fun q hq => by
      rw [kc.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h5 hq),
        kb.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h3 hq),
        ka.gpr q (by simp only [List.mem_singleton]; rintro rfl; exact h3 hq)]
    have d5 : d.gpr .x5 = c.gpr .x5 := kd.gpr _ h5
    have hbor := sub_borrow (b.gpr .x5) (b.gpr .x2) true
    rw [← dc, ← cc, b2, b5, h2, nafWord_toNat] at hbor
    rw [c3, b3, cr, hrl, nafSign_toNat] at ed
    have hlt := regsVal_lt d (.x5 :: rest)
    rw [List.length_cons, hrl, show 64 * (n + 1) = 64 * n + 64 by omega_arith, Nat.pow_add] at hlt
    simp only [regsVal] at hv hlt et ⊢
    rw [et, d5]
    rw [d5] at hlt
    have hr := Naf5.recurrence k j
    have hm := Naf5.magnitude_le k j
    have hnext := Naf5.residual_boundB (B := 64 * n) (k := Naf5.residual k j) (j := 1) hb (by
      have := hR.pos; omega_arith)
    rw [show Naf5.residual (Naf5.residual k j) 1 = Naf5.residual k (j + 1) from rfl] at hnext
    have hP : 2 ^ (64 * n - 1) * 2 = 2 ^ (64 * n) := by
      rw [← Nat.pow_succ]; congr 1; have := hR.pos; omega_arith
    have ho := rep_ones n
    -- Name the numbers.
    generalize (c.gpr .x5).toNat = A at hbor hlt ⊢
    generalize (s.gpr .x5).toNat = X at hbor hv
    generalize regsVal s rest = Rs at ed hv
    generalize regsVal d rest = Rd at ed hlt ⊢
    generalize Naf5.residual k j = r at hr hv hb
    generalize Naf5.residual k (j + 1) = r' at hr hnext ⊢
    generalize Naf5.magnitude k j = mag at hr hm hbor ed
    generalize 2 ^ (64 * n - 1) = P' at hnext hP
    generalize 2 ^ (64 * n) = P at ed hlt hb hP ho
    revert hbor ed hr ho
    cases Naf5.negative k j <;> cases c.c <;> cases d.c <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, rep_zero, Bool.not_true, Bool.not_false,
        Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega_arith
  · exact ((((ka.mono (by sub_regs)).trans (kb.mono (by sub_regs))).trans (kc.mono (by sub_regs))).trans
      (kd.mono (by sub_regs))).trans (kt.mono (by sub_regs))

/-! ## The loop -/

/-- The recoding after `j` digits: the residual in `limbs n`, the constants,
the count `64 n + 1 - j`, the pointer at digit `j` and the digits before it. -/
structure PrepSt (n : Nat) (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : regsVal s (limbs n) = Naf5.residual k j
  mask : s.gpr (cst n 0) = 31
  sign : s.gpr (cst n 1) = 16
  zero : s.gpr (cst n 2) = 0
  one : s.gpr (cst n 3) = 1
  count : s.gpr .x19 = BitVec.ofNat 64 (64 * n + 1 - j)
  ptr : s.gpr .x20 = off base (bits + j)
  digits : ∀ i < j, s.mem (off base (bits + i)) = Naf5.byte k i

theorem digitStore_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hbj : bits + j < size)
    (hp : s.gpr .x20 = off base (bits + j))
    (hd : s.gpr .x2 = BitVec.ofInt 64 (Naf5.digit k j)) :
    WP isa (.block ([.strb .x2 .x20 0, .addImm .x .x20 .x20 1] : List Instr)) s fun t =>
      t.gpr .x20 = off base (bits + (j + 1)) ∧
      t.mem = s.mem.writeW (off base (bits + j)) (Naf5.byte k j) ∧ KeepRegs [.x20] s t := by
  rw [show ([.strb .x2 .x20 0, .addImm .x .x20 .x20 1] : List Instr) =
    [.strb .x2 .x20 0] ++ [.addImm .x .x20 .x20 1] from rfl, WP.block_append_iff]
  have hw : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 0) 1 := by
    rw [hp]; simp only [BitVec.add_zero]
    exact ⟨_, hs.wr, hs.contains (by omega_arith) (by decide)⟩
  refine WP.mono (strb_ok s (by decide) hw) fun a ha => ?_
  subst a
  refine WP.mono (addImm_ok _ (d := .x20) (n := .x20) (imm := 1) (by decide)) fun t ⟨ht, kt⟩ => ?_
  refine ⟨?_, ?_, ⟨kt.gpr, kt.rd, kt.wr, kt.sp⟩⟩
  · rw [ht]; change s.gpr .x20 + BitVec.ofNat 64 1 = _
    rw [hp]; unfold off; rw [Offset.add_add]; congr 1
  · rw [kt.mem]; simp only [hp, BitVec.add_zero, hd, nafByte_word]

theorem Regs.limb_ne {n : Nat} (hR : Regs n) {r : Reg} (hr : r ∈ limbs n) :
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x16, .x17, .x19, .x20] :=
  hR.avoid r (List.mem_append_left _ hr)

theorem Regs.cst_notin {n : Nat} (hR : Regs n) {i : Nat} (hi : i < 4) : cst n i ∉ limbs n := by
  have hd := (List.nodup_append.mp hR.nodup).2.2
  intro h
  exact hd _ h _ (by
    simp only [csts, List.mem_cons, List.not_mem_nil, or_false]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp) rfl

theorem prepStep_ok {n : Nat} (hR : Regs n) {s : State} {base : Addr} {size bits k j : Nat}
    (hI : PrepSt n base size bits k j s) (hb : bits + (64 * n + 1) ≤ size) (hj : j < 64 * n + 1)
    (hv : Naf5.residual k j ≤ 2 ^ (64 * n)) :
    WP isa (prepStep n) s fun t => PrepSt n base size bits k (j + 1) t ∧
      KeepRegs (clobs n) s t ∧ Outside base bits (64 * n + 1) s.mem t.mem := by
  have cn : ∀ {i}, i < 4 → cst n i ∉ [Reg.x1, .x2, .x3] ∧ cst n i ∉ [Reg.x20] ∧
      cst n i ∉ Reg.x3 :: limbs n ∧ cst n i ∉ [Reg.x19] := fun hi => by
    obtain ⟨a1, a2, a3, a19, a20⟩ := hR.cst_ne hi
    have := hR.cst_notin hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨a1, a2, a3⟩, a20, ⟨a3, this⟩, a19⟩
  have ln : ∀ r ∈ limbs n, r ∉ [Reg.x1, .x2, .x3] ∧ r ∉ [Reg.x20] := fun r hr => by
    have := hR.limb_ne hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨⟨this.2.1, this.2.2.1, this.2.2.2.1⟩, this.2.2.2.2.2.2.2.2⟩
  rw [prepStep]
  refine WP.seq (WP.mono (chooseDigit_ok hR s hI.mask hI.sign hI.one) fun a ⟨ha, ka⟩ => ?_)
  have va : regsVal a (limbs n) = Naf5.residual k j :=
    (regsVal_congr fun r hr => ka.gpr r (ln r hr).1).trans hI.value
  have da : a.gpr .x2 = BitVec.ofInt 64 (Naf5.digit k j) := by
    rw [ha]; apply nafRaw_eq
    have hh := hI.value
    rw [limbs_eq hR, regsVal] at hh
    omega_arith
  have pa : a.gpr .x20 = off base (bits + j) := (ka.gpr _ (by decide)).trans hI.ptr
  have sa := hI.scr.of_keeps ka (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (digitStore_ok sa (by omega_arith) pa da) fun b ⟨pb, mb, kb⟩ => ?_
  have sb := sa.of_keepRegs kb (by decide)
  have vb : regsVal b (limbs n) = Naf5.residual k j :=
    (regsVal_congr fun r hr => kb.gpr r (ln r hr).2).trans va
  rw [WP.block_append_iff]
  refine WP.mono (subtractShift_ok hR b k j
    (by rw [kb.gpr _ (cn (by decide)).2.1, ka.gpr _ (cn (by decide)).1, hI.zero])
    (by rw [kb.gpr .x2 (by decide)]; exact da) vb hv) fun c ⟨vc, kc⟩ => ?_
  have pc : c.gpr .x20 = off base (bits + (j + 1)) := (kc.gpr _ (by
    intro h; exact (hR.limb_ne (r := .x20) (by simpa using h)) (by simp))).trans pb
  have sc := sb.of_keeps kc (by
    intro h; exact (hR.limb_ne (r := .x0) (by simpa using h)) (by simp))
  have cc : c.gpr .x19 = BitVec.ofNat 64 (64 * n + 1 - j) := by
    rw [kc.gpr _ (by intro h; exact (hR.limb_ne (r := .x19) (by simpa using h)) (by simp)),
      kb.gpr _ (by decide), ka.gpr _ (by decide), hI.count]
  have hle := hR.le
  refine WP.mono (decCounter_ok c (by omega_arith) (by omega_arith) cc) fun t ⟨ct, kt⟩ => ?_
  have st := sc.of_keeps kt (by decide)
  have mt : t.mem = s.mem.writeW (off base (bits + j)) (Naf5.byte k j) := by
    rw [kt.mem, kc.mem, mb, ka.mem]
  have O := writeW8_outside s.mem base (Naf5.byte k j) (d := bits + j) (by have := hI.scr.nowrap; omega_arith)
  have keepC : ∀ {i}, i < 4 → t.gpr (cst n i) = s.gpr (cst n i) := fun hi => by
    rw [kt.gpr _ (cn hi).2.2.2, kc.gpr _ (cn hi).2.2.1, kb.gpr _ (cn hi).2.1, ka.gpr _ (cn hi).1]
  refine ⟨⟨st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [regsVal_congr fun r hr => kt.gpr r (by
      intro h; exact (hR.limb_ne hr) (by simp only [List.mem_singleton] at h; simp [h]))]
    exact vc
  · rw [keepC (by decide), hI.mask]
  · rw [keepC (by decide), hI.sign]
  · rw [keepC (by decide), hI.zero]
  · rw [keepC (by decide), hI.one]
  · rw [ct]; congr 1
  · rw [kt.gpr _ (by decide), pc]
  · intro i hi
    rw [mt]
    by_cases hij : i = j
    · subst i; exact writeW8_self ..
    · rw [O _ (by
        have hoff : ofs base (off base (bits + i)) = bits + i := ofs_off0 base (by have := hI.scr.nowrap; omega_arith)
        rw [hoff]; omega_arith)]
      exact hI.digits i (by omega_arith)
  · refine ⟨fun r hr => ?_, kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
      kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)), kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
    simp only [clobs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simpa using hr.1.1.2.2.2.1), kc.gpr r (by
        simp only [List.mem_cons, not_or]; exact ⟨hr.1.1.2.2.1, hr.1.2⟩),
      kb.gpr r (by simpa using hr.1.1.2.2.2.2), ka.gpr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.1.1.1, hr.1.1.2.1, hr.1.1.2.2.1⟩)]
  · rw [mt]; exact O.mono (by omega_arith) (by omega_arith)

theorem init_facts1 : ∀ n < 10, top n ≠ cst n 0 ∧ top n ≠ cst n 1 ∧ top n ≠ cst n 2 ∧
    top n ≠ cst n 3 ∧ top n ≠ .x19 ∧ top n ≠ .x20 := by
  decide

theorem init_facts1' : ∀ n < 10, cst n 0 ≠ cst n 1 ∧ cst n 0 ≠ cst n 2 ∧ cst n 0 ≠ cst n 3 ∧
    cst n 1 ≠ cst n 2 ∧ cst n 1 ≠ cst n 3 ∧ cst n 2 ≠ cst n 3 := by
  decide

theorem init_facts2 : ∀ n < 10, ∀ r ∈ low n, r ≠ top n ∧ r ≠ cst n 0 ∧ r ≠ cst n 1 ∧ r ≠ cst n 2 ∧
    r ≠ cst n 3 ∧ r ≠ .x19 ∧ r ≠ .x20 := by
  decide

theorem init_facts3 : ∀ n < 10, ∀ i < 4, cst n i ≠ .x19 ∧ cst n i ≠ .x20 := by
  decide

theorem init_facts4 : ∀ n < 10, top n ≠ .x0 ∧ cst n 0 ≠ .x0 ∧ cst n 1 ≠ .x0 ∧ cst n 2 ≠ .x0 ∧
    cst n 3 ≠ .x0 := by
  decide

theorem init_ok (K : WinCfg) (hR : Regs K.M.n) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src + 8 * K.M.n ≤ size) (hsrc8 : src % 8 = 0)
    (hbits : K.bits < 4096) :
    WP isa (.block (prepInit K src)) s fun t =>
      PrepSt K.M.n base size K.bits (wordsVal s.mem base src K.M.n) 0 t ∧
      KeepRegs (clobs K.M.n) s t ∧ t.mem = s.mem := by
  have hlow : (low K.M.n).Nodup := by
    have := (List.nodup_append.mp hR.nodup).1
    rw [limbs] at this
    exact (List.nodup_append.mp this).1
  have hlx0 : Reg.x0 ∉ low K.M.n := fun h =>
    hR.limb_ne (r := .x0) (List.mem_append_left _ h) (by simp)
  rw [prepInit, WP.block_append_iff, loads_eq]
  refine WP.mono (loadsR_ok (low K.M.n) hs.ptr (a := src) (by rw [hR.len]; omega_arith) hsrc8 hlow hlx0)
    fun a ⟨va, ka, _⟩ => ?_
  have sa := hs.of_keeps ka hlx0
  -- The distinct registers written.
  have h7 : K.M.n < 10 := by have := hR.le; omega_arith
  obtain ⟨t0, t1, t2, t3, t19, t20⟩ := init_facts1 K.M.n h7
  obtain ⟨c01, c02, c03, c12, c13, c23⟩ := init_facts1' K.M.n h7
  have hlo := init_facts2 K.M.n h7
  have cx := init_facts3 K.M.n h7
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok a (top K.M.n) 0) fun b ⟨db, kb⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok b (cst K.M.n 0) 31) fun c ⟨dc, kc⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok c (cst K.M.n 1) 16) fun d ⟨dd, kd⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok d (cst K.M.n 2) 0) fun e ⟨de, ke⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok e (cst K.M.n 3) 1) fun f ⟨df, kf⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok f .x19 _) fun g ⟨dg, kg⟩ => ?_
  refine WP.mono (addImm_ok g (d := .x20) (n := .x0) hbits) fun t ⟨dt, kt⟩ => ?_
  have ks : ∀ r, r ≠ top K.M.n → r ≠ cst K.M.n 0 → r ≠ cst K.M.n 1 → r ≠ cst K.M.n 2 →
      r ≠ cst K.M.n 3 → r ≠ .x19 → r ≠ .x20 → t.gpr r = a.gpr r := fun r h0 h1 h2 h3 h4 h5 h6 => by
    rw [kt.gpr r (by simpa using h6), kg.gpr r (by simpa using h5), kf.gpr r (by simpa using h4),
      ke.gpr r (by simpa using h3), kd.gpr r (by simpa using h2), kc.gpr r (by simpa using h1),
      kb.gpr r (by simpa using h0)]
  have ka0 : a.gpr .x0 = s.gpr .x0 := ka.gpr _ hlx0
  have hl6 := hR.le
  have ne : ∀ {r q : Reg}, r ≠ q → r ∉ [q] := fun h => by simpa using h
  have tTop : t.gpr (top K.M.n) = 0 := by
    rw [kt.gpr _ (ne t20), kg.gpr _ (ne t19), kf.gpr _ (ne t3), ke.gpr _ (ne t2), kd.gpr _ (ne t1),
      kc.gpr _ (ne t0), db]; rfl
  have tC0 : t.gpr (cst K.M.n 0) = 31 := by
    rw [kt.gpr _ (ne (cx 0 (by decide)).2), kg.gpr _ (ne (cx 0 (by decide)).1), kf.gpr _ (ne c03),
      ke.gpr _ (ne c02), kd.gpr _ (ne c01), dc]; rfl
  have tC1 : t.gpr (cst K.M.n 1) = 16 := by
    rw [kt.gpr _ (ne (cx 1 (by decide)).2), kg.gpr _ (ne (cx 1 (by decide)).1), kf.gpr _ (ne c13),
      ke.gpr _ (ne c12), dd]; rfl
  have tC2 : t.gpr (cst K.M.n 2) = 0 := by
    rw [kt.gpr _ (ne (cx 2 (by decide)).2), kg.gpr _ (ne (cx 2 (by decide)).1), kf.gpr _ (ne c23), de]; rfl
  have tC3 : t.gpr (cst K.M.n 3) = 1 := by
    rw [kt.gpr _ (ne (cx 3 (by decide)).2), kg.gpr _ (ne (cx 3 (by decide)).1), df]; rfl
  have t19 : t.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n + 1) := by
    rw [kt.gpr _ (by decide), dg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  have g0 : g.gpr .x0 = s.gpr .x0 := by
    obtain ⟨z0, z1, z2, z3, z4⟩ := init_facts4 K.M.n h7
    rw [kg.gpr _ (by decide), kf.gpr _ (ne z4.symm), ke.gpr _ (ne z3.symm), kd.gpr _ (ne z2.symm),
      kc.gpr _ (ne z1.symm), kb.gpr _ (ne z0.symm), ka0]
  have hlow' : ∀ r ∈ low K.M.n, t.gpr r = a.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hlo r hr
    exact ks r h0 h1 h2 h3 h4 h5 h6
  have tmem : t.mem = s.mem := by
    rw [kt.mem, kg.mem, kf.mem, ke.mem, kd.mem, kc.mem, kb.mem, ka.mem]
  have twr : t.wr = s.wr := by
    rw [kt.wr, kg.wr, kf.wr, ke.wr, kd.wr, kc.wr, kb.wr, ka.wr]
  refine ⟨⟨⟨?_, twr ▸ hs.wr, hs.nowrap, hs.enc⟩, ?_, tC0, tC1, tC2, tC3, ?_, ?_, fun i hi => absurd hi (by omega_arith)⟩,
    ⟨fun r hr => ?_, ?_, twr, ?_⟩, tmem⟩
  · rw [kt.gpr _ (by decide), g0, hs.x0]
  · rw [limbs, regsVal_append, regsVal_congr hlow', va, hR.len]
    simp only [regsVal, tTop, Naf5.residual_zero]
    simp
  · rw [t19]; rfl
  · rw [dt, g0, hs.x0]; simp only [off, Nat.add_zero]
  · simp only [clobs, csts, limbs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨⟨⟨-, -, -, h19, h20⟩, hl, htop⟩, hc0, hc1, hc2, hc3⟩ := hr
    rw [ks r htop hc0 hc1 hc2 hc3 h19 h20]
    exact ka.gpr r hl
  · rw [kt.rd, kg.rd, kf.rd, ke.rd, kd.rd, kc.rd, kb.rd, ka.rd]
  · rw [kt.sp, kg.sp, kf.sp, ke.sp, kd.sp, kc.sp, kb.sp, ka.sp]

/-- `prep` writes the `64 n + 1` digits of the scalar of `n` words at `src`. -/
theorem prep_ok (K : WinCfg) (hR : Regs K.M.n) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src + 8 * K.M.n ≤ size) (hsrc8 : src % 8 = 0)
    (hbits : K.bits < 4096) (hb : K.bits + (64 * K.M.n + 1) ≤ size) :
    WP isa (prep K src) s fun t =>
      PrepSt K.M.n base size K.bits (wordsVal s.mem base src K.M.n) (64 * K.M.n + 1) t ∧
      KeepRegs (clobs K.M.n) s t ∧ Outside base K.bits (64 * K.M.n + 1) s.mem t.mem := by
  let k := wordsVal s.mem base src K.M.n
  have hk : k < 2 ^ (64 * K.M.n) := wordsVal_lt ..
  have hle := hR.le
  let D := 64 * K.M.n + 1
  let I (m : Nat) (t : State) := PrepSt K.M.n base size K.bits k (D - m) t ∧
    KeepRegs (clobs K.M.n) s t ∧ Outside base K.bits D s.mem t.mem
  rw [prep]
  refine WP.seq (WP.mono (init_ok K hR hs hsrc hsrc8 hbits) fun a ⟨ia, ka, ma⟩ => ?_)
  refine countLoop_ok (Inv := I) (n := D) (by omega_arith) ?_ ?_ (by omega_arith) ?_
  · intro m t hm hmD hI
    have hp := Naf5.residual_boundB (B := 64 * K.M.n) (Nat.le_of_lt hk) (j := D - m) (by omega_arith)
    have hp' : Naf5.residual k (D - m) ≤ 2 ^ (64 * K.M.n) :=
      Nat.le_trans hp (Nat.pow_le_pow_right (by decide) (by omega_arith))
    refine WP.mono (prepStep_ok hR hI.1 hb (by omega_arith) hp') fun u ⟨iu, ku, ou⟩ => ?_
    have he : D - (m - 1) = D - m + 1 := by omega_arith
    refine ⟨⟨?_, hI.2.1.trans ku, hI.2.2.trans ou⟩, ?_⟩
    · rw [he]; exact iu
    · rw [iu.count]; congr 1; omega_arith
  · intro t hI
    exact hI
  · refine ⟨?_, ka, ?_⟩
    · simpa only [Nat.sub_self] using ia
    · rw [ma]; intro _ _; rfl

end VG.Proof.Weierstrass.AArch64.PubNaf
