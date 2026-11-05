module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.SearchInit
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.RsaKeyGen.AArch64.SearchInit
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import Mathlib.Tactic.SplitIfs

/-! # Starting the RSA prime search on AArch64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.SearchInit

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaKeyGen.SearchInit
open VG.Impl.Bignum.AArch64 (movi st countLoop)
open VG.Impl.RsaKeyGen.AArch64.SearchInit

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem and7 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `validate`: `x13` is 1 exactly for a valid width and exponent length. -/
theorem validate_ok (s : State) :
    WP isa (.block validate) s fun t =>
      (t.gpr .x13 = (if initValid (s.gpr .x1).toNat (s.gpr .x3).toNat then 1 else 0) ∧
        t.mem = s.mem) ∧ Keep [.x9, .x10, .x11, .x12, .x13, .x14] s t := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  obtain ⟨e, he, hy⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x3).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  rw [hx, hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
  refine WP.keep [.x9, .x10, .x11, .x12, .x13, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  unfold validate
  brun [hx, hy, imm64 (show 32 < 65536 by decide), imm64 (show 513 < 65536 by decide),
    imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide), imm64 (show 7 < 65536 by decide),
    imm64 (show 9 < 65536 by decide), and7 n hl,
    subs_ge hl (show 32 < 2 ^ 64 by decide), subs_ge hl (show 513 < 2 ^ 64 by decide),
    subs_ge he (show 1 < 2 ^ 64 by decide), subs_ge he (show 9 < 2 ^ 64 by decide),
    subs_ge (show 0 < 2 ^ 64 by decide) (show n % 8 < 2 ^ 64 by omega)]
  split_ifs <;> simp only [decide_eq_true_eq] at * <;>
    first | rfl | (exfalso; omega)

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  change (0#0 ++ m a : BitVec (0 + 8)) = m a
  exact BitVec.zero_width_append _ _

theorem zext_zext (a : Byte) : (a.setWidth 32).setWidth 64 = a.setWidth 64 := by
  ext i hi; simp

/-! ## Whether the exponent is 3 -/

/-- After `j` leading octets. -/
def LeadInv (s : State) (P : Addr) (j : Nat) (u : State) : Prop :=
  u.gpr .x2 = P + BitVec.ofNat 64 j ∧ u.gpr .x9 = orOf (Spec.Rsa.bytesAt s.mem P j) ∧ u.mem = s.mem ∧
    Keep [.x2, .x9, .x10, .x11, .x12] s u

theorem isThree_body {s u : State} {P : Addr} {len j : Nat} (hj : j < len - 1)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P j u) :
    WP isa (.block (([.ldrb .x11 .x2 0, .logic .orr .x .x9 .x9 .x11, .addImm .x .x2 .x2 1] : List Instr) ++
      ([.subImm .x .x10 .x10 1] : List Instr))) u fun v =>
      LeadInv s P (j + 1) v ∧ v.gpr .x10 = u.gpr .x10 - BitVec.ofNat 64 1 := by
  obtain ⟨hx2, hx9, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
    rw [k.rd, k.wr]; exact hrd j (by omega)
  refine WP.mono (WP.keep [.x2, .x9, .x10, .x11] (Q := fun v =>
      v.gpr .x2 = P + BitVec.ofNat 64 (j + 1) ∧
      v.gpr .x9 = orOf (Spec.Rsa.bytesAt s.mem P j) ||| (u.mem (P + BitVec.ofNat 64 j)).setWidth 64 ∧
      v.mem = u.mem ∧ v.gpr .x10 = u.gpr .x10 - BitVec.ofNat 64 1) ?_ (by decide) (by decide)
      (by decide +kernel)) fun v ⟨⟨h2, h9, hmv, h10⟩, kv⟩ => ⟨⟨h2, ?_, hmv.trans hm, (k.trans kv).mono (by decide)⟩, h10⟩
  · brun [hx2, hx9, hr, zext_zext, read_one, BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [h9, bytesAt_succ, orOf_snoc, hm]

theorem sub_one {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · rintro rfl; rfl

/-- The last octet XOR 3, ORed with the leading ones. -/
theorem isThree_last {s u : State} {P : Addr} {len : Nat} (h1 : 1 ≤ len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P (len - 1) u) :
    WP isa (.block [.ldrb .x11 .x2 0, movi .x12 3, .logic .eor .x .x11 .x11 .x12,
      .logic .orr .x .x9 .x9 .x11]) u fun t =>
      (t.gpr .x9 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧ t.mem = s.mem ∧
        Keep [.x2, .x9, .x10, .x11, .x12] s t := by
  obtain ⟨hx2, hx9, hm, k⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 1)) 1 := by
    rw [k.rd, k.wr]; exact hrd (len - 1) (by omega)
  refine WP.mono (WP.keep [.x9, .x11, .x12] (Q := fun t => t.gpr .x9 =
      orOf (Spec.Rsa.bytesAt s.mem P (len - 1)) |||
        ((u.mem (P + BitVec.ofNat 64 (len - 1))).setWidth 64 ^^^ 3) ∧ t.mem = u.mem) ?_ (by decide)
      (by decide) (by decide +kernel)) fun t ⟨⟨h9, hmt⟩, kt⟩ =>
    ⟨?_, hmt.trans hm, (k.trans kt).mono (by decide)⟩
  · brun [hx2, hx9, hr, zext_zext, read_one, BitVec.add_zero, imm64 (show 3 < 65536 by decide)]
    rfl
  · have hb : Spec.Rsa.bytesAt s.mem P len =
        Spec.Rsa.bytesAt s.mem P (len - 1) ++ [s.mem (P + BitVec.ofNat 64 (len - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [h9, hm, hb, os2ip_eq_three]

/-- `isThree`: `x9` is 0 iff `e` (`len` octets at `x2`) is 3. -/
theorem isThree_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .x2 = P)
    (hl : s.gpr .x3 = BitVec.ofNat 64 len) (h1 : 1 ≤ len) (h8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa isThree s fun t =>
      (t.gpr .x9 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧ t.mem = s.mem ∧
        Keep [.x2, .x9, .x10, .x11, .x12] s t := by
  unfold isThree
  refine WP.seq (WP.mono (WP.keep [.x9, .x10] (Q := fun t =>
      t.gpr .x9 = 0 ∧ t.gpr .x10 = BitVec.ofNat 64 (len - 1) ∧ t.mem = s.mem)
    (by brun [hl, imm64 (show 0 < 65536 by decide), sub_one h1 (by omega)]) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨h9, h10, hm⟩, k⟩ => ?_)
  have h0 : LeadInv s P 0 t := ⟨by rw [k.gpr .x2 (by decide), hp, BitVec.add_zero],
    by rw [h9]; rfl, hm, k.mono (by decide)⟩
  have hloop : WP isa (.ite (.zero .x .x10) (.block [])
      (countLoop .x10 [.ldrb .x11 .x2 0, .logic .orr .x .x9 .x9 .x11, .addImm .x .x2 .x2 1])) t
      (LeadInv s P (len - 1)) := by
    refine WP.ite _ (by rw [VG.Proof.MlKem.AArch64.eval_zero, h10, ofNat_beq_zero (by omega)])
      (fun hz => ?_) (fun hz => ?_)
    · have hz : len - 1 = 0 := of_decide_eq_true hz
      exact WP.block_nil (by rw [hz]; exact h0)
    · have hz : len - 1 ≠ 0 := of_decide_eq_false hz
      exact wp_countdown (N := len - 1) (by omega) (by omega) (LeadInv s P)
        (fun i hi u hI _ => isThree_body (len := len) hi hrd hI) h0 h10
  exact WP.seq (WP.mono hloop fun u hu => isThree_last h1 hrd hu)

/-! ## The four words -/

theorem initialize_ok {s : State} {B : Addr} {L : Nat} {three : Bool}
    (scr : Scr s B 32) (h0 : s.gpr .x0 = B) (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (hL : L ≤ 512)
    (hz : (s.gpr .x9 == 0) = three) :
    WP isa (.block initializeState) s
      fun t => t.gpr .x0 = 1 ∧ t.mem = written s.mem B (initWords L three) := by
  obtain ⟨k, hk, h9⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x9 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x9).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  rw [h9, ofNat_beq_zero hk] at hz
  have hc : decide (k ≤ 0) = three := by rw [← hz]; exact decide_eq_decide.mpr (by omega)
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  have e8 := shl_ofNat L 3 (by omega)
  have e32 := shl_ofNat L 5 (by omega)
  have e64 := shl_ofNat L 6 (by omega)
  have e15 := shl_ofNat L 15 (by omega)
  have e40 : BitVec.ofNat 64 (L * 2 ^ 3) + BitVec.ofNat 64 (L * 2 ^ 5) = BitVec.ofNat 64 (40 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e32769 : BitVec.ofNat 64 (L * 2 ^ 15) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e64' : BitVec.ofNat 64 (L * 2 ^ 6) = BitVec.ofNat 64 (64 * L) := by congr 1; omega
  have e32' : BitVec.ofNat 64 (L * 2 ^ 5) = BitVec.ofNat 64 (32 * L) := by congr 1; omega
  unfold initializeState written initWords
  cases three <;>
  brun [h0, h1, h9, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide), e8, e32, e64,
    e15, e40, e32769, subs_ge (show 0 < 2 ^ 64 by decide) hk, hc, h00, scr.st (d := 8) (by decide),
    scr.st (d := 16) (by decide), scr.st (d := 24) (by decide)] <;>
  simp only [e64', e32', List.getD_cons_zero, List.getD_cons_succ] <;> rfl

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) :
    WP isa (.block clear) s fun t => t.gpr .x0 = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold clear written
  brun [h0, imm64 (show 0 < 65536 by decide), h00, scr.st (d := 8) (by decide),
    scr.st (d := 16) (by decide), scr.st (d := 24) (by decide)]
  rfl

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B P : Addr) (t : State) : Prop :=
  if initValid L len then
    t.gpr .x0 = 1 ∧ t.mem = written m B (initWords L (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P len) = 3)))
  else t.gpr .x0 = 0 ∧ t.mem = written m B [0, 0, 0, 0]

theorem init_ok {s : State} {B P : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) (hp : s.gpr .x2 = P)
    (hrd : (s.gpr .x3).toNat ≤ 8 →
      ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .x1).toNat (s.gpr .x3).toNat s.mem B P) := by
  unfold init
  refine WP.seq (WP.mono (validate_ok s) fun u ⟨⟨h13, hm⟩, k⟩ => ?_)
  have scu := scr.congr k.wr
  have hu0 : u.gpr .x0 = B := (k.gpr .x0 (by decide)).trans h0
  by_cases hv : initValid (s.gpr .x1).toNat (s.gpr .x3).toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h13
    refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl) (fun h => by cases h)
      fun _ => ?_
    obtain ⟨h32, h512, hmod, h1, h8⟩ := hv
    have hl : u.gpr .x3 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
      rw [k.gpr .x3 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hru : ∀ i < (s.gpr .x3).toNat, InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 i) 1 := by
      rw [k.rd, k.wr]; exact hrd h8
    refine WP.seq (WP.mono (isThree_ok ((k.gpr .x2 (by decide)).trans hp) hl h1 h8 hru)
      fun z ⟨hzi, hmz, kz⟩ => ?_)
    have hz : (z.gpr .x9 == 0) = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (s.gpr .x3).toNat) = 3) := by
      rw [← hm]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact hzi
    have hz1 : z.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [kz.gpr .x1 (by decide), k.gpr .x1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (initialize_ok (scu.congr kz.wr) ((kz.gpr .x0 (by decide)).trans hu0) hz1 h512 hz)
      fun t ⟨ht, hmt⟩ => ?_
    unfold InitPost
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h32, h512, hmod, h1, h8⟩)]
    exact ⟨ht, by rw [hmt, hmz, hm]⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h13
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl)
      (fun _ => WP.mono (clear_ok scu hu0) fun t ⟨ht, hmt⟩ => ?_) fun h => by cases h
    unfold InitPost
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨ht, by rw [hmt, hm]⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩] ∧
    (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .x1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) with
  | none => ((t.gpr .x0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = List.replicate 4 0
  | some values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧
      ∃ first, Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 =
        (values ++ [first]).map (BitVec.ofNat 64) ∧
        Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (s.gpr .x1).toNat) 0 first

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .x1).toNat (s.gpr .x3).toNat s.mem (s.gpr .x0) (s.gpr .x2) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  have hl : (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length = (s.gpr .x3).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [primeInit_eq, hl]
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [h.1]; rfl, _, ?_, SearchInit.first_valid hv⟩
    rw [h.2, initWords, written_words]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, decide_eq_true_eq]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome⟩ := h
  have scr : Scr s (s.gpr .x0) 32 := Scr.of_mem (by rw [hwr]; simp) hroom
  have hreads : (s.gpr .x3).toNat ≤ 8 →
      ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
    fun _ i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.x0, .x2, .x9, .x10, .x11, .x12, .x13, .x14]
    (init_ok scr rfl rfl hreads) (by decide +kernel)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, result_post hp⟩

def InitInput (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2.1 ∧ s.gpr .x2 = p.2.2.1 ∧ s.gpr .x3 = p.2.2.2

/-- After `validate`: `x13` is a function of the public width and length. -/
def InitValid (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  InitInput p s ∧ s.gpr .x13 = (if initValid p.2.1.toNat p.2.2.2.toNat then 1 else 0)

private theorem validate_ready (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) (h : InitInput p s) :
    WP isa (.block validate) s (InitValid p) :=
  WP.mono (validate_ok s) fun _ ⟨⟨h13, _⟩, k⟩ =>
    ⟨⟨(k.gpr .x0 (by decide)).trans h.1, (k.gpr .x1 (by decide)).trans h.2.1,
      (k.gpr .x2 (by decide)).trans h.2.2.1, (k.gpr .x3 (by decide)).trans h.2.2.2⟩,
      by rw [h13, h.2.1, h.2.2.2]⟩

private theorem input_pins : Pins InitInput [.x0, .x1, .x2, .x3] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm,
    h₁.2.2.2.trans h₂.2.2.2.symm]

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have ct : RelCT isa (Two InitInput) init fun _ _ => True := by
    unfold init
    refine RelCT.seq (two_piece [.x0, .x1, .x2, .x3] input_pins (by taint_decide) validate_ready) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => ?_)
      (two_taint [.x0, .x1, .x2, .x3] (fun p _ _ h₁ h₂ => input_pins p _ _ h₁.1.1 h₂.1.1) (by taint_decide))
      (two_taint [.x0, .x1, .x2, .x3] (fun p _ _ h₁ h₂ => input_pins p _ _ h₁.1.1 h₂.1.1) (by taint_decide))
    rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, h₁.2, h₂.2]
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hsp, h0, h1, h2, h3⟩ := h
  exact ⟨(s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3), ⟨rfl, rfl, rfl, rfl⟩,
    ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩, hsp⟩

private def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 3 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.primeInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.RsaKeyGen.AArch64.SearchInit
