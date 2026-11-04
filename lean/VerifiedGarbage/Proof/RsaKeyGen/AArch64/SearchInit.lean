module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.SearchInit
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.RsaKeyGen.AArch64.SearchInit
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import Mathlib.Tactic.SplitIfs

/-! # Starting the RSA prime search on AArch64: correctness, constant time

`validate` leaves `x13 = 1` exactly for a width in 32..=512 and an exponent
of 1 to 8 octets (`validate_ok`); then the width's low bits, `loadE` (`e`
into `x6`, `loadE_ok`) and the four words (`words_ok`). Every branch and
every address is a function of the four arguments: `e`, which only `cselc`
uses, does not decide any.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.SearchInit

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64.Generation (initWritten initWritten_words imm64 shift_ofNat)
open VG.Impl.RsaKeyGen.AArch64.SearchInit

/-- The bounds `validate` checks. -/
def boundsValid (L len : Nat) : Prop := 32 ≤ L ∧ L ≤ 512 ∧ 1 ≤ len ∧ len ≤ 8

instance (L len : Nat) : Decidable (boundsValid L len) := by unfold boundsValid; infer_instance

/-- `validate`: `x13` is 1 exactly for valid bounds. -/
theorem validate_ok (s : State) :
    WP isa (.block validate) s fun t =>
      (t.gpr .x13 = (if boundsValid (s.gpr .x1).toNat (s.gpr .x3).toNat then 1 else 0) ∧
        t.mem = s.mem) ∧ Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16] s t := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  obtain ⟨g, hg, hgx⟩ : ∃ g, g < 2 ^ 64 ∧ s.gpr .x3 = BitVec.ofNat 64 g :=
    ⟨_, (s.gpr .x3).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, hgx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg]
  refine WP.keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16] ?_ (by decide) (by decide)
    (by decide +kernel)
  unfold validate
  brun [hx, hgx, imm64 (show 32 < 65536 by decide), imm64 (show 513 < 65536 by decide),
    imm64 (show 1 < 65536 by decide), imm64 (show 9 < 65536 by decide),
    imm64 (show 0 < 65536 by decide),
    subs_ge hl (show 32 < 2 ^ 64 by decide), subs_ge hl (show 513 < 2 ^ 64 by decide),
    subs_ge hg (show 1 < 2 ^ 64 by decide), subs_ge hg (show 9 < 2 ^ 64 by decide)]
  by_cases hv : boundsValid n g
  · rw [ite_eq_left hv]
    obtain ⟨h1, h2, h3, h4⟩ := hv
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> first | rfl | (exfalso; omega)
  · rw [ite_eq_right hv]
    simp only [boundsValid, not_and] at hv
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> first | rfl | (exfalso; omega)

theorem and7 (x : BitVec 64) : (x &&& BitVec.ofNat 64 7 == 0) = decide (x.toNat % 8 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  have e : ∀ y : BitVec 64, (y &&& BitVec.ofNat 64 7).toNat = y.toNat % 8 := fun y => by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [e] at this; exact this
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [e]; exact h)

/-- Whether the width is a multiple of 8, in `x10`. -/
theorem multiple_ok (s : State) :
    WP isa (.block [Impl.Bignum.AArch64.movi .x9 7, .logic .and .x .x10 .x1 .x9]) s fun t =>
      (isa.eval (.zero .x .x10) t = some (decide ((s.gpr .x1).toNat % 8 = 0)) ∧ t.mem = s.mem) ∧
        Keep [.x9, .x10] s t := by
  refine WP.keep [.x9, .x10] ?_ (by decide) (by decide) (by decide +kernel)
  brun [imm64 (show 7 < 65536 by decide)]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, and7]

/-- `loadE`: `e` (`len ≤ 8` octets at `P`, most significant first) into `x6`. -/
theorem loadE_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .x2 = P)
    (hl : s.gpr .x3 = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hl8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa loadE s fun t => (t.gpr .x6).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) ∧
      t.mem = s.mem ∧ Keep [.x4, .x5, .x6, .x7] s t := by
  let eB := Spec.Rsa.bytesAt s.mem P len
  have hlen : eB.length = len := by simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hval : ∀ i (hi : i < eB.length), s.mem (P + BitVec.ofNat 64 i) = eB[i] := fun i hi => by
    simp only [eB, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  unfold loadE Impl.Bignum.AArch64.countLoop
  refine WP.seq (WP.mono (WP.keep [.x4, .x5, .x6] (Q := fun t => t.gpr .x4 = P ∧
      t.gpr .x5 = BitVec.ofNat 64 len ∧ t.gpr .x6 = 0 ∧ t.mem = s.mem)
    (by brun [hp, hl, imm64 (show 0 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x5) (N := len) (by omega) (by omega)
    (fun i t => (t.gpr .x6).toNat = pre eB i ∧ t.gpr .x4 = P + BitVec.ofNat 64 i ∧ t.mem = s.mem ∧
      Keep [.x4, .x5, .x6, .x7] s t) ?_
    ⟨by rw [h3]; rfl, by rw [h1]; exact (BitVec.add_zero P).symm, hm₁, k₁.mono (by decide)⟩ h2)
    fun t ⟨h3', _, hm, k⟩ => ⟨by rw [h3']; have := pre_len eB; rw [hlen] at this; exact this, hm, k⟩
  intro i hi t ⟨hb, h1', hm, k⟩ _
  have hi' : i < eB.length := by rw [hlen]; exact hi
  have hpre : pre eB i < 2 ^ 56 := by
    have := pre_lt eB (i := i) (by omega)
    calc pre eB i < 256 ^ i := this
      _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ 56 := by decide
  have hrd' : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 i) 1 := by
    rw [k.rd, k.wr]; exact hrd i hi
  have hbyte : t.mem (P + BitVec.ofNat 64 i) = eB[i] := by rw [hm]; exact hval i hi'
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x4, .x6, .x7] (Q := fun t₁ =>
      t₁.gpr .x6 = (t.gpr .x6 <<< 8) + ((t.mem.read (P + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 ∧
      t₁.gpr .x4 = P + BitVec.ofNat 64 i + BitVec.ofNat 64 1 ∧ t₁.mem = t.mem)
    (by brun [h1', hrd']) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3₁, h1₁, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (dec_ok t₁ .x5) fun t' ⟨⟨h2', m', _⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
  · have e1 : (t.gpr .x6 <<< 8).toNat = (t.gpr .x6).toNat * 256 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hb' : (((t.mem.read (P + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 : BitVec 64).toNat =
        eB[i].toNat := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, VG.Proof.MlKem.AArch64.read_one, hbyte]
      have := eB[i].isLt
      omega
    have := eB[i].isLt
    rw [k'.gpr .x6 (by decide), h3₁, BitVec.toNat_add, e1, hb', hb, pre_succ eB hi',
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [k'.gpr .x4 (by decide), h1₁, BitVec.add_assoc, ← BitVec.ofNat_add]
  · exact ((k.trans k₁).trans k').mono (by decide)
  · rw [h2', k₁.gpr .x5 (by decide)]

/-- The four words `primeInit` gives, for a width `L` and whether `e` is 3. -/
def initWords (L : Nat) (three : Bool) : List (BitVec 64) :=
  [BitVec.ofNat 64 (if three then 64 * L else 40 * L), BitVec.ofNat 64 L,
    BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (32 * L)]

theorem sub3_zero (E : Nat) (hE : E < 2 ^ 64) :
    decide ((BitVec.ofNat 64 E - BitVec.ofNat 64 3 &&& (BitVec.ofNat 64 E - BitVec.ofNat 64 3)) = 0) =
      decide (E = 3) := by
  rw [BitVec.and_self]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have h' := congrArg (· + BitVec.ofNat 64 3) h
    simp only [BitVec.sub_add_cancel] at h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hE] at this
    simpa using this
  · rintro rfl; rfl

private theorem exec_tst_x (s : State) (n m : Reg) :
    exec (.tst .x n m) s = some { s with
      nf := (s.read .x n &&& s.read .x m).msb
      zf := decide ((s.read .x n &&& s.read .x m) = 0)
      c := false
      vf := false } := rfl

private theorem exec_csel_eq (s : State) (d n m : Reg) :
    exec (.cselc .x d n m .eq) s =
      some (s.write .x d (if s.zf then s.read .x n else s.read .x m)) := rfl

/-- `words`: the four words for the width `L` in `x1` and `e` in `x6`. -/
theorem words_ok {s : State} {B : Addr} {L E : Nat} (scr : Scr s B 32) (h0 : s.gpr .x0 = B)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (h6 : s.gpr .x6 = BitVec.ofNat 64 E)
    (hE : E < 2 ^ 64) :
    WP isa (.block words) s fun t => t.gpr .x0 = 1 ∧
      t.mem = initWritten s.mem B (BitVec.ofNat 64 (if E = 3 then 64 * L else 40 * L))
        (BitVec.ofNat 64 L) (BitVec.ofNat 64 (32769 * L)) (BitVec.ofNat 64 (32 * L)) := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  have e40 : BitVec.ofNat 64 L <<< 3 <<< 2 + BitVec.ofNat 64 L <<< 3 = BitVec.ofNat 64 (40 * L) := by
    rw [shift_ofNat, shift_ofNat, ← BitVec.ofNat_add]; congr 1; omega
  have e64 : BitVec.ofNat 64 L <<< 6 = BitVec.ofNat 64 (64 * L) := by
    rw [shift_ofNat]; congr 1; omega
  have e15 : BitVec.ofNat 64 L <<< 15 + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [shift_ofNat, ← BitVec.ofNat_add]; congr 1; omega
  have e5 : BitVec.ofNat 64 L <<< 5 = BitVec.ofNat 64 (32 * L) := by
    rw [shift_ofNat]; congr 1; omega
  unfold words initWritten
  brun [h0, h1, h6, imm64 (show 1 < 65536 by decide), h00, scr.st (d := 8) (by decide),
    scr.st (d := 16) (by decide), scr.st (d := 24) (by decide), e40, e64, e15, e5, exec_tst_x, exec_csel_eq, State.read, sub3_zero E hE]
  by_cases h3 : E = 3 <;> simp only [h3, RegUpd.zf_write, decide_true, decide_false, ite_true, ite_false, off,
    Bool.false_eq_true]

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) :
    WP isa (.block clear) s fun t => t.gpr .x0 = 0 ∧ t.mem = initWritten s.mem B 0 0 0 0 := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold clear initWritten
  brun [h0, imm64 (show 0 < 65536 by decide), h00, scr.st (d := 8) (by decide), scr.st (d := 16) (by decide),
    scr.st (d := 24) (by decide)]
  rfl

/-! ## The whole initialization -/

abbrev initValid (L len : Nat) : Prop := 32 ≤ L ∧ L ≤ 512 ∧ L % 8 = 0 ∧ 1 ≤ len ∧ len ≤ 8

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B P : Addr) (t : State) : Prop :=
  if initValid L len then
    t.gpr .x0 = 1 ∧ t.mem = initWritten m B
      (BitVec.ofNat 64 (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P len) = 3 then 64 * L else 40 * L))
      (BitVec.ofNat 64 L) (BitVec.ofNat 64 (32769 * L)) (BitVec.ofNat 64 (32 * L))
  else t.gpr .x0 = 0 ∧ t.mem = initWritten m B 0 0 0 0

private theorem clear_post {t : State} {B P : Addr} {L len : Nat} {m : Mem}
    (scr : Scr t B 32) (h0 : t.gpr .x0 = B) (hm : t.mem = m) (hv : ¬initValid L len) :
    WP isa (.block clear) t (InitPost L len m B P) := by
  refine WP.mono (clear_ok scr h0) fun u ⟨ha, hu⟩ => ?_
  unfold InitPost
  rw [ite_eq_right hv]
  exact ⟨ha, by rw [hu, hm]⟩

theorem os2ip_lt (bs : List Byte) (h : bs.length ≤ 8) : Spec.Rsa.os2ip bs < 2 ^ 64 := by
  have := pre_lt bs (i := bs.length) (Nat.le_refl _)
  rw [pre_len] at this
  calc Spec.Rsa.os2ip bs < 256 ^ bs.length := this
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
    _ = 2 ^ 64 := by decide

theorem init_ok {s : State} {B P : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) (hp : s.gpr .x2 = P)
    (hrd : (s.gpr .x3).toNat ≤ 8 →
      ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .x1).toNat (s.gpr .x3).toNat s.mem B P) := by
  unfold init
  refine WP.seq (WP.mono (validate_ok s) fun u ⟨⟨h13, hm⟩, k⟩ => ?_)
  have scu := scr.congr k.wr
  have hu0 : u.gpr .x0 = B := (k.gpr .x0 (by decide)).trans h0
  by_cases hb : boundsValid (s.gpr .x1).toNat (s.gpr .x3).toNat
  · rw [ite_eq_left hb] at h13
    refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (multiple_ok u) fun v ⟨⟨he, hmv⟩, kv⟩ => ?_)
    rw [k.gpr .x1 (by decide)] at he
    have scv := scu.congr kv.wr
    have hv0 : v.gpr .x0 = B := (kv.gpr .x0 (by decide)).trans hu0
    by_cases h8 : (s.gpr .x1).toNat % 8 = 0
    · have hv : initValid (s.gpr .x1).toNat (s.gpr .x3).toNat := ⟨hb.1, hb.2.1, h8, hb.2.2⟩
      refine WP.ite true (by rw [he]; simp [h8]) (fun _ => ?_) fun h => by cases h
      have hkv : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16] → v.gpr r = s.gpr r :=
        fun r hr => (kv.gpr r (fun h => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          rcases h with rfl | rfl <;> simp))).trans (k.gpr r hr)
      have hrv : ∀ i < (s.gpr .x3).toNat, InRegions (v.rd ++ v.wr) (P + BitVec.ofNat 64 i) 1 := by
        rw [kv.rd, kv.wr, k.rd, k.wr]; exact hrd hb.2.2.2
      have hl : v.gpr .x3 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
        rw [hkv .x3 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      unfold initializeState
      refine WP.seq (WP.mono (loadE_ok ((hkv .x2 (by decide)).trans hp) hl hb.2.2.1 hb.2.2.2 hrv)
        fun w ⟨h6, hmw, kw⟩ => ?_)
      have hlen : (Spec.Rsa.bytesAt v.mem P (s.gpr .x3).toNat).length ≤ 8 := by
        simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hb.2.2.2
      have hE := os2ip_lt _ hlen
      refine WP.mono (words_ok (scv.congr kw.wr) ((kw.gpr .x0 (by decide)).trans hv0)
        (L := (s.gpr .x1).toNat)
        (by rw [kw.gpr .x1 (by decide), hkv .x1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
        (by rw [← h6, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hE) fun t ⟨ht, hmt⟩ => ?_
      unfold InitPost
      rw [ite_eq_left hv]
      refine ⟨ht, ?_⟩
      rw [hmt, hmw, hmv, hm]
    · refine WP.ite false (by rw [he]; simp [h8]) (fun h => by cases h) fun _ =>
        clear_post scv hv0 (hmv.trans hm) fun hv => h8 hv.2.2.1
  · rw [ite_eq_right hb] at h13
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl)
      (fun _ => clear_post scu hu0 hm fun hv => hb ⟨hv.1, hv.2.1, hv.2.2.2⟩) fun h => by cases h

/-! ## The contract -/

theorem primeInit_eq (L : Nat) (eB : List Byte) :
    Spec.RsaKeyGen.primeInit L eB =
      if initValid L eB.length then
        some [if Spec.Rsa.os2ip eB = 3 then 64 * L else 40 * L, L, 32769 * L, 32 * L]
      else none := by
  unfold Spec.RsaKeyGen.primeInit initValid
  by_cases hv : 32 ≤ L ∧ L ≤ 512 ∧ L % 8 = 0 ∧ 1 ≤ eB.length ∧ eB.length ≤ 8
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hv
    have hb : (32 ≤ L && L ≤ 512 && L % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
    rw [hb, ite_eq_left_of_eq_true _ _ (eq_true rfl),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2, h3, h4, h5⟩)]
    simp only [Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeRequest, Spec.RsaKeyGen.primeEntropy,
      Spec.Entropy.request, Option.some.injEq, List.cons.injEq, and_true]
    exact ⟨by split <;> omega, trivial, trivial, by omega⟩
  · have hb : (32 ≤ L && L ≤ 512 && L % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
      omega
    rw [hb, ite_eq_right_of_eq_false _ _ (eq_false hv)]
    rfl

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩] ∧
    (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .x1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) with
  | none => ((t.gpr .x0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = List.replicate 4 0
  | some values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = values.map (BitVec.ofNat 64)

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
    refine ⟨by rw [h.1]; rfl, ?_⟩
    rw [h.2, initWritten_words]
    simp only [List.map_cons, List.map_nil]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, initWritten_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome⟩ := h
  have scr : Scr s (s.gpr .x0) 32 := Scr.of_mem (by rw [hwr]; simp) hroom
  have hreads : (s.gpr .x3).toNat ≤ 8 →
      ∀ i < (s.gpr .x3).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
    fun _ i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep
    [.x0, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16]
    (init_ok scr rfl rfl hreads) (by decide +kernel)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, result_post hp⟩

def InitInput (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2.1 ∧ s.gpr .x2 = p.2.2.1 ∧ s.gpr .x3 = p.2.2.2

/-- After `validate`: `x13` is a function of the public arguments. -/
def InitValid (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  InitInput p s ∧ s.gpr .x13 = (if boundsValid p.2.1.toNat p.2.2.2.toNat then 1 else 0)

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
  have pins (b : Bool) : Pins (fun p s => InitValid p s ∧ isa.eval (.zero .x .x13) s = some b)
      [.x0, .x1, .x2, .x3] := fun p s t h₁ h₂ => input_pins p s t h₁.1.1 h₂.1.1
  have ct : RelCT isa (Two InitInput) init fun _ _ => True := by
    unfold init
    refine RelCT.seq (two_piece [.x0, .x1, .x2, .x3] input_pins (by taint_decide) validate_ready) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => ?_) (two_taint [.x0, .x1, .x2, .x3] (pins true) (by taint_decide))
      (two_taint [.x0, .x1, .x2, .x3] (pins false) (by taint_decide))
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
