module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore

/-!
# A candidate on RISC-V: a witness's round

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/WRound.lean`): `passed_ok`, after
a passing round, one more witness (`hIdx`), and `hStat := 1` once there are at
least 17 (from 1) of them and `hChecks` uniform ones (`hUni`), else 4;
`round_ok`, the round (`roundCall_ok`) and its outcome, `hStat := 2` for a
failure.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni passed)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (ge_val Prep RcPost Kept keeps_word keeps_byte)
open VG.Proof.Bignum (slot Frm word off ofs writeW_outside word_writeW_self)

/-- The status after a passing round, from `I` witnesses of which `U` uniform. -/
abbrev statOf (I U ch : Nat) : Nat := if 17 ≤ I + 1 ∧ ch ≤ U then 1 else 4

/-- The registers `passed` writes. -/
def psRegs : List Reg := [.t2, .t3, .t4, .t5]

/-- After a passing round, from `I` witnesses of which `U` uniform. -/
theorem passed_ok {s : State} {B : Addr} {Z w I U ch : Nat} (e : Env s B Z w)
    (hk : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hk' : I + 1 < 2 ^ 63) (hu' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (.block passed) s fun s' =>
      (s'.mem = (s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))).writeW (off B (8 * hStat))
          (BitVec.ofNat 64 (statOf I U ch))) ∧ Keep psRegs s s' := by
  have hs := e.hs
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have r176 : s.mem.readW (B + 176#64) 64 = BitVec.ofNat 64 I := hk
  have o176 := writeW_outside s.mem B (BitVec.ofNat 64 (I + 1)) (d := 176) (by omega)
  have r16 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (I + 1))).readW (B + 16#64) 64 = BitVec.ofNat 64 U :=
    (o176.word (by omega) (by omega)).trans hu
  have r168 : (s.mem.writeW (B + 176#64) (BitVec.ofNat 64 (I + 1))).readW (B + 168#64) 64 = BitVec.ofNat 64 ch :=
    (o176.word (by omega) (by omega)).trans hch
  have ek : BitVec.ofNat 64 I + 1#64 = BitVec.ofNat 64 (I + 1) := by rw [← BitVec.ofNat_add]
  have g1 := ge_val (BitVec.ofNat 64 (I + 1)) (BitVec.ofNat 64 17)
  have g2 := ge_val (BitVec.ofNat 64 U) (BitVec.ofNat 64 ch)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at g1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at g2
  simp only [passed, geFlag, ldh, sth, hIdx, hUni, hChecks, hStat]
  brun [e.s6, hs.ld (d := 176) (n := 8) (by omega), hs.al8 (d := 176) (by omega) (by decide),
    hs.st (d := 176) (n := 8) (by omega), hs.ld (d := 16) (n := 8) (by omega), hs.al8 (d := 16) (by omega) (by decide),
    hs.ld (d := 168) (n := 8) (by omega), hs.al8 (d := 168) (by omega) (by decide),
    hs.st (d := 160) (n := 8) (by omega), hs.al8 (d := 160) (by omega) (by decide),
    r176, exec_li (show imm12 17 by decide), exec_li (show imm12 3 by decide),
    exec_li (show imm12 4 by decide)]
  simp only [ek, r16, r168]
  rw [show (1#64 : BitVec 64) = BitVec.ofInt 64 1 from rfl, g1, g2]
  have hv : BitVec.ofNat 64 4 - (BitVec.ofNat 64 (if ch ≤ U then 1 else 0) &&&
      BitVec.ofNat 64 (if 17 ≤ I + 1 then 1 else 0)) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (statOf I U ch) := by
    by_cases h1 : ch ≤ U <;> by_cases h2 : 17 ≤ I + 1 <;> simp [statOf, h1, h2] <;> decide
  rw [hv]

/-- A byte the round and its outcome keep: one the round keeps, outside
`hStat` and `hIdx`. -/
def RKept (w i : Nat) : Prop := Kept w i ∧ ∀ k ∈ [20, 22], i < 8 * k ∨ 8 * k + 8 ≤ i

/-- What a witness's round leaves. -/
structure RdPost (s : State) (B : Addr) (L w c a I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) =
    BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then statOf I U ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then I + 1 else I)
  kept : ∀ i, i < 8 * L → RKept w i → t.mem (B + BitVec.ofNat 64 i) = s.mem (B + BitVec.ofNat 64 i)
  frame : Frame [⟨B, 8 * L⟩, below s.sp 96] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → t.gpr r = s.gpr r

/-- A word whose bytes are all `RKept`. -/
theorem RdPost.word {s t : State} {B : Addr} {L w c a I U ch d : Nat} (h : RdPost s B L w c a I U ch t)
    (hd : d + 8 ≤ 8 * L) (hk : ∀ i, d ≤ i → i < d + 8 → RKept w i) : word t.mem B d = word s.mem B d :=
  (Mem.readW_congr fun i hi => by
    rw [show off B d + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact (h.kept _ (by omega_arith) (hk _ (by omega_arith) (by omega_arith))).symm).symm

/-- A change only at offsets below `e` keeps memory outside the `8 L` bytes at
`B`, for `e ≤ 8 L`. -/
theorem frame_of_low {B : Addr} {L e : Nat} {m m' : Mem} (h : ∀ x, e ≤ ofs B x → m' x = m x) (he : e ≤ 8 * L)
    (rs : List Region) : Frame (⟨B, 8 * L⟩ :: rs) m m' := by
  intro x hx
  have hb := hx _ (List.mem_cons_self ..)
  simp only [Region.Contains, Nat.not_le] at hb
  exact h x (by show e ≤ (x - B).toNat; omega)

/-- Array `j ≤ 27` of the working space lies past the header and inside its
`8 L` bytes. -/
theorem slot_bounds {w L j : Nat} (hL : 256 + 28 * (8 * (w + 2)) ≤ 8 * L) (hj : j ≤ 27) :
    256 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ 8 * L := by
  have e : slot w j = 256 + j * (8 * (w + 2)) := rfl
  have hm : j * (8 * (w + 2)) ≤ 27 * (8 * (w + 2)) := Nat.mul_le_mul_right _ hj
  rw [e]
  omega

theorem ofs_byte (B : Addr) {i : Nat} (hi : i < 2 ^ 64) : ofs B (B + BitVec.ofNat 64 i) = i := by
  simp only [VG.Proof.Bignum.ofs]
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem round_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a I U ch : Nat} (h : Prep s B L w c)
    (ha : A s.mem B w 4 = a) (hac : a < c)
    (hal : s.sp.toNat % 16 = 0) (hsp : 96 ≤ s.sp.toNat) (hstk : (below s.sp 96).Disjoint ⟨B, 8 * L⟩)
    (hI : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I) (hU : word s.mem B (8 * hUni) = BitVec.ofNat 64 U)
    (hch : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch) (hI' : I + 1 < 2 ^ 63) (hU' : U < 2 ^ 63)
    (hch' : ch < 2 ^ 63) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.round R.name R.code) s (RdPost s B L w c a I U ch) := by
  have e := h.env
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  unfold VG.Impl.RsaKeyGen.RISCV64.Witness.round
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.roundCall_ok R h ha hac hal hsp hstk)
    fun u hu => ?_)
  have kw : ∀ d, d + 8 ≤ 256 → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word u.mem B d = word s.mem B d :=
    fun d hd hk => keeps_word hu.keeps (by omega_arith) hk
  have hsu := hu.prep.env.hs
  have hnw := hsu.nowrap
  have hL : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := hu.prep.env.hZ
  -- A store to `hStat` or `hIdx` keeps `Prep`, the round's bytes and the frame.
  have keepP : ∀ (t : State), (∀ x, (ofs B x < 160 ∨ 168 ≤ ofs B x) → (ofs B x < 176 ∨ 184 ≤ ofs B x) →
      t.mem x = u.mem x) → Env t B (8 * L) w → t.gpr .t1 = u.gpr .t1 →
      Prep t B L w c ∧ (∀ i, i < 8 * L → RKept w i → t.mem (B + BitVec.ofNat 64 i) = s.mem (B + BitVec.ofNat 64 i)) ∧
        Frame [⟨B, 8 * L⟩, below s.sp 96] s.mem t.mem := by
    intro t hb et ht1
    have wq : ∀ d, d + 8 ≤ 8 * L → (d + 8 ≤ 160 ∨ 168 ≤ d) → (d + 8 ≤ 176 ∨ 184 ≤ d) →
        word t.mem B d = word u.mem B d := fun d hd h1 h2 =>
      Mem.readW_congr fun i hi => hb _ (by rw [VG.Proof.Bignum.ofs_off B (by omega_arith)]; omega)
        (by rw [VG.Proof.Bignum.ofs_off B (by omega_arith)]; omega)
    refine ⟨hu.prep.keep et (hu.prep.t1_of ht1) (fun d hd => ?_) (fun j hj => ?_), fun i hi hk => ?_, ?_⟩
    · obtain ⟨s0, s0'⟩ := slot_bounds (j := 0) hL (by decide)
      obtain ⟨s27', s27⟩ := slot_bounds (j := 27) hL (by decide)
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wq _ (by omega) (by omega) (by omega)
    · simp only [A, VG.Proof.Bignum.RISCV64.Pre.wordsVal_eq_wv]
      obtain ⟨sj, sj'⟩ := slot_bounds (j := j) hL (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide)
      exact VG.Proof.Bignum.wv_congr fun i hi => wq _ (by omega) (by omega) (by omega)
    · have h20 := hk.2 20 (by simp)
      have h22 := hk.2 22 (by simp)
      have hi' : i < 2 ^ 64 := by omega_arith
      rw [hb _ (by rw [ofs_byte B hi']; omega) (by rw [ofs_byte B hi']; omega)]
      exact keeps_byte hu.keeps hi hk.1
    · exact hu.frame.trans (frame_of_low (e := 184) (fun x hx => hb x (by omega) (by omega)) (by omega) _)
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) hu.a0) (fun hz => ?_) (fun hz => ?_)
  · have hr : Proof.MillerRabin.Round.round c a = false := by
      by_contra hc; simp [hc] at hz
    have st := hsu.st (d := 160) (n := 8) (by omega)
    refine WP.mono (WP.rdwr <| WP.keep [.t2] (Q := fun t => t.mem = u.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2)) (by
      simp only [sth, hStat]
      brun [hu.prep.env.s6, st, hsu.al8 (d := 160) (by omega) (by decide), exec_li (show imm12 2 by decide)])
      (by decide)) fun t ⟨⟨tm, kt⟩, trd, twr, tsp⟩ => ?_
    have et := hu.prep.env.keep kt (by decide)
    have wo := writeW_outside u.mem B (d := 8 * hStat) (BitVec.ofNat 64 2) (by simp only [hStat]; omega)
    obtain ⟨p, kk, fr⟩ := keepP t (fun x h1 _ => by rw [tm]; exact wo x (by simpa only [hStat] using h1)) et
      (kt.gpr (by decide))
    refine ⟨p, ?_, ?_, kk, fr, trd.trans hu.rd, twr.trans hu.wr, tsp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, (writeW_outside _ _ _ (by simp only [hStat]; omega)).word (by simp only [hStat, hIdx]; omega)
        (by simp only [hIdx]; omega), kw _ (by simp only [hIdx]; omega) (by simp only [hIdx]; kept_tac), hI]
      rfl
    · rw [kt.gpr (fun hm => h2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; decide)),
        hu.cs r hr h1]
  · have hr : Proof.MillerRabin.Round.round c a = true := by
      by_contra hc; simp [hc] at hz
    have kI : word u.mem B (8 * hIdx) = BitVec.ofNat 64 I := by
      rw [kw _ (by simp only [hIdx]; omega) (by simp only [hIdx]; kept_tac), hI]
    have kU : word u.mem B (8 * hUni) = BitVec.ofNat 64 U := by
      rw [kw _ (by simp only [hUni]; omega) (by simp only [hUni]; kept_tac), hU]
    have kC : word u.mem B (8 * hChecks) = BitVec.ofNat 64 ch := by
      rw [kw _ (by simp only [hChecks]; omega) (by simp only [hChecks]; kept_tac), hch]
    refine WP.mono (WP.rdwr (passed_ok hu.prep.env kI kU kC hI' hU' hch')) fun t ⟨⟨tm, kt⟩, trd, twr, tsp⟩ => ?_
    have et := hu.prep.env.keep kt (by decide)
    have wo1 := writeW_outside u.mem B (d := 8 * hIdx) (BitVec.ofNat 64 (I + 1)) (by simp only [hIdx]; omega)
    have wo2 := writeW_outside (u.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 (I + 1))) B (d := 8 * hStat)
      (BitVec.ofNat 64 (statOf I U ch)) (by simp only [hStat]; omega)
    obtain ⟨p, kk, fr⟩ := keepP t (fun x h1 h2 => by
      rw [tm]; exact (wo2 x (by simpa only [hStat] using h1)).trans (wo1 x (by simpa only [hIdx] using h2))) et
      (kt.gpr (by decide))
    refine ⟨p, ?_, ?_, kk, fr, trd.trans hu.rd, twr.trans hu.wr, tsp.trans hu.sp, fun r hr h1 h2 => ?_⟩
    · rw [tm, hr]; exact word_writeW_self _ _ _ _
    · rw [tm, hr, (writeW_outside _ _ _ (by simp only [hStat]; omega)).word (by simp only [hStat, hIdx]; omega)
        (by simp only [hIdx]; omega)]
      exact word_writeW_self _ _ _ _
    · rw [kt.gpr h2, hu.cs r hr h1]

end VG.Proof.RsaKeyGen.RISCV64.Cand
