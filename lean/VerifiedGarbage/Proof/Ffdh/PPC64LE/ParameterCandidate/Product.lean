module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Trial
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Product
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Entry
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Mem

-- separate module: its proofs build in parallel with those of `TestsFn` and `Residue`, which `Main` also imports

/-!
# An FFDH parameter candidate on PPC64LE: trial division by products

`prodLoad_ok`, `prodInv_ok`: the product `M` of four of the table's entries
and `−M⁻¹ mod 2⁶⁴`; `prodReduce_ok`: the candidate reduced modulo `M`
(`redc64_math`); `prodEntry_ok`: an entry's test on the residue
(`acc_entry_math`); `prodGroup_ok` and `prodLoop_ok`: the groups, until one
divides.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen
open VG.Proof.Mont (w32 val32 word_eq_w32)
open VG.PPC64LE.RegUpd (gpr_writeCarry ca_writeCarry mem_writeCarry)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hBad)
open VG.Proof.Ffdh.ParameterCandidate (redc64_math prod_word_math wordProd wordProd_facts dvd_wordProd
  acc_entry_math)

/-- The table's first `N` entries at `T`, readable. -/
def TabRows (T : Addr) (N : Nat) (s : State) : Prop :=
  ∀ k < N, s.mem.readW (T + BitVec.ofNat 64 (8 * k)) 64 = BitVec.ofNat 64 (TrialTable32.entry k) ∧
    InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * k)) 8

/-- An entry's low half is its prime. -/
theorem tab_low {m : Mem} {T : Addr} {k : Nat} (hk : k < 1024)
    (h : m.readW (T + BitVec.ofNat 64 (8 * k)) 64 = BitVec.ofNat 64 (TrialTable32.entry k)) :
    (m.readW (T + BitVec.ofNat 64 (8 * k)) 32).toNat = tabEntry k := by
  have e := word_eq_w32 m T (8 * k)
  have hb := VG.Proof.RsaKeyGen.TrialTable32.entry_bound hk
  have hl := VG.Proof.RsaKeyGen.TrialTable32.entry_low hk
  have hx : w32 m T (8 * k) < 2 ^ 32 := (m.readW (VG.Proof.Mont.off T (8 * k)) 32).isLt
  simp only [VG.Proof.Mont.word, VG.Proof.Mont.off] at e hx
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at e
  show w32 m T (8 * k) = tabEntry k
  rw [← hl, e]
  omega

theorem tab_addr (T : Addr) (k j : Nat) :
    T + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * j) = T + BitVec.ofNat 64 (8 * (k + j)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- `prodLoad`: `r0 :=` the product of the four entries of group `i`. -/
theorem prodLoad_ok {u : State} {T : Addr} {i N : Nat} (h23 : u.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * i)))
    (hi : 4 * i + 4 ≤ N) (hN : N ≤ 1024) (htab : TabRows T N u) :
    WP isa (.block prodLoad) u fun t => (t.gpr .r0 = BitVec.ofNat 64 (wordProd i) ∧ t.mem = u.mem) ∧
      Keep [.r0, .r9] u t := by
  have row : ∀ j < 4, (u.mem.readW (u.gpr .r23 + BitVec.ofNat 64 (8 * j)) 32).toNat = tabEntry (4 * i + j) ∧
      InRegions (u.rd ++ u.wr) (u.gpr .r23 + BitVec.ofNat 64 (8 * j)) 4 := fun j hj => by
    rw [h23, tab_addr]
    obtain ⟨hv, hr⟩ := htab (4 * i + j) (by omega)
    exact ⟨tab_low (by omega) hv, by
      have := VG.CallLay.inRegions_sub (off := 0) (l := 4) hr (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  obtain ⟨v0, r0⟩ := row 0 (by decide)
  obtain ⟨v1, r1⟩ := row 1 (by decide)
  obtain ⟨v2, r2⟩ := row 2 (by decide)
  obtain ⟨v3, r3⟩ := row 3 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.add_zero] at v0 r0
  simp only [Nat.reduceMul] at v1 r1 v2 r2 v3 r3
  have b0 := (VG.Proof.RsaKeyGen.tabEntry_facts (i := 4 * i) (by omega)).2.2
  have b1 := (VG.Proof.RsaKeyGen.tabEntry_facts (i := 4 * i + 1) (by omega)).2.2
  have b2 := (VG.Proof.RsaKeyGen.tabEntry_facts (i := 4 * i + 2) (by omega)).2.2
  have b3 := (VG.Proof.RsaKeyGen.tabEntry_facts (i := 4 * i + 3) (by omega)).2.2
  refine WP.keep _ ?_ (by decide)
  simp only [prodLoad]
  prun [r0, r1, r2, r3, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth, v0, v1, v2, v3, BitVec.toNat_ofNat]
  unfold wordProd
  have h01 : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 26 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b0 (Nat.le_of_lt b1) (by omega)) (by decide)
  have h012 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 39 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h01 (Nat.le_of_lt b2) (by omega)) (by decide)
  have h0123 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) * tabEntry (4 * i + 3) < 2 ^ 52 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h012 (Nat.le_of_lt b3) (by omega)) (by decide)
  rw [Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) < 2 ^ 64), Nat.mod_eq_of_lt (by omega : tabEntry (4 * i + 1) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i + 2) < 2 ^ 64), Nat.mod_eq_of_lt (by omega : tabEntry (4 * i + 3) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) *
      tabEntry (4 * i + 3) < 2 ^ 64)]

theorem prodInv_split : prodInv = ([.logic .or .r12 .r0 .r0] : List Instr) ++ (newtonStep ++ (newtonStep ++
    (newtonStep ++ (newtonStep ++ (newtonStep ++ ([.li .r3 0, .sub .r12 .r3 .r12, .logic .or .r8 .r0 .r0] :
      List Instr)))))) := by
  simp only [prodInv, List.append_assoc]

/-- `prodInv`: `r12 := −M⁻¹ mod 2⁶⁴` for the odd `M` in `r0`, and `M` into
`r8`. -/
theorem prodInv_ok {u : State} {M : Nat} (h0 : u.gpr .r0 = BitVec.ofNat 64 M) (hM : M < 2 ^ 64)
    (hodd : M % 2 = 1) :
    WP isa (.block prodInv) u fun t =>
      (t.gpr .r8 = BitVec.ofNat 64 M ∧ t.gpr .r0 = BitVec.ofNat 64 M ∧ (M * (t.gpr .r12).toNat + 1) % 2 ^ 64 = 0 ∧
        t.mem = u.mem) ∧ Keep [.r3, .r4, .r8, .r12] u t := by
  have hMv : (u.gpr .r0).toNat = M := by rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
  rw [prodInv_split, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = u.gpr .r0 ∧ t.gpr .r0 = u.gpr .r0 ∧ t.mem = u.mem)
    (by prun; exact BitVec.or_self) (by decide)) fun t₀ ⟨⟨h12, h0', hm₀⟩, k₀⟩ => ?_
  have e₀ : (((t₀.gpr .r0).toNat : Int) * (t₀.gpr .r12).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [h0', h12, hMv]
    have h1 := VG.Proof.Bignum.odd_sq _ hodd
    have h2 : ((M : Int) * M) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show ((M : Int) * M - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₄ (j := 32) (by decide) (VG.Proof.Bignum.emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨⟨e₅, hb₅, hm₅⟩, k₅⟩ => ?_
  have hb : t₅.gpr .r0 = u.gpr .r0 := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans h0'))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb, hMv] at e₅
  have hm : t₅.mem = u.mem := by rw [hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]
  refine WP.mono (WP.keep [.r3, .r8, .r12] (Q := fun t => t.gpr .r12 = 0 - t₅.gpr .r12 ∧
      t.gpr .r8 = u.gpr .r0 ∧ t.gpr .r0 = u.gpr .r0 ∧ t.mem = u.mem) (by prun [hb, hm]; exact ⟨rfl, BitVec.or_self⟩) (by decide))
    fun t ⟨⟨t12, t8, t0, tm⟩, k⟩ => ⟨⟨by rw [t8, h0], by rw [t0, h0], ?_, tm⟩, (kk.trans k).mono (by decide)⟩
  rw [t12, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  have := VG.Proof.MillerRabin.PPC64LE.Search.neg_inv64 e₅
  rwa [Nat.mod_eq_of_lt (BitVec.isLt _)] at this

/-- Montgomery's step on the words: what `prodWord` leaves in `r7`. -/
def redcVal (acc x mv M : Nat) : Nat :=
  (acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
    ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64


/-- A carry bit, of a sum below `2⁶⁵`. -/
theorem carry_nat {X : Nat} (h : X < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ X)).toNat = X / 18446744073709551616 := by
  by_cases hx : 18446744073709551616 ≤ X
  · simp only [hx, decide_true, Bool.toNat_true]; omega
  · simp only [hx, decide_false, Bool.toNat_false]; omega

/-- `prodWord`'s result, from the machine's operations. -/
theorem redc_bv {acc x M : Nat} {mv : BitVec 64} (hacc : acc < 2 ^ 64) (hx : x < 2 ^ 64) (hM : M < 2 ^ 52) :
    BitVec.ofNat 64
      ((BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 acc).toNat + x) * mv).toNat *
          (BitVec.ofNat 64 M).toNat / 18446744073709551616)).toNat +
        (BitVec.ofNat 64 (BitVec.toNat (0 : BitVec 64) +
          (decide (18446744073709551616 ≤ (BitVec.ofNat 64 acc).toNat + x)).toNat)).toNat +
        (decide (18446744073709551616 ≤ (BitVec.ofNat 64 ((BitVec.ofNat 64 acc).toNat + x) * mv *
            BitVec.ofNat 64 M).toNat + (BitVec.ofNat 64 ((BitVec.ofNat 64 acc).toNat + x)).toNat)).toNat) =
      BitVec.ofNat 64 (redcVal acc x mv.toNat M) := by
  have e64 : (18446744073709551616 : Nat) = 2 ^ 64 := rfl
  have hmv := mv.isLt
  have ea : (BitVec.ofNat 64 acc).toNat = acc := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacc]
  have eM : (BitVec.ofNat 64 M).toNat = M := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [ea, eM]
  generalize hX : acc + x = X
  have hX2 : X < 2 * 18446744073709551616 := by omega
  have eq1 : (BitVec.ofNat 64 X * mv).toNat = X % 2 ^ 64 * mv.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have eq2 : (BitVec.ofNat 64 X * mv * BitVec.ofNat 64 M).toNat = X % 2 ^ 64 * mv.toNat % 2 ^ 64 * M % 2 ^ 64 := by
    rw [BitVec.toNat_mul, eq1, eM]
  have eq3 : (BitVec.ofNat 64 X).toNat = X % 2 ^ 64 := BitVec.toNat_ofNat _ _
  rw [eq1, eq2, eq3, show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.zero_add, carry_nat hX2]
  generalize hq : X % 2 ^ 64 * mv.toNat % 2 ^ 64 = q
  have hq' : q < 2 ^ 64 := hq ▸ Nat.mod_lt _ (by decide)
  have hqM : q * M < 2 ^ 64 * 2 ^ 52 := Nat.mul_lt_mul'' hq' hM
  have hlo : X % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hqm : q * M % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  rw [carry_nat (by omega)]
  unfold redcVal
  rw [hX, hq]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q * M / 18446744073709551616 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : X / 18446744073709551616 < 2 ^ 64)]
  simp only [e64]
  omega

theorem prodWord_ok {u : State} {B : Addr} {Z d acc M : Nat} {mv : BitVec 64} (hs : Scr u B Z)
    (h5 : u.gpr .r5 = off B d) (h7 : u.gpr .r7 = BitVec.ofNat 64 acc) (h8 : u.gpr .r8 = BitVec.ofNat 64 M)
    (h12 : u.gpr .r12 = mv) (h14 : u.gpr .r14 = 0) (hacc : acc < M + 2) (hM : M < 2 ^ 52) (hZ : d + 8 ≤ Z) :
    WP isa (.block prodWord) u fun t =>
      (t.gpr .r7 = BitVec.ofNat 64 (redcVal acc (word u.mem B d).toNat mv.toNat M) ∧ t.gpr .r5 = off B (d + 8) ∧
        t.mem = u.mem) ∧ Keep [.r0, .r3, .r4, .r5, .r7, .r9] u t := by
  refine WP.keep _ ?_ (by decide)
  have hld : InRegions (u.rd ++ u.wr) (off B d) 8 := hs.ld hZ
  simp only [prodWord]
  prun [h5, h7, h8, h12, h14, hld, BitVec.add_zero, exec_addc, exec_addze, exec_adde, exec_mulhu,
    gpr_writeCarry, ca_writeCarry, mem_writeCarry]
  exact redc_bv (by omega) (BitVec.isLt _) hM

/-- After `j` words of the pass. -/
def RInv (u : State) (B : Addr) (o M : Nat) (mv : BitVec 64) (j : Nat) (t : State) : Prop :=
  ((∃ acc, t.gpr .r7 = BitVec.ofNat 64 acc ∧ acc < M + 2 ∧ acc * 2 ^ (64 * j) % M = wv u.mem B o j % M) ∧
    t.gpr .r5 = off B (o + 8 * j) ∧ t.gpr .r8 = BitVec.ofNat 64 M ∧ t.gpr .r12 = mv ∧ t.gpr .r14 = 0 ∧
    t.mem = u.mem) ∧ Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r9, .r14] u t

/-- `prodReduce`: the `w` words of array 0 reduced modulo `M`. -/
theorem prodReduce_ok {u : State} {B : Addr} {Z o w M : Nat} {mv : BitVec 64} (hs : Scr u B Z)
    (h10 : u.gpr .r10 = off B o) (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h8 : u.gpr .r8 = BitVec.ofNat 64 M)
    (h12 : u.gpr .r12 = mv) (hinv : (M * mv.toNat + 1) % 2 ^ 64 = 0) (hM : M < 2 ^ 52) (hw : 1 ≤ w)
    (hw' : w ≤ 128) (hZ : o + 8 * w ≤ Z) :
    WP isa prodReduce u fun t =>
      ((∃ acc, t.gpr .r7 = BitVec.ofNat 64 acc ∧ acc < M + 2 ∧ acc * 2 ^ (64 * w) % M = wv u.mem B o w % M) ∧
        t.mem = u.mem) ∧ Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r9, .r14] u t := by
  unfold prodReduce
  refine WP.seq (WP.mono (WP.keep [.r5, .r6, .r7, .r14] (Q := fun v => v.gpr .r5 = off B o ∧
      v.gpr .r6 = BitVec.ofNat 64 w ∧ v.gpr .r7 = BitVec.ofNat 64 0 ∧ v.gpr .r14 = 0 ∧ v.mem = u.mem) ?_
      (by decide)) fun v ⟨⟨v5, v6, v7, v14, vm⟩, kv⟩ => ?_)
  · prun [h10, h11, BitVec.add_zero]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono (wp_countdown (cnt := .r6) (N := w) (by omega) (by omega) (RInv u B o M mv)
    (fun j hj t ⟨⟨⟨acc, t7, hacc, hv⟩, t5, t8, t12, t14, tm⟩, kt⟩ _ => ?_)
    ⟨⟨⟨0, v7, by omega, by simp [wv]⟩, by rw [v5, Nat.mul_zero, Nat.add_zero],
      by rw [kv.gpr .r8 (by decide), h8], by rw [kv.gpr .r12 (by decide), h12], v14, vm⟩, kv.mono (by decide)⟩ v6)
    fun t ⟨⟨hacc, _, _, _, _, tm⟩, kt⟩ => ⟨⟨hacc, tm⟩, kt⟩
  rw [WP.block_append_iff]
  have ht : Scr t B Z := hs.congr kt.wr
  refine WP.mono (prodWord_ok ht t5 t7 t8 t12 t14 hacc hM (by omega)) fun t₁ ⟨⟨a7, a5, am⟩, k1⟩ => ?_
  refine WP.mono (subi_ok t₁ .r6 (by decide)) fun t₂ e => ?_
  subst e
  have hx : (word t.mem B (o + 8 * j)).toNat < 2 ^ 64 := BitVec.isLt _
  obtain ⟨hlt, hmod⟩ := redc64_math (M := M) (mv := mv.toNat) (acc := acc) (x := (word t.mem B (o + 8 * j)).toNat)
    (by rw [Nat.mul_comm] at hinv ⊢; exact hinv) hacc hx
  have hk := kt.trans (k1.trans (Keep.write t₁ .r6 (t₁.gpr .r6 - BitVec.ofNat 64 1)))
  rw [tm] at a7 hlt hmod
  refine ⟨⟨⟨⟨redcVal acc (word u.mem B (o + 8 * j)).toNat mv.toNat M, ?_, hlt, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
    hk.mono (by decide)⟩, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a7
  · have hmod' : redcVal acc (word u.mem B (o + 8 * j)).toNat mv.toNat M * 2 ^ 64 % M =
        (acc + (word u.mem B (o + 8 * j)).toNat) % M := hmod
    have key := prod_word_math (M := M) (j := j) (V := wv u.mem B o j) hmod' hv
    rw [show wv u.mem B o (j + 1) = wv u.mem B o j + 2 ^ (64 * j) * (word u.mem B (o + 8 * j)).toNat from rfl]
    exact key
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [a5, show o + 8 * j + 8 = o + 8 * (j + 1) by omega]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k1.gpr .r8 (by decide), t8]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k1.gpr .r12 (by decide), t12]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k1.gpr .r14 (by decide), t14]
  · rw [mem_write, am, tm]
  · simp only [gpr_write, ↓reduceIte]
    rw [k1.gpr .r6 (by decide)]

/-- `r6 := ` the flag of `acc ∈ {0, s}` (`r3` and `r8`), or'ed into `r25`. -/
theorem flagOr_bits {p q : Prop} [Decidable p] [Decidable q] {b : Bool} :
    BitVec.ofNat 64 (if b then 1 else 0) ||| (BitVec.ofNat 64 (if p then 1 else 0) |||
      BitVec.ofNat 64 (if q then 1 else 0)) =
      BitVec.ofNat 64 (if (b || decide (p ∨ q)) then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> cases b <;> simp [hp, hq]

/-- Entry `4 i + j` tested on `acc`, the candidate `c` reduced modulo the
group's product (header word `hTrialN`): `r25 :=` the flag of it or of
an earlier entry dividing `c`. -/
theorem prodEntry_ok {u : State} {B T : Addr} {Z i N j w acc c : Nat} {b : Bool} (hs : Scr u B Z)
    (h31 : u.gpr .r31 = B) (h23 : u.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * i))) (htab : TabRows T N u)
    (hi : 4 * i + 4 ≤ N) (hN : N ≤ 1024) (hj : j < 4) (hacc : word u.mem B (8 * hTrialN) = BitVec.ofNat 64 acc)
    (hacc' : acc < 2 ^ 64) (hval : acc * 2 ^ (64 * w) % wordProd i = c % wordProd i)
    (h25 : u.gpr .r25 = BitVec.ofNat 64 (if b then 1 else 0)) (hZ : 8 * hTrialN + 8 ≤ Z) :
    WP isa (prodEntry j) u fun t =>
      (t.gpr .r25 = BitVec.ofNat 64 (if (b || decide (c % tabEntry (4 * i + j) = 0)) then 1 else 0) ∧
        t.mem = u.mem) ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r0, .r25] u t := by
  have hk : 4 * i + j < 1024 := by omega
  obtain ⟨hodd, h3, h8162⟩ := VG.Proof.RsaKeyGen.tabEntry_facts hk
  have hinv := VG.Proof.RsaKeyGen.TrialTable32.inverse_entry hk
  have hlo := VG.Proof.RsaKeyGen.TrialTable32.entry_low hk
  have hhi := VG.Proof.RsaKeyGen.TrialTable32.entry_high hk
  have heb := VG.Proof.RsaKeyGen.TrialTable32.entry_bound hk
  have hsv := (TrialTable32.inverse (BitVec.ofNat 32 (tabEntry (4 * i + j)))).isLt
  have hdvd : tabEntry (4 * i + j) ∣ wordProd i := dvd_wordProd hj
  obtain ⟨hT, hTr⟩ := htab (4 * i + j) (by omega)
  have ea : u.gpr .r23 + BitVec.ofNat 64 (8 * j) = T + BitVec.ofNat 64 (8 * (4 * i + j)) := by
    rw [h23, tab_addr]
  generalize tabEntry (4 * i + j) = s at hodd h3 h8162 hinv hlo hhi hsv hdvd ⊢
  generalize (TrialTable32.inverse (BitVec.ofNat 32 s)).toNat = sv at hinv hhi hsv
  unfold prodEntry
  refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5, .r8, .r9] (Q := fun v => v.gpr .r8 = BitVec.ofNat 64 s ∧
      v.gpr .r9 = BitVec.ofNat 64 sv ∧ v.gpr .r3 = BitVec.ofNat 64 0 ∧ v.gpr .r5 = off B (8 * hTrialN) ∧
      v.gpr .r4 = BitVec.ofNat 64 (2 * 1) ∧ v.mem = u.mem) ?_ (by rfl)) fun v ⟨⟨v8, v9, v3, v5, v4, vm⟩, kv⟩ => ?_)
  · have hv8 : u.mem.readW (u.gpr .r23 + BitVec.ofNat 64 (8 * j)) 64 = BitVec.ofNat 64 (TrialTable32.entry (4 * i + j)) := by
      rw [ea]; exact hT
    have hr8 : InRegions (u.rd ++ u.wr) (u.gpr .r23 + BitVec.ofNat 64 (8 * j)) 8 := by rw [ea]; exact hTr
    have hs8 : BitVec.ofNat 64 (TrialTable32.entry (4 * i + j)) >>> 32 = BitVec.ofNat 64 sv ∧
        BitVec.ofNat 64 (TrialTable32.entry (4 * i + j)) <<< 32 >>> 32 = BitVec.ofNat 64 s := by
      refine ⟨?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt heb, hhi, Nat.mod_eq_of_lt (by omega)]
      · apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt heb,
          show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
          Nat.mul_div_cancel _ (Nat.two_pow_pos 32), hlo, Nat.mod_eq_of_lt (by omega)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, BitVec.add_zero] at hv8 hr8 hs8 <;>
      simp only [hTrialN] <;>
      prun [hv8, hr8, h31, BitVec.add_zero, hs8.1, hs8.2]
  have hv' : Scr v B Z := hs.congr kv.wr
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.PPC64LE.Trial.digits_ok hv' v5 v3 v4 v8 v9 (by omega) (by omega)
      hinv (by decide) (by decide) hZ)
    fun x ⟨⟨⟨acc2, x3, hacc2, hacv⟩, xm⟩, kx⟩ => ?_)
  have hv32 : val32 v.mem B (8 * hTrialN) (2 * 1) = acc := by
    rw [VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv, vm]
    show wv u.mem B (8 * hTrialN) 0 + 2 ^ (64 * 0) * (word u.mem B (8 * hTrialN + 8 * 0)).toNat = acc
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hacc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacc']
  rw [hv32] at hacv
  have hc := acc_entry_math (w := w) hdvd hval (by rw [show 64 * 1 = 64 from rfl] at hacv; exact hacv)
  have key : c % s = 0 ↔ acc2 = 0 ∨ acc2 = s := VG.Proof.RsaKeyGen.trial_div hodd hacc2 hc
  have x8 : x.gpr .r8 = BitVec.ofNat 64 s := (kx.gpr .r8 (by decide)).trans v8
  have x25 : x.gpr .r25 = BitVec.ofNat 64 (if b then 1 else 0) :=
    (kx.gpr .r25 (by decide)).trans ((kv.gpr .r25 (by decide)).trans h25)
  refine WP.mono (WP.keep [.r6, .r7, .r25] (Q := fun y =>
      y.gpr .r25 = BitVec.ofNat 64 (if (b || decide (acc2 = 0 ∨ acc2 = s)) then 1 else 0) ∧ y.mem = x.mem) ?_
      (by decide))
    fun y ⟨⟨y25, ym⟩, ky⟩ => ⟨⟨?_, by rw [ym, xm, vm]⟩, ((kv.trans kx).trans ky).mono (by decide)⟩
  · prun [x3, x8, x25, VG.Proof.RsaKeyGen.PPC64LE.Trial.zero_flag (show acc2 < 2 ^ 63 by omega),
      VG.Proof.RsaKeyGen.PPC64LE.Trial.eq_flag (show acc2 < 2 ^ 63 by omega) (show s < 2 ^ 63 by omega)]
    exact flagOr_bits
  · rw [y25, show decide (acc2 = 0 ∨ acc2 = s) = decide (c % s = 0) from decide_eq_decide.mpr key.symm]

/-- Whether one of group `i`'s four entries divides `c`. -/
def groupHit (c i : Nat) : Bool :=
  ((((false || decide (c % tabEntry (4 * i + 0) = 0)) || decide (c % tabEntry (4 * i + 1) = 0)) ||
    decide (c % tabEntry (4 * i + 2) = 0)) || decide (c % tabEntry (4 * i + 3) = 0))

theorem trialPrefix_group (c i : Nat) :
    VG.Proof.RsaKeyGen.trialPrefix c (4 * (i + 1)) = (VG.Proof.RsaKeyGen.trialPrefix c (4 * i) || groupHit c i) := by
  rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by omega, VG.Proof.RsaKeyGen.trialPrefix_succ,
    VG.Proof.RsaKeyGen.trialPrefix_succ, VG.Proof.RsaKeyGen.trialPrefix_succ, VG.Proof.RsaKeyGen.trialPrefix_succ]
  simp only [groupHit, VG.Proof.RsaKeyGen.entryDivides, Bool.false_or, Bool.or_assoc, Nat.add_zero]

/-- `(n − 4) & (f − 1)`: 0 for the flag `f = 1`, `n − 4` for `f = 0`. -/
theorem count4_flag {n : Nat} (hn : 4 ≤ n) (b : Bool) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 4) &&& (BitVec.ofNat 64 (if b then 1 else 0) - BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (if b then 0 else n - 4) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hn]
  · simp only [↓reduceIte]
    rw [show BitVec.ofNat 64 1 - BitVec.ofNat 64 1 = 0#64 by decide, BitVec.and_zero]

/-- The registers a group writes. -/
def groupRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r22, .r23, .r24, .r25]

/-- Group `i`: `r22 :=` its flag of dividing `c` (array 0), `r23` to the
next, `r24` four fewer or 0 on a hit; header word `hTrialN` the only one
written. -/
theorem prodGroup_ok {v : State} {B T : Addr} {Z o w c i N n : Nat} (hs : Scr v B Z)
    (h10 : v.gpr .r10 = off B o) (h11 : v.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h31 : v.gpr .r31 = B)
    (hc : wv v.mem B o w = c) (hw : 1 ≤ w) (hw' : w ≤ 128) (hZ : o + 8 * w ≤ Z) (hZ' : 216 ≤ Z)
    (h23 : v.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * i))) (htab : TabRows T N v) (hi : 4 * i + 4 ≤ N)
    (hN : N ≤ 1024) (hdj : ∀ m', Frm B [(8 * hTrialN, 8)] v.mem m' →
      ∀ k < N, m'.readW (T + BitVec.ofNat 64 (8 * k)) 64 = v.mem.readW (T + BitVec.ofNat 64 (8 * k)) 64)
    (h24 : v.gpr .r24 = BitVec.ofNat 64 n) (hn : 4 ≤ n) :
    WP isa prodGroup v fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if groupHit c i then 1 else 0) ∧
        t.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * (i + 1))) ∧
        t.gpr .r24 = BitVec.ofNat 64 (if groupHit c i then 0 else n - 4) ∧
        Frm B [(8 * hTrialN, 8)] v.mem t.mem) ∧ Keep groupRegs v t := by
  have hM := wordProd_facts (i := i) (by omega)
  unfold prodGroup
  have hli : WP isa (.block (prodLoad ++ prodInv)) v fun b =>
      (b.gpr .r8 = BitVec.ofNat 64 (wordProd i) ∧ (wordProd i * (b.gpr .r12).toNat + 1) % 2 ^ 64 = 0 ∧
        b.mem = v.mem) ∧ Keep [.r0, .r3, .r4, .r8, .r9, .r12] v b :=
    WP.block_append (WP.mono (prodLoad_ok h23 hi hN htab) fun a ⟨⟨a0, am⟩, ka⟩ =>
      WP.mono (prodInv_ok a0 (by omega) hM.1) fun b ⟨⟨b8, _, binv, bm⟩, kb⟩ =>
        ⟨⟨b8, binv, bm.trans am⟩, (ka.trans kb).mono (by decide)⟩)
  refine WP.seq (WP.mono hli fun b ⟨⟨b8, binv, bm⟩, kb⟩ => ?_)
  have hsb : Scr b B Z := hs.congr kb.wr
  refine WP.seq (WP.mono (prodReduce_ok hsb ((kb.gpr .r10 (by decide)).trans h10)
      ((kb.gpr .r11 (by decide)).trans h11) b8 rfl binv hM.2 hw hw' hZ)
    fun d ⟨⟨⟨acc, d7, hacc, hval⟩, dm⟩, kd⟩ => ?_)
  rw [bm, hc] at hval
  have kbd := kb.trans kd
  have d31 : d.gpr .r31 = B := (kbd.gpr .r31 (by decide)).trans h31
  have st208 : InRegions d.wr (B + BitVec.ofNat 64 208) 8 := by
    rw [kbd.wr]; exact hs.st (d := 208) (by omega)
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun e => e.gpr .r25 = 0 ∧
      e.mem = v.mem.writeW (B + BitVec.ofNat 64 (8 * hTrialN)) (BitVec.ofNat 64 acc)) ?_ (by decide))
    fun e ⟨⟨e25, em⟩, ke⟩ => ?_)
  · simp only [VG.Impl.MillerRabin.PPC64LE.Search.sth, hTrialN]
    prun [d31, st208, d7, dm, bm]
    rfl
  have hacc' : acc < 2 ^ 64 := by omega
  have ke' := kbd.trans ke
  have fe : Frm B [(8 * hTrialN, 8)] v.mem e.mem := by
    rw [em]; exact VG.Proof.MillerRabin.PPC64LE.Search.frm_writeW (a := 208) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  have tabE : ∀ {f : State}, f.mem = e.mem → f.rd = e.rd → f.wr = e.wr → TabRows T N f := fun fm frd fwr k hk => by
    obtain ⟨a, b'⟩ := htab k hk
    refine ⟨by rw [fm, hdj _ fe k hk]; exact a, ?_⟩
    rw [frd, fwr, ke.rd, ke.wr, kd.rd, kd.wr, kb.rd, kb.wr]; exact b'
  have hw208 : ∀ {f : State}, f.mem = e.mem → word f.mem B (8 * hTrialN) = BitVec.ofNat 64 acc := fun fm => by
    rw [fm, em]; exact VG.Proof.MillerRabin.PPC64LE.Search.rw_self _ _ _
  have hse : Scr e B Z := hs.congr ke'.wr
  have e23 : e.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * i)) := (ke'.gpr .r23 (by decide)).trans h23
  have e31 : e.gpr .r31 = B := (ke'.gpr .r31 (by decide)).trans h31
  refine WP.seq (WP.mono (prodEntry_ok (j := 0) (b := false) hse e31 e23 (tabE rfl rfl rfl) hi hN (by decide)
      (hw208 rfl) hacc' hval (by rw [e25]; rfl) (by simp only [hTrialN]; omega)) fun f₁ ⟨⟨f25, fm⟩, kf₁⟩ => ?_)
  refine WP.seq (WP.mono (prodEntry_ok (j := 1) (hse.congr kf₁.wr) ((kf₁.gpr .r31 (by decide)).trans e31)
      ((kf₁.gpr .r23 (by decide)).trans e23) (tabE fm kf₁.rd kf₁.wr) hi hN (by decide) (hw208 fm) hacc' hval f25
      (by simp only [hTrialN]; omega)) fun f₂ ⟨⟨f25', fm'⟩, kf₂⟩ => ?_)
  have k12 := kf₁.trans kf₂
  refine WP.seq (WP.mono (prodEntry_ok (j := 2) (hse.congr k12.wr) ((k12.gpr .r31 (by decide)).trans e31)
      ((k12.gpr .r23 (by decide)).trans e23) (tabE (fm'.trans fm) k12.rd k12.wr) hi hN (by decide)
      (hw208 (fm'.trans fm)) hacc' hval f25' (by simp only [hTrialN]; omega)) fun f₃ ⟨⟨f25'', fm''⟩, kf₃⟩ => ?_)
  have k13 := k12.trans kf₃
  refine WP.seq (WP.mono (prodEntry_ok (j := 3) (hse.congr k13.wr) ((k13.gpr .r31 (by decide)).trans e31)
      ((k13.gpr .r23 (by decide)).trans e23) (tabE (fm''.trans (fm'.trans fm)) k13.rd k13.wr) hi hN (by decide)
      (hw208 (fm''.trans (fm'.trans fm))) hacc' hval f25'' (by simp only [hTrialN]; omega))
    fun f₄ ⟨⟨f25''', fm'''⟩, kf₄⟩ => ?_)
  have k14 := k13.trans kf₄
  have f23 : f₄.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * i)) := (k14.gpr .r23 (by decide)).trans e23
  have f24 : f₄.gpr .r24 = BitVec.ofNat 64 n :=
    (k14.gpr .r24 (by decide)).trans ((ke'.gpr .r24 (by decide)).trans h24)
  refine WP.mono (WP.keep [.r6, .r22, .r23, .r24] (Q := fun t =>
      t.gpr .r22 = BitVec.ofNat 64 (if groupHit c i then 1 else 0) ∧
      t.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * (i + 1))) ∧
      t.gpr .r24 = BitVec.ofNat 64 (if groupHit c i then 0 else n - 4) ∧ t.mem = f₄.mem) ?_ (by decide))
    fun t ⟨⟨t22, t23, t24, tm⟩, kt⟩ => ⟨⟨t22, t23, t24, by rw [tm, fm''', fm'', fm']; rw [fm]; exact fe⟩,
      (((ke'.trans k14).trans kt)).mono (by decide)⟩
  have hg : f₄.gpr .r25 = BitVec.ofNat 64 (if groupHit c i then 1 else 0) := f25'''
  prun [hg, f23, f24, count4_flag hn, BitVec.or_self]
  show T + BitVec.ofNat 64 (8 * (4 * i) + 32) = _
  rw [show 8 * (4 * i) + 32 = 8 * (4 * (i + 1)) by omega]

theorem trialPrefix_mono_true {c m n : Nat} (hmn : m ≤ n) (h : VG.Proof.RsaKeyGen.trialPrefix c m = true) :
    VG.Proof.RsaKeyGen.trialPrefix c n = true := by
  unfold VG.Proof.RsaKeyGen.trialPrefix at *
  obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) hmn), hd⟩

/-- The loop's state with `m` groups left of `N / 4`: `k` groups tested,
none dividing `c`. -/
def LInv (u : State) (B T : Addr) (c N m : Nat) (v : State) : Prop :=
  ∃ k, m = N / 4 - k ∧ k < N / 4 ∧ (v.gpr .r23 = T + BitVec.ofNat 64 (8 * (4 * k)) ∧
    v.gpr .r24 = BitVec.ofNat 64 (N - 4 * k) ∧ VG.Proof.RsaKeyGen.trialPrefix c (4 * k) = false ∧
    Frm B [(8 * hTrialN, 8)] u.mem v.mem) ∧ Keep groupRegs u v

/-- The arguments of `prodLoop`. -/
structure LArgs (u : State) (B T : Addr) (Z o w c N : Nat) : Prop where
  scr : Scr u B Z
  r10 : u.gpr .r10 = off B o
  r11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r31 : u.gpr .r31 = B
  c : wv u.mem B o w = c
  w1 : 1 ≤ w
  w2 : w ≤ 128
  z : o + 8 * w ≤ Z
  o : 216 ≤ o
  tab : TabRows T N u
  n4 : N % 4 = 0
  n1 : 4 ≤ N
  n2 : N ≤ 1024
  dj : ∀ m', Frm B [(8 * hTrialN, 8)] u.mem m' →
    ∀ k < N, m'.readW (T + BitVec.ofNat 64 (8 * k)) 64 = u.mem.readW (T + BitVec.ofNat 64 (8 * k)) 64

/-- Whether the loop goes on after group `k`: none of its entries divides
`c`, and it is not the last. -/
def lgo (c N k : Nat) : Bool := !groupHit c k && decide (k + 1 ≠ N / 4)

/-- One group: the loop goes on exactly when it does not divide and is not
the last. -/
theorem lstep_ok {u : State} {B T : Addr} {Z o w c N m : Nat} (ha : LArgs u B T Z o w c N) {v : State}
    (hI : LInv u B T c N m v) :
    WP isa prodGroup v fun t =>
      isa.eval (.nonzero .d .r24) t = some (lgo c N (N / 4 - m)) ∧
        (lgo c N (N / 4 - m) = false →
          (t.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix c N then 1 else 0) ∧
          Frm B [(8 * hTrialN, 8)] u.mem t.mem) ∧ Keep groupRegs u t) ∧
        (lgo c N (N / 4 - m) = true → 0 < m ∧ LInv u B T c N (m - 1) t) := by
  obtain ⟨k, hm, hk, ⟨v23, v24, hpre, vf⟩, kv⟩ := hI
  have hkm : N / 4 - m = k := by omega
  rw [hkm]
  have hnw := ha.scr.nowrap
  have ho := ha.o
  have hzw := ha.z
  have hn4 := ha.n4
  have hn2 := ha.n2
  have hn1 := ha.n1
  have hsv : Scr v B Z := ha.scr.congr kv.wr
  have hcv : wv v.mem B o w = c := by
    rw [vf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hTrialN]; omega) (by omega)]
    exact ha.c
  have htv : TabRows T N v := fun j hj => by
    obtain ⟨a, b⟩ := ha.tab j hj
    exact ⟨by rw [ha.dj _ vf j hj]; exact a, by rw [kv.rd, kv.wr]; exact b⟩
  have hdv : ∀ m', Frm B [(8 * hTrialN, 8)] v.mem m' →
      ∀ j < N, m'.readW (T + BitVec.ofNat 64 (8 * j)) 64 = v.mem.readW (T + BitVec.ofNat 64 (8 * j)) 64 :=
    fun m' hf j hj => by rw [ha.dj _ (vf.trans hf) j hj, ha.dj _ vf j hj]
  refine WP.mono (prodGroup_ok hsv ((kv.gpr .r10 (by decide)).trans ha.r10) ((kv.gpr .r11 (by decide)).trans ha.r11)
    ((kv.gpr .r31 (by decide)).trans ha.r31) hcv ha.w1 ha.w2 ha.z (by omega) v23 htv (by omega) ha.n2 hdv v24
    (by omega)) fun t ⟨⟨t22, t23, t24, tf⟩, kt⟩ => ?_
  have kut := kv.trans kt
  have kut' : Keep groupRegs u t := kut.mono (by intro r hr; simp only [List.mem_append] at hr; rcases hr with hr | hr <;> exact hr)
  have hpre' := trialPrefix_group c k
  rw [hpre, Bool.false_or] at hpre'
  by_cases hit : groupHit c k
  · have hg : lgo c N k = false := by simp [lgo, hit]
    simp only [hit, ↓reduceIte] at t22 t24
    refine ⟨?_, fun _ => ⟨⟨?_, vf.trans tf⟩, kut'⟩, fun h => absurd (hg ▸ h) (by decide)⟩
    · rw [VG.PPC64LE.eval_nonzero, t24, hg]; rfl
    · rw [t22, trialPrefix_mono_true (m := 4 * (k + 1)) (by omega) (by rw [hpre']; exact hit)]
      rfl
  · have hit' : groupHit c k = false := Bool.eq_false_iff.mpr hit
    simp only [hit', Bool.false_eq_true, ↓reduceIte] at t22 t24
    rw [hit'] at hpre'
    by_cases hl : k + 1 = N / 4
    · have hN : 4 * (k + 1) = N := by omega
      have hg : lgo c N k = false := by simp [lgo, hit', hl]
      refine ⟨?_, fun _ => ⟨⟨?_, vf.trans tf⟩, kut'⟩, fun h => absurd (hg ▸ h) (by decide)⟩
      · rw [VG.PPC64LE.eval_nonzero_ofNat' _ _ (by omega) t24, hg]
        simp only [Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not]
        omega
      · rw [t22, ← hN, hpre']; rfl
    · have hg : lgo c N k = true := by simp [lgo, hit', hl]
      refine ⟨?_, fun h => absurd (hg ▸ h) (by decide), fun _ => ?_⟩
      · rw [VG.PPC64LE.eval_nonzero_ofNat' _ _ (by omega) t24, hg]
        simp only [Option.some.injEq, decide_eq_true_eq]
        omega
      · exact ⟨by omega, k + 1, by omega, by omega, ⟨t23, by rw [t24, show N - 4 * k - 4 = N - 4 * (k + 1) by omega],
          hpre', vf.trans tf⟩, kut'⟩

/-- `prodLoop`: the first `N` entries, by groups of four, until one divides. -/
theorem prodLoop_ok {u : State} {B T : Addr} {Z o w c N : Nat} (ha : LArgs u B T Z o w c N)
    (h23 : u.gpr .r23 = T) (h24 : u.gpr .r24 = BitVec.ofNat 64 N) :
    WP isa prodLoop u fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix c N then 1 else 0) ∧
        Frm B [(8 * hTrialN, 8)] u.mem t.mem) ∧ Keep groupRegs u t := by
  have hn1 := ha.n1
  refine WP.loop (M := isa) (LInv u B T c N) (fun m v hI => ?_) (N / 4) u
    ⟨0, by omega, by omega, ⟨by rw [h23]; exact (BitVec.add_zero T).symm, by rw [h24, Nat.mul_zero,
      Nat.sub_zero], by simp [VG.Proof.RsaKeyGen.trialPrefix], Frm.refl _ _ _⟩, Keep.refl _ _⟩
  refine WP.mono (lstep_ok ha hI) fun t ⟨he, hf, ht⟩ => ?_
  cases e : lgo c N (N / 4 - m)
  · exact .inl ⟨by rw [he, e], hf e⟩
  · obtain ⟨hm, hI'⟩ := ht e
    exact .inr ⟨by rw [he, e], m - 1, by omega, hI'⟩

/-! ## In the candidate's working space -/

/-- The table's address and the count `n`. -/
theorem MB.prodA {p : PP} {x : Nat} {B : Prop} {T : Addr} {u : State} (h : MB p T x B u) (n : Nat)
    (hn : n < 2 ^ 15) :
    WP isa (.block [.adrSym .r23 TrialTable32.symbol, .li .r24 n]) u fun v =>
      (v.gpr .r23 = T ∧ v.gpr .r24 = BitVec.ofNat 64 n ∧ v.mem = u.mem) ∧
      (∀ r, r ∉ [Reg.r23, Reg.r24] → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      v.syms = u.syms := by
  refine WP.cons (exec_adrSym (by decide)) ?_
  prun [h.tab.sym, exec_li hn]
  refine ⟨fun r hr => ?_, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  simp only [h1, h2, ↓reduceIte]

/-- The table's address and the count for the requested width. -/
theorem MB.prodC {p : PP} {x : Nat} {B : Prop} {T : Addr} {u : State} (h : MB p T x B u) :
    WP isa (.block [.adrSym .r23 TrialTable32.symbol, ldh .r3 hBits, .subi .r3 .r3 1025, .lsr .d .r3 .r3 63,
      .lsl .r3 .r3 9, .li .r4 1024, .sub .r24 .r4 .r3]) u fun v =>
      (v.gpr .r23 = T ∧ v.gpr .r24 = BitVec.ofNat 64 (trialN p.bits) ∧ v.mem = u.mem) ∧
      (∀ r, r ∉ [Reg.r3, Reg.r4, Reg.r23, Reg.r24] → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
      v.sp = u.sp ∧ v.syms = u.syms := by
  have hb2 := h.st.dims.b2
  have l40 : InRegions (u.rd ++ u.wr) (p.B + BitVec.ofNat 64 40) 8 := h.st.ld (d := 40) (by decide)
  have hbits : u.mem.readW (p.B + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 p.bits := h.st.args.bits'
  refine WP.cons (exec_adrSym (by decide)) ?_
  simp only [ldh, hBits]
  prun [h.tab.sym, h.st.r31, l40, hbits, trialCount_eq hb2]
  refine ⟨fun r hr => ?_, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  have h3 : r ≠ .r3 := fun h => hr (by subst h; decide)
  have h4 : r ≠ .r4 := fun h => hr (by subst h; decide)
  simp only [h1, h2, h3, h4, ↓reduceIte]

/-- What `prodLoop` needs, once the table's address and the count are in
`r23` and `r24`. -/
theorem MB.largs {p : PP} {x : Nat} {B : Prop} {T : Addr} {u v : State} {N : Nat} (h : MB p T x B u)
    (vm : v.mem = u.mem) (vg : ∀ r, r ∉ [Reg.r3, Reg.r4, Reg.r23, Reg.r24] → v.gpr r = u.gpr r) (vrd : v.rd = u.rd)
    (vwr : v.wr = u.wr) (hN4 : N % 4 = 0) (hN1 : 4 ≤ N) (hN2 : N ≤ 1024) :
    LArgs v p.B T p.Z (slot (wOf p.bits) 0) (wOf p.bits) x N := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := by simp [slot, hdrBytes]
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  refine ⟨h.st.scr.congr vwr, by rw [vg _ (by decide)]; exact h.ph.r10, by rw [vg _ (by decide)]; exact h.ph.r11,
    by rw [vg _ (by decide)]; exact h.st.r31, by rw [vm]; exact h.n, by omega_arith, by omega_arith,
    by rw [hsl]; omega_arith, by rw [hsl]; omega_arith, fun i hi => ⟨by rw [vm]; exact h.tab.tab i (by omega_arith), ?_⟩,
    hN4, hN1, hN2, fun m' hf k hk => ?_⟩
  · refine ⟨_, by rw [vrd]; exact List.mem_append_left _ h.tab.rd, ?_⟩
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    have := h.tab.fit
    rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · have ht := (h.tab.step (t := { u with mem := m' }) rfl (by rw [← vm]; exact hf)
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hTrialN]; omega_arith) rfl).tab k (by omega)
    rw [vm]
    exact ht.trans (h.tab.tab k (by omega)).symm

/-- The loop's flag or'ed into `hBad`. -/
theorem MB.orBadP {p : PP} {x : Nat} {B : Prop} {T : Addr} {u w : State} {n : Nat} (h : MB p T x B u)
    (w22 : w.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix x n then 1 else 0))
    (wf : Frm p.B [(8 * hTrialN, 8)] u.mem w.mem)
    (wg : ∀ r, r ∉ [Reg.r3, Reg.r4, Reg.r23, Reg.r24] ++ groupRegs → w.gpr r = u.gpr r)
    (wrd : w.rd = u.rd) (wwr : w.wr = u.wr) (wsp : w.sp = u.sp) (syw : w.syms = u.syms) :
    WP isa (.block [ldh .r5 hBad, .logic .or .r5 .r5 .r22, sth .r5 hBad]) w
      (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false)) := by
  have l200 : InRegions (w.rd ++ w.wr) (p.B + BitVec.ofNat 64 200) 8 := by
    rw [wrd, wwr]; exact h.st.ld (d := 200) (by decide)
  have s200 : InRegions w.wr (p.B + BitVec.ofNat 64 200) 8 := by rw [wwr]; exact h.st.st (d := 200) (by decide)
  have w31 : w.gpr .r31 = p.B := (wg _ (by decide)).trans h.st.r31
  have hold : w.mem.readW (p.B + BitVec.ofNat 64 200) 64 = word u.mem p.B 200 :=
    wf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hTrialN]; omega) (by omega)
  refine WP.mono_syms (WP.mono (WP.keep [.r5] (Q := fun t => t.mem = w.mem.writeW (p.B + BitVec.ofNat 64 200)
      (word u.mem p.B 200 ||| w.gpr .r22))
    (by simp only [ldh, sth, hBad]; prun [w31, l200, s200, hold]) (by decide)) fun t h => h)
    fun t ⟨tm, kt⟩ syt => ?_
  have fst : Frm p.B [(208, 8), (200, 8)] u.mem t.mem := by
    rw [tm]
    exact VG.Proof.MillerRabin.PPC64LE.Search.frm_writeW (wf.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp [hTrialN]) _ ⟨(200, 8), by simp, by decide, by decide⟩ (by decide)
  have hbad : word t.mem p.B (8 * hBad) = 0#64 ↔ B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false := by
    show t.mem.readW (p.B + BitVec.ofNat 64 200) 64 = 0#64 ↔ _
    rw [tm, VG.Proof.MillerRabin.PPC64LE.Search.rw_self, BitVec.or_eq_zero_iff, w22, ← h.bad]
    refine and_congr Iff.rfl ?_
    cases VG.Proof.RsaKeyGen.trialPrefix x n <;> decide
  exact h.step (regs := ([.r3, .r4, .r23, .r24] ++ groupRegs) ++ [.r5]) fst
    (fun r hr => (kt.gpr r fun h' => hr (List.mem_append_right _ h')).trans (wg r fun h' => hr
      (List.mem_append_left _ h')))
    (kt.rd.trans wrd) (kt.wr.trans wwr) (kt.sp.trans wsp)
    (by decide) (by decide) (by decide) (by decide) (by decide) hbad (syt.trans syw)

/-- Trial division of array 0 by the first `n` entries, by products. -/
theorem prodSieveN_ok {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} {n : Nat} (h : MB p T x B s)
    (hn4 : n % 4 = 0) (hn1 : 4 ≤ n) (hn2 : n ≤ 1024) :
    WP isa (prodSieveN n) s (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x n = false)) := by
  unfold prodSieveN
  refine WP.seq (WP.mono (h.prodA n (by omega)) fun v ⟨⟨v23, v24, vm⟩, vg, vrd, vwr, vsp, syv⟩ => ?_)
  have ha := h.largs vm (fun r hr => vg r fun h' => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h'))) vrd vwr
    hn4 hn1 hn2
  refine WP.seq (WP.mono_syms (prodLoop_ok ha v23 v24) fun w ⟨⟨w22, wf⟩, kw⟩ syw => ?_)
  rw [vm] at wf
  exact h.orBadP w22 wf (fun r hr => (kw.gpr r fun h' => hr (List.mem_append_right _ h')).trans
    (vg r fun h' => hr (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')))))
    (kw.rd.trans vrd) (kw.wr.trans vwr) (kw.sp.trans vsp) (syw.trans syv)

/-- Trial division of array 0 by the first `trialN bits` entries, by
products. -/
theorem prodSieve_ok {p : PP} {x : Nat} {B : Prop} {T : Addr} {s : State} (h : MB p T x B s) :
    WP isa prodSieve s (MB p T x (B ∧ VG.Proof.RsaKeyGen.trialPrefix x (trialN p.bits) = false)) := by
  unfold prodSieve
  refine WP.seq (WP.mono h.prodC fun v ⟨⟨v23, v24, vm⟩, vg, vrd, vwr, vsp, syv⟩ => ?_)
  have hN : trialN p.bits % 4 = 0 ∧ 4 ≤ trialN p.bits ∧ trialN p.bits ≤ 1024 := by unfold trialN; split <;> decide
  have ha := h.largs vm vg vrd vwr hN.1 hN.2.1 hN.2.2
  refine WP.seq (WP.mono_syms (prodLoop_ok ha v23 v24) fun w ⟨⟨w22, wf⟩, kw⟩ syw => ?_)
  rw [vm] at wf
  exact h.orBadP w22 wf (fun r hr => (kw.gpr r fun h' => hr (List.mem_append_right _ h')).trans
    (vg r fun h' => hr (List.mem_append_left _ h'))) (kw.rd.trans vrd) (kw.wr.trans vwr) (kw.sp.trans vsp)
    (syw.trans syv)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
