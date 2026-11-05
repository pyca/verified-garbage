module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcTable
public import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.ContextRows
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Scalar
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's context on RISC-V: the width and the metadata

`bound_ok`: the bound's bit length, from its first nonzero octet;
`width_ok`: the recognized width if it is below it (`width_eq`, the spec's
`generationScalarBits`); `metadata_ok`: the width, its bytes and the rows
into the context's first three words; `ctx_words`: the context's words from
its parts. -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (bptr scan_ok scanRegs bptr_bnd)
open VG.Spec.RsaKeyGen (bitLength)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (A)

/-! ## The bound's bit length -/

/-- `boundPtr`, from the domain's registers. -/
theorem bp_ok' {s : State} {D : Addr} {k L : Nat} (h2 : s.gpr .a2 = D) (h3 : s.gpr .a3 = BitVec.ofNat 64 L)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 k) (hL : L ≤ 3 * k) (hk : k ≤ 1024) :
    WP isa VG.Impl.Ffdh.RISCV64.GenerateKey.boundPtr s fun t => (t.gpr .t3 = off (bptr D k L) 0 ∧ t.mem = s.mem) ∧ Keep [.t2, .t3] s t := by
  refine WP.keep _ ?_ (by rfl)
  unfold VG.Impl.Ffdh.RISCV64.GenerateKey.boundPtr
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => (t.gpr .t2 == 0) = decide (L = 3 * k) ∧ t.mem = s.mem)
    (by unfold VG.Impl.Ffdh.RISCV64.GenerateKey.hasQ; brun [h3, h4]; exact Derive.sub_3k_zero (by omega_arith) (by omega_arith))
    (by rfl) (by rfl)) fun s₁ ⟨⟨t2, m1⟩, k1⟩ => ?_)
  refine WP.ite (s₁.gpr .t2 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [t2, decide_eq_true_eq] at hb
    refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off (off D (2 * k)) 0 ∧ t.mem = s₁.mem)
      (by brun [(k1.gpr (r := .a2) (by decide)).trans h2, (k1.gpr (r := .a4) (by decide)).trans h4,
        Derive.q_addr]) (by rfl) (by rfl)) fun t ⟨⟨t3, mt⟩, _⟩ => ⟨?_, by rw [mt, m1]⟩
    rw [t3]; unfold bptr; rw [ite_eq_left hb]
  · have hq : ¬ L = 3 * k := by rw [t2] at hb; simpa using hb
    refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off D 0 ∧ t.mem = s₁.mem)
      (by brun [(k1.gpr (r := .a2) (by decide)).trans h2, add_ofNat_zero]) (by rfl) (by rfl))
      fun t ⟨⟨t3, mt⟩, _⟩ => ⟨?_, by rw [mt, m1]⟩
    rw [t3]; unfold bptr; rw [ite_eq_right hq]

/-- The count of `{0, 1, 3, …, 127}` below `x`: the bit length of an octet. -/
def blv (x : BitVec 64) : BitVec 64 :=
  0 + (if (0 : BitVec 64) < x then 1 else 0) + (if BitVec.ofNat 64 1 < x then 1 else 0) +
    (if BitVec.ofNat 64 3 < x then 1 else 0) + (if BitVec.ofNat 64 7 < x then 1 else 0) +
    (if BitVec.ofNat 64 15 < x then 1 else 0) + (if BitVec.ofNat 64 31 < x then 1 else 0) +
    (if BitVec.ofNat 64 63 < x then 1 else 0) + (if BitVec.ofNat 64 127 < x then 1 else 0)

theorem blv_sum : ∀ L ≤ 8, (0 + (if 0 < L then 1 else 0) + (if 1 < L then 1 else 0) + (if 2 < L then 1 else 0) +
    (if 3 < L then 1 else 0) + (if 4 < L then 1 else 0) + (if 5 < L then 1 else 0) + (if 6 < L then 1 else 0) +
    (if 7 < L then 1 else 0) : BitVec 64) = BitVec.ofNat 64 L := by decide

theorem blv_ok {b : Byte} (hb : b ≠ 0) : blv (b.setWidth 64) = BitVec.ofNat 64 (bitLength b.toNat) := by
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hn : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hlt := b.isLt
  obtain ⟨lo, hi⟩ := VG.Proof.Ffdh.KeyScalar.bitLength_bounds hn
  have hL8 : bitLength b.toNat ≤ 8 := VG.Proof.Ffdh.ContextRows.bitLength_le_of_lt hlt
  rw [e]
  generalize bitLength b.toNat = L at lo hi hL8 ⊢
  generalize b.toNat = n at hn hlt lo hi ⊢
  have key : ∀ i, 2 ^ i ≤ n ↔ i < L := fun i => ⟨fun h => by
      refine Classical.byContradiction fun hc => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show L ≤ i by omega_arith)
      omega_arith,
    fun h => Nat.le_trans (Nat.pow_le_pow_right (show 0 < 2 by decide) (show i ≤ L - 1 by omega_arith)) lo⟩
  have c : ∀ c, c < 256 → (BitVec.ofNat 64 c < BitVec.ofNat 64 n) = (c < n) := fun c hc => by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_arith)]
  have k0 := key 0; have k1 := key 1; have k2 := key 2; have k3 := key 3
  have k4 := key 4; have k5 := key 5; have k6 := key 6; have k7 := key 7
  simp only [Nat.reducePow] at k0 k1 k2 k3 k4 k5 k6 k7
  unfold blv
  simp only [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, c 0 (by decide), c 1 (by decide), c 3 (by decide),
    c 7 (by decide), c 15 (by decide), c 31 (by decide), c 63 (by decide), c 127 (by decide),
    show (0 < n) = (0 < L) from propext (by omega_arith), show (1 < n) = (1 < L) from propext (by omega_arith),
    show (3 < n) = (2 < L) from propext (by omega_arith), show (7 < n) = (3 < L) from propext (by omega_arith),
    show (15 < n) = (4 < L) from propext (by omega_arith), show (31 < n) = (5 < L) from propext (by omega_arith),
    show (63 < n) = (6 < L) from propext (by omega_arith), show (127 < n) = (7 < L) from propext (by omega_arith)]
  exact blv_sum L hL8

/-- `bitLen`: `t2 := ` the count of `{0, 1, 3, …, 127}` below `s2`. -/
theorem bitLen_ok (s : State) :
    WP isa (.block bitLen) s fun t => (t.gpr .t2 = blv (s.gpr .s2) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold bitLen blStep
  brun [fin64_exec_li_zero, Pub.pub_li1, fin64_exec_li_lit (show 3 < 2048 by decide),
    fin64_exec_li_lit (show 7 < 2048 by decide), fin64_exec_li_lit (show 15 < 2048 by decide),
    fin64_exec_li_lit (show 31 < 2048 by decide), fin64_exec_li_lit (show 63 < 2048 by decide),
    fin64_exec_li_lit (show 127 < 2048 by decide)]
  rfl

/-- The registers `bound` writes. -/
def bbRegs : List Reg := scanRegs ++ [.t2, .t3, .s3]

/-- `bound`: `s3 :=` the bit length of the bound's `k` octets (q's, or p's
without q), from its first nonzero octet. -/
theorem bound_ok {s : State} {D : Addr} {k L : Nat} (h2 : s.gpr .a2 = D) (h3 : s.gpr .a3 = BitVec.ofNat 64 L)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 k) (hL : L = 2 * k ∨ L = 3 * k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hp : L ≠ 3 * k → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) % 2 = 1 ∧
      1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k))
    (hlead : (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L)).getD
      (VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L))) 0 ≠ 0) :
    WP isa bound s fun t =>
      (t.gpr .s3 = BitVec.ofNat 64 (bitLength (Spec.Ffdh.scalarBound
        (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt s.mem D L)))) ∧ t.mem = s.mem) ∧ Keep bbRegs s t := by
  have hl : (Spec.Rsa.bytesAt s.mem D L).length = L := by simp [Spec.Rsa.bytesAt]
  have hd : (Spec.Rsa.bytesAt s.mem D L).length = 2 * k ∨ (Spec.Rsa.bytesAt s.mem D L).length = 3 * k := by
    rw [hl]; exact hL
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length hd
  have hne : VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) ≠ [] := fun he => by
    rw [he] at hbl; simp at hbl; omega_arith
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits hk hd (fun h3' => by
    rw [Proof.Ffdh.take_bytesAt s.mem D (by omega_arith)]; exact hp (by rw [hl] at h3'; exact h3'))
  have hbits' : bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt s.mem D L))) =
      8 * (k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L)) - 1) +
        bitLength ((VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L)).getD
          (VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L))) 0).toNat := by
    rw [hbits, Proof.Ffdh.getD_of]
  rw [hbits']
  generalize hbd : VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) = bd at hlead hne hld ⊢
  unfold bound
  refine WP.seq (WP.mono (bp_ok' h2 h3 h4 (by omega_arith) hk') fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have hbytes : Spec.Rsa.bytesAt s₁.mem (bptr D k L) k = bd := by rw [m1, bptr_bnd _ _ hL, hbd]
  have hrdP : ∀ i < k, InRegions (s₁.rd ++ s₁.wr) (off (bptr D k L) i) 1 := fun i hi => by
    rw [k1.2.1, k1.2.2]
    unfold bptr
    split
    · rw [Derive.off_off]; exact hrd _ (by omega_arith)
    · exact hrd _ (by omega_arith)
  refine WP.seq (WP.mono (scan_ok hk (by omega_arith) hrdP a3 ((k1.gpr (by decide)).trans h4))
    fun u hu => WP.seq (WP.mono hu fun s₂ ⟨⟨a1, a2', m2⟩, k2⟩ => ?_))
  rw [hbytes] at a1 a2'
  have k12 := k1.trans k2
  unfold boundBl
  rw [WP.block_append_iff]
  refine WP.mono (bitLen_ok s₂) fun s₃ ⟨⟨t2, m3⟩, k3⟩ => ?_
  rw [a2', blv_ok hlead] at t2
  have hb8 : bitLength (bd.getD (VG.Proof.Ffdh.lead bd) 0).toNat ≤ 8 :=
    VG.Proof.Ffdh.ContextRows.bitLength_le_of_lt (BitVec.isLt _)
  have g4 : s₃.gpr .a4 = BitVec.ofNat 64 k := ((k12.trans k3).gpr (by decide)).trans h4
  have g1 : s₃.gpr .s1 = BitVec.ofNat 64 (VG.Proof.Ffdh.lead bd) := (k3.gpr (by decide)).trans a1
  refine WP.mono (WP.keep [.s3] (Q := fun t => t.gpr .s3 = BitVec.ofNat 64 (8 * (k - VG.Proof.Ffdh.lead bd - 1) +
      bitLength (bd.getD (VG.Proof.Ffdh.lead bd) 0).toNat) ∧ t.mem = s₃.mem) (by
    brun [g4, g1, t2, exec_addi_neg_lit (show 8 ≤ 2048 by decide),
      ofNat_sub'' (show VG.Proof.Ffdh.lead bd ≤ k by omega_arith) (show k < 2 ^ 64 by omega_arith),
      ofNat_shl3' (show 8 * (k - VG.Proof.Ffdh.lead bd) < 2 ^ 64 by omega_arith),
      ofNat_sub'' (show 8 ≤ 8 * (k - VG.Proof.Ffdh.lead bd) by omega_arith)
        (show 8 * (k - VG.Proof.Ffdh.lead bd) < 2 ^ 64 by omega_arith), ← BitVec.ofNat_add]
    congr 1; omega_arith) (by rfl) (by rfl)) fun t ⟨⟨a3', mt⟩, kt⟩ => ?_
  exact ⟨⟨a3', by rw [mt, m3, m2, m1]⟩, ((k12.trans k3).trans kt).mono (by decide)⟩

/-! ## The width -/

/-- The width: the recognized one `cap` if it is not zero and below the
bound's bit length `bl`, else `bl`. -/
abbrev widthOf (cap bl : Nat) : Nat := if cap ≠ 0 ∧ cap < bl then cap else bl

theorem ofNat_lt_ofNat' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = (a < b) := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `width`: `s9 := widthOf cap bl`, `cap` in `a5` and `bl` in `s3`. -/
theorem width_ok {s : State} {cap bl : Nat} (h5 : s.gpr .a5 = BitVec.ofNat 64 cap)
    (h3 : s.gpr .s3 = BitVec.ofNat 64 bl) (hc : cap < 2 ^ 32) (hb : bl < 2 ^ 32) :
    WP isa width s fun t => (t.gpr .s9 = BitVec.ofNat 64 (widthOf cap bl) ∧ t.mem = s.mem) ∧
      Keep [.t3, .s9] s t := by
  unfold width
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 (if cap < bl then 1 else 0) ∧
      t.mem = s.mem) (by
    brun [h5, h3, ofNat_lt_ofNat' (show cap < 2 ^ 64 by omega_arith) (show bl < 2 ^ 64 by omega_arith)]
    split <;> rfl) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have g5 : s₁.gpr .a5 = BitVec.ofNat 64 cap := (k1.gpr (by decide)).trans h5
  have g3 : s₁.gpr .s3 = BitVec.ofNat 64 bl := (k1.gpr (by decide)).trans h3
  refine WP.ite (decide (cap = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) g5) (fun hz => ?_) (fun hz => ?_)
  · have hz' : cap = 0 := by simpa using hz
    refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = BitVec.ofNat 64 bl ∧ t.mem = s₁.mem)
      (by brun [g3, add_ofNat_zero]) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, kt⟩ => ?_
    exact ⟨⟨by rw [t9]; simp [widthOf, hz'], tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
  · have hz' : cap ≠ 0 := by simpa using hz
    refine WP.ite (decide (¬ cap < bl)) ((Steps.eval_zero_ofNat _ _ (by split <;> omega_arith) a3).trans (by
      split <;> simp_all)) (fun hl => ?_) (fun hl => ?_)
    · have hl' : ¬ cap < bl := by simpa using hl
      refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = BitVec.ofNat 64 bl ∧ t.mem = s₁.mem)
        (by brun [g3, add_ofNat_zero]) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, kt⟩ => ?_
      exact ⟨⟨by rw [t9]; simp [widthOf, hl'], tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
    · have hl' : cap < bl := by simpa using hl
      refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = BitVec.ofNat 64 cap ∧ t.mem = s₁.mem)
        (by brun [g5, add_ofNat_zero]) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, kt⟩ => ?_
      exact ⟨⟨by rw [t9]; simp [widthOf, hz', hl'], tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩

theorem recognized_le {a : Spec.Ffdh.Parameters} {b : Nat} (h : Spec.Ffdh.vettedExponentBits a = some b) :
    b ≤ 400 := by
  unfold Spec.Ffdh.vettedExponentBits at h
  repeat' split at h
  all_goals cases h
  all_goals decide

/-- The width the code computes is the spec's. -/
theorem width_eq {k : Nat} {dom : List Byte} (hk : 0 < k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hn : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
    widthOf (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
        (bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))) =
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
  rw [VG.Proof.Ffdh.VettedGroupFacts.recognize_spec hk hd hn]
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp [widthOf]
  | some b =>
    have := VG.Proof.Ffdh.ContextRows.recognized_nonzero he
    simp only [Option.getD_some, widthOf]
    by_cases hb : b < bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
    · rw [ite_eq_left_iff.mpr (fun h' => absurd ⟨this, hb⟩ h')]; exact (Nat.min_eq_left (by omega_arith)).symm
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h'.2 hb)]; exact (Nat.min_eq_right (by omega_arith)).symm

theorem recognize_lt {k : Nat} {dom : List Byte} (hk : 0 < k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hn : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
    VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom ≤ 400 := by
  rw [VG.Proof.Ffdh.VettedGroupFacts.recognize_spec hk hd hn]
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp
  | some b => exact recognized_le he

/-- The bound's first significant octet is not zero. -/
theorem lead_ne {k : Nat} {dom : List Byte} (hk : 1 ≤ k) (hd : dom.length = 2 * k ∨ dom.length = 3 * k)
    (hv : Spec.Ffdh.domainValid k dom = true) :
    (VG.Proof.Ffdh.KeyScalar.bnd k dom).getD (VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k dom)) 0 ≠ 0 := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hpf : 2 ≤ (Spec.Ffdh.domainOf k dom).p ∧ (Spec.Ffdh.domainOf k dom).p % 2 = 1 := by
    have := hv'.1
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    omega_arith
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length hd
  have hne : VG.Proof.Ffdh.KeyScalar.bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega_arith
  have hld := VG.Proof.Ffdh.lead_lt hne
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) hk hd (fun _ => ⟨hpf.2, by
    have : (Spec.Ffdh.domainOf k dom).p = Spec.Rsa.os2ip (dom.take k) := rfl; omega_arith⟩)
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega_arith
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega_arith
  rw [Proof.Ffdh.getD_of hld]
  intro hb0
  by_cases hlast : VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k dom) + 1 <
      (VG.Proof.Ffdh.KeyScalar.bnd k dom).length
  · exact VG.Proof.Ffdh.lead_nonzero hne hlast hb0
  · rw [hb0] at hbits
    have : bitLength (0 : Byte).toNat = 0 := rfl
    rw [this] at hbits
    have hpos := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega_arith)).2
    rw [hbits] at hpos
    rw [hbl] at hlast hld
    have : k - VG.Proof.Ffdh.lead (VG.Proof.Ffdh.KeyScalar.bnd k dom) - 1 = 0 := by omega_arith
    rw [this] at hpos
    omega_arith

/-! ## The metadata -/

theorem exec_lui13 {s : State} {d : Reg} : exec (.lui d 13) s = some (s.write d (BitVec.ofNat 64 53248)) := rfl

theorem rows_mul (bits : Nat) (hb : bits ≤ 8192) :
    ((BitVec.ofNat 64 bits + BitVec.ofNat 64 4) * (BitVec.ofNat 64 53248 - BitVec.ofNat 64 819)) >>> 18 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) := by
  rw [show BitVec.ofNat 64 53248 - BitVec.ofNat 64 819 = BitVec.ofNat 64 52429 from rfl, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.FixedBaseComb.rows, Spec.Rsa.FixedBaseComb.teeth]
  rw [Nat.mod_eq_of_lt (show bits + 4 < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 52429 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show (bits + 4) * 52429 < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show (bits + 5 - 1) / 5 < 2 ^ 64 by omega_arith)]
  omega_arith

/-- `metadata`: the width (`s9`), its bytes and the rows into the context's
words 0–2 (at `s10`); `s9 :=` the rows. -/
theorem metadata_ok {s : State} {C : Addr} {bits : Nat} (hc : Scr s C 24) (h10 : s.gpr .s10 = C)
    (h9 : s.gpr .s9 = BitVec.ofNat 64 bits) (hb : bits ≤ 8192) :
    WP isa (.block metadata) s fun t =>
      (word t.mem C 0 = BitVec.ofNat 64 bits ∧ word t.mem C 8 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
        word t.mem C 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
        t.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧ Outside C 0 24 s.mem t.mem) ∧
      Keep [.t3, .t4, .t5, .s9] s t := by
  have hn := hc.nowrap
  have h10' : s.gpr .s10 = off C 0 := by rw [h10]; simp [off]
  have i0 := hc.st (d := 0) (n := 8) (by decide)
  have i8 := hc.st (d := 8) (n := 8) (by decide)
  have i16 := hc.st (d := 16) (n := 8) (by decide)
  have l0 := hc.al8 (d := 0) (by decide) (by decide)
  have l8 := hc.al8 (d := 8) (by decide) (by decide)
  have l16 := hc.al8 (d := 16) (by decide) (by decide)
  have e7 : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [← BitVec.ofNat_add, ofNat_shr3 (by omega_arith)]
  have rm := rows_mul bits hb
  refine WP.mono (WP.keep [.t3, .t4, .t5, .s9] (Q := fun t => t.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      t.mem = ((s.mem.writeW (off C 0) (BitVec.ofNat 64 bits)).writeW (off C 8)
        (BitVec.ofNat 64 ((bits + 7) / 8))).writeW (off C 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)))
    (by
      unfold metadata
      brun [h9, h10', exec_lui13, exec_addi_neg_lit (show 819 ≤ 2048 by decide), i0, i8, i16, l0, l8, l16, e7, rm]
      simp only [BitVec.add_zero]) (by rfl) (by rfl))
    fun t ⟨⟨t9, tm⟩, kt⟩ => ?_
  have o0 := writeW_outside s.mem C (d := 0) (BitVec.ofNat 64 bits) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off C 0) (BitVec.ofNat 64 bits)) C (d := 8)
    (BitVec.ofNat 64 ((bits + 7) / 8)) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off C 0) (BitVec.ofNat 64 bits)).writeW (off C 8)
    (BitVec.ofNat 64 ((bits + 7) / 8))) C (d := 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) (by omega_arith)
  refine ⟨⟨?_, ?_, ?_, t9, ?_⟩, kt⟩
  · rw [tm, o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o2.word (by omega_arith) (by omega_arith)]; exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact ((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))

/-! ## The prefix rows -/

/-- `storePrefix`: p and `R² mod p` to the context's rows 0 and 1. -/
theorem storePrefix_ok {s : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) :
    WP isa storePrefix s fun t =>
      (wordsVal t.mem C (rowOff w 0) w = A s.mem B w 0 ∧ wordsVal t.mem C (rowOff w 1) w = A s.mem B w 1 ∧
        Outside C (rowOff w 0) (16 * w) s.mem t.mem ∧ Outside B Z (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M) ∧
      Keep [.t2, .t3, .t4, .t5, .s0] s t := by
  have hCn := h.hc.nowrap
  have hZn := h.win.scr.nowrap
  have a0 := h.slZ (show 0 < 24 by decide)
  have a1 := h.slZ (show 1 < 24 by decide)
  unfold storePrefix
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 0 ∧ u.mem = s.mem)
    (by brun [fin64_exec_li_zero]; rfl) (by rfl) (by rfl)) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  have ts1 := h.same k1 (by decide) m1
  refine WP.seq (WP.mono (ts1.store (j := 0) (a := 0) (by decide) a2 (by decide)) fun t₂ ⟨⟨r0, o2, b2, ts2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 1 ∧ u.mem = t₂.mem)
    (by brun [Pub.pub_li1]) (by rfl) (by rfl)) fun t₃ ⟨⟨a2', m3⟩, k3⟩ => ?_)
  have ts3 := ts2.same k3 (by decide) m3
  refine WP.mono (ts3.store (j := 1) (a := 1) (by decide) a2' (by decide)) fun t ⟨⟨r1, o4, b4, ts4⟩, k4⟩ => ?_
  have fit0 : rowOff w 0 + 8 * w ≤ rowOff w 1 := by unfold rowOff; omega_arith
  have hr1 := row_fits (w := w) (j := 1) (by decide)
  refine ⟨⟨?_, ?_, ?_, fun y hy => by rw [b4 y hy, m3, b2 y hy, m1], ts4⟩,
    (((k1.trans k2).trans k3).trans k4).mono (by decide)⟩
  · rw [Outside.wordsVal o4 (Or.inl fit0) (by unfold rowOff ctxWords at *; omega_arith), m3, r0, m1]
  · rw [r1, m3]
    show wordsVal t₂.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w
    rw [Outside.wordsVal b2 (Or.inl (by omega_arith)) (by omega_arith), m1]
  · intro y hy
    rw [o4 y (by unfold rowOff at *; omega_arith), m3, o2 y (by unfold rowOff at *; omega_arith), m1]

/-! ## The context's words -/

theorem toWords_row {m : Mem} {C : Addr} {w j V : Nat} (h : wordsVal m C (rowOff w j) w = V) :
    VG.Proof.Ffdh.ContextRows.row m C w j = Spec.Rsa.toWords V w := by
  rw [VG.Proof.Ffdh.ContextRows.row_self, ← Pub.wsv_wv, show 24 + 8 * w * j = rowOff w j by
    unfold rowOff; rw [Nat.mul_assoc], h]

/-- The context's words from its metadata, its prefix rows and its entries. -/
theorem ctx_words {m : Mem} {C : Addr} {k : Nat} {dom : List Byte}
    (h0 : word m C 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)))
    (h8 : word m C 8 = BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) + 7) / 8))
    (h16 : word m C 16 =
      BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom))))
    (hp : wordsVal m C (rowOff ((k + 7) / 8) 0) ((k + 7) / 8) = (Spec.Ffdh.domainOf k dom).p)
    (hr : wordsVal m C (rowOff ((k + 7) / 8) 1) ((k + 7) / 8) =
      2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % (Spec.Ffdh.domainOf k dom).p)
    (he : Ents m C (Spec.Ffdh.domainOf k dom).g (Spec.Ffdh.domainOf k dom).p ((k + 7) / 8)
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) 32) :
    Spec.Rsa.wordsAt m C (3 + 34 * ((k + 7) / 8)) = VG.Proof.Ffdh.generationValues k dom := by
  rw [VG.Proof.Ffdh.ContextRows.generationValues_parts]
  simp only [Spec.Rsa.modulusWords]
  exact VG.Proof.Ffdh.ContextRows.ctx_words h0 h8 h16 (toWords_row hp)
    (toWords_row (by rw [hr, ← Nat.pow_add, show 64 * ((k + 7) / 8) + 64 * ((k + 7) / 8) = 128 * ((k + 7) / 8) by omega_arith]))
    (fun a ha => toWords_row (m := m) (C := C) (w := (k + 7) / 8) (j := 2 + a) (by rw [Nat.add_comm 2 a]; exact he a ha))

end VG.Proof.Ffdh.RISCV64.Cached
