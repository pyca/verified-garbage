module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the powers

`mid1_ok`: after the front, `X` loaded and checked, the input loaded again,
then `m₁ = c^dP mod p` and `m₂ = c^dQ mod q` in the primes' working spaces
(`M1`), with `p`, `q` and `qInv` masked.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays Frm)

/-! ## Numbers of the entry state -/

abbrev vN (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀))
abbrev vC (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a4) (ck s₀))
abbrev vP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a6) (cpL s₀))
abbrev vQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀))
abbrev vDP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 2) (cpL s₀))
abbrev vDQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 4) (cqL s₀))
abbrev vQI (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 6) (cpL s₀))
/-- The mask. -/
abbrev cb (s₀ : State) : Bool := crtMask (vN s₀) (ck s₀) (vC s₀) (vP s₀) (vQ s₀) (vQI s₀)
/-- The masked `p`, `q` and `qInv`. -/
abbrev mP (s₀ : State) : Nat := if cb s₀ then vP s₀ else 3
abbrev mQ (s₀ : State) : Nat := if cb s₀ then vQ s₀ else 3
abbrev mQI (s₀ : State) : Nat := if cb s₀ then vQI s₀ else 0
/-- The primes' working spaces' words, and their offsets in the scratch. -/
abbrev cwP (s₀ : State) : Nat := wordsOf (cpL s₀)
abbrev cwQ (s₀ : State) : Nat := wordsOf (cqL s₀)
abbrev oPa (s₀ : State) : Nat := slot (cwX s₀) 8
abbrev oQa (s₀ : State) : Nat := slot (cwX s₀) 8 + slot (cwP s₀) 24
/-- `m₁` and `m₂`. -/
abbrev vm1 (s₀ : State) : Nat := vC s₀ ^ vDP s₀ % mP s₀
abbrev vm2 (s₀ : State) : Nat := vC s₀ ^ vDQ s₀ % mQ s₀

theorem mask_true {nb cb pb qb ib : List Byte} {k : Nat} (hk : 64 ≤ k) (hpl : pb.length < k)
    (hql : qb.length < k)
    (h : crtMask (Spec.Rsa.os2ip nb) k (Spec.Rsa.os2ip cb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (Spec.Rsa.os2ip ib) = true) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ∧ Spec.Rsa.os2ip cb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip ib < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      1 < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip qb ∧ Spec.Rsa.os2ip qb % 2 = 1 := by
  simp only [crtMask, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hc⟩, hi⟩, hpq⟩ := h
  obtain ⟨hodd, _, hP, hQ⟩ := VG.Proof.Bignum.crt_bounds_of hv hk rfl hpl rfl hql
  obtain ⟨hq1, hqo⟩ := VG.Proof.Bignum.factor_facts hpq hP hodd
  obtain ⟨hp1, hpo⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact hpq) hQ hodd
  exact ⟨hv, hc, hi, hpq, hp1, hpo, hq1, hqo⟩

theorem pow256_le {L w : Nat} (h : L ≤ 8 * w) : 256 ^ L ≤ 2 ^ (64 * w) := by
  rw [VG.Proof.Bignum.pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)

theorem os2ip_lt' (bs : List Byte) {L : Nat} (h : bs.length = L) : Spec.Rsa.os2ip bs < 256 ^ L := by
  have := VG.Proof.Bignum.os2ip_lt bs; rwa [h] at this

theorem three_lt_pow {L : Nat} (h : 1 ≤ L) : 3 < 256 ^ L :=
  Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 256) (by decide) h)

/-- What the masked numbers satisfy. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    1 < mP s₀ ∧ mP s₀ % 2 = 1 ∧ 1 < mQ s₀ ∧ mQ s₀ % 2 = 1 ∧ mP s₀ < 256 ^ cpL s₀ ∧
      mQ s₀ < 256 ^ cqL s₀ ∧ mQI s₀ < mP s₀ ∧ mQI s₀ < 256 ^ cpL s₀ := by
  have h3p := three_lt_pow hP.p1
  have h3q := three_lt_pow hP.q1
  unfold mP mQ mQI
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide, by decide, h3p, h3q, by decide, by omega_arith⟩
  · simp only [↓reduceIte]
    obtain ⟨_, _, hi, _, hp1, hpo, hq1, hqo⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
    exact ⟨hp1, hpo, hq1, hqo, os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _),
      os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _), hi, os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)⟩

/-! ## Working spaces in the scratch -/

/-- A number of `W` words below `2^(64 n)`, `n ≤ W`, is its first `n` words. -/
theorem wordsVal_trunc {m : Mem} {B : Addr} {d W n v : Nat} (h : wordsVal m B d W = v) (hv : v < 2 ^ (64 * n))
    (hn : n ≤ W) : wordsVal m B d n = v := by
  rw [Pre.wordsVal_eq_wv] at h ⊢
  have e := VG.Proof.Bignum.wv_add m B d n (W - n)
  rw [Nat.add_sub_cancel' hn, h] at e
  by_cases h0 : VG.Proof.Bignum.wv m B (d + 8 * n) (W - n) = 0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * VG.Proof.Bignum.wv m B (d + 8 * n) (W - n) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
    omega_arith

theorem Scr.sub {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h : d + n ≤ Z) (h8 : d % 8 = 0) (hn0 : 0 < n) :
    Scr s (Mont.off B d) n := by
  have hn := hs.nowrap
  have ha := hs.al
  obtain ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr
  have e : (Mont.off B d).toNat = B.toNat + d := by
    simp only [Mont.off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  refine ⟨⟨B₀, o + d, L, hm, ?_, ?_, hL'⟩, ?_, ?_⟩
  · rw [hb]; simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]
  · exact Nat.le_trans (by rw [Nat.add_assoc]; exact Nat.add_le_add_left h o) hL
  · rw [e]; omega
  · rw [e]; omega

theorem Scr.le {s : State} {B : Addr} {Z n : Nat} (hs : Scr s B Z) (h : n ≤ Z) : Scr s B n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩,
    by have := hs.nowrap; omega_arith, hs.al⟩

theorem ofs_reb (S x : Addr) {b : Nat} (hb : b < 2 ^ 64) :
    (b ≤ ofs S x ∧ ofs (Mont.off S b) x = ofs S x - b) ∨ (ofs S x < b ∧ 2 ^ 64 - b ≤ ofs (Mont.off S b) x) :=
  VG.Proof.Bignum.ofs_rebase S x hb

/-- The scratch's first `n` bytes are apart from its `k` at `b`. -/
theorem sepXB {S : Addr} {n b k : Nat} (h : n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs S x < n → k ≤ ofs (Mont.off S b) x := fun x hx => by
  rcases ofs_reb S x (b := b) (by omega_arith) with ⟨_, _⟩ | ⟨_, h2⟩ <;> omega_arith

theorem sepBX {S : Addr} {n b k : Nat} (h : n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S b) x < k → n ≤ ofs S x := fun x hx => by
  rcases ofs_reb S x (b := b) (by omega_arith) with ⟨_, _⟩ | ⟨_, h2⟩ <;> omega_arith

theorem sepBB {S : Addr} {a n b k : Nat} (h : a + n ≤ b) (hb : b + k ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S a) x < n → k ≤ ofs (Mont.off S b) x := fun x hx => by
  rcases ofs_reb S x (b := a) (by omega_arith) with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    rcases ofs_reb S x (b := b) (by omega_arith) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith

/-- A byte within `k` of `b` is within the scratch's `Z`. -/
theorem sepIn {S : Addr} {b k Z : Nat} (h : b + k ≤ Z) (hZ : Z ≤ 2 ^ 64) (hk : 0 < k) :
    ∀ x, ofs (Mont.off S b) x < k → ofs S x < Z := fun x hx => by
  rcases ofs_reb S x (b := b) (by omega_arith) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith

theorem out_reb {S : Addr} {a o n : Nat} {m m' : Mem} (h : Mont.Outside (Mont.off S a) o n m m')
    (h' : a + o + n ≤ 2 ^ 64) (hn : 0 < n) : Mont.Outside S (a + o) n m m' := fun x hx => h x (by
  rcases ofs_reb S x (b := a) (by omega_arith) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith)

theorem wordsVal_off (m : Mem) (S : Addr) (a : Nat) : ∀ d k,
    wordsVal m (Mont.off S a) d k = wordsVal m S (a + d) k
  | _, 0 => rfl
  | d, k + 1 => by
    simp only [wordsVal]
    rw [wordsVal_off m S a (d + 8) k, show a + (d + 8) = a + d + 8 by omega_arith]
    congr 3
    simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem word_off' (m : Mem) (S : Addr) (a d : Nat) : Mont.word m (Mont.off S a) d = Mont.word m S (a + d) := by
  simp only [Mont.word, Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem wordsOf_le_of {l k : Nat} (h : l ≤ k) (hk : 9 ≤ k) : wordsOf l ≤ (k + 7) / 8 := by
  unfold wordsOf; split <;> omega_arith

end VG.Proof.Bignum.RISCV64.Crt
