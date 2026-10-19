module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # First-nonzero selection in the public modulus-width scan -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def scanNext (found : Nat × Byte) (remaining : Nat) (b : Byte) : Nat × Byte :=
  if found.1 = 0 ∧ b ≠ 0 then (remaining, b) else found

theorem ofNat_beq_zero {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == (0#64)) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hv := congrArg BitVec.toNat h
    change n % 2 ^ 64 = 0 at hv
    rwa [Nat.mod_eq_of_lt hn] at hv
  · intro h; rw [h]

theorem byte_widen_zero (b : Byte) : b.zeroExtend 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (b.setWidth 64).toNat = 0 at he
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; subst b; rfl

theorem significantChoose_ok {s : State} {found : Nat × Byte} {remaining : Nat} {b : Byte}
    (h8 : s.gpr .x8 = BitVec.ofNat 64 found.1)
    (h9 : s.gpr .x10 = found.2.zeroExtend 64)
    (ha : s.gpr .x3 = b.zeroExtend 64)
    (hc : s.gpr .x9 = BitVec.ofNat 64 remaining) (hf64 : found.1 < 2 ^ 64) :
    WP isa Checks.significantChoose s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (scanNext found remaining b).1 ∧
      t.gpr .x10 = (scanNext found remaining b).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.x3, .x8, .x10] s t := by
  unfold Checks.significantChoose
  by_cases hf : found.1 = 0
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x8 == (0#64)) = some true
      rw [h8, ofNat_beq_zero hf64]; simp [hf]
    · by_cases hb : b = 0
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
        · change some (s.gpr .x3 != (0#64)) = some false
          rw [ha, hb]; rfl
        · have hn : scanNext found remaining b = found := by simp [scanNext, hb]
          rw [hn]; exact ⟨h8, h9, rfl, Keep.refl _ _⟩
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change some (s.gpr .x3 != (0#64)) = some true
          rw [ha]
          have hn : b.zeroExtend 64 ≠ (0#64) := mt (byte_widen_zero b).mp hb
          simp only [bne, beq_eq_false_iff_ne.mpr hn, Bool.not_false]
        · have hn : scanNext found remaining b = (remaining, b) := ite_eq_left ⟨hf, hb⟩
          rw [hn]
          refine WP.mono (WP.keep [.x8, .x10] (Q := fun t =>
            t.gpr .x8 = BitVec.ofNat 64 remaining ∧ t.gpr .x10 = b.zeroExtend 64 ∧ t.mem = s.mem)
            ?_ rfl rfl rfl) fun t ⟨⟨ht8, ht9, htm⟩, hkt⟩ => ⟨ht8, ht9, htm, hkt.mono (by decide)⟩
          brun [hc, ha]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    · change some (s.gpr .x8 == (0#64)) = some false
      rw [h8, ofNat_beq_zero hf64]; simp [hf]
    · have hn : scanNext found remaining b = found := by simp [scanNext, hf]
      rw [hn]; exact ⟨h8, h9, rfl, Keep.refl _ _⟩

theorem significantByte_ok {s : State} {p : Addr} {found : Nat × Byte} {remaining : Nat}
    (hsi : s.gpr .x1 = p) (hcx : s.gpr .x9 = BitVec.ofNat 64 remaining)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 found.1) (h9 : s.gpr .x10 = found.2.zeroExtend 64)
    (hr : InRegions (s.rd ++ s.wr) p 1)
    (hfound : found.1 < 2 ^ 64) (h1 : 1 ≤ remaining) (h64 : remaining < 2 ^ 64) :
    WP isa Checks.significantByte s fun t =>
      t.gpr .x1 = p + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (remaining - 1) ∧
      t.gpr .x8 = BitVec.ofNat 64 (scanNext found remaining (s.mem p)).1 ∧
      t.gpr .x10 = (scanNext found remaining (s.mem p)).2.zeroExtend 64 ∧
      (t.gpr .x9 == (0#64)) = decide (remaining = 1) ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x10, .x1, .x9] s t := by
  unfold Checks.significantByte seqs
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u =>
    u.gpr .x3 = (s.mem p).zeroExtend 64 ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hua, hum⟩, hku⟩ => ?_)
  · brun [hsi, hr]
    apply BitVec.eq_of_toNat_eq
    simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.zeroExtend]
    have := (s.mem p).isLt
    simp
    omega
  have hu8 := (hku.gpr .x8 (by decide)).trans h8
  have hu9 := (hku.gpr .x10 (by decide)).trans h9
  have huc := (hku.gpr .x9 (by decide)).trans hcx
  refine WP.seq (WP.mono (significantChoose_ok hu8 hu9 hua huc hfound)
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hvsi := ((hku.trans hkv).gpr .x1 (by decide)).trans hsi
  have hvc := ((hku.trans hkv).gpr .x9 (by decide)).trans hcx
  have hsub : BitVec.ofNat 64 remaining - 1 = BitVec.ofNat 64 (remaining - 1) := by
    change BitVec.ofNat 64 remaining - BitVec.ofNat 64 1 = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.mono (WP.keep [.x1, .x9] (Q := fun t =>
    t.gpr .x1 = p + 1 ∧ t.gpr .x9 = BitVec.ofNat 64 (remaining - 1) ∧ t.mem = v.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨htsi, htc, htm⟩, hkt⟩ => ?_
  · brun [hvsi, hvc]
    exact ⟨rfl, hsub⟩
  · refine ⟨htsi, htc, (hkt.gpr .x8 (by decide)).trans hv8, (hkt.gpr .x10 (by decide)).trans hv9,
      ?_, (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩
    rw [htc, ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.Dsa.AArch64
