module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # The public actual-width scan's first-nonzero selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The scan keeps the first nonzero byte and its remaining buffer width. -/
def scanNext (found : Nat × Byte) (remaining : Nat) (b : Byte) : Nat × Byte :=
  if found.1 = 0 ∧ b ≠ 0 then (remaining, b) else found

theorem byte_zext_eq_zero (b : Byte) : (b.zeroExtend 64 == 0) = (b == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    change (b.setWidth 64).toNat = 0 at h'
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at h'
    exact BitVec.eq_of_toNat_eq h'
  · intro h; subst b; rfl

/-- A byte as `ldrb` loads it. -/
theorem ldrb_byte (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = (m a).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat]
  have := (m a).isLt
  simp
  omega

theorem ofNat_eqz {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  rw [eq_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Selection only changes the saved first-byte pair; it never writes memory. -/
theorem significantChoose_ok {s : State} {found : Nat × Byte} {remaining : Nat} {b : Byte}
    (h8 : s.gpr .x8 = BitVec.ofNat 64 found.1)
    (h9 : s.gpr .x9 = found.2.zeroExtend 64)
    (ha : s.gpr .x3 = b.zeroExtend 64)
    (hc : s.gpr .x2 = BitVec.ofNat 64 remaining)
    (hfound : found.1 < 2 ^ 64) :
    WP isa Checks.significantChoose s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (scanNext found remaining b).1 ∧
      t.gpr .x9 = (scanNext found remaining b).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.x3, .x8, .x9] s t := by
  unfold Checks.significantChoose
  by_cases hf : found.1 = 0
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · rw [eval_zero, h8, ofNat_eqz hfound, hf]; rfl
    by_cases hb : b = 0
    · refine WP.ite true ?_ (fun _ => WP.block_nil ?_) (fun h => Bool.noConfusion h)
      · rw [eval_zero, ha, byte_zext_eq_zero, hb, beq_self_eq_true]
      · have hn : scanNext found remaining b = found := by simp [scanNext, hb]
        rw [hn]
        exact ⟨h8, h9, rfl, Keep.refl _ _⟩
    · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
      · rw [eval_zero, ha, byte_zext_eq_zero, beq_eq_false_iff_ne.mpr hb]
      · have hn : scanNext found remaining b = (remaining, b) := ite_eq_left ⟨hf, hb⟩
        rw [hn]
        refine WP.mono (WP.keep [.x8, .x9] (Q := fun t =>
          t.gpr .x8 = BitVec.ofNat 64 remaining ∧ t.gpr .x9 = b.zeroExtend 64 ∧ t.mem = s.mem)
          ?_ (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨ht8, ht9, htm⟩, hkt⟩ =>
            ⟨ht8, ht9, htm, hkt.mono (by decide)⟩
        brun [hc, ha, BitVec.add_zero]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    · rw [eval_zero, h8, ofNat_eqz hfound, decide_eq_false hf]
    · have hn : scanNext found remaining b = found := by simp [scanNext, hf]
      rw [hn]
      exact ⟨h8, h9, rfl, Keep.refl _ _⟩

/-- One byte of the public scan preserves memory and advances exactly once. -/
theorem significantByte_ok {s : State} {p : Addr} {found : Nat × Byte} {remaining : Nat}
    (hsi : s.gpr .x1 = p) (hcx : s.gpr .x2 = BitVec.ofNat 64 remaining)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 found.1) (h9 : s.gpr .x9 = found.2.zeroExtend 64)
    (hr : InRegions (s.rd ++ s.wr) p 1)
    (hfound : found.1 < 2 ^ 64) (h1 : 1 ≤ remaining) (h64 : remaining < 2 ^ 64) :
    WP isa Checks.significantByte s fun t =>
      t.gpr .x1 = p + 1 ∧ t.gpr .x2 = BitVec.ofNat 64 (remaining - 1) ∧
      t.gpr .x8 = BitVec.ofNat 64 (scanNext found remaining (s.mem p)).1 ∧
      t.gpr .x9 = (scanNext found remaining (s.mem p)).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.x3, .x8, .x9, .x1, .x2] s t := by
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  unfold Checks.significantByte seqs
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u =>
    u.gpr .x3 = (s.mem p).zeroExtend 64 ∧ u.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hua, hum⟩, hku⟩ => ?_)
  · brun [hsi, e0, hr, ldrb_byte]
  have hu8 := (hku.gpr .x8 (by decide)).trans h8
  have hu9 := (hku.gpr .x9 (by decide)).trans h9
  have huc := (hku.gpr .x2 (by decide)).trans hcx
  refine WP.seq (WP.mono (significantChoose_ok hu8 hu9 hua huc hfound)
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hvsi := ((hku.trans hkv).gpr .x1 (by decide)).trans hsi
  have hvc := ((hku.trans hkv).gpr .x2 (by decide)).trans hcx
  have hsub := ofNat_sub_one' h1 h64
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t =>
    t.gpr .x1 = p + 1 ∧ t.gpr .x2 = BitVec.ofNat 64 (remaining - 1) ∧ t.mem = v.mem) ?_
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨htsi, htc, htm⟩, hkt⟩ =>
      ⟨htsi, htc, (hkt.gpr .x8 (by decide)).trans hv8, (hkt.gpr .x9 (by decide)).trans hv9,
        (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩
  brun [hvsi, hvc, hsub]
  rfl

end VG.Proof.Dsa.AArch64
