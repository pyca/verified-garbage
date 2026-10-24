module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Save
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_public` on PPC64LE: the function

`vg_ffdh_check_public(domain = r3, domain_len = r4, p_len = r5, y = r6,
y_len = r7, scratch = r8, scratch_len = r9)` (`cpContract`): `checkPublic`
saves the nonvolatile registers in the working space's header, sets up the
registers (`setup_ok`), loads and checks p (`loadP_ok`), checks y
(`checkY_ok`) and restores the registers (`cp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- `domain`, `domain_len` bytes at `r3`. -/
abbrev domR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩

/-- `y`, `y_len` bytes at `r6`. -/
abbrev yR (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩

/-- The working space, `scratch_len` words at `r8`. -/
abbrev scrR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩

/-- `vg_ffdh_check_public`, on the registers. -/
def cpContract : Contract isa where
  pre s :=
    s.rd = [domR s, yR s] ∧ s.wr = [scrR s] ∧ (domR s).Disjoint (scrR s) ∧ (yR s).Disjoint (scrR s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧
      Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧ (s.gpr .r7).toNat = (s.gpr .r5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r9).toNat
  post s t :=
    Spec.Ffdh.domainValid (s.gpr .r5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) = true →
      ((t.gpr .r3).setWidth 32).toNat =
        if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (s.gpr .r5).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat),
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)⟩ then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat).map (·.toNat)

/-- The registers `setup` and the copy of `y` write. -/
def setupRegs : List Reg := [.r10, .r11, .r21, .r26, .r27, .r28, .r29, .r31]

/-- `setup` and `r26 := y`, the working space at `r23`. -/
theorem setup_ok {s : State} {S D Y : Addr} {k L : Nat} (h3 : s.gpr .r3 = D)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (h5 : s.gpr .r5 = BitVec.ofNat 64 k) (h6 : s.gpr .r6 = Y)
    (h23 : s.gpr .r23 = S) (hk : k ≤ 1024) :
    WP isa (.block (setup ++ [.addi .r26 .r6 0])) s fun t =>
      (t.gpr .r21 = D ∧ t.gpr .r27 = BitVec.ofNat 64 L ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r31 = S ∧ t.gpr .r26 = Y ∧ t.mem = s.mem) ∧
      Keep setupRegs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h4, h5, h6, h23, BitVec.add_zero, Pub.ofNat_add7_shr3 k (by omega), Pub.ofNat_shl3, Pub.ofNat_shl1,
    hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

end VG.Proof.Ffdh.PPC64LE.Domain
