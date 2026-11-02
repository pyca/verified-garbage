module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS verification on AArch64: the result, by cases

`verifyOut G s`: what the contract asks of a call from `s`. It is `false`
if the modulus' first byte is zero (`verifyOut_zero`), and otherwise that
RSAVP1's result, or zeros, starts with `lo` zero bytes and ends with a
consistent encoding of `emBits = 8 (k - 1) + log₂ n₀` bits
(`verifyOut_enc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64 (ebV)
open VG.Proof.RsaPss.AArch64.Sgn (bytesAt_cons fb)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- In the frame: the slots and the callee-saved registers' values. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Fr s t.mem

/-- RSAVP1's result, or zeros. -/
abbrev pubX (s : State) : List Byte := (pubOut s).getD (Spec.RsaPss.zeros (s.gpr .x1).toNat)

/-- The salt length `verify` expects. -/
abbrev sLenV (s : State) : Option Nat := if anyV s = 0 then some (s.gpr .x7).toNat else none

/-- `emBits`, `emLen` and `lo` of a call from `s`. -/
abbrev ebS (s : State) : Nat := ebV (s.gpr .x1).toNat (s.mem (s.gpr .x0)).toNat
abbrev elS (s : State) : Nat := Spec.RsaPss.emLength (ebS s)
abbrev loS (s : State) : Nat := (s.gpr .x1).toNat - elS s

theorem pubX_length (s : State) : (pubX s).length = (s.gpr .x1).toNat := by
  unfold pubX
  cases h : pubOut s with
  | none => simp [Spec.RsaPss.zeros]
  | some y => rw [Option.getD_some, RsaPss.publicOpChecked_length' h, bytesAt_length]

variable (G : Spec.Mgf1.Hash)

/-- The result `verifyContract.post` asks for. -/
def verifyOut (s : State) : Bool :=
  Spec.RsaPss.verify G G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x1).toNat)
    (Spec.RsaPss.expectedSaltLen (s.gpr .x7) ((stackArg s 0).setWidth 32))

theorem anyV_eq (s : State) : anyV s = 0 ↔ (stackArg s 0).setWidth 32 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [anyV, BitVec.toNat_setWidth] at this ⊢
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    omega
  · intro h; unfold anyV; rw [h]; rfl

theorem expected_eq (s : State) :
    Spec.RsaPss.expectedSaltLen (s.gpr .x7) ((stackArg s 0).setWidth 32) = sLenV s := by
  unfold Spec.RsaPss.expectedSaltLen sLenV
  by_cases h : anyV s = 0
  · rw [ite_eq_left h, ite_eq_left ((anyV_eq s).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun e => h ((anyV_eq s).mpr e))]

theorem verifyOut_zero {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) = 0) :
    verifyOut G s = false := by
  unfold verifyOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.verify_zero G ..

section
variable {s : State} (hk1 : 64 ≤ (s.gpr .x1).toNat) (hk2 : (s.gpr .x1).toNat ≤ 1024)
  (h0 : s.mem (s.gpr .x0) ≠ 0)
include hk1 hk2 h0

theorem eb_bounds : 1 ≤ ebS s ∧ ebS s ≤ Proof.RsaPss.maxEmBits ∧ loS s + elS s = (s.gpr .x1).toNat ∧ loS s ≤ 1 := by
  have h0' : (s.mem (s.gpr .x0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hl8 := RsaPss.log2_lt8 (s.mem (s.gpr .x0))
  unfold loS elS ebS Spec.RsaPss.emLength ebV Proof.RsaPss.maxEmBits
  omega

omit hk2 in
/-- `emBits`, from the modulus' length and first byte. -/
theorem emBits_of :
    Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)) - 1 = ebS s := by
  rw [bytesAt_cons _ _ (by omega), RsaPss.emBits_eq _ h0, bytesAt_length]
  rfl

/-- Verifying: `lo` zero bytes, then a consistent encoding. -/
theorem verifyOut_enc :
    verifyOut G s = ((pubX s).take (loS s) == Spec.RsaPss.zeros (loS s) &&
      Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len) ((pubX s).drop (loS s)) (ebS s)
        (sLenV s)) := by
  obtain ⟨hb1, -, hlok, -⟩ := eb_bounds hk1 hk2 h0
  have hel : 1 ≤ elS s := by unfold elS Spec.RsaPss.emLength; omega
  unfold verifyOut pubX pubOut
  rw [expected_eq, RsaPss.verify_encode G (emBits_of hk1 h0) (by rw [bytesAt_length, bytesAt_length])
    (by rw [bytesAt_length]; unfold elS at hlok hel; omega), bytesAt_length]

end

/-- `lo ≤ 1` zero bytes: none, or the first byte zero. -/
theorem take_zeros {x : List Byte} {lo : Nat} (hlo : lo ≤ 1) (hx : 1 ≤ x.length) :
    (x.take lo == Spec.RsaPss.zeros lo) = (lo == 0 || x.getD 0 0 == 0) := by
  rcases (by omega : lo = 0 ∨ lo = 1) with rfl | rfl
  · rfl
  · obtain ⟨b, x, rfl⟩ : ∃ b y, x = b :: y := by
      cases x with
      | nil => simp at hx
      | cons b y => exact ⟨b, y, rfl⟩
    simp [Spec.RsaPss.zeros]

end VG.Proof.RsaPss.AArch64.Vfy
