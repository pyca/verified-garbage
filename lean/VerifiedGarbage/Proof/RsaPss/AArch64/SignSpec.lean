module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS signing on AArch64: the outcome, by cases

`signOut G s`: what the contract asks of a call from `s`. It is `invalid`
if the modulus' first byte is zero (`signOut_zero`), and otherwise that of
the private operation on `lo` zero bytes and `encode`'s encoding into
`emBits = 8 (k - 1) + log₂ n₀` bits, or `invalid` if there is none
(`signOut_enc`); `EM` holds those bytes (`em_input`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64 (off off_add ebV)

/-- The outcome `signContract.post` asks for. -/
def signOut (G : Spec.Mgf1.Hash) (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len) (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat)

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

variable (G : Spec.Mgf1.Hash)

theorem signOut_zero {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) = 0) :
    signOut G s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero G ..

/-- `emBits`, from the modulus' length and first byte. -/
theorem emBits_of {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) - 1 =
      ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat := by
  rw [bytesAt_cons _ _ hk, RsaPss.emBits_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rfl

/-- Signing is the private operation on `lo` zero bytes and the encoding. -/
theorem signOut_enc {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    signOut G s = match Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat)
        (ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat) with
      | some e => privOut s (Spec.RsaPss.zeros ((s.gpr .x3).toNat -
          Spec.RsaPss.emLength (ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat)) ++ e)
      | none => .invalid := by
  unfold signOut privOut
  rw [RsaPss.sign_encode G (emBits_of hk h0), VG.Proof.RsaPkcs1Sig.bytesAt_length]
  cases Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) (ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat) <;>
    rfl

/-- `EM`: `lo` zero bytes, then the encoding. -/
theorem em_input {m : Mem} {S : Addr} {k lo el : Nat} {e : List Byte} (hlok : lo + el = k) (hlo : lo ≤ 1)
    (hz : lo = 1 → m (off S oEm) = 0) (he : Spec.Rsa.bytesAt m (off S (oEm + lo)) el = e) :
    Spec.Rsa.bytesAt m (off S oEm) k = Spec.RsaPss.zeros lo ++ e := by
  rcases (by omega : lo = 0 ∨ lo = 1) with rfl | rfl
  · rw [Nat.add_zero] at he
    rw [← he, show k = el by omega]
    rfl
  · rw [bytesAt_cons _ _ (by omega), hz rfl, show off S oEm + 1 = off S (oEm + 1) from off_add S oEm 1,
      show k - 1 = el by omega, he]
    rfl

end VG.Proof.RsaPss.AArch64.Sgn
