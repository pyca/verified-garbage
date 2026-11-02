module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply

/-! # A fast-setup squaring uses the verified callable prepared multiplier -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem mm_congr {c w x y : Nat} (odd : c % 2 = 1) :
    VG.Proof.MillerRabin.Word32.mm c w x y * 2 ^ (64 * w) % c = x * y % c := by
  unfold VG.Proof.MillerRabin.Word32.mm
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_comm (VG.Proof.MillerRabin.Word32.rinv c w),
    Nat.mul_mod, VG.Proof.MillerRabin.Word32.R_rinv odd, ← Nat.mul_mod, Nat.mul_one]

theorem square_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {capacity c : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) (M : Modulus g c s.mem)
    (caller : Caller g capacity p s) (odd : c % 2 = 1)
    (lt : val32 s.mem g.W (g.array 6) g.words < c) :
    WP isa (VG.Impl.MillerRabin.X86.mulY name mont 6) s fun t =>
      Context g t ∧ Modulus g c t.mem ∧ Caller g capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words < c ∧
      val32 t.mem g.W (g.array 6) g.words * 2 ^ (64 * g.w) % c =
        val32 s.mem g.W (g.array 6) g.words * val32 s.mem g.W (g.array 6) g.words % c ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem := by
  refine WP.mono (mulY_ok verified noSp stack v C length M (by unfold Proof.Rsa.Mont.Operand; decide) odd lt caller.readLen
    (by rw [caller.sp]; exact caller.low) (by rw [caller.sp]; exact caller.stackFar)) ?_
  rintro t ⟨V, O, K, Ct, Mt, F⟩
  rw [caller.sp] at F
  exact ⟨Ct, Mt, caller.keepFrame K (by decide) F,
    by rw [V]; exact VG.Proof.MillerRabin.Word32.mm_lt (by omega),
    by rw [V]; exact mm_congr odd, O, K, F⟩

end VG.Proof.RsaKeyGen.X86.FastR2
