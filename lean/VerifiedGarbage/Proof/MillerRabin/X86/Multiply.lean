module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.MillerRabin.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.CallSetup
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame

/-! # The round's multiplication operation reuses its prepared modulus -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem mulY_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {capacity b c : Nat} (length : g.L = 8 * capacity) (M : Modulus g c s.mem)
    (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1)
    (rightLt : val32 s.mem g.W (g.array b) g.words < c)
    (readLen : readSrc s (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity))
    (fit : 80 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)) :
    WP isa (mulY name code b) s fun t =>
      val32 t.mem g.W (g.array 6) g.words = Word32.mm c g.w
        (val32 s.mem g.W (g.array 6) g.words) (val32 s.mem g.W (g.array b) g.words) ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Context g t ∧ Modulus g c t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below (s.gpr .esp) 80]) s.mem t.mem := by
  unfold mulY
  refine WP.seq (WP.mono (mulSetup_ok C capacity b readLen) fun a ⟨A, M₁, K⟩ => ?_)
  have Ca := C.keepMem K (by decide) M₁
  have Ma : Modulus g c a.mem := by rw [M₁]; exact M
  have sp : a.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  refine WP.mono (mulCall_ok verified noSp stack v Ca length Ma A right odd
    (by rw [M₁]; exact rightLt) (by rw [sp]; exact fit) (by rw [sp]; exact far)) ?_
  rintro t ⟨V, O, Kt, Ct, Mt, F⟩
  rw [M₁] at V O F
  rw [sp] at F
  exact ⟨V, O, K.trans Kt, Ct, Mt, F⟩

end VG.Proof.MillerRabin.X86
