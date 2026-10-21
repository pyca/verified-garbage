module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionStore
import VerifiedGarbage.Proof.Rsa.X86.DivLoop

/-! # Complete native quotient and remainder for RSA key generation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem divisionFrom_ok {s : State} {B : Addr} {Z n src divisor quotient remainder : Nat}
    (h : Ws s B Z n 4) (input : DivisionInputs Z n src divisor)
    (output : DivisionOutputs Z n quotient remainder) (positive : 0 < val32 s.mem B divisor n) :
    WP isa (divisionFrom n src divisor quotient remainder) s fun t =>
      Ws t B Z n 4 ∧
      Outs B [(hdr, 4 * (4 * (n + 2))), (quotient, 4 * n), (remainder, 4 * n)] s.mem t.mem ∧
      val32 t.mem B quotient n = val32 s.mem B src n / val32 s.mem B divisor n ∧
      val32 t.mem B remainder n = val32 s.mem B src n % val32 s.mem B divisor n ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold divisionFrom
  refine WP.seq (WP.mono (divisionLoad_ok h input) fun u ⟨hu, Ou, numerator, modulus, Ku⟩ => ?_)
  have ctx := division_context hu
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok ctx) fun v ⟨_, Ov, Kv, computed⟩ => ?_)
  have result := computed (by rw [modulus]; exact positive)
    (by rw [modulus]; exact val32_lt s.mem B divisor n)
  rw [numerator, modulus] at result
  have hv := hu.rest Kv
  have remBound : (divisionGeometry B Z n).value v.mem 1 < 2 ^ (32 * n) := by
    rw [result.1]
    exact Nat.lt_trans (Nat.mod_lt _ positive) (val32_lt s.mem B divisor n)
  refine WP.mono (divisionStore_ok hv output remBound) fun t ⟨ht, Ot, Q, R, Kt⟩ => ?_
  refine ⟨ht, ?_, Q.trans result.2, R.trans result.1,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  have priorFrame : Outside B hdr (4 * (4 * (n + 2))) s.mem v.mem := Ou.trans (division_frame Ov)
  exact (Outs.of_outside priorFrame (List.mem_cons_self ..)).trans
    (Ot.mono (fun r hr => List.mem_cons_of_mem _ hr))

end VG.Proof.RsaKeyGen.X86.Key
