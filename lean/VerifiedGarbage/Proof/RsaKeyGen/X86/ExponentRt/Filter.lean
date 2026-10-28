module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFilterContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Fast
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.General
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentClass
import VerifiedGarbage.Proof.RsaKeyGen.EvenExponent
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words

/-! # The exponent filter at a run-time width returns the exact coprimality bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.ExponentRt VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG.Proof.RsaKeyGen.X86.ExponentFilter (Input Output)

theorem nontrivial_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : exponent % 2 = 1) :
    WP isa (.seq (.block (equal 65537)) (.ite .e fast general)) s
      (Output base size w candidate exponent s) := by
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.equal_ok S.scratch S.header (by decide : 65537 < 2 ^ 32))
    fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  have lenA : a.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by rw [M]; exact len
  rw [S.exponentEq] at Z
  by_cases common : exponent = 65537
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true common]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine WP.mono (fast_ok A.scratch A.width A.widthBound A.space lenA A.saved A.fit A.separate)
      fun t ⟨result, F, Kt⟩ => ?_
    apply Output.prepend (s := s) (a := a) _ M K
    refine ⟨?_, A.stackFrameValue F, F.mono (fun _ mem => List.mem_cons_of_mem _ mem), Kt, A.stackWorkspaceFrame F⟩
    simpa only [common] using result
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false common]) (fun impossible => nomatch impossible) (fun _ => ?_)
    refine WP.mono (general_ok A.scratch A.width A.widthBound A.space lenA A.saved A.large A.odd A.exponentEq odd
      A.fit A.separate) fun t ⟨result, original, F, Kt, W⟩ => ?_
    exact (show Output base size w candidate exponent a t from ⟨result, original, F, Kt, W⟩).prepend M K

theorem odd_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : exponent % 2 = 1) :
    WP isa (.seq (.block (equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
      (.seq (.block (equal 65537)) (.ite .e fast general)))) s
      (Output base size w candidate exponent s) := by
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.equal_ok S.scratch S.header (by decide : 1 < 2 ^ 32))
    fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  rw [S.exponentEq] at Z
  by_cases one : exponent = 1
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true one]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    apply Output.prepend (s := s) (a := a) _ M K
    apply A.readonlyOutput _ T.mem T.keeps
    rw [T.gpr]
    simp only [one, Nat.gcd_one_right, decide_true, Bool.toNat_true]
    rfl
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false one]) (fun impossible => nomatch impossible) (fun _ => ?_)
    exact WP.mono (nontrivial_ok A (by rw [M]; exact len) odd) fun _ H => H.prepend M K

theorem filter_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa filter s (Output base size w candidate exponent s) := by
  unfold filter
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.parity_ok S.scratch S.header) fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  rw [S.exponentEq] at Z
  by_cases even : exponent % 2 = 0
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true even]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    apply Output.prepend (s := s) (a := a) _ M K
    apply A.readonlyOutput _ T.mem T.keeps
    rw [T.gpr]
    simp only [decide_eq_false (VG.Proof.RsaKeyGen.even_exponent_rejected S.odd S.large even), Bool.toNat_false]
    rfl
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false even]) (fun impossible => nomatch impossible) (fun _ => ?_)
    exact WP.mono (odd_ok A (by rw [M]; exact len) (by omega)) fun _ H => H.prepend M K

end VG.Proof.RsaKeyGen.X86.ExponentRt
