module
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.KcResult

import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Public modulus and exponent validation for both key-check APIs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem modulus_ok {g : CallGeometry} {s : State} (h : Inputs g s)
    (lo : 64 ≤ (g.args 1).toNat) (hi : (g.args 1).toNat ≤ 1024) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 0))
      (.block VG.Impl.Bignum.X86.modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have zero : 2 * 0 < scratchArg g.full := by cases g.full <;> decide
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 0 (by cases g.full <;> decide)).readSrc
    (h.arguments 1 (by cases g.full <;> decide)).readSrc) fun u ⟨p, c, m, r⟩ => ?_)
  refine WP.mono (modulusCheck_ok u lo hi (by rw [p]; exact h.inputFit 0 zero)
    (by rw [p, r.2.1, r.2.2]; exact h.inputRead 0 zero)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨z, mt, rt⟩ => ?_
  rw [p, m] at z
  exact ⟨z, mt.trans m, (r.mono (by decide)).trans (rt.mono (by decide))⟩

theorem exponent_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) VG.Impl.Bignum.X86.exponentCheck) s
      fun t => t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (numbers g s.mem).e).toNat ∧
        t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have one : 2 * 1 < scratchArg g.full := by cases g.full <;> decide
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 2 (by cases g.full <;> decide)).readSrc
    (h.arguments 3 (by cases g.full <;> decide)).readSrc) fun u ⟨p, c, m, r⟩ => ?_)
  refine WP.mono (exponentCheck_ok u (eb := inputBytes g s.mem 1)
    (by rw [inputBytes, bytesAt_length]; exact h.inputPositive 1 one)
    (by rw [inputBytes, bytesAt_length]; exact (g.args 3).isLt)
    (by rw [inputBytes, bytesAt_length]; exact h.inputFit 1 one)
    (by rw [inputBytes, bytesAt_length, r.2.1, r.2.2]; exact h.inputRead 1 one)
    (by intro i hi; rw [m]; simp only [inputBytes, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]; rfl)
    p (by rw [inputBytes, bytesAt_length]; simpa only [CallGeometry.buffer, BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨v, mt, rt⟩ => ?_
  exact ⟨v, mt.trans m, (r.mono (by decide)).trans (rt.mono (by decide))⟩

theorem failure_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa failure s fun t => Inputs g t ∧ t.gpr .eax = 0 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨h.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), T.gpr, T.mem, T.keeps⟩

theorem invalid_modulus (full : Bool) (k : Nat) (v : Vals) (h : Spec.Rsa.modulusValid v.n k = false) :
    validity full k v = false := by
  cases full <;> simp only [validity, Bool.false_eq_true, ite_false, ite_true,
    Spec.Rsa.keyValid, Spec.Rsa.crtKeyValid, h, Bool.false_and]

theorem invalid_exponent (full : Bool) (k : Nat) (v : Vals) (h : Spec.Rsa.exponentValid v.e = false) :
    validity full k v = false := by
  cases full <;> simp only [validity, Bool.false_eq_true, ite_false, ite_true,
    Spec.Rsa.keyValid, Spec.Rsa.crtKeyValid, h, Bool.and_false, Bool.false_and]
end VG.Proof.Rsa.X86.KeyCheck
