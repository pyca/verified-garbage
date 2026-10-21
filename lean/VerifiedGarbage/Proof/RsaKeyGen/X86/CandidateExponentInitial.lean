module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentTimingInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSave
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateExponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Public exponent bytes enter filtering with one shared native value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateExponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure Initial (workspace p e : BitVec 32) (size w candidate len exponent : Nat) (s : State) : Prop where
  scratch : Scr s (workspace.setWidth 64) size
  stack : s.gpr .esp = p
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  candidateEq : val32 s.mem (workspace.setWidth 64) (slot w 0) (2 * w) = candidate
  large : 1 < candidate
  odd : candidate % 2 = 1
  pointer : s.mem.readW (off (workspace.setWidth 64) 12) 32 = e
  length : w32 s.mem (workspace.setWidth 64) 16 = len
  ePositive : 0 < len
  eBound : len ≤ 8
  eFit : e.toNat + len ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len
  separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨workspace.setWidth 64, size⟩
  exponentEq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) = exponent
  fit : 40 ≤ p.toNat
  separateStack : p.toNat ≤ (workspace.setWidth 64).toNat ∨ (workspace.setWidth 64).toNat + size + 40 ≤ p.toNat

theorem Initial.header {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : 256 ≤ size := by
  have space := S.space
  have width := S.width
  unfold slot stride VG.Impl.Bignum.hdrBytes at space
  omega

theorem Initial.savedLo {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : 400 ≤ slot w 5 := by
  have width := S.width
  unfold slot stride VG.Impl.Bignum.hdrBytes
  omega

theorem Initial.workspace {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem Initial.save_ok {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateSave.save (2 * w) (slot w 0) (slot w 5)) s fun t =>
      Scr t (workspace.setWidth 64) size ∧ Outside (workspace.setWidth 64) (slot w 5) (8 * w) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have gap : slot w 0 + 8 * w ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  refine WP.mono (CandidateSave.save_ok S.scratch (by have := S.width; omega)
    (by have := S.space; omega) (by have := S.space; omega) (Or.inr (Or.inr (by omega)))
    (by rw [S.candidateEq]; exact S.odd)) fun t ⟨_, O, K⟩ => ?_
  rw [show 4 * (2 * w) = 8 * w by omega] at O
  exact ⟨S.scratch.of_keeps K (by decide), O, K.mono (by decide)⟩

theorem Initial.prepare_ok {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateExponent.prepare w) s
      (ExponentFilter.TimingInput workspace p size w candidate exponent) := by
  refine WP.mono (CandidateExponent.prepare_ok S.scratch S.width S.widthBound S.space S.candidateEq S.large S.odd
    S.pointer S.length S.ePositive S.eBound S.eFit S.readable S.separateE
    (by rw [S.stack]; exact S.fit) (by rw [S.stack]; exact S.separateStack)) fun t ⟨I, _, _, K⟩ => ?_
  rw [S.exponentEq] at I
  exact ⟨I, (K.1 .esp (by decide)).trans S.stack⟩

end VG.Proof.RsaKeyGen.X86.CandidateExponent
