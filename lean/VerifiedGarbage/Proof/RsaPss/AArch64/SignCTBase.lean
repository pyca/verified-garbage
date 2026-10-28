module
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT

/-!
# RSASSA-PSS signing on AArch64: constant time, the public data

The pointers, the lengths and the bytes of `n` and `e` are public (`PubS`,
from `signContract.pub`); the digest, the salt and the private key are
secret. Two runs with the same public data as an anchor `a` (`E`) are
related at each point of the code by what correctness says there (`At`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64.Sgn (stackArgs_thirteen)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 13, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat

theorem PubS.refl (s : State) : PubS s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

theorem pubS_of (G : Spec.Mgf1.Hash) {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPss.signContract G G abi S).pub s₁ s₂) :
    PubS s₁ s₂ := by
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  obtain ⟨hn, he⟩ := leak_eq2 (by rw [bytesAt_length, bytesAt_length, h3]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm,
      a10.symm, a11.symm, a12.symm]

/-- An entry state with the anchor's public data. -/
def E (D K : Nat) (a s : State) : Prop := PreS D K s ∧ PubS a s

/-- `J` at a point of the code, from an entry state with the anchor `a`'s
public data. -/
def At (D K : Nat) (J : State → State → Prop) (a t : State) : Prop := ∃ s, E D K a s ∧ J s t

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem n0 : s.mem (s.gpr .x2) = a.mem (a.gpr .x2) := by
  have hk := h.1.k1
  have e3 := h.gpr (r := .x3) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x2) (k := (s.gpr .x3).toNat) (by omega),
    bytesAt_cons a.mem (a.gpr .x2) (k := (a.gpr .x3).toNat) (by rw [← e3]; omega)] at this
  exact (List.cons.inj this).1

theorem scr : scr s = scr a := h.2.args 11 (by decide)

end E

/-- The first byte of `n`. -/
abbrev nx (s : State) : Nat := (s.mem (s.gpr .x2)).toNat

end VG.Proof.RsaPss.AArch64.Sgn
