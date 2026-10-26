module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelect
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive

/-! # Complete native private-exponent computation from encoded input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86 (byteAddr)
open VG.Impl.RsaKeyGen.X86.Key

def dPartRanges (n : Nat) : List (Nat × Nat) := loadExponentRanges n ++ exponentRanges n

theorem dPart_ok {s : State} {B : Addr} {Z n len : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (width : 2 ≤ n) (positive : 0 < len) (bound : len ≤ 8)
    (pointer : s.mem.readW (off B 56) 32 = p)
    (length : s.mem.readW (off B 60) 32 = BitVec.ofNat 32 len)
    (fit : p.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (byteAddr p) len)
    (separate : Region.Disjoint ⟨byteAddr p, len⟩ ⟨off B kEv, 8⟩)
    (one : num s.mem B n aOne = 1) :
    WP isa (dPart n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (dPartRanges n) s.mem t.mem ∧
      val32 t.mem B kEv 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len) ∧
      num t.mem B n aE = val32 t.mem B kEv 2 ∧
      slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr p) len)) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dPart
  refine WP.seq (WP.mono (loadExponent_ok h width positive bound pointer length fit readable separate)
    fun u ⟨hu, Ou, exponent, loaded, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (loadExponent_preserves_num (by decide) (h.fit64 (by decide)) Ou).trans one
  have Lu : num u.mem B n aL = num s.mem B n aL :=
    loadExponent_preserves_num (by decide) (h.fit64 (by decide)) Ou
  refine WP.mono (dSelect_ok hu width loaded oneU) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  rw [exponent, Lu] at inverse
  refine ⟨ht, (Ou.mono (fun r hr => List.mem_append_left _ hr)).trans
    (Ot.mono (fun r hr => List.mem_append_right _ hr)),
    (exponent_preserves_e Ot).trans exponent, ?_, bit, inverse, (Ku.mono (by decide)).trans Kt⟩
  exact (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ot).trans
    (loaded.trans (exponent_preserves_e Ot).symm)

end VG.Proof.RsaKeyGen.X86.Key
