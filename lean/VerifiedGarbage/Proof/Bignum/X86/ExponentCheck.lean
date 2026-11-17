module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentScan
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentTestMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Bignum.X86.ExponentTest`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.ExponentTests`, which this module and modules that import it used -/

section

/-! # Test the public exponent's upper bound, parity and lower bound -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentBoundsTest_ok (s : State) :
    WP isa (.block exponentBoundsTest) s fun t =>
      t.zf = some (exponentBounds (s.gpr .ebx) (s.gpr .edx)) ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentBoundsTest
  refine wp_movS rfl fun s1 a _ => ?_
  refine wp_shr (by decide) fun s2 b _ => ?_
  refine wp_movS rfl fun s3 c _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s4 d => ?_
  refine wp_logicS (.inr rfl) rfl fun s5 e => ?_
  refine wp_orS rfl fun s6 f => ?_
  refine wp_cmpS rfl fun t g z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [z, f.gpr, e.other .ebp (by decide), d.other .ebp (by decide),
      c.other .ebp (by decide), b.gpr, a.gpr, e.gpr, d.gpr, c.gpr,
      b.other .ebx (by decide), a.other .ebx (by decide)]
    simp only [exponentBounds, ite_true, show AluOp.xor ≠ AluOp.and by decide,
      ite_false, BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [g.mem, f.mem, e.mem, d.mem, c.mem, b.mem, a.mem]
  · exact ((((((a.keeps.mono (by decide)).widen b.keeps).widen c.keeps).widen d.keeps).widen
      e.keeps).widen f.keeps).trans (g.keeps _)

theorem exponentOneTest_ok (s : State) :
    WP isa (.block exponentOneTest) s fun t =>
      t.zf = some (exponentIsOne (s.gpr .ebx) (s.gpr .edx)) ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentOneTest
  refine wp_movS rfl fun s1 a _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s2 b => ?_
  refine wp_orS rfl fun s3 c => ?_
  refine wp_cmpS rfl fun t d z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [z, c.gpr, b.gpr, a.gpr, b.other .edx (by decide), a.other .edx (by decide)]
    simp only [exponentIsOne, show AluOp.xor ≠ AluOp.and by decide,
      ite_false, BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [d.mem, c.mem, b.mem, a.mem]
  · exact (((a.keeps.mono (by decide)).widen b.keeps).widen c.keeps).trans (d.keeps _)

theorem exponentResult_ok (s : State) (b : Bool) :
    WP isa (exponentResult b) s fun t => t.gpr .eax = BitVec.ofNat 32 b.toNat ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  unfold exponentResult
  refine wp_movS rfl fun t h _ => WP.block_nil ?_
  exact ⟨h.gpr, h.mem, h.keeps.mono (by decide)⟩

end VG.Proof.Bignum.X86

end

end

/-! # The public-exponent decision matches the shared RSA limits exactly -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentTest_ok (s : State) :
    WP isa exponentTest s fun t =>
      t.gpr .eax = BitVec.ofNat 32
        (exponentBounds (s.gpr .ebx) (s.gpr .edx) && !exponentIsOne (s.gpr .ebx) (s.gpr .edx)).toNat ∧
      t.mem = s.mem ∧ Keeps [.ebp, .eax] s t := by
  rw [exponentTest, WP.seq_iff]
  refine WP.mono (exponentBoundsTest_ok s) ?_
  rintro u ⟨zero, memU, restU⟩
  refine WP.ite (exponentBounds (s.gpr .ebx) (s.gpr .edx)) zero ?_ ?_
  · intro bounds
    rw [WP.seq_iff]
    refine WP.mono (exponentOneTest_ok u) ?_
    rintro v ⟨one, memV, restV⟩
    rw [restU.1 .ebx (by decide), restU.1 .edx (by decide)] at one
    refine WP.ite (exponentIsOne (s.gpr .ebx) (s.gpr .edx)) one ?_ ?_
    · intro invalid
      refine WP.mono (exponentResult_ok v false) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, invalid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
    · intro valid
      refine WP.mono (exponentResult_ok v true) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by simpa [bounds, valid] using value, memT.trans (memV.trans memU), restU.trans (restV.trans restT)⟩
  · intro invalid
    refine WP.mono (exponentResult_ok u false) ?_
    rintro t ⟨value, memT, restT⟩
    exact ⟨by simpa only [invalid, Bool.false_and] using value, memT.trans memU, restU.trans restT⟩

end VG.Proof.Bignum.X86

end

end

/-! # The i686 validator implements the shared public-exponent predicate -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem exponentCheck_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentCheck s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentCheck, WP.seq_iff]
  refine WP.mono (exponentScan_ok s positive countFit sourceFit read bytes ptr count) ?_
  rintro u ⟨lo, hi, memU, restU⟩
  refine WP.mono (exponentTest_ok u) ?_
  rintro t ⟨value, memT, restT⟩
  rw [lo, hi, exponentTest_value] at value
  exact ⟨value, memT.trans memU, restU.trans (restT.mono (by decide))⟩

theorem exponentCheck_words_ok (s : State) {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length) :
    WP isa exponentCheck s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat ∧
      t.gpr .ebx = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
      t.gpr .edx = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb)) ∧
      t.mem = s.mem ∧ Keeps exponentClobbers s t := by
  rw [exponentCheck, WP.seq_iff]
  refine WP.mono (exponentScan_ok s positive countFit sourceFit read bytes ptr count) ?_
  rintro u ⟨lo, hi, memU, restU⟩
  refine WP.mono (exponentTest_ok u) ?_
  rintro t ⟨value, memT, restT⟩
  rw [lo, hi, exponentTest_value] at value
  exact ⟨value, (restT.1 .ebx (by decide)).trans lo,
    (restT.1 .edx (by decide)).trans hi, memT.trans memU, restU.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.X86
