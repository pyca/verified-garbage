module
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedContext
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorLayout
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCandidate

/-! # One generator-search body restores its prepared context from persistent state -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorBody_ok {G : PrimeConfig} {frame : Addr} {parent : BitVec 32}
    {words : Nat → BitVec 32} {s : State}
    (L : GeneratorLayout G frame parent) (R : PrimePrepared G s)
    (F : SearchFrame s frame) (W : FrameWords s.mem frame words) (saved : words 5 = parent)
    (base : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 = G.base)
    (fit : (words 21).toNat + G.len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) ((words 21).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(words 21).setWidth 64, G.len⟩ ⟨G.base, G.size⟩)
    (exponentRead : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr)
      (off ((generatorExponentPointer parent).setWidth 64) d) 4)
    (outputWrite : ∀ e k, e + k ≤ G.len → InRegions s.wr
      (off ((generatorOutputPointer parent).setWidth 64) e) k) :
    WP isa (generatorBody G.len) s fun t =>
      let h := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((words 21).setWidth 64) G.len)
      let e := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((generatorExponentPointer parent).setWidth 64) G.len)
      let accepted := 1 < h ∧ h < G.modulus - 1 ∧ 1 < h ^ e % G.modulus
      PrimeReady G t ∧ SearchFrame t frame ∧
      FrameWords t.mem frame (frameUpdate words 19 (if accepted then 1 else 3)) ∧
      (accepted → Spec.Rsa.bytesAt t.mem ((generatorOutputPointer parent).setWidth 64) G.len =
        Spec.Dsa.encodeBE G.len (h ^ e % G.modulus)) ∧
      Frame [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩, ⟨off frame 76, 4⟩,
        ⟨(generatorOutputPointer parent).setWidth 64, G.len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold generatorBody
  refine WP.seq (WP.mono (generatorArguments_ok F W) fun a ⟨di, si, mem, Ka⟩ => ?_)
  have prepared := R.frame (by rw [mem]; exact Frame.refl [] s.mem) (by simp) Ka (by decide)
  have Ra := prepared.restore (by rw [di, saved, base])
  have resources : GeneratorResources G frame parent words a :=
    ⟨Ra, F.keeps Ka (by decide), by rw [mem]; exact W, saved,
      by intro d hd; rw [Ka.2.1, Ka.2.2]; exact exponentRead d hd,
      by intro e k hk; rw [Ka.2.2]; exact outputWrite e k hk⟩
  refine WP.mono (generatorCandidate_ok L resources
    (by rw [si]; exact fit)
    (by intro d hd; rw [si, Ka.2.1, Ka.2.2]; exact read d hd)
    (by rw [si]; exact apart)) fun t ⟨Rt, Ft, Wt, output, Ot, Kt⟩ => ?_
  rw [si, mem] at Wt output
  rw [mem] at Ot
  exact ⟨Rt, Ft, Wt, output, Ot, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
