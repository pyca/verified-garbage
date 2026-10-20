module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.QCandidate

/-! # The seed-search frame produces the specified subgroup candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem qBuild_ok {H : Hash} (K : HashOK H) {s : State} {base : Addr} {words : Nat → BitVec 32} (len : Nat)
    (F : SearchFrame s base) (W : FrameWords s.mem base words)
    (R : HashResources K (words 1) (words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q) (words 14) len s)
    (hn : 2 ≤ len) (hD : H.D = len) (hF : H.F = len)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * len) bs)
    (hashLen : ∀ bs, (Spec.Dsa.seedHash (8 * len) bs).length = len) :
    WP isa (qBuild H len) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem
        ((words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q).setWidth 64) len) =
        Spec.Dsa.qCandidate (8 * len) (Spec.Sha256.bytesAt s.mem ((words 1).setWidth 64) len) ∧
      Frame [⟨(words 14 + 512#32).setWidth 64, H.S⟩,
        ⟨(words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q).setWidth 64, H.F⟩,
        ⟨(words 14).setWidth 64, K.Wb⟩, stk s] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold qBuild
  refine WP.seq (WP.mono (qHashArgs_ok F W) fun a ⟨si, di, bp, mem, Ka⟩ => ?_)
  refine WP.mono (qCandidate_ok K len (R.keeps Ka (by decide)) hn hD hF hash hashLen si di bp)
    fun t ⟨value, O, Kt⟩ => ?_
  rw [mem] at value O
  have stack : stk a = stk s := by unfold stk; rw [Ka.1 _ (by decide)]
  rw [stack] at O
  exact ⟨value, O, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
