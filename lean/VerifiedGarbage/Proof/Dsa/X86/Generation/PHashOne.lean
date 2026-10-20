module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHash
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashArguments

/-! # One contribution, driven entirely by persistent search-frame values -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pHashOne_ok {H : Hash} (K : HashOK H) {s : State} {base : Addr}
    {source wrapped hashes scratch : BitVec 32} (bs : List Byte) {offset count j : Nat}
    (F : SearchFrame s base)
    (sourceSlot : s.mem.readW (off base 4) 32 = source)
    (wrappedSlot : s.mem.readW (off base 12) 32 = wrapped)
    (hashesSlot : s.mem.readW (off base 16) 32 = hashes)
    (scratchSlot : s.mem.readW (off base 56) 32 = scratch)
    (offsetSlot : s.mem.readW (off base 8) 32 = BitVec.ofNat 32 offset)
    (R : HashResources K wrapped (hashes + BitVec.ofNat 32 ((count - j) * bs.length)) scratch bs.length s)
    (lengthBound : bs.length < 2 ^ 31) (offsetBound : offset + j < 2 ^ 24)
    (sourceFit : source.toNat + bs.length ≤ 2 ^ 32)
    (sourceRead : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (source.setWidth 64) i) 1)
    (wrappedWrite : ∀ i < bs.length, InRegions s.wr (off (wrapped.setWidth 64) i) 1)
    (bytes : ∀ i < bs.length, s.mem (off (source.setWidth 64) i) = bs.getD i 0)
    (apart : ∀ i < bs.length, ∀ k < bs.length, off (source.setWidth 64) i ≠ off (wrapped.setWidth 64) k) :
    WP isa (pHashOne H bs.length count j) s fun t =>
      (Spec.Sha256.bytesAt t.mem ((hashes + BitVec.ofNat 32 ((count - j) * bs.length)).setWidth 64) H.F).take H.D =
        K.SH.H.hash (Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + offset + j)) ∧
      Frame [⟨wrapped.setWidth 64, bs.length⟩, ⟨(scratch + 512#32).setWidth 64, H.S⟩,
        ⟨(hashes + BitVec.ofNat 32 ((count - j) * bs.length)).setWidth 64, H.F⟩,
        ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold pHashOne
  refine WP.seq (WP.mono (pContributionArgs_ok F bs.length count j)
    fun a ⟨si, di, ax, dx, bp, mem, Ka⟩ => ?_)
  rw [sourceSlot] at si
  rw [wrappedSlot] at di
  rw [hashesSlot] at dx
  rw [scratchSlot] at bp
  rw [offsetSlot, ← BitVec.ofNat_add] at ax
  refine WP.mono (pSeedHash_ok K bs (R.keeps Ka (by decide)) lengthBound offsetBound si di dx ax bp sourceFit
    (by intro i hi; rw [Ka.2.1, Ka.2.2]; exact sourceRead i hi)
    (by intro i hi; rw [Ka.2.2]; exact wrappedWrite i hi)
    (by intro i hi; rw [mem]; exact bytes i hi) apart) fun t ⟨value, O, Kt⟩ => ?_
  refine ⟨?_, ?_, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
  · simpa only [Nat.add_assoc] using value
  · rw [mem, show stk a = stk s from congrArg (fun sp => below sp 48) (Ka.1 _ (by decide))] at O
    exact O
end VG.Proof.Dsa.X86.Generation
