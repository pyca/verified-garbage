module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHash
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAdd

/-! # A p-candidate contribution hashes the exact wrapped seed -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pHashArgs_ok {s : State} : WP isa (.block pHashArgs) s fun t =>
    t.gpr .esi = s.gpr .edi ∧ t.gpr .edi = s.gpr .edx ∧ t.mem = s.mem ∧ Keeps [.esi, .edi] s t := by
  unfold pHashArgs
  refine wp_movS rfl fun a sa _ => wp_movS rfl fun t at' _ => WP.block_nil ?_
  exact ⟨(at'.other _ (by decide)).trans sa.gpr, at'.gpr.trans (sa.other _ (by decide)), at'.mem.trans sa.mem,
    (sa.keeps.mono (by decide)).trans (at'.keeps.mono (by decide))⟩

theorem pSeedHash_ok {H : Hash} (K : HashOK H) {s : State} {source wrapped output scratch : BitVec 32}
    (bs : List Byte) {offset : Nat} (R : HashResources K wrapped output scratch bs.length s)
    (lengthBound : bs.length < 2 ^ 31) (offsetBound : offset < 2 ^ 24)
    (si : s.gpr .esi = source) (di : s.gpr .edi = wrapped) (dx : s.gpr .edx = output)
    (ax : s.gpr .eax = BitVec.ofNat 32 offset) (bp : s.gpr .ebp = scratch)
    (sourceFit : source.toNat + bs.length ≤ 2 ^ 32)
    (sourceRead : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (source.setWidth 64) i) 1)
    (wrappedWrite : ∀ i < bs.length, InRegions s.wr (off (wrapped.setWidth 64) i) 1)
    (bytes : ∀ i < bs.length, s.mem (off (source.setWidth 64) i) = bs.getD i 0)
    (apart : ∀ i < bs.length, ∀ j < bs.length, off (source.setWidth 64) i ≠ off (wrapped.setWidth 64) j) :
    WP isa (pSeedHash H bs.length) s fun t =>
      (Spec.Sha256.bytesAt t.mem (output.setWidth 64) H.F).take H.D =
        K.SH.H.hash (Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + offset)) ∧
      Frame [⟨wrapped.setWidth 64, bs.length⟩, ⟨(scratch + 512#32).setWidth 64, H.S⟩,
        ⟨output.setWidth 64, H.F⟩, ⟨scratch.setWidth 64, K.Wb⟩, stk s] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi] s t := by
  unfold pSeedHash
  refine WP.seq (WP.mono (seedAdd_ok bs lengthBound offsetBound si di sourceFit R.inputBound ax sourceRead wrappedWrite bytes apart)
    fun a ⟨wrappedBytes, Oa, Ka⟩ => ?_)
  have Fa : Frame [⟨wrapped.setWidth 64, bs.length⟩] s.mem a.mem := by
    intro x hx
    apply Oa x
    intro i hi eq
    apply hx ⟨wrapped.setWidth 64, bs.length⟩ (by simp)
    rw [eq]
    exact Offset.contains_base _ hi (by omega)
  refine WP.seq (WP.mono pHashArgs_ok fun b ⟨sib, dib, mem, Kb⟩ => ?_)
  have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi] s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
  refine WP.mono (seedHash_ok K bs.length (R.keeps Ksb (by decide))
    (sib.trans ((Ka.1 _ (by decide)).trans di)) (dib.trans ((Ka.1 _ (by decide)).trans dx))
    ((Ksb.1 _ (by decide)).trans bp)) fun t ⟨hashed, Ft, Kt⟩ => ?_
  refine ⟨?_, ?_, Ksb.trans (Kt.mono (by decide))⟩
  · rw [mem] at hashed
    change _ = K.SH.H.hash (Spec.Rsa.bytesAt a.mem (wrapped.setWidth 64) bs.length) at hashed
    rw [wrappedBytes] at hashed
    exact hashed
  · have Fb : Frame [⟨wrapped.setWidth 64, bs.length⟩] s.mem b.mem := by rw [mem]; exact Fa
    have stack : stk b = stk s := congrArg (fun sp => below sp 48) (Ksb.1 _ (by decide))
    rw [stack] at Ft
    exact (Fb.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans
      (Ft.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))
end VG.Proof.Dsa.X86.Generation
