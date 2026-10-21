module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFastSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32

/-! # The 65537 fast path restores EDI and keeps all candidate bytes read-only -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.ExponentFilter VG.Impl.Bignum.X86.PublicContext

theorem fast_ok {s : State} {w : Nat} {p : BitVec 32}
    (positive : 0 < w) (lengthBound : 8 * w < 2 ^ 32)
    (fit : 20 ≤ (s.gpr .esp).toNat) (sourceFit : p.toNat + 8 * w ≤ 2 ^ 32)
    (pointer : s.gpr .edi + BitVec.ofNat 32 (slot w 5) = p)
    (sourceRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4)
    (sourceFar : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint (below (s.gpr .esp) 20)) :
    WP isa (fast w) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)).toNat ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold fast
  refine WP.frameAlloc (by decide) (by decide) (by decide) fit (NoSp.of_all (by rfl)) ?_
  let initial := allocFrame 20 s
  have C : Sieve.StackContext (s.gpr .esp - 20#32) initial := FilterStack.allocated_context fit
  refine WP.seq (WP.mono (fastArgs_ok (w := w) C) fun a ⟨ptrA, endA, savedA, Oa, Ka⟩ => ?_)
  have ptr : a.gpr .edi = p := by rw [ptrA, allocFrame_gpr _ _ (by decide), pointer]
  have Ca := C.keep Ka (by decide)
  have frameA : Frame [below (s.gpr .esp) 20] s.mem a.mem := by
    simpa only [allocFrame_mem, below, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame (Oa.mono (o' := 0) (n' := 20) (by decide) (by decide)) (by decide)
  have value : val32 a.mem (p.setWidth 64) 0 (2 * w) = val32 s.mem (p.setWidth 64) 0 (2 * w) := by
    apply val32_congr
    intro i index
    exact congrArg BitVec.toNat (frameA.readW (r := ⟨p.setWidth 64, 8 * w⟩)
      (Offset.contains_base _ (by omega) (by omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact sourceFar) (by decide))
  refine WP.seq (WP.mono (FermatExponent.code_ok a p w 4 positive (by omega) (by omega)
    (by
      intro i index
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := sourceRead i index
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    (Ca.access 4 (by decide)) (by
      change a.mem.readW (a.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4)) 32 = _
      rw [Ca.address 4 (by decide), endA, allocFrame_gpr _ _ (by decide), pointer]
      rw [show 4 * (2 * w) = 8 * w by omega]) ptr) fun b ⟨result, Mb, Kb⟩ => ?_)
  have Cb := Ca.keep Kb (by decide)
  refine wp_movS (v := initial.gpr .edi) (by
    change readSrc b (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some (initial.gpr .edi)
    rw [Cb.read 0 (by decide), Mb, savedA]) fun t T _ => WP.block_nil ?_
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] initial t :=
    ((Ka.mono (by decide)).trans Kb).widen T.keeps
  have restored : t.gpr .edi = initial.gpr .edi := T.gpr
  have Kbody : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] initial t := by
    refine ⟨?_, Kall.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, FilterStack.freed_keeps Kbody (by decide)⟩
  · rw [freed_gpr _ _ (by decide), T.other .eax (by decide), result, value]
  · rw [freed_mem, T.mem, Mb]
    exact frameA

end VG.Proof.RsaKeyGen.X86.ExponentFilter
