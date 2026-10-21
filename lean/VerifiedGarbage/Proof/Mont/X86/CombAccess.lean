module

import VerifiedGarbage.Proof.Mont.X86.CombCopy
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Public comb table access shares its pointer setup and copying proof. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem publicSelect_ok {s : State} {base : Addr} {size n tab dst : Nat}
    (hs : Scr s base size) (hn : 0 < n) (header : 8 ≤ size)
    (src : entry n tab (w32 s.mem base 4)+8*n ≤ size) (out : dst+8*n ≤ size)
    (sep : dst+8*n ≤ entry n tab (w32 s.mem base 4) ∨
      entry n tab (w32 s.mem base 4)+8*n ≤ dst) :
    WP isa (VG.Impl.Mont.X86.Comb.publicSelect n tab dst) s fun t =>
      Outside base dst (8*n) s.mem t.mem ∧
      wordsVal t.mem base dst n = wordsVal s.mem base (entry n tab (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.publicSelect
  refine WP.seq (WP.mono (copySetup_ok hs (by have := hs.size_lt; omega)
    (readSrc_sc hs (d := 4) header)) fun u ⟨M, P, Q, C, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.mono (copyLoop_ok (x := entry n tab (w32 s.mem base 4)) (y := 0) (sd := 0) (dd := dst)
    (N := 2*n) ⟨hu.wr, hu.nowrap⟩ (by omega) (by simp) (by simp)
    (by omega) (by omega) (by omega) P Q C) fun t ⟨O, V, K'⟩ => ?_
  refine ⟨?_, ?_, K.trans (K'.mono (by decide))⟩
  · simpa only [Nat.zero_add, show 4*(2*n) = 8*n by omega, M] using O
  · simpa only [wordsVal_eq_val32, Nat.zero_add, Nat.add_zero, M] using V

theorem copyToComb_ok {s : State} {base : Addr} {size n tab src : Nat}
    (hs : Scr s base size) (hn : 0 < n)
    (input : src+8*n ≤ size) (out : entry n tab (s.gpr .esi).toNat+8*n ≤ size)
    (sep : src+8*n ≤ entry n tab (s.gpr .esi).toNat ∨
      entry n tab (s.gpr .esi).toNat+8*n ≤ src) :
    WP isa (VG.Impl.Mont.X86.Comb.copyToComb n tab src) s fun t =>
      Outside base (entry n tab (s.gpr .esi).toNat) (8*n) s.mem t.mem ∧
      wordsVal t.mem base (entry n tab (s.gpr .esi).toNat) n = wordsVal s.mem base src n ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.copyToComb
  refine WP.seq (WP.mono (copySetup_ok hs (by have := hs.size_lt; omega) rfl)
    fun u ⟨M, P, Q, C, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.mono (copyLoop_ok (x := 0) (y := entry n tab (s.gpr .esi).toNat) (sd := src) (dd := 0)
    (N := 2*n) ⟨hu.wr, hu.nowrap⟩ (by omega) (by simp) (by simp)
    (by omega) (by omega) (by omega) Q P C) fun t ⟨O, V, K'⟩ => ?_
  refine ⟨?_, ?_, K.trans (K'.mono (by decide))⟩
  · simpa only [Nat.add_zero, show 4*(2*n) = 8*n by omega, M] using O
  · simpa only [wordsVal_eq_val32, Nat.zero_add, Nat.add_zero, M] using V

end VG.Proof.Mont.X86.Comb
