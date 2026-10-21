module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs

public import VerifiedGarbage.Proof.Framework.X86.ArgTaint

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.CacheHead
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Cache setup leaks only the public workspace geometry -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem cache_trace {s t u v : State} {W : Addr} {L S : Nat} {A B : Nat → BitVec 32}
    (hw : Ws s W L) (tw : Ws t W L) (ha : RawArgs s W L A) (ta : RawArgs t W L B)
    (base : (A 0).toNat = W.toNat) (tbase : (B 0).toNat = W.toNat)
    (scratch : w32 s.mem W 80 = (W.toNat + S) % 2 ^ 32)
    (tscratch : w32 t.mem W 80 = (W.toNat + S) % 2 ^ 32) (header : 84 ≤ L)
    (agree : VG.X86.Taint.Agree (argTaint [] 24) s t) {ls lt : List Leak}
    (ES : Exec isa (.block VG.Impl.Mont.X86.PreparedSquare.cache) s ls u)
    (ET : Exec isa (.block VG.Impl.Mont.X86.PreparedSquare.cache) t lt v) :
    ls = lt ∧ VG.X86.Taint.Agree (argTaint [] 24) u v := by
  have relation : RelCT isa (fun x y => x = s ∧ y = t ∧ VG.X86.Taint.Agree (argTaint [] 24) x y)
      (.block VG.Impl.Mont.X86.PreparedSquare.cache) (VG.X86.Taint.Agree (argTaint [] 24)) := by
    change RelCT isa _ (.block (cacheHead ++ (saveCode ++ cacheTail))) _
    refine RelCT.block_append (RelCT.seq ?_ cacheRest_relCT)
    intro x y lx ly z z' H EX EY
    obtain ⟨rfl, rfl, H⟩ := H
    obtain ⟨trace, Agree⟩ := cacheHead_relCT _ _ _ _ _ _ H EX EY
    obtain ⟨eax, ecx, _, _⟩ := wp_result (cacheHead_ok hw ha base scratch header) EX
    obtain ⟨teax, tecx, _, _⟩ := wp_result (cacheHead_ok tw ta tbase tscratch header) EY
    refine ⟨trace, arg_republish Agree ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [eax, teax]
      exact BitVec.eq_of_toNat_eq (base.trans tbase.symm)
    · exact ecx.trans tecx.symm
  exact relation _ _ _ _ _ _ ⟨rfl, rfl, agree⟩ ES ET

end VG.Proof.Mont.X86.PreparedSquare
