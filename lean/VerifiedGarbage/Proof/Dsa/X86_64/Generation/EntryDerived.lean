module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameDerivations

/-! # Initialize the three workspace pointers and the witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def workspaceSlots : List (Nat × Nat) := [(3, wrappedSeed), (4, hashes), (14, VG.Impl.Dsa.Generation.Layout.hash)]

def workspaceWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (derivedWords workspaceSlots B W) 16 0

theorem entryDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block Impl.Dsa.X86_64.Generation.entryDerived) s fun t =>
      Rep t.mem F S V (workspaceWords B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.entryDerived
  apply WP.block_append
  refine WP.mono (frameDerivations_ok workspaceSlots (by
    intro slot hs
    simp only [workspaceSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hbase) fun u ⟨Ru, fu, ku⟩ => ?_
  refine WP.mono (frameZero_ok G Ru ((ku.gpr (by decide)).trans hsp)
    (by rw [ku.2.2]; exact hfr) (by decide : 16 < nW)) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
