module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryArguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryDerived
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Complete ABI argument initialization before size dispatch -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def entryWords (regs : Reg → BitVec 64) (incoming W : Nat → BitVec 64) : Nat → BitVec 64 :=
  workspaceWords (incoming 384) (copiedWords argumentSlots incoming (registerWords headerSlots regs W))

theorem argumentSlots_bounds {slot : Nat × Nat} (hs : slot ∈ argumentSlots) :
    frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64 := by
  simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem entrySetup_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (off F slot.1) 8) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.entryHeader ++ Impl.Dsa.X86_64.Generation.entryIncoming ++
      Impl.Dsa.X86_64.Generation.entryDerived)) s fun t =>
      Rep t.mem F S V (entryWords s.gpr (word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (entryHeader_ok G R hsp hfr) fun u ⟨Ru, fu, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (entryIncoming_ok G Ru ((ku.gpr (by simp)).trans hsp)
    (by rw [ku.2.2]; exact hfr) (fun slot hs => by rw [ku.2.1, ku.2.2]; exact hr slot hs))
    fun v ⟨Rv, fv, kv⟩ => ?_
  have words := copiedWords_congr argumentSlots (word u.mem F) (word s.mem F)
    (fun slot hs => frame_input_word fu (argumentSlots_bounds hs).1 (argumentSlots_bounds hs).2)
    (registerWords headerSlots s.gpr W)
  rw [words] at Rv
  have base : copiedWords argumentSlots (word s.mem F) (registerWords headerSlots s.gpr W) 5 = word s.mem F 384 := by
    rfl
  refine WP.mono (entryDerived_ok G Rv ((kv.gpr (by decide)).trans ((ku.gpr (by simp)).trans hsp))
    (by rw [kv.2.2, ku.2.2]; exact hfr) base) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, (fu.trans fv).trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
