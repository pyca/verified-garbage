module
public import VerifiedGarbage.Proof.Rsa.X86.KcABI
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.KcResult
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Rsa.X86.KcBounds
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Rsa.X86.KcInstalled
import VerifiedGarbage.Proof.Rsa.X86.KcResources
import VerifiedGarbage.Proof.Rsa.X86.KcBodyPublic
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Words

/-! # Key validation preserves saved registers and the return address -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem body_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Outside g.base 16 (g.size - 16) m m')
    (saved : Saved m (off g.base) regs PublicFn.savedRegisters) :
    Saved m' (off g.base) regs PublicFn.savedRegisters := by
  have low : 16 ≤ g.size := by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega
  have high : g.size ≤ 2 ^ 64 := by have := h.ws.workspace.nowrap; omega
  have frame := outside_frame f (by omega)
  intro p hp
  have bound : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (frame.readW (r := ⟨g.base, 16⟩) (Offset.contains_base _ bound (by omega)) ?_ (by decide)).trans (saved p hp)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.base_disjoint g.base (Nat.le_refl 16) (by omega)

theorem operation_ok {full : Bool} {s : State} (a : ABI full s) :
    WP isa (code full) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (validity full (arg s 1).toNat (numbers (caller full s) s.mem)).toNat ∧
      abiPreserved s t := by
  have low : 16 ≤ (caller full s).size := by have := a.used; omega
  have high : (caller full s).size ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, ku, ou⟩ => ?_)
  refine WP.seq (WP.mono (body_ok inputs a.lengths.1 a.lengths.2 rfl (a.numberBounds u.mem))
    fun v ⟨⟨iv, value, frame⟩, kv⟩ => ?_)
  have saveV := body_saved inputs frame saved
  have whole : Frame [⟨(caller full s).base, (caller full s).size⟩] s.mem v.mem := by
    have f := outside_frame (ou.trans (frame.mono (by omega) (by omega))) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using f
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact a.retApart) (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (ku.1 _ (by decide))) ret⟩
  rw [numbers_entry a ou] at value
  rw [restored.other .eax (by decide)]
  exact value
end VG.Proof.Rsa.X86.KeyCheck
