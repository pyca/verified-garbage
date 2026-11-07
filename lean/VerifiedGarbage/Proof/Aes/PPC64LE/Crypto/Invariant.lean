module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Output
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: batch and tail loops share this invariant and its preservation proof.
/-! # POWER8 AES data-loop invariant -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (mask byteMask counterBase counterMask counterControl key data counterWord)

def loopGprs : List Reg := [.r6, .r7, .r8, .r9, .r10, .r12]

/-- The data loops' configuration: `n` blocks read at `D` and written at `E`
(either `D` or apart from it), through the stores' offset register `o`,
which holds `E - D` and which the loops do not write. -/
structure LoopConfig (inverse ctr : Bool) (o : Reg) (base : State) (nr n : Nat) (D E : Addr) : Prop where
  inputs : Inputs nr base
  size : 16*n ≤ 2^64
  writes : (⟨E, 16*n⟩ : Region) ∈ base.wr
  sep : (⟨base.gpr .r3, 240⟩ : Region).Disjoint ⟨E, 16*n⟩
  direction : ctr = true → inverse = false
  reads : (⟨D, 16*n⟩ : Region) ∈ base.rd ++ base.wr
  off : base.gpr o = E - D
  free : o ∉ loopGprs
  alias : E = D ∨ (⟨D, 16*n⟩ : Region).Disjoint ⟨E, 16*n⟩

structure LoopInv (inverse ctr : Bool) (base : State) (nr n : Nat) (D E : Addr) (icb : Spec.Gcm.Block)
    (k : Nat) (s : State) : Prop where
  bound : k ≤ n
  keep : Keep loopGprs base s
  ptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*k)
  left : s.gpr .r7 = BitVec.ofNat 64 (n-k)
  processed : Processed base.mem s.mem E n k (outputState inverse ctr nr (schedule nr base) icb base.mem D)
  frame : Frame [⟨E, 16*n⟩] base.mem s.mem
  mask : s.vpr mask = byteMask
  control : ctr = true → s.vpr counterMask = counterControl
  counterPrefix : ctr = true → (s.vpr counterBase).extractLsb' 32 96 = icb.extractLsb' 32 96
  counter : ctr = true → (s.gpr .r8).setWidth 32 = icb.extractLsb' 0 32 + BitVec.ofNat 32 k

theorem LoopInv.inputs {inverse ctr : Bool} {o : Reg} {base s : State} {nr n k : Nat} {D E : Addr}
    {icb : Spec.Gcm.Block}
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb k s) :
    Inputs nr s := by
  refine ⟨(h.keep.gpr (by decide)).trans hc.inputs.zero, h.mask,
    (h.keep.gpr (by decide)).trans hc.inputs.rounds, hc.inputs.min, hc.inputs.max, ?_⟩
  intro j hj
  rw [h.keep.2.1, h.keep.2.2, h.keep.gpr (by decide)]
  exact hc.inputs.reads j hj

theorem LoopInv.schedule_eq {inverse ctr : Bool} {o : Reg} {base s : State} {nr n k : Nat} {D E : Addr}
    {icb : Spec.Gcm.Block}
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb k s) :
    schedule nr s = schedule nr base := by
  rw [Crypto.schedule, h.keep.gpr (by decide)]
  exact bytesAt_frame (R := ⟨base.gpr .r3, 240⟩) h.frame hc.sep (by change 16*(nr+1) ≤ 240; have := hc.inputs.max; omega) (by change 240 ≤ 2^64; decide)

theorem loop_group_ok {inverse ctr : Bool} {o : Reg} {base s : State} {nr n k N : Nat} {D E : Addr}
    {icb : Spec.Gcm.Block}
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb k s)
    (hN : N ≤ 8) (hkn : k+N ≤ n) :
    WP isa (Impl.Aes.PPC64LE.Crypto.group inverse ctr N o) s (LoopInv inverse ctr base nr n D E icb (k+N)) := by
  have hw : (⟨E, 16*n⟩ : Region) ∈ s.wr := by rw [h.keep.2.2]; exact hc.writes
  have hrd : (⟨D, 16*n⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.keep.2.1, h.keep.2.2]; exact hc.reads
  have hO : s.gpr o = E - D := (h.keep.gpr hc.free).trans hc.off
  have ho : o ∉ [.r6, .r8, .r9, .r10] := fun hm => hc.free (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide)
  have hF : ∀ i < N, ∀ v, aesState v = result inverse nr (schedule nr s) (aesState (readValue ctr s i)) →
      ∀ m, Processed base.mem m E n (k+i) (outputState inverse ctr nr (schedule nr base) icb base.mem D) →
        Frame [⟨E, 16*n⟩] s.mem m →
        aesState (outputAt ctr v m (D + BitVec.ofNat 64 (16*(k+i)))) =
          outputState inverse ctr nr (schedule nr base) icb base.mem D (k+i) := by
    intro i hi v hv m hm hf
    rw [h.schedule_eq hc, input_state ctr s icb h.ptr h.counterPrefix h.counter i
      (src_stateAt hc.alias hc.size h.processed h.frame (by omega) (by omega))] at hv
    exact output_state inverse ctr nr (schedule nr base) icb
      (src_stateAt hc.alias hc.size hm (h.frame.trans hf) (Nat.le_refl _) (by omega)) hc.direction hv
  refine WP.mono (group_ok inverse ctr N o s hN hkn hc.size (h.inputs hc) h.control hw hrd ho hO h.ptr
    h.processed hF) fun t ht => ?_
  have hfacts := batchFacts ⟨N, by omega⟩
  have hm : t.vpr mask = s.vpr mask := ht.fixed mask (by simp [hfacts.2.2.1, mask, key, data, counterWord])
  have hctrl : t.vpr counterMask = s.vpr counterMask :=
    ht.fixed counterMask (by simp [hfacts.2.2.2.2.1, counterMask, key, data, counterWord])
  have hbase : t.vpr counterBase = s.vpr counterBase :=
    ht.fixed counterBase (by simp [hfacts.2.2.2.1, counterBase, key, data, counterWord])
  refine ⟨hkn, (h.keep.trans ht.keep).mono (by simp [loopGprs]), ht.ptr, ?_, ht.processed,
    h.frame.trans ht.frame, hm.trans h.mask, ?_, ?_, ?_⟩
  · rw [ht.left, h.left]
    rw [Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · intro he; rw [hctrl]; exact h.control he
  · intro he; rw [hbase]; exact h.counterPrefix he
  · intro he
    rw [ht.counter, he]
    simp only [ite_true]
    rw [BitVec.setWidth_add _ _ (by decide), h.counter he, BitVec.setWidth_ofNat_of_le (by decide),
      BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Aes.PPC64LE.Crypto
