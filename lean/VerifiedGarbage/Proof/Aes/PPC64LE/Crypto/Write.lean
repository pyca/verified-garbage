module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Read
public import VerifiedGarbage.Proof.Aes.Memory
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: batch stores share the same memory invariant for ECB and CTR.
/-! # POWER8 AES batch outputs -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs mask byteMask data)

structure WriteInv (s₀ : State) (m₀ : Mem) (D : Addr) (n k N c : Nat) (F : Nat → Spec.Aes.State) (s : State) : Prop where
  keep : Keep [.r6] s₀ s
  ptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*(k+c))
  processed : Processed m₀ s.mem D n (k+c) F
  frame : Frame [⟨D, 16*n⟩] s₀.mem s.mem
  val : ∀ i, c ≤ i → i < N → s.vpr (breg i) = s₀.vpr (breg i)
  fixed : ∀ r, r ∉ data :: batchRegs c → s.vpr r = s₀.vpr r

theorem write_step (ctr : Bool) {s₀ s : State} {m₀ : Mem} {D : Addr} {n k N c : Nat} {F : Nat → Spec.Aes.State}
    (hN : N ≤ 8) (hc : c < N) (hkn : k+N ≤ n) (hsize : 16*n ≤ 2^64)
    (hw : (⟨D, 16*n⟩ : Region) ∈ s₀.wr) (h0 : s₀.gpr .r0 = 0) (hm : s₀.vpr mask = byteMask)
    (hF : ∀ i < N, ∀ m, Processed m₀ m D n (k+i) F →
      aesState (outputAt ctr (s₀.vpr (breg i)) m (D + BitVec.ofNat 64 (16*(k+i)))) = F (k+i))
    (h : WriteInv s₀ m₀ D n k N c F s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.writeBlock ctr (breg c))) s
      (WriteInv s₀ m₀ D n k N (c+1) F) := by
  have hc8 : c < 8 := by omega
  have all := batchFacts ⟨8, by decide⟩
  have facts := batchFacts ⟨c, by omega⟩
  have hbm : breg c ≠ mask := fun he => all.2.2.1 (he ▸ breg_mem hc8)
  have hbd : breg c ≠ data := fun he => all.2.2.2.2.2.2 (he ▸ breg_mem hc8)
  have hz : s.gpr .r0 = 0 := (h.keep.gpr (by decide)).trans h0
  have hmm : s.vpr mask = byteMask := (h.fixed mask (by simp [facts.2.2.1, mask, data])).trans hm
  have hwr : InRegions s.wr (s.gpr .r6) 16 := by
    rw [h.keep.2.2, h.ptr]
    exact ⟨⟨D, 16*n⟩, hw, Offset.contains_base D (by omega) (by omega)⟩
  have hx : aesState (outputVector ctr (breg c) s) = F (k+c) := by
    rw [outputVector, h.val c (Nat.le_refl _) hc, h.ptr]
    exact hF c hc s.mem h.processed
  refine WP.mono (writeBlock_ok ctr (breg c) s hbm hbd hz hmm hwr) fun t ht => ?_
  have hp := h.processed.store hsize (show k+c < n by omega) (v := rev128 (outputVector ctr (breg c) s)) (by
    intro j hj
    change VG.VectorCrypto.vbyte (rev128 (outputVector ctr (breg c) s)) j = _
    rw [← VG.Proof.Aes.Vector.getD_st _ hj]
    exact congrArg (fun x : Spec.Aes.State => x.getD j 0) hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.keep.trans ht.keep).mono (by simp)
  · rw [ht.ptr, h.ptr]
    change D + BitVec.ofNat 64 (16*(k+c)) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  · rw [ht.mem, h.ptr]
    simpa only [Nat.add_assoc] using hp.1
  · rw [ht.mem, h.ptr]
    exact h.frame.trans hp.2
  · intro i hi hin
    have hi8 : i < 8 := by omega
    have hbc : breg i ≠ breg c := breg_ne hi8 hc8 (by omega)
    have hbid : breg i ≠ data := fun he => all.2.2.2.2.2.2 (he ▸ breg_mem hi8)
    rw [ht.v (breg i) (by simp [hbc, hbid])]
    exact h.val i (by omega) hin
  · intro r hr
    have hr' : r ≠ data ∧ r ∉ batchRegs c ∧ r ≠ breg c := by
      simpa only [batchRegs_succ, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] using hr
    rw [ht.v r (by simp [hr'.1, hr'.2.2])]
    exact h.fixed r (by simp [hr'.1, hr'.2.1])

theorem write_ok (ctr : Bool) {s : State} {m₀ : Mem} {D : Addr} {n k N : Nat} {F : Nat → Spec.Aes.State}
    (hN : N ≤ 8) (hkn : k+N ≤ n) (hsize : 16*n ≤ 2^64)
    (hw : (⟨D, 16*n⟩ : Region) ∈ s.wr) (h0 : s.gpr .r0 = 0) (hm : s.vpr mask = byteMask)
    (hptr : s.gpr .r6 = D + BitVec.ofNat 64 (16*k)) (hp : Processed m₀ s.mem D n k F)
    (hF : ∀ i < N, ∀ m, Processed m₀ m D n (k+i) F →
      aesState (outputAt ctr (s.vpr (breg i)) m (D + BitVec.ofNat 64 (16*(k+i)))) = F (k+i)) :
    WP isa (.block ((batchRegs N).flatMap (Impl.Aes.PPC64LE.Crypto.writeBlock ctr))) s
      (WriteInv s m₀ D n k N N F) := by
  rw [batchRegs, List.flatMap_map]
  refine wp_range_flatMap (M := isa) (fun c => WriteInv s m₀ D n k N c F)
    (fun c t hc ht => write_step ctr hN hc hkn hsize hw h0 hm hF ht) N (Nat.le_refl _) s ?_
  exact ⟨Keep.refl _ _, by simpa only [Nat.add_zero] using hptr,
    by simpa only [Nat.add_zero] using hp, Frame.refl _ _, fun _ _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Aes.PPC64LE.Crypto
