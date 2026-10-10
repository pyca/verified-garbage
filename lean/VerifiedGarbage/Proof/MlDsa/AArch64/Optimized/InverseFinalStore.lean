import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCanonicalBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice

/-! ## From `InverseHalfStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def halfStores (half : Fin 2) : List (VReg × Nat) :=
  (List.finRange 4).map fun j => ((regs 7)[4*half.val+j.val],128*(4*half.val+j.val))

def halfCode (half : Fin 2) : List Instr := canonicalBatchCode (halfPairs half) .v31 ++
  (halfStores half).map (fun p => Instr.strq p.1 .x2 p.2)

def halfWrite (half : Fin 2) (v : Vector (BitVec 128) 8) (base : Addr) (m : Mem) : Mem :=
  (List.finRange 4).foldl (fun m j => m.write (base+BitVec.ofNat 64 (128*(4*half.val+j.val))) 16 v[4*half.val+j.val]) m

theorem half_writeSlice {s : State} {v : Vector (BitVec 128) 8} (half : Fin 2)
    (hb : Bank s (regs 7) v) (base : Addr) :
    writeSlice (halfStores half) base s.v s.mem=halfWrite half v base s.mem := by
  simp only [writeSlice,halfStores,List.foldl_map,halfWrite]
  congr 1
  funext m j
  rw [hb ⟨4*half.val+j.val,by omega⟩]

theorem halfStore_ok (half : Fin 2) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 7) v)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧
        VMem mid t (halfWrite half (halfValues half v (s.v .v31)) (s.gpr .x2) s.mem)) →
      Bank t (regs 7) (halfValues half v (s.v .v31)) → WP isa (.block rest) t Q) :
    WP isa (.block (halfCode half ++ rest)) s Q := by
  simp only [halfCode,List.append_assoc]
  refine canonicalBank_ok half hb fun mid hc hb' => ?_
  refine store_many_ok (halfStores half) .x2 ?_ ?_ fun t hm => ?_
  · intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    omega
  · intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    simpa only [hc.wr,hc.gpr] using hw ⟨4*half.val+j.val,by omega⟩
  · rw [half_writeSlice half hb',hc.gpr,hc.mem] at hm
    refine k t ⟨mid,hc,hm⟩ ?_
    intro j
    rw [hm.v]
    exact hb' j

/-- Arithmetic and stores may be interleaved without weakening the final
register frame: memory is restored only in the intermediate witness. -/
theorem frame_store_trans {s a b c t : State} {m₁ m₂ : Mem}
    (ha : VChg runRegs s a) (hb : VMem a b m₁)
    (hc : VChg runRegs b c) (ht : VMem c t m₂) :
    ∃ mid, VChg runRegs s mid ∧ VMem mid t m₂ := by
  refine ⟨{c with mem := s.mem},?_,?_⟩
  · refine ⟨?_,hc.gpr.trans (hb.gpr.trans ha.gpr),rfl,
      hc.rd.trans (hb.rd.trans ha.rd),hc.wr.trans (hb.wr.trans ha.wr),
      hc.sp.trans (hb.sp.trans ha.sp)⟩
    intro r hr
    change c.v r=s.v r
    rw [hc.get r hr,hb.v,ha.get r hr]
  · exact ⟨ht.gpr,ht.v,ht.mem,ht.rd,ht.wr,ht.sp⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseFinalStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def canonicalValues (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => canonicalVector v[j.val] q

def finalStoreCode : List Instr := halfCode 0 ++ halfCode 1

theorem halfValues_both (v : Vector (BitVec 128) 8) (q : BitVec 128) :
    halfValues 1 (halfValues 0 v q) q=canonicalValues v q := by
  refine Vector.ext fun j hj => ?_
  simp only [halfValues, canonicalValues, Vector.getElem_ofFn, Fin.isValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and, Nat.mul_one]
  by_cases h : j < 4
  · simp only [h, ite_true, show ¬(4 ≤ j ∧ j < 8) by omega, ite_false]
  · simp only [h, ite_false, show 4 ≤ j ∧ j < 8 by omega, and_self, ite_true]

/-- The two halves of a bank write the whole bank. -/
theorem halfWrite_halves (c : Vector (BitVec 128) 8) (p : Addr) (m : Mem) :
    halfWrite 1 c p (halfWrite 0 c p m) = writeBank c p 128 m := rfl

theorem halfWrite_congr {half : Fin 2} {v w : Vector (BitVec 128) 8}
    (h : ∀ j : Fin 4, v[4*half.val+j.val] = w[4*half.val+j.val]) (p : Addr) (m : Mem) :
    halfWrite half v p m = halfWrite half w p m := by
  unfold halfWrite
  congr 1
  funext m j
  rw [h j]

theorem halfWrite_both (v : Vector (BitVec 128) 8) (q : BitVec 128) (p : Addr) (m : Mem) :
    halfWrite 1 (halfValues 1 (halfValues 0 v q) q) p (halfWrite 0 (halfValues 0 v q) p m)=
      writeBank (canonicalValues v q) p 128 m := by
  have h0 : halfWrite 0 (halfValues 0 v q) p m = halfWrite 0 (canonicalValues v q) p m :=
    halfWrite_congr (fun j => by
      simp only [halfValues, canonicalValues, Vector.getElem_ofFn, Fin.isValue, Fin.val_zero,
        Nat.mul_zero, Nat.zero_add, Nat.zero_le, true_and, j.isLt, ite_true]) p m
  rw [halfValues_both, h0, halfWrite_halves]

theorem finalStore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 7) v)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧
        VMem mid t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem)) →
      Bank t (regs 7) (canonicalValues v (s.v .v31)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalStoreCode ++ rest)) s Q := by
  simp only [finalStoreCode,List.append_assoc]
  refine halfStore_ok 0 hb hw fun s₁ ⟨a,ha,hm₁⟩ hb₁ => ?_
  have hq : s₁.v .v31=s.v .v31 := by rw [hm₁.v,ha.get .v31 (by decide)]
  refine halfStore_ok 1 hb₁ ?_ fun t ⟨b,hb',hm₂⟩ hbt => ?_
  · intro i
    simpa only [hm₁.wr,hm₁.gpr,ha.wr,ha.gpr] using hw i
  · have hm₂' : VMem b t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem) := by
      simpa only [hq,hm₁.gpr,ha.gpr,hm₁.mem,halfWrite_both] using hm₂
    refine k t (frame_store_trans ha hm₁ hb' hm₂') ?_
    simpa only [hq,halfValues_both] using hbt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
