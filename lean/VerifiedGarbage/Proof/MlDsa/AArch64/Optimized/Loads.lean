import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem wp_ldrq wp_strq)

/-- A fused slice's loads preserve the entire non-vector machine state. The
source base may be the output base or a disjoint input polynomial. -/
theorem load_many_ok (loads : List (VReg × Nat)) (base : Reg)
    (hd : (loads.map Prod.fst).Nodup)
    (ho : ∀ p ∈ loads, p.2 % 16 = 0 ∧ p.2 < 4096 * 16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀ p ∈ loads, InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 p.2) 16)
    (k : ∀ t, VChg (loads.map Prod.fst) s t →
      (∀ p ∈ loads, t.v p.1 = s.mem.read (s.gpr base + BitVec.ofNat 64 p.2) 16) →
      WP isa (.block rest) t Q) :
    WP isa (.block (loads.map (fun p => Instr.ldrq p.1 base p.2) ++ rest)) s Q := by
  induction loads generalizing s with
  | nil => exact k s (VChg.refl _ _) (by simp)
  | cons p loads ih =>
    have hn := (List.nodup_cons.mp hd).1
    have ht := (List.nodup_cons.mp hd).2
    change WP isa (.block (.ldrq p.1 base p.2 :: (loads.map (fun p => Instr.ldrq p.1 base p.2) ++ rest))) s Q
    refine wp_ldrq (ho p (by simp)) rfl (hr p (by simp)) fun s₁ h₁ => ?_
    refine ih ht (fun p hp => ho p (List.mem_cons_of_mem _ hp)) ?_ fun s₂ h₂ hv => ?_
    · intro p hp
      simpa only [h₁.rd, h₁.wr, h₁.gpr] using hr p (List.mem_cons_of_mem _ hp)
    · refine k s₂ (VChg.mono (h₁.chg.trans h₂) (by simp)) ?_
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [h₂.get _ hn, h₁.v]
      · rw [hv q hq, h₁.mem, h₁.gpr]

/-- Exact memory resulting from a vector slice's stores. -/
def writeSlice (stores : List (VReg × Nat)) (base : Addr) (v : VReg → BitVec 128) : Mem → Mem
  | m => stores.foldl (fun m p => m.write (base + BitVec.ofNat 64 p.2) 16 (v p.1)) m

theorem store_many_ok (stores : List (VReg × Nat)) (base : Reg)
    (ho : ∀ p ∈ stores, p.2 % 16 = 0 ∧ p.2 < 4096 * 16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀ p ∈ stores, InRegions s.wr (s.gpr base + BitVec.ofNat 64 p.2) 16)
    (k : ∀ t, VMem s t (writeSlice stores (s.gpr base) s.v s.mem) →
      WP isa (.block rest) t Q) :
    WP isa (.block (stores.map (fun p => Instr.strq p.1 base p.2) ++ rest)) s Q := by
  induction stores generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons p stores ih =>
    change WP isa (.block (.strq p.1 base p.2 :: (stores.map (fun p => Instr.strq p.1 base p.2) ++ rest))) s Q
    refine wp_strq (ho p (by simp)) rfl (hr p (by simp)) fun s₁ h₁ => ?_
    refine ih (fun p hp => ho p (List.mem_cons_of_mem _ hp)) ?_ fun s₂ h₂ => ?_
    · intro p hp
      simpa only [h₁.wr, h₁.gpr] using hr p (List.mem_cons_of_mem _ hp)
    · refine k s₂ ⟨h₂.gpr.trans h₁.gpr, h₂.v.trans h₁.v, ?_,
        h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩
      rw [h₂.mem, h₁.gpr, h₁.v, h₁.mem]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized
