import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def productTemps : List VReg := [.v24,.v25,.v26,.v27,.v28]
def productClobs (js : List (Fin 8)) : List VReg :=
  productTemps++js.flatMap (fun j => [vr j.val,vr (8+j.val)])
def productInput (s : State) (j p e : Nat) : BitVec 32 :=
  centeredProduct (vword (s.mem.read (s.gpr .x13+BitVec.ofNat 64 (16*j)) 16) e)
    (vword (s.mem.read (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j)) 16) e)

theorem bank_not_clob {j : Fin 8} {js : List (Fin 8)} (hj : j∉js) {p : Nat} (hp : p<2) :
    vr (8*p+j.val)∉productClobs js := by
  intro h
  rcases List.mem_append.mp h with h | h
  · have hb := bank_safe (j := 8*p+j.val) (by omega)
    apply hb
    simp only [productTemps,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have he : j=i := by
      apply Fin.ext
      rcases h with h | h
      · have hx := bank_injective (by omega) (by omega) h
        omega
      · have hx := bank_injective (by omega) (by omega) h
        omega
    exact hj (he ▸ hi)

theorem productBank_ok (js : List (Fin 8)) (hn : js.Nodup)
    {s : State} (hc : ProductConstants s)
    (hr : ∀j∈js,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (16*j.val)) 16 ∧
      ∀p<2,InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*p+16*j.val)) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg (productClobs js) s t → ProductConstants t →
      (∀j∈js,∀p<2,∀e<4,vword (t.v (vr (8*p+j.val))) e=productInput s j.val p e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (js.flatMap (fun j => product j.val)++rest)) s Q := by
  induction js generalizing s with
  | nil => exact k s (VChg.refl _ _) hc (by simp)
  | cons j js ih =>
    have nn := List.nodup_cons.mp hn
    have rr := hr j (by simp)
    simp only [List.flatMap_cons,List.append_assoc]
    refine product_ok j hc rr.1 rr.2 fun a ha ca va => ?_
    refine ih nn.2 ca ?_ fun t ht ct vt => ?_
    · intro i hi
      rw [ha.rd,ha.wr,ha.gpr]
      exact hr i (List.mem_cons_of_mem _ hi)
    · refine k t ((ha.trans ht).mono ?_) ct ?_
      · intro r hm
        simp only [productClobs,productTemps,List.flatMap_cons,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false] at *
        grind only
      · intro i hi p hp e he
        rcases List.mem_cons.mp hi with rfl | hi
        · rw [ht.get _ (bank_not_clob nn.1 hp),va p hp e he]
          rfl
        · rw [vt i hi p hp e he]
          unfold productInput
          rw [ha.mem,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
