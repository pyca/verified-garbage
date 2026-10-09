import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (foldedFlags flagStep flagsTailN_ok)

theorem Rows.of_control {v blocks : Nat} {σ s t : State} {L : Nat → List Zq} {rs : List Reg}
    (h : Rows v blocks σ L s) (ht : Only rs s t)
    (hregs : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : Rows v blocks σ L t := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (hregs r hr)),h.blockBound,?_,?_,h.length,?_,?_⟩
  · simpa only [ht.mem] using h.pairs
  · simpa only [ht.mem] using h.bytes
  · simpa only [ht.mem] using h.counts
  · simpa only [ht.mem] using h.stored

def flagsCode (n : Nat) : List Instr :=
  .ldr .x .x27 .x19 7904::(List.range n).flatMap flagStep

theorem flagsRows_ok {v blocks : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) :
    WP isa (.block (flagsCode (v-1))) s fun t => Rows v blocks σ L t ∧
      t.gpr .x27=foldedFlags (fun k => s.mem.readW (countP σ k) 64) (v-1) := by
  have hv : 0<v ∧ v≤4 := by have:=hp.streams; omega
  have hr (i : Nat) (hi : i<v) : InRegions (s.rd++s.wr) (countP σ i) 8 :=
    in_scr_rd hp h.env.wr (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
  unfold flagsCode
  refine wp_ldrx (a := countP σ 0) (by decide) (by rw [h.env.x19]; rfl)
    (hr 0 hv.1) fun a ha h27 => ?_
  refine WP.mono (flagsTailN_ok (n := v-1) (by omega) (s := a) (b := scr σ)
    (by rw [ha.get .x19]; exact h.env.x19)
    (C := fun k => s.mem.readW (countP σ k) 64)
    (fun i _ => by rw [ha.mem]; rfl) h27
    (fun i hi => by rw [ha.rd,ha.wr]; exact hr i (by omega))) fun t ⟨ht,he⟩ => ?_
  refine ⟨h.of_control ((ha.trans ht).mono (by decide :
    [Reg.x27]++[.x6,.x27] ⊆ [.x6,.x27])) ?_,he⟩
  intro r hrmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrmem
  rcases hrmem with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
