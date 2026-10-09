import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def foldedFlags (C : Nat→BitVec 64) (n : Nat) : BitVec 64 :=
 (List.range n).foldl (fun a i=>a|||C (i+1)) (C 0)

theorem foldedFlags_succ (C : Nat→BitVec 64) (n : Nat) :
    foldedFlags C (n+1)=foldedFlags C n|||C (n+1) := by
  simp only [foldedFlags,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

def flagStep (i : Nat) : List Instr :=
 [.ldr .x .x6 .x19 (7904+8*(i+1)),.logic .orr .x .x27 .x27 .x6]

theorem flagStep_ok {s : State} {i : Nat} (hi : i<3) {b : Addr} (hb : s.gpr .x19=b)
    (hr : InRegions (s.rd++s.wr) (countAt b (i+1)) 8) :
    WP isa (.block (flagStep i)) s fun t=>Only [.x6,.x27] s t ∧
      t.gpr .x27=s.gpr .x27|||s.mem.readW (countAt b (i+1)) 64 := by
  unfold flagStep
  refine wp_ldrx (by omega) (by rw [hb]; rfl) hr fun a ha h6=>
    wp_orr fun t ht h27=>wp_nil ⟨(ha.trans ht).mono (by decide),?_⟩
  rw [h27,h6,ha.get .x27]

theorem flagsTailN_ok {n : Nat} (hn : n≤3) {s : State} {b : Addr} (hb : s.gpr .x19=b) {C : Nat→BitVec 64}
    (hc : ∀i<n+1,s.mem.readW (countAt b i) 64=C i) (h27 : s.gpr .x27=C 0)
    (hr : ∀i<n+1,InRegions (s.rd++s.wr) (countAt b i) 8) :
    WP isa (.block ((List.range n).flatMap flagStep)) s fun t=>Only [.x6,.x27] s t ∧
      t.gpr .x27=foldedFlags C n := by
  refine wp_range_flatMap (M := isa) (N := n)
    (fun k t=>Only [.x6,.x27] s t ∧ t.gpr .x27=foldedFlags C k)
    (fun k t hk ht=>?_) n (Nat.le_refl _) s ⟨Only.refl _ _,h27⟩
  refine WP.mono (flagStep_ok (s := t) (i := k) (b := b) (by omega) (by rw [ht.1.get .x19]; exact hb)
    (by rw [ht.1.rd,ht.1.wr]; exact hr (k+1) (by omega))) fun u ⟨hu,he⟩=>?_
  refine ⟨(ht.1.trans hu).mono (by decide),?_⟩
  rw [he,ht.2,ht.1.mem,hc (k+1) (by omega),foldedFlags_succ]

theorem flags_ok {s : State} {b : Addr} (hb : s.gpr .x19=b) {C : Nat→BitVec 64}
    (hc : ∀i<4,s.mem.readW (countAt b i) 64=C i)
    (hr : ∀i<4,InRegions (s.rd++s.wr) (countAt b i) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) s fun t=>
      (Only [.x6,.x27] s t ∧ t.gpr .x27=foldedFlags C 3) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  change WP isa (.block (.ldr .x .x27 .x19 7904::(List.range 3).flatMap flagStep)) s _
  refine wp_ldrx (by decide) (by rw [hb]; rfl) (hr 0 (by decide)) fun a ha h27=>?_
  refine WP.mono (flagsTailN_ok (n := 3) (by decide) (s := a) (b := b) (C := C) (by rw [ha.get .x19]; exact hb)
    (fun i hi=>by rw [ha.mem]; exact hc i hi) (by rw [h27,hc 0 (by decide)])
    (fun i hi=>by rw [ha.rd,ha.wr]; exact hr i hi)) fun t ⟨ht,he⟩=>
    ⟨(ha.trans ht).mono (by decide),he⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
