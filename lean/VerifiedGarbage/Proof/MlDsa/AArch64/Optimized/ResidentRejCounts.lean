import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_movz)
open VG.Proof.Sha3.AArch64 (Mupd wp_str)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej (counts)

def countR (s : State) : Region := ⟨at' s counts,32⟩
def initCountsCode (v : Nat) : List Instr := [.movz .x .x4 256 0]++
  (List.range v).map fun k => .str .x .x4 .x19 (counts+8*k)

theorem countsStore_ok (v : Nat) (hv : v≤4) {s : State} {p : Addr}
    (h19 : s.gpr .x19=p) (h4 : s.gpr .x4=256)
    (hw : ∀i<v,InRegions s.wr (p+BitVec.ofNat 64 (counts+8*i)) 8) :
    WP isa (.block ((List.range v).map fun k => .str .x .x4 .x19 (counts+8*k))) s fun t =>
      Mupd s t t.mem ∧ Frame [⟨p+BitVec.ofNat 64 counts,32⟩] s.mem t.mem ∧
      ∀i<v,t.mem.readW (p+BitVec.ofNat 64 (counts+8*i)) 64=256 := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd s t t.mem ∧ Frame [⟨p+BitVec.ofNat 64 counts,32⟩] s.mem t.mem ∧
      ∀i<k,t.mem.readW (p+BitVec.ofNat 64 (counts+8*i)) 64=256)
    (fun k t hk ⟨ht,hf,hs⟩ => ?_) v (Nat.le_refl _) s
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := p+BitVec.ofNat 64 (counts+8*k))
    (by unfold counts; constructor <;> omega) (by rw [ht.gpr,h19])
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains p (d := counts+8*k) (e := counts) (n := 8) (k := 32)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr,h4]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep
        (Offset.sep p (d := counts+8*i) (e := counts+8*k) (n := 8) (k := 8)
          (by omega) (by unfold counts; omega) (by unfold counts; omega)) (by decide)]
      exact hs i (by omega)

theorem initCounts_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) :
    WP isa (.block (initCountsCode v)) s fun t => Env v σ t ∧
      Frame [countR σ] s.mem t.mem ∧ ∀i<v,t.mem.readW (countP σ i) 64=256 := by
  rw [initCountsCode,List.cons_append,List.nil_append]
  refine wp_movz fun a ha ea => ?_
  have h4 : a.gpr .x4=256 := by rw [ea]; rfl
  refine WP.mono (countsStore_ok v (by have:=hp.streams; omega)
    (by rw [ha.get .x19]; exact he.x19) h4
    (fun i hi => in_scr hp (ha.wr.trans he.wr) (by have:=hp.streams; unfold counts; omega)))
    fun t ⟨ht,hf,hs⟩ => ?_
  have hframe : Frame [countR σ] s.mem t.mem := by rw [←ha.mem]; exact hf
  refine ⟨he.lowStep hframe (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.sub_base (scr σ) (by decide))
    (ht.rd.trans ha.rd) (ht.wr.trans ha.wr) (ht.sp.trans ha.sp)
    (fun r hr => by rw [ht.gpr,ha.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)]),hframe,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
