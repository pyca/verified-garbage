import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailLoadWords

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.Sha3.AArch64.Sha3.Vector (low)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Final input word of the first commitment-rate block. -/
theorem loadLast_ok {s : State}
    (hin : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8) :
    WP isa (.block [.ldr .x .x6 .x1 64,.vop (.dup .d2 .v16 .x6)]) s fun t =>
      RegKeep [.x6] s t ∧ t.mem=s.mem ∧ ∀i<25,
      low t (vreg i)=if i=16 then s.mem.readW (s.gpr .x1+64) 64 else low s (vreg i) := by
  refine wp_ldr (by decide) rfl hin fun a ha =>
    wp_vop (d:=.v16) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.upd ha).trans (RegKeep.vupd ht)).mono (by simp),ht.mem.trans ha.mem,?_⟩
  intro i hi
  by_cases he : i=16
  · subst i
    rw [ite_eq_left rfl]
    change vdword (t.v .v16) 0=_
    rw [ht.v,ha.gpr]
    exact vdword_ofVDwords_0 _ _
  · have he' : vreg i≠.v16 := by
      change vreg i≠vreg 16
      rw [ne_eq,vreg_inj i (by omega) 16 (by decide)]
      exact he
    simp only [he,ite_false,low,ht.get _ he',ha.vec]

structure Zeroed (s : State) (n : Nat) (t : State) : Prop where
  keep : RegKeep [] s t
  mem : t.mem=s.mem
  lanes : ∀i<25, low t (vreg i)=if 17≤i ∧ i<17+n then 0 else low s (vreg i)

/-- The capacity words of the low-lane SHAKE state start at zero. -/
theorem zeroCapacity_ok (s : State) :
    WP isa (.block ((List.range 8).map fun i => .vop (.movi0 (vreg (17+i))))) s (Zeroed s 8) := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa) (Zeroed s) (fun j t hj ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,?_⟩
  · refine wp_vop (d:=vreg (17+j)) rfl fun u hu => WP.block_nil_iff.mpr
      ⟨(ht.keep.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.mem,?_⟩
    intro i hi
    by_cases he : i=17+j
    · subst i
      rw [ite_eq_left (by omega)]
      change vdword (u.v (vreg (17+j))) 0=0
      rw [hu.v]
      rfl
    · have he' : vreg i≠vreg (17+j) := by
        rw [ne_eq,vreg_inj i (by omega) (17+j) (by omega)]; exact he
      change vdword (u.v (vreg i)) 0=_
      rw [hu.get _ he']
      change low t (vreg i)=_
      rw [ht.lanes i hi]
      have hh : (17≤i ∧ i<17+j)↔(17≤i ∧ i<17+(j+1)) := by omega
      simp only [hh]
  · intro i hi
    rw [ite_eq_right (by omega)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
