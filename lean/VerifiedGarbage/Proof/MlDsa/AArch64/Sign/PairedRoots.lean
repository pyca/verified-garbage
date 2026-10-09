import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Proof.MlDsa.AArch64.Optimized

structure PairedRoots (S : Nat) (s : State) : Prop where
  held : ∀ i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=VG.Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0
  fit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  readable : Covers [⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩] (s.rd++s.wr)
  writable : ∀ r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩ : Region).Disjoint r
  stack : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩ : Region).Disjoint (below s.sp S)

theorem PairedRoots.apart_write {S : Nat} 
    {s : State} (h : PairedRoots S s) {p : Addr} {n : Nat}
    (hp : InRegions s.wr p n) : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩ : Region).Disjoint ⟨p,n⟩ := by
  obtain ⟨r,hr,hp⟩ := hp
  intro a ha hb
  apply h.writable r hr a ha
  apply hp.byte
  change (a-p).toNat+1≤n at hb
  omega

/-- A caller frame preserves roots, including across calls that use stack
space. Symbol equality is explicit rather than inferred from register ABI. -/
theorem PairedRoots.step {S : Nat} 
    {s t : State} {ws : List (Ptr × Nat)} (h : PairedRoots S s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀ w∈ws,InRegions s.wr (pa s w.1) w.2) : PairedRoots S t := by
  refine ⟨?_,by simpa only [hy] using h.fit,?_,?_,?_⟩
  · intro i hi
    rw [hy,hp.frame.readW (r := ⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)]
    · exact h.held i hi
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨w,hwmem,rfl⟩ := List.mem_map.mp hr
        exact h.apart_write (hw w hwmem)
      · obtain rfl := List.mem_singleton.mp hr
        exact h.stack
  · simpa only [hy,hp.rd,hp.wr] using h.readable
  · simpa only [hy,hp.wr] using h.writable
  · simpa only [hy,hp.sp] using h.stack

theorem PairedRoots.step_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s t : State}
    {ws : List (Ptr × Nat)} (h : PairedRoots S s) (L : Lay S rbs wbs s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀ w∈ws,inB wbs w.1 w.2=true) : PairedRoots S t :=
  h.step hp hy (fun w hwmem => L.inW (hw w hwmem))

end VG.Proof.MlDsa.AArch64.Sign
