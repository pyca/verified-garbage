import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCall

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Proof.MlDsa.AArch64.Optimized

/-- A static root table is disjoint from every writable caller region and
from the call stack. Its address is obtained from the current symbol map. -/
structure StaticTable (S : Nat) (name : String) (words : List (BitVec 64)) (s : State) : Prop where
  held : ∀ i<488,s.mem.readW (s.syms name+BitVec.ofNat 64 (8*i)) 64=words.getD i 0
  fit : (s.syms name).toNat+3904≤2^64
  readable : Covers [⟨s.syms name,3904⟩] (s.rd++s.wr)
  writable : ∀ r∈s.wr,(⟨s.syms name,3904⟩ : Region).Disjoint r
  stack : (⟨s.syms name,3904⟩ : Region).Disjoint (below s.sp S)

/-- Both tables needed by the optimized signer, separate from polynomial
invariants so the scalar fallback need not assume either table. -/
structure StaticRoots (S : Nat) (s : State) : Prop where
  forward : StaticTable S "VG_MLDSA_NTT_EXPANDED"
    VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNttWords s
  inverse : StaticTable S "VG_MLDSA_INV_FOLDED"
    VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords s

theorem StaticTable.apart_write {S : Nat} {name : String} {words : List (BitVec 64)}
    {s : State} (h : StaticTable S name words s) {p : Addr} {n : Nat}
    (hp : InRegions s.wr p n) : (⟨s.syms name,3904⟩ : Region).Disjoint ⟨p,n⟩ := by
  obtain ⟨r,hr,hp⟩ := hp
  intro a ha hb
  apply h.writable r hr a ha
  apply hp.byte
  change (a-p).toNat+1≤n at hb
  omega

/-- A caller frame preserves roots, including across calls that use stack
space. Symbol equality is explicit rather than inferred from register ABI. -/
theorem StaticTable.step {S : Nat} {name : String} {words : List (BitVec 64)}
    {s t : State} {ws : List (Ptr × Nat)} (h : StaticTable S name words s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀ w∈ws,InRegions s.wr (pa s w.1) w.2) : StaticTable S name words t := by
  refine ⟨?_,by simpa only [hy] using h.fit,?_,?_,?_⟩
  · intro i hi
    rw [hy,hp.frame.readW (r := ⟨s.syms name,3904⟩)
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

theorem StaticRoots.step {S : Nat} {s t : State} {ws : List (Ptr × Nat)}
    (h : StaticRoots S s) (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀ w∈ws,InRegions s.wr (pa s w.1) w.2) : StaticRoots S t :=
  ⟨h.forward.step hp hy hw,h.inverse.step hp hy hw⟩

/-- Existing checked writable-slot membership suffices for preservation. -/
theorem StaticRoots.step_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s t : State}
    {ws : List (Ptr × Nat)} (h : StaticRoots S s) (L : Lay S rbs wbs s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀ w∈ws,inB wbs w.1 w.2=true) : StaticRoots S t :=
  h.step hp hy (fun w hwmem => L.inW (hw w hwmem))

theorem StaticRoots.nttTableAt {S : Nat} {s : State} (h : StaticRoots S s) {p : Addr}
    (hp : InRegions s.wr p 1024) : NttTableAt s p :=
  ⟨h.forward.held,h.forward.fit,h.forward.apart_write hp⟩

/-- Wrap an existing phase proof while retaining immutable roots. The machine
semantics supplies symbol preservation independently of the phase's ABI. -/
theorem StaticRoots.wp {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    {ws : List (Ptr × Nat)} {code : Prog isa} {Q : State → Prop}
    (h : StaticRoots S s) (L : Lay S rbs wbs s)
    (hw : ∀ w∈ws,inB wbs w.1 w.2=true)
    (hc : WP isa code s fun t => PPostB S s t ws ∧ Q t) :
    WP isa code s fun t => PPostB S s t ws ∧ Q t ∧ StaticRoots S t := by
  exact WP.mono_syms hc fun t ht hy => ⟨ht.1,ht.2,h.step_layout L ht.1 hy hw⟩

/-- The optimized phase invariant adds static roots to the existing semantic
state; no polynomial or rejection-schedule invariant is weakened. -/
def RootedSt (p : Params) (S : Nat) (σ s : State) : Prop := St p S σ s ∧ StaticRoots S s

theorem RootedSt.step {p : Params} {S : Nat} {σ s t : State} {ws : List (Ptr × Nat)}
    (h : RootedSt p S σ s) (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hc : stChk p ws=true) (hw : ∀ w∈ws,inB (sgW p) w.1 w.2=true) : RootedSt p S σ t :=
  ⟨h.1.step hp hc,h.2.step_layout h.1.lay hp hy hw⟩

end VG.Proof.MlDsa.AArch64.Sign
