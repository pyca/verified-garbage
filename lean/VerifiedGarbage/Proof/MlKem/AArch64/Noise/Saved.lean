module

import VerifiedGarbage.Proof.MlKem.AArch64.Shared
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arith

/-! # Register records shared by paired samplers -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Impl.MlKem.AArch64.Paired (saved)

def savedR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 1800,48⟩
def Saved (p : Addr) (s : State) (m : Mem) : Prop :=
  ∀ i < 6, m.readW (p + BitVec.ofNat 64 (1800+8*i)) 64 = s.gpr (saved.getD i .x0)

theorem Saved.frame {p : Addr} {s : State} {m m' : Mem} (h : Saved p s m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR p).Disjoint r) : Saved p s m' := by
  intro i hi
  rw [hf.readW (r := savedR p) (by
    change (Region.mk (p + BitVec.ofNat 64 1800) 48).Contains _ 8
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h i hi

theorem saves_ok {s : State} {p : Addr} (hp : s.gpr .x2 = p)
    (hin : ∀ i < 6, InRegions s.wr (p + BitVec.ofNat 64 (1800+8*i)) 8) :
    WP isa (.block (saved.zipIdx.map fun (r,i) => .str .x r .x2 (1800+8*i))) s fun t =>
      Keep [] s t ∧ Saved p s t.mem ∧ Frame [savedR p] s.mem t.mem := by
  change WP isa (.block ((List.range 6).map fun i => .str .x (saved.getD i .x0) .x2 (1800+8*i))) s _
  refine WP.mono (WP.preservedV (KeyGen.saves_ok p .x2 1800 saved (by decide) (by decide)
    6 (by decide) hp hin) (hc := rfl)) fun t ⟨⟨hg,hr,hw,hsp,hv,hf⟩,hvc⟩ => ?_
  exact ⟨⟨fun r _ => congrFun hg r,hr,hw,hsp,hvc⟩,hv,hf⟩


/-- Restore the base register last, keeping the record address live until then. -/
theorem restores_ok {s initial : State} {p : Addr} (hp : s.gpr .x19 = p)
    (hs : Saved p initial s.mem)
    (hin : ∀ i < 6, InRegions (s.rd++s.wr) (p + BitVec.ofNat 64 (1800+8*i)) 8) :
    WP isa (.block (saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))) s fun t =>
      Only saved s t ∧ (∀ r ∈ saved, t.gpr r = initial.gpr r) := by
  change WP isa (.block [.ldr .x .x30 .x19 1840,.ldr .x .x23 .x19 1832,
    .ldr .x .x22 .x19 1824,.ldr .x .x21 .x19 1816,.ldr .x .x20 .x19 1808,
    .ldr .x .x19 .x19 1800]) s _
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*5)) (by decide)
    (by rw [hp]) (hin 5 (by decide)) fun s1 h1 e1 => ?_
  have o1 : Only [.x30] s s1 := h1
  have v1 : s1.gpr .x30 = initial.gpr .x30 := by
    rw [e1]; exact hs 5 (by decide)
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*4)) (by decide)
    (by rw [o1.get .x19 (by decide),hp]) (by rw [o1.rd,o1.wr]; exact hin 4 (by decide)) fun s2 h2 e2 => ?_
  have o2 : Only [.x30,.x23] s s2 := (o1.trans h2).mono (by simp)
  have v2 : s2.gpr .x23 = initial.gpr .x23 := by
    rw [e2,o1.mem]; exact hs 4 (by decide)
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*3)) (by decide)
    (by rw [o2.get .x19 (by decide),hp]) (by rw [o2.rd,o2.wr]; exact hin 3 (by decide)) fun s3 h3 e3 => ?_
  have o3 : Only [.x30,.x23,.x22] s s3 := (o2.trans h3).mono (by simp)
  have v3 : s3.gpr .x22 = initial.gpr .x22 := by
    rw [e3,o2.mem]; exact hs 3 (by decide)
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*2)) (by decide)
    (by rw [o3.get .x19 (by decide),hp]) (by rw [o3.rd,o3.wr]; exact hin 2 (by decide)) fun s4 h4 e4 => ?_
  have o4 : Only [.x30,.x23,.x22,.x21] s s4 := (o3.trans h4).mono (by simp)
  have v4 : s4.gpr .x21 = initial.gpr .x21 := by
    rw [e4,o3.mem]; exact hs 2 (by decide)
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*1)) (by decide)
    (by rw [o4.get .x19 (by decide),hp]) (by rw [o4.rd,o4.wr]; exact hin 1 (by decide)) fun s5 h5 e5 => ?_
  have o5 : Only [.x30,.x23,.x22,.x21,.x20] s s5 := (o4.trans h5).mono (by simp)
  have v5 : s5.gpr .x20 = initial.gpr .x20 := by
    rw [e5,o4.mem]; exact hs 1 (by decide)
  refine wp_ldrx (a := p + BitVec.ofNat 64 (1800+8*0)) (by decide)
    (by rw [o5.get .x19 (by decide),hp]) (by rw [o5.rd,o5.wr]; exact hin 0 (by decide)) fun s6 h6 e6 => wp_nil ?_
  have o6 : Only [.x30,.x23,.x22,.x21,.x20,.x19] s s6 := (o5.trans h6).mono (by simp)
  have v6 : s6.gpr .x19 = initial.gpr .x19 := by
    rw [e6,o5.mem]; exact hs 0 (by decide)
  refine ⟨o6.mono (by decide),?_⟩
  intro r hr
  simp only [saved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact v6
  · rw [h6.get .x20 (by decide)]; exact v5
  · rw [h6.get .x21 (by decide),h5.get .x21 (by decide)]; exact v4
  · rw [h6.get .x22 (by decide),h5.get .x22 (by decide),h4.get .x22 (by decide)]; exact v3
  · rw [h6.get .x23 (by decide),h5.get .x23 (by decide),h4.get .x23 (by decide),h3.get .x23 (by decide)]; exact v2
  · rw [h6.get .x30 (by decide),h5.get .x30 (by decide),h4.get .x30 (by decide),h3.get .x30 (by decide),h2.get .x30 (by decide)]; exact v1
 
/-- During a paired sampler, the saved registers are protected by the memory record. -/
structure Partial (rs : List Region) (s t : State) : Prop where
  cs : ∀ r ∈ preserved, r ∉ saved → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  frame : Frame rs s.mem t.mem

theorem Partial.trans {rs : List Region} {s t u : State}
    (h : Partial rs s t) (k : Partial rs t u) : Partial rs s u :=
  ⟨fun r hr hn => (k.cs r hr hn).trans (h.cs r hr hn),k.rd.trans h.rd,k.wr.trans h.wr,
    k.sp.trans h.sp,fun r hr => (k.vcs r hr).trans (h.vcs r hr),h.frame.trans k.frame⟩
theorem Partial.mono {rs ts : List Region} {s t : State} (h : Partial rs s t)
    (hm : ∀ r ∈ rs,r ∈ ts) : Partial ts s t :=
  ⟨h.cs,h.rd,h.wr,h.sp,h.vcs,h.frame.mono hm⟩
theorem Partial.of_kept {rs : List Region} {s t : State} (h : Kept rs s t) : Partial rs s t :=
  ⟨fun r hr hn => h.cs r hr (fun e => hn (by rw [e]; decide)),h.rd,h.wr,h.sp,h.vcs,h.frame⟩
theorem Partial.restore {rs : List Region} {s t u : State} (h : Partial rs s t)
    (ho : Only saved t u) (hr : ∀ r ∈ saved,u.gpr r=s.gpr r) : Kept rs s u := by
  refine ⟨fun r hp _ => ?_,ho.sp.trans h.sp,ho.rd.trans h.rd,ho.wr.trans h.wr,?_,
    fun r hp => (ho.vcs r hp).trans (h.vcs r hp)⟩
  · by_cases hs : r ∈ saved
    · exact hr r hs
    · rw [ho.get r hs]; exact h.cs r hp hs
  · rw [ho.mem]; exact h.frame

end VG.Proof.MlKem.AArch64.Noise
