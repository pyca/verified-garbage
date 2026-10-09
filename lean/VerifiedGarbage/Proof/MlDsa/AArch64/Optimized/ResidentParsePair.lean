import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

structure PairAccess (d : Nat) (s : State) : Prop where
  r0 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)) 16
  r1 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 16) 16
  r2 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 (2*d-16)) 16
  w : ∀ p ∈ [Reg.x21,.x22], ∀ j<16, ∀ g<4, InRegions s.wr
    (s.gpr p+BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 (16*g)) 16
  sep : ∀ off ∈ [840,1520], ∀ p ∈ [Reg.x21,.x22],
    (Region.mk (s.gpr .x19+BitVec.ofNat 64 off) (32*d)).Disjoint ⟨s.gpr p,1024⟩
  outputs : (Region.mk (s.gpr .x21) 1024).Disjoint ⟨s.gpr .x22,1024⟩

structure PairParsed (d : Nat) (s t : State) : Prop where
  ready : ParseReady d t
  left : Parsed t.mem (s.gpr .x21) s.mem (s.gpr .x19+840) d 256
  right : Parsed t.mem (s.gpr .x22) s.mem (s.gpr .x19+1520) d 256
  frame : Frame [⟨s.gpr .x21,1024⟩,⟨s.gpr .x22,1024⟩] s.mem t.mem
  gpr : ∀ r, r≠.x0 → r≠.x4 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ v, v∉bodyTemps++initVectors → t.v v=s.v v
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Reuse the initialized constants for both independent SHAKE streams. -/
theorem parsePair_ready_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20)
    (hr : ParseReady d s) (hp : PairAccess d s) :
    WP isa (.seq (parse d .x21 840) (parse d .x22 1520)) s (PairParsed d s) := by
  apply WP.seq
  refine WP.mono (parse_ok s hd (by decide) (by decide) hr
    (hp.sep 840 (by decide) .x21 (by decide)) (hp.r0 840 (by decide))
    (hp.r1 840 (by decide)) (hp.r2 840 (by decide)) (hp.w .x21 (by decide))) ?_
  intro a ha
  have a19 := ha.gpr .x19 (by decide) (by decide) (by decide) (by decide)
  have a22 := ha.gpr .x22 (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (parse_ok a hd (by decide) (by decide) ha.ready
    (by simpa only [a19,a22] using hp.sep 1520 (by decide) .x22 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r0 1520 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r1 1520 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r2 1520 (by decide))
    (by simpa only [a22,ha.wr] using hp.w .x22 (by decide))) ?_
  intro t ht
  have hf : Frame [⟨s.gpr .x22,1024⟩] a.mem t.mem := by simpa only [a22] using ht.frame
  refine ⟨ht.ready,?_,?_,?_,?_,?_,ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp⟩
  · exact ha.values.keep (by decide) hf (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.outputs)
  · intro i hi
    have hv := ht.values i hi
    rw [a22,a19] at hv
    rw [fieldValue_keep hd hi ha.frame (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.sep 1520 (by decide) .x21 (by decide))] at hv
    exact hv
  · exact (ha.frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (hf.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
  · intro r h0 h4 h9 h11
    exact (ht.gpr r h0 h4 h9 h11).trans (ha.gpr r h0 h4 h9 h11)
  · intro v hv
    have hvb : v∉bodyTemps := fun hm => hv (List.mem_append_left _ hm)
    exact (ht.vec v hvb).trans (ha.vec v hvb)

theorem PairAccess.keep {d : Nat} {s t : State} (h : PairAccess d s)
    (h19 : t.gpr .x19=s.gpr .x19) (h21 : t.gpr .x21=s.gpr .x21)
    (h22 : t.gpr .x22=s.gpr .x22) (hr : t.rd=s.rd) (hw : t.wr=s.wr) : PairAccess d t := by
  have hg : ∀ p ∈ [Reg.x21,.x22], t.gpr p=s.gpr p := by
    intro p hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact h21
    · exact h22
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [h19,hr,hw] using h.r0
  · simpa only [h19,hr,hw] using h.r1
  · simpa only [h19,hr,hw] using h.r2
  · intro p hp; simpa only [hg p hp,hw] using h.w p hp
  · intro off ho p hp; simpa only [h19,hg p hp] using h.sep off ho p hp
  · simpa only [h21,h22] using h.outputs

/-- Complete selected parser, including one-time shared vector constants. -/
theorem parseBoth_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) (hp : PairAccess d s) :
    WP isa (parseBoth d) s (PairParsed d s) := by
  unfold parseBoth
  apply WP.seq
  refine WP.mono (init_ok s hd) ?_
  intro a ha
  have h19 := ha.2.2.2.1 .x19 (by decide) (by decide)
  have h21 := ha.2.2.2.1 .x21 (by decide) (by decide)
  have h22 := ha.2.2.2.1 .x22 (by decide) (by decide)
  have hm := ha.2.2.2.2.2.1
  have hr := ha.2.2.2.2.2.2.1
  have hw := ha.2.2.2.2.2.2.2.1
  have hs := ha.2.2.2.2.2.2.2.2
  refine WP.mono (parsePair_ready_ok a hd ⟨ha.1,ha.2.1⟩ (hp.keep h19 h21 h22 hr hw)) ?_
  intro t ht
  refine ⟨ht.ready,?_,?_,?_,?_,?_,ht.rd.trans hr,ht.wr.trans hw,ht.sp.trans hs⟩
  · simpa only [h19,h21,hm] using ht.left
  · simpa only [h19,h22,hm] using ht.right
  · simpa only [h21,h22,hm] using ht.frame
  · intro r h0 h4 h9 h11
    exact (ht.gpr r h0 h4 h9 h11).trans (ha.2.2.2.1 r h9 h11)
  · intro v hv
    exact (ht.vec v hv).trans (ha.2.2.2.2.1 v (fun hm => hv (List.mem_append_right _ hm)))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
