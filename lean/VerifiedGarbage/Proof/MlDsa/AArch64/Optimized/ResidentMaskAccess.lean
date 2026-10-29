module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbArgs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackMemory

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! ## From `ResidentMaskInit.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResidentParsePair.lean`, which only this module imported.
section

@[expose] public section

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
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (pro zero absorb)

theorem Env.lowStep {σ s t : State} {rs : List Reg} {W : List Region} (h : Env σ s)
    (hk : RegKeep rs s t) (hf : Frame W s.mem t.mem)
    (hregs : ∀ r∈[Reg.x19,.x20,.x21,.x22,.x30],r∉rs)
    (hsub : ∀ r∈W, r.Sub ⟨σ.gpr .x4,7904⟩) : Env σ t := by
  refine h.step hk hf hregs ?_ ?_ ?_
  · intro r hr
    exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],fun x hx =>
      (Region.sub_prefix (by decide : 7904≤8192)) x (hsub r hr x hx)⟩
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7968) 144).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7968) (n := 144) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7904) 4).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7904) (n := 4) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)

theorem Env.seedBytes {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    Spec.Sha3.bytesAt s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 =
      Spec.Sha3.bytesAt σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 := by
  apply List.ext_getElem
  · rw [VG.Proof.MlKem.bytesAt_length,VG.Proof.MlKem.bytesAt_length]
  · intro i hi _
    rw [VG.Proof.MlKem.bytesAt_length] at hi
    rw [VG.Proof.MlKem.bytesAt_getElem,VG.Proof.MlKem.bytesAt_getElem,Offset.add_add]
    exact h.frame.bytes (R := ⟨σ.gpr .x0,132⟩) (i := 66*p+i) hp.seedSep (by change 132≤2^64; decide) (by change 66*p+i<132; omega)

theorem Env.seedState {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    seedState s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p))=
      seedState σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) := by
  rw [seedState_eq,seedState_eq,h.seedBytes hp hpn]

/-- Build the paired padded seed state while preserving the captured ABI and
both polynomial destination pointers. -/
theorem maskInit_ok (σ : State) (hp : Pre σ) :
    WP isa (.block (pro ++ zero ++ absorb 0)) σ fun t => Env σ t ∧
      PairAt t.mem (σ.gpr .x4) (seedState σ.mem (σ.gpr .x0)) (seedState σ.mem (σ.gpr .x0+66)) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_env σ hp) ?_
  intro a ha
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok ha.base (fun i hi => by
    rw [ha.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ (by omega) (by omega)⟩)) ?_
  intro b ⟨hb,hfb,hzb⟩
  have eb : Env σ b := ha.lowStep hb hfb (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide))
  refine WP.mono (absorb0_ok b (by rw [eb.rd,eb.wr,eb.seed]; exact hp.seed)
    (by rw [eb.wr,eb.base]; exact hp.scratch)
    (by rw [eb.seed,eb.base]
        exact (hp.seedSep ⟨σ.gpr .x4,8192⟩ (by simp [writes])).sub_right (Region.sub_prefix (by decide)))
    (by simpa only [eb.base] using hzb)) ?_
  intro t ⟨ht,hft,hpt⟩
  have hf : Frame [pairR (σ.gpr .x4)] b.mem t.mem := by simpa only [eb.base] using hft
  refine ⟨eb.lowStep ht hf (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide)),?_⟩
  rw [eb.base,eb.seed] at hpt
  have hleft : seedState b.mem (σ.gpr .x0)=seedState σ.mem (σ.gpr .x0) := by
    simpa only [Nat.mul_zero,BitVec.add_zero] using eb.seedState hp (p := 0) (by decide)
  have hright : seedState b.mem (σ.gpr .x0+66)=seedState σ.mem (σ.gpr .x0+66) :=
    eb.seedState hp (p := 1) (by decide)
  simpa only [hleft,hright] using hpt

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskSponge.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_mov wp_addImm)

def SpongePost (σ t : State) : Prop := Env σ t ∧
  Resident.StreamOutput t.mem (σ.gpr .x4+840) 8 5 (seedState σ.mem (σ.gpr .x0)) ∧
  Resident.StreamOutput t.mem (σ.gpr .x4+1520) 8 5 (seedState σ.mem (σ.gpr .x0+66))

theorem spongeArgs_ok (s : State) :
    WP isa (.block [Impl.MlKem.AArch64.mov .x23 .x19,.addImm .x .x24 .x19 840,
      .addImm .x .x25 .x19 1520]) s fun t => Only [.x23,.x24,.x25] s t ∧
      t.gpr .x23=s.gpr .x19 ∧ t.gpr .x24=s.gpr .x19+840 ∧ t.gpr .x25=s.gpr .x19+1520 := by
  refine wp_mov fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((ha.trans hb).trans ht).mono (by simp)
  · rw [ht.get .x23,hb.get .x23,ea]
  · rw [ht.get .x24,eb,ha.get .x19]; rfl
  · rw [et,hb.get .x19,ha.get .x19]; rfl

/-- Five resident permutations and vector squeezes, retaining all outer
sampler state and its saved ABI record. -/
theorem sponge_ok (core : Resident.Core) {σ s : State} (hp : Pre σ) (he : Env σ s)
    (hpair : PairAt s.mem (σ.gpr .x4) (seedState σ.mem (σ.gpr .x0)) (seedState σ.mem (σ.gpr .x0+66)))
    (h23 : s.gpr .x23=σ.gpr .x4) (h24 : s.gpr .x24=σ.gpr .x4+840)
    (h25 : s.gpr .x25=σ.gpr .x4+1520) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith core.code .x23 .x24 .x25 .x19) s (SpongePost σ) := by
  have hw (off len : Nat) (hb : off+len≤8192) :
      InRegions s.wr (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hp0 : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 840) 680).Disjoint (pairR (σ.gpr .x4)) := by
    have hh := Offset.disjoint (σ.gpr .x4) (d := 840) (n := 680) (e := 0) (k := 400)
      (Or.inr (by decide)) (by decide) (by decide)
    simpa only [BitVec.add_zero,pairR] using hh
  have hp1 : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 1520) 680).Disjoint (pairR (σ.gpr .x4)) := by
    have hh := Offset.disjoint (σ.gpr .x4) (d := 1520) (n := 680) (e := 0) (k := 400)
      (Or.inr (by decide)) (by decide) (by decide)
    simpa only [BitVec.add_zero,pairR] using hh
  refine WP.mono (Resident.maskPairWith_ok core hpair h23 h24 h25
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) hp0 hp1
    (fun i hi => hr (16*i) 16 (by omega)) (fun i hi => hw (16*i) 16 (by omega))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (by decide) (by decide) (by decide) (by decide) (by rw [he.base])
    (fun k hk => by rw [Offset.add_add]; exact hw _ _ (by omega))
    (fun k hk => by rw [Offset.add_add]; exact hw _ _ (by omega))
    (Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))
    (Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))) ?_
  intro t ht
  have hk : RegKeep [.x6,.x7,.x15,.x16,.x24,.x25,.x28] s t := by
    refine ⟨?_,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.2.2.2.2.1 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.1
  refine ⟨he.lowStep hk ht.2.2.2.1 (by decide) ?_,ht.2.1,ht.2.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.sub_base _ (by decide)
  · exact Offset.sub_base _ (by decide)
  · exact Region.sub_prefix (by decide)
  · exact Offset.sub_base _ (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

theorem pairAccess_ok {σ s : State} {d : Nat} (hp : Pre σ) (he : Env σ s)
    (hd : d=18 ∨ d=20) : PairAccess d s := by
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hs : ∀ p∈[Reg.x21,.x22],
      (Region.mk (σ.gpr .x4) 8192).Disjoint ⟨s.gpr p,1024⟩ := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1]; exact hp.out1Sep.symm
    · rw [he.out2]; exact hp.out2Sep.symm
  have hw : ∀ p∈[Reg.x21,.x22], (Region.mk (s.gpr p) 1024)∈s.wr := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1,he.wr]; exact hp.out1
    · rw [he.out2,he.wr]; exact hp.out2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro off hoff j hj
    rw [he.base,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro p hp' j hj g hg
    rw [Offset.add_add]
    exact ⟨_,hw p hp',Offset.contains_base _ (by omega) (by omega)⟩
  · intro off hoff p hp'
    rw [he.base]
    refine (hs p hp').sub_left (Offset.sub_base _ ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · rw [he.out1,he.out2]; exact hp.outputs

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
