import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.P256.EcdhInverse.Extract

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def extract20a : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x8 .x4 .x28,
   .lsl .x .x8 .x8 22,
   .lsr .x .x26 .x8 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x8 .x26 .x8 43,
   .movz .x .x11 0 0,
   .movk .x .x11 16 1,
   .lsl .x .x28 .x11 21,
   .add .x .x11 .x11 .x28,
   .add .x .x9 .x4 .x11,
   .lsr .x .x26 .x9 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x9 .x26 .x9 42,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x10 .x5 .x28,
   .lsl .x .x10 .x10 22,
   .lsr .x .x26 .x10 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x10 .x26 .x10 43,
   .add .x .x11 .x5 .x11,
   .lsr .x .x26 .x11 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x11 .x26 .x11 42]

theorem extract20a_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract20a) s fun t =>
      t.gpr .x8=((s.gpr .x4+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x9=(s.gpr .x4+2199024304128).sshiftRight 42 ∧
      t.gpr .x10=((s.gpr .x5+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x11=(s.gpr .x5+2199024304128).sshiftRight 42 ∧
      Keeps [.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract20a,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,
    show (22:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide,show (42:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h8,h9,h10,h11,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h8,h9,h10,h11,h26,h28,↓reduceIte]

def extract20b : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x12 .x4 .x28,
   .lsl .x .x12 .x12 22,
   .lsr .x .x26 .x12 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x12 .x26 .x12 43,
   .movz .x .x15 0 0,
   .movk .x .x15 16 1,
   .lsl .x .x28 .x15 21,
   .add .x .x15 .x15 .x28,
   .add .x .x13 .x4 .x15,
   .lsr .x .x26 .x13 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x13 .x26 .x13 42,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x14 .x5 .x28,
   .lsl .x .x14 .x14 22,
   .lsr .x .x26 .x14 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x14 .x26 .x14 43,
   .add .x .x15 .x5 .x15,
   .lsr .x .x26 .x15 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x15 .x26 .x15 42]

theorem extract20b_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract20b) s fun t =>
      t.gpr .x12=((s.gpr .x4+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x13=(s.gpr .x4+2199024304128).sshiftRight 42 ∧
      t.gpr .x14=((s.gpr .x5+1048576) <<< 22).sshiftRight 43 ∧
      t.gpr .x15=(s.gpr .x5+2199024304128).sshiftRight 42 ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract20b,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,
    show (22:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide,show (42:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h12,h13,h14,h15,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h12,h13,h14,h15,h26,h28,↓reduceIte]

def extract19 : List Instr :=
  [.movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x12 .x4 .x28,
   .lsl .x .x12 .x12 21,
   .lsr .x .x26 .x12 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x12 .x26 .x12 43,
   .movz .x .x15 0 0,
   .movk .x .x15 16 1,
   .lsl .x .x28 .x15 21,
   .add .x .x15 .x15 .x28,
   .add .x .x13 .x4 .x15,
   .lsr .x .x26 .x13 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x13 .x26 .x13 43,
   .movz .x .x28 0 0,
   .movk .x .x28 16 1,
   .add .x .x14 .x5 .x28,
   .lsl .x .x14 .x14 21,
   .lsr .x .x26 .x14 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x14 .x26 .x14 43,
   .add .x .x15 .x5 .x15,
   .lsr .x .x26 .x15 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x15 .x26 .x15 43]

theorem extract19_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block extract19) s fun t =>
      t.gpr .x12=((s.gpr .x4+1048576) <<< 21).sshiftRight 43 ∧
      t.gpr .x13=(s.gpr .x4+2199024304128).sshiftRight 43 ∧
      t.gpr .x14=((s.gpr .x5+1048576) <<< 21).sshiftRight 43 ∧
      t.gpr .x15=(s.gpr .x5+2199024304128).sshiftRight 43 ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [extract19,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (16*0:Nat)<Size.x.bits by decide,
    show (16*1:Nat)<Size.x.bits by decide,show (21:Nat)<Size.x.bits by decide,show (63:Nat)<Size.x.bits by decide,
    show (43:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h12,h13,h14,h15,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h12,h13,h14,h15,h26,h28,↓reduceIte]

theorem extract20a_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 20 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 20) (hlo : m.lo 20)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract20a) s fun t =>
      t.gpr .x8=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^20 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^20 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega
  have hu : -(2:Int)^(20-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega
  have hq : -(2:Int)^(20-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega
  refine WP.mono (extract20a_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

theorem extract20b_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 20 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 20) (hlo : m.lo 20)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract20b) s fun t =>
      t.gpr .x12=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^20 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^20 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega
  have hu : -(2:Int)^(20-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega
  have hq : -(2:Int)^(20-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega
  refine WP.mono (extract20b_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 22).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 42=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

theorem extract19_ok (s : State) (a b : Nat) (m : MSt)
    (ha : a<2^20) (hb : b<2^20) (hm : m.rel 19 ((a:Int)-2^41) ((b:Int)-2^62))
    (hbound : m.bnd 19) (hlo : m.lo 19)
    (h4 : s.gpr .x4=BitVec.ofInt 64 m.f) (h5 : s.gpr .x5=BitVec.ofInt 64 m.g)
    (h27 : s.gpr .x27=0) :
    WP isa (.block extract19) s fun t =>
      t.gpr .x12=BitVec.ofInt 64 (-m.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-m.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-m.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-m.r) ∧
      Keeps [.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  have hf : m.f=(m.u*((a:Int)-2^41)+m.v*((b:Int)-2^62))/2^19 := by
    obtain ⟨hf,_⟩ := hm
    norm_num at hf ⊢
    omega
  have hg : m.g=(m.q*((a:Int)-2^41)+m.r*((b:Int)-2^62))/2^19 := by
    obtain ⟨_,hg⟩ := hm
    norm_num at hg ⊢
    omega
  have hu : -(2:Int)^(19-1)≤m.u := by have := hlo.1; norm_num at this ⊢; omega
  have hq : -(2:Int)^(19-1)≤m.q := by have := hlo.2.2.1; norm_num at this ⊢; omega
  refine WP.mono (extract19_run s h27) fun t ⟨tu,tv,tq,tr,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,kt⟩
  · rw [tu,h4]
    change ((BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20)) <<< 21).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hf]
    exact extract_low (by decide) ha hb hbound.1 hu
  · rw [tv,h4]
    change (BitVec.ofInt 64 m.f+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 43=_
    rw [←BitVec.ofInt_add,←add_assoc,hf]
    exact extract_high (by decide) ha hb hbound.1 hu
  · rw [tq,h5]
    change ((BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20)) <<< 21).sshiftRight 43=_
    rw [←BitVec.ofInt_add,hg]
    exact extract_low (by decide) ha hb hbound.2 hq
  · rw [tr,h5]
    change (BitVec.ofInt 64 m.g+BitVec.ofInt 64 (2^20+2^41)).sshiftRight 43=_
    rw [←BitVec.ofInt_add,←add_assoc,hg]
    exact extract_high (by decide) ha hb hbound.2 hq

end VG.Proof.P256.EcdhInverse
