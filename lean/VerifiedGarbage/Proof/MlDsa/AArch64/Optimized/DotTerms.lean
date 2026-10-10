import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad

/-! ## From `DotAcc.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def dotAcc (first : Bool) : List Instr :=
  if first then [.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
  else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)]

def accWord (first : Bool) (p : BitVec 64) (a b : BitVec 32) : BitVec 64 :=
  if first then product a b else p+product a b

theorem dotAcc_ok (first : Bool) (p : Nat → BitVec 64) {s : State}
    (ha : first=false → s.v .v18=ofVDwords (p 0) (p 1)) (hb : first=false → s.v .v19=ofVDwords (p 2) (p 3))
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v18,.v19] s t →
      t.v .v18=ofVDwords (accWord first (p 0) (vword (s.v .v16) 0) (vword (s.v .v17) 0))
        (accWord first (p 1) (vword (s.v .v16) 1) (vword (s.v .v17) 1)) →
      t.v .v19=ofVDwords (accWord first (p 2) (vword (s.v .v16) 2) (vword (s.v .v17) 2))
        (accWord first (p 3) (vword (s.v .v16) 3) (vword (s.v .v17) 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotAcc first++rest)) s Q := by
  cases first
  · refine wp_vop (d:=.v18) rfl fun a h1 => ?_
    have ea : a.v .v18=ofVDwords
        (p 0+product (vword (s.v .v16) 0) (vword (s.v .v17) 0))
        (p 1+product (vword (s.v .v16) 1) (vword (s.v .v17) 1)) := by
      rw [h1.v,ha rfl]
      simp only [Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero,
        vdword_ofVDwords_0,vdword_ofVDwords_1,product]
    refine wp_vop (d:=.v19) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v18,ea]; rfl
    · rw [h2.v,h1.get .v19,h1.get .v16,h1.get .v17,hb rfl]
      simp only [ite_true,Nat.add_zero,Nat.reduceAdd,vdword_ofVDwords_0,
        vdword_ofVDwords_1,accWord,Bool.false_eq_true,ite_false,product]
  · refine wp_vop (d:=.v18) rfl fun a h1 => ?_
    refine wp_vop (d:=.v19) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v18,h1.v]; rfl
    · rw [h2.v,h1.get .v16,h1.get .v17]; rfl

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized

def dotInput (s : State) (r : Reg) (off k e : Nat) : BitVec 32 :=
  vword (s.mem.read (s.gpr r+BitVec.ofNat 64 (1024*k+off)) 16) e

def dotAccum (s : State) (off n e : Nat) : BitVec 64 :=
  dotWord (fun k => dotInput s .x13 off k e) (fun k => dotInput s .x14 off k e) n

theorem dotInput_chg {s t : State} {rs : List VReg} (h : VChg rs s t) :
    dotInput t=dotInput s := by
  funext r off k e
  simp only [dotInput,h.mem,h.gpr]

theorem dotAccum_chg {s t : State} {rs : List VReg} (h : VChg rs s t) :
    dotAccum t=dotAccum s := by
  funext off n e
  simp only [dotAccum,dotInput_chg h]

theorem dotTerm_ok {s : State} {off k : Nat}
    (ho : (1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    (h18 : k≠0 → s.v .v18=ofVDwords (dotAccum s off k 0) (dotAccum s off k 1))
    (h19 : k≠0 → s.v .v19=ofVDwords (dotAccum s off k 2) (dotAccum s off k 3))
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19] s t →
      t.v .v18=ofVDwords (dotAccum s off (k+1) 0) (dotAccum s off (k+1) 1) →
      t.v .v19=ofVDwords (dotAccum s off (k+1) 2) (dotAccum s off (k+1) 3) →
      WP isa (.block rest) t Q) : WP isa (.block (dotTerm off k++rest)) s Q := by
  unfold dotTerm
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  have he : (if k=0 then [Instr.vop (.umull false .v18 .v16 .v17),.vop (.umull true .v19 .v16 .v17)]
      else [.vop (.umlal false .v18 .v16 .v17),.vop (.umlal true .v19 .v16 .v17)])=dotAcc (decide (k=0)) := by
    simp [dotAcc]
  rw [he]
  refine dotAcc_ok (decide (k=0)) (dotAccum s off k) ?_ ?_ fun t ht e18 e19 => ?_
  · intro hn
    rw [h2.get .v18,h1.get .v18]
    exact h18 (by simpa using hn)
  · intro hn
    rw [h2.get .v19,h1.get .v19]
    exact h19 (by simpa using hn)
  · have hc : VChg [.v16,.v17,.v18,.v19] s t :=
      ((h1.chg.trans h2.chg).trans ht).mono (by
        intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    have ev e : accWord (decide (k=0)) (dotAccum s off k e)
        (vword (b.v .v16) e) (vword (b.v .v17) e)=dotAccum s off (k+1) e := by
      rw [h2.get .v16,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
      change accWord (decide (k=0)) (dotAccum s off k e)
        (dotInput s .x13 off k e) (dotInput s .x14 off k e)=_
      simp only [dotAccum,dotWord_succ,accWord]
      by_cases hk : k=0
      · subst k; simp [dotWord_zero]
      · simp [hk]
    exact next t hc (by simpa only [ev] using e18) (by simpa only [ev] using e19)

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `DotTerms.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized

theorem dotTerms_ok (n : Nat) {s : State} {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19] s t →
      (n≠0 → t.v .v18=ofVDwords (dotAccum s off n 0) (dotAccum s off n 1)) →
      (n≠0 → t.v .v19=ofVDwords (dotAccum s off n 2) (dotAccum s off n 3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (dotTerm off)++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact next s (VChg.refl _ _) (by simp) (by simp)
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    refine ih (fun k hk => ho k (by omega)) (fun k hk => hr k (by omega)) fun a ha e18 e19 => ?_
    have hr' : InRegions (a.rd++a.wr) (a.gpr .x13+BitVec.ofNat 64 (1024*n+off)) 16 ∧
        InRegions (a.rd++a.wr) (a.gpr .x14+BitVec.ofNat 64 (1024*n+off)) 16 := by
      rw [ha.rd,ha.wr,ha.gpr]; exact hr n (by omega)
    refine dotTerm_ok (ho n (by omega)) hr'.1 hr'.2 ?_ ?_ fun t ht a18 a19 => ?_
    · rw [dotAccum_chg ha]; exact e18
    · rw [dotAccum_chg ha]; exact e19
    · refine next t ((ha.trans ht).mono (by simp)) (fun _ => ?_) (fun _ => ?_)
      · simpa only [dotAccum_chg ha] using a18
      · simpa only [dotAccum_chg ha] using a19

theorem dotLoad_ok {n : Nat} (hn : 0<n) {d : VReg} (h30 : d≠.v30) (h31 : d≠.v31)
    {s : State} (hc : ProductConstants s) {off : Nat}
    (ho : ∀k<n,(1024*k+off)%16=0 ∧ 1024*k+off<4096*16)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 (1024*k+off)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 (1024*k+off)) 16)
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v16,.v17,.v18,.v19,.v20,d] s t → ProductConstants t →
      (∀e<4,vword (t.v d) e=centeredDot (fun k => dotInput s .x13 off k e)
        (fun k => dotInput s .x14 off k e) n) → WP isa (.block rest) t Q) :
    WP isa (.block (dotLoad n d off++rest)) s Q := by
  unfold dotLoad
  rw [List.append_assoc]
  refine dotTerms_ok n ho hr fun a ha e18 e19 => ?_
  have ca := hc.chg ha (by decide) (by decide)
  refine dotReduce_ok h31 (dotAccum s off n) (e18 (by omega)) (e19 (by omega)) ca.qv ca.qiv
    fun t ht ev => ?_
  have h : VChg [.v16,.v17,.v18,.v19,.v20,d] s t := (ha.trans ht).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  exact next t h (hc.chg h (by simp [Ne.symm h30]) (by simp [Ne.symm h31])) ev

end VG.Proof.MlDsa.AArch64.Optimized

end
