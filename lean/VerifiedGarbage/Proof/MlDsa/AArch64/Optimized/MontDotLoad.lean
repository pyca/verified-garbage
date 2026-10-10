import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad

/-! ## From `MontDotVec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

def reduce (d : VReg) : List Instr :=
  [.vop (.perm .uzp1 .s4 .v4 .v2 .v3),.vop (.mul .v4 .v4 .v17),
   .vop (.umlal false .v2 .v4 .v16),.vop (.umlal true .v3 .v4 .v16),
   .vop (.perm .uzp2 .s4 d .v2 .v3)]

theorem reduce_ok {d : VReg} {s : State} {rest : List Instr} {Q : State → Prop}
    (p : Nat → BitVec 64)
    (a₁ : s.v .v2=ofVDwords (p 0) (p 1)) (a₂ : s.v .v3=ofVDwords (p 2) (p 3))
    (hq : s.v .v16=ofVWords (BitVec.ofNat 32 q) (BitVec.ofNat 32 q)
      (BitVec.ofNat 32 q) (BitVec.ofNat 32 q))
    (hqi : s.v .v17=ofVWords (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv)
      (BitVec.ofNat 32 montQInv) (BitVec.ofNat 32 montQInv))
    (k : ∀ t,VChg [.v2,.v3,.v4,d] s t →
      t.v d=ofVWords (redc (p 0)) (redc (p 1)) (redc (p 2)) (redc (p 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (reduce d++rest)) s Q := by
  have eq_q : (BitVec.ofNat 32 q).setWidth 64=BitVec.ofNat 64 q := by decide
  refine wp_vop (d := .v4) rfl fun s₃ h₃ => ?_
  have a₃ : s₃.v .v4 = ofVWords ((p 0).extractLsb' 0 32) ((p 1).extractLsb' 0 32)
      ((p 2).extractLsb' 0 32) ((p 3).extractLsb' 0 32) := by
    rw [h₃.v, a₁, a₂]; exact unzip_wide false _ _ _ _
  refine wp_vop (d := .v4) rfl fun s₄ h₄ => ?_
  have a₄ : s₄.v .v4 = ofVWords (multiplier (p 0)) (multiplier (p 1))
      (multiplier (p 2)) (multiplier (p 3)) := by
    rw [h₄.v, a₃, h₃.get .v17, hqi, map2_words]
    rfl
  refine wp_vop (d := .v2) rfl fun s₅ h₅ => ?_
  have a₅ : s₅.v .v2 = ofVDwords
      (p 0 + (multiplier (p 0)).setWidth 64 * BitVec.ofNat 64 q)
      (p 1 + (multiplier (p 1)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₅.v, h₄.get .v2, h₃.get .v2, a₁, a₄,
      h₄.get .v16, h₃.get .v16, hq]
    simp only [ite_false, Bool.false_eq_true, Nat.zero_add, Nat.add_zero, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_0,
      vword_ofVWords_1, eq_q]
  refine wp_vop (d := .v3) rfl fun s₆ h₆ => ?_
  have a₆ : s₆.v .v3 = ofVDwords
      (p 2 + (multiplier (p 2)).setWidth 64 * BitVec.ofNat 64 q)
      (p 3 + (multiplier (p 3)).setWidth 64 * BitVec.ofNat 64 q) := by
    rw [h₆.v, h₅.get .v3, h₄.get .v3, h₃.get .v3, a₂, h₅.get .v4, a₄,
      h₅.get .v16, h₄.get .v16, h₃.get .v16, hq]
    simp only [ite_true, Nat.add_zero, Nat.reduceAdd, vdword_ofVDwords_0, vdword_ofVDwords_1, vword_ofVWords_2,
      vword_ofVWords_3, eq_q]
  refine wp_vop (d := d) rfl fun s₇ h₇ => k s₇
    (VChg.mono (rs' := [.v2,.v3,.v4,d])
      ((((h₃.chg.trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg)
      (by intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  rw [h₇.v, h₆.get .v2, a₅, a₆]
  exact unzip_wide true _ _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotAcc.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def dotAcc (first : Bool) : List Instr :=
  if first then [.vop (.umull false .v2 .v0 .v1),.vop (.umull true .v3 .v0 .v1)]
  else [.vop (.umlal false .v2 .v0 .v1),.vop (.umlal true .v3 .v0 .v1)]

def accWord (first : Bool) (p : BitVec 64) (a b : BitVec 32) : BitVec 64 :=
  if first then product a b else p+product a b

theorem dotAcc_ok (first : Bool) (p : Nat → BitVec 64) {s : State}
    (ha : first=false → s.v .v2=ofVDwords (p 0) (p 1)) (hb : first=false → s.v .v3=ofVDwords (p 2) (p 3))
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v2,.v3] s t →
      t.v .v2=ofVDwords (accWord first (p 0) (vword (s.v .v0) 0) (vword (s.v .v1) 0))
        (accWord first (p 1) (vword (s.v .v0) 1) (vword (s.v .v1) 1)) →
      t.v .v3=ofVDwords (accWord first (p 2) (vword (s.v .v0) 2) (vword (s.v .v1) 2))
        (accWord first (p 3) (vword (s.v .v0) 3) (vword (s.v .v1) 3)) →
      WP isa (.block rest) t Q) : WP isa (.block (dotAcc first++rest)) s Q := by
  cases first
  · refine wp_vop (d:=.v2) rfl fun a h1 => ?_
    have ea : a.v .v2=ofVDwords
        (p 0+product (vword (s.v .v0) 0) (vword (s.v .v1) 0))
        (p 1+product (vword (s.v .v0) 1) (vword (s.v .v1) 1)) := by
      rw [h1.v,ha rfl]
      simp only [Bool.false_eq_true,ite_false,Nat.zero_add,Nat.add_zero,
        vdword_ofVDwords_0,vdword_ofVDwords_1,product]
    refine wp_vop (d:=.v3) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v2,ea]; rfl
    · rw [h2.v,h1.get .v3,h1.get .v0,h1.get .v1,hb rfl]
      simp only [ite_true,Nat.add_zero,Nat.reduceAdd,vdword_ofVDwords_0,
        vdword_ofVDwords_1,accWord,Bool.false_eq_true,ite_false,product]
  · refine wp_vop (d:=.v2) rfl fun a h1 => ?_
    refine wp_vop (d:=.v3) rfl fun b h2 => ?_
    refine k b ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · rw [h2.get .v2,h1.v]; rfl
    · rw [h2.v,h1.get .v0,h1.get .v1]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot

def dotTerm (off k : Nat) : List Instr :=
  [.ldrq .v0 .x1 (1024*k+off),.ldrq .v1 .x2 (1024*k+off)] ++
    dotAcc (decide (k=0))

def dotInput (s : State) (r : Reg) (off k e : Nat) : BitVec 32 :=
  vword (s.mem.read (s.gpr r+BitVec.ofNat 64 (1024*k+off)) 16) e

def dotAccum (s : State) (off n e : Nat) : BitVec 64 :=
  dotWord (fun k => dotInput s .x1 off k e) (fun k => dotInput s .x2 off k e) n

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
    (ha : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k+off)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16)
    (h18 : k≠0 → s.v .v2=ofVDwords (dotAccum s off k 0) (dotAccum s off k 1))
    (h19 : k≠0 → s.v .v3=ofVDwords (dotAccum s off k 2) (dotAccum s off k 3))
    {rest : List Instr} {Q : State → Prop}
    (next : ∀t,VChg [.v0,.v1,.v2,.v3] s t →
      t.v .v2=ofVDwords (dotAccum s off (k+1) 0) (dotAccum s off (k+1) 1) →
      t.v .v3=ofVDwords (dotAccum s off (k+1) 2) (dotAccum s off (k+1) 3) →
      WP isa (.block rest) t Q) : WP isa (.block (dotTerm off k++rest)) s Q := by
  unfold dotTerm
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  have hb' : InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 (1024*k+off)) 16 := by
    rw [h1.chg.rd,h1.chg.wr,h1.chg.gpr]; exact hb
  refine wp_ldrq ho rfl hb' fun b h2 => ?_
  refine dotAcc_ok (decide (k=0)) (dotAccum s off k) ?_ ?_ fun t ht e18 e19 => ?_
  · intro hn
    rw [h2.get .v2,h1.get .v2]
    exact h18 (by simpa using hn)
  · intro hn
    rw [h2.get .v3,h1.get .v3]
    exact h19 (by simpa using hn)
  · have hc : VChg [.v0,.v1,.v2,.v3] s t :=
      ((h1.chg.trans h2.chg).trans ht).mono (by
        intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    have ev e : accWord (decide (k=0)) (dotAccum s off k e)
        (vword (b.v .v0) e) (vword (b.v .v1) e)=dotAccum s off (k+1) e := by
      rw [h2.get .v0,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
      change accWord (decide (k=0)) (dotAccum s off k e)
        (dotInput s .x1 off k e) (dotInput s .x2 off k e)=_
      simp only [dotAccum,dotWord_succ,accWord]
      by_cases hk : k=0
      · subst k; simp [dotWord_zero]
      · simp [hk]
    exact next t hc (by simpa only [ev] using e18) (by simpa only [ev] using e19)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end
