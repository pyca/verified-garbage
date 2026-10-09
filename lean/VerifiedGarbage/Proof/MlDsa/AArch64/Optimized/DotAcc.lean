import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec

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
