import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVec

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
