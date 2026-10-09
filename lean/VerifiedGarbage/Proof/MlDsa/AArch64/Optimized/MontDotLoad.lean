import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotAcc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductLoad

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
