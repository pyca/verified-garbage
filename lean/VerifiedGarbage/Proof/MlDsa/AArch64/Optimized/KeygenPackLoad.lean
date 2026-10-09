import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

structure Constants (b : Nat) (s : State) : Prop where
  bias : ∀e<4,vword (s.v .v16) e=BitVec.ofNat 32 b
  modulus : ∀e<4,vword (s.v .v17) e=8380417#32

theorem Constants.chg {b : Nat} {s t : State} {rs : List VReg}
    (h : Constants b s) (k : VChg rs s t) (h16 : VReg.v16∉rs) (h17 : VReg.v17∉rs) :
    Constants b t := ⟨by rw [k.get _ h16]; exact h.bias,by rw [k.get _ h17]; exact h.modulus⟩

theorem loadOne_ok (signed : Bool) (b : Nat) {r : VReg}
    (hr : r∉[VReg.v4,.v16,.v17]) {s : State} (hc : signed=true → Constants b s)
    {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [r,.v4] s t → (signed=true → Constants b t) →
      (∀e<4,vword (t.v r) e=if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e)
        else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e) → WP isa (.block rest) t Q) :
    WP isa (.block (.ldrq r .x0 off :: ((if signed then convert r else [])++rest))) s Q := by
  have h16 : VReg.v16≠r := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact Ne.symm hr.2.1
  have h17 : VReg.v17≠r := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact Ne.symm hr.2.2
  refine wp_ldrq ho rfl hin fun a ha => ?_
  cases signed with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,List.nil_append]
    exact k a (ha.chg.mono (by simp)) (by simp) (by intro e he; rw [ha.v]; rfl)
  | true =>
    simp only [↓reduceIte]
    have ca := (hc rfl).chg ha.chg (by simpa using h16) (by simpa using h17)
    refine convert_ok r hr b ca.bias ca.modulus fun t ht hv => ?_
    have hk : VChg [r,.v4] s t := (ha.chg.trans ht).mono (by simp)
    refine k t hk (fun _=>(hc rfl).chg hk (by simp [h16]) (by simp [h17])) ?_
    intro e he
    rw [hv e he,ha.v]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
