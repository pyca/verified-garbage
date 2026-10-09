import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackBlock

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

structure Ready (g : Nat) (s : State) : Prop extends HighPack.PackReady g s where
  factor : ∀e<4,vword (s.v .v21) e=BitVec.ofNat 32 (2*g)
  one : ∀e<4,vword (s.v .v22) e=1
  z : ∀e<4,vword (s.v .v23) e=0

 theorem four_ok {g : Nat} (hg : IsG g) {r : VReg}
    (_hr : r∈([.v0,.v1,.v2,.v3] : List VReg)) {off : Nat} {s : State}
    (hc : Ready g s) (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg [r,.v4,.v5,.v6,.v7,.v26] s t →
      (∀e<4,vword (t.v r) e=value g
        (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 off) 16) e)
        (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 off) 16) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g r off++rest)) s Q := by
  change WP isa (.block (.ldrq .v4 .x5 off :: .ldrq .v5 .x4 off ::
    (Impl.MlDsa.AArch64.Optimized.HighPack.hf g .v6 .v4 ++ (adjustCode ++
      (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20 ++
        (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20 ++ (.vop (.mov r .v6)::rest))))))) s Q
  refine wp_ldrq ho rfl ha fun a h1=>wp_ldrq ho rfl
    (by rw [h1.rd,h1.wr,h1.gpr]; exact hh) fun b h2=>?_
  have cb : HighPack.HighConstants g b := hc.toHighConstants.chg (h1.chg.trans h2.chg)
    (by decide) (by decide) (by decide) (by decide)
  refine HighPack.hf_ok hg (by decide) (by decide) cb.add cb.mul cb.round fun c h3 hraw=>?_
  have keep3 := (h1.chg.trans h2.chg).trans h3
  refine adjust_ok
    (fun e he=>by rw [keep3.get .v23 (by decide)]; exact hc.z e he)
    (fun e he=>by rw [keep3.get .v22 (by decide)]; exact hc.one e he) fun d h4 hadj=>?_
  have keep4 := keep3.trans h4
  have vpre : ∀e<4,vword (d.v .v6) e=before g
      (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 off) 16) e)
      (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 off) 16) e) := by
    intro e he
    rw [hadj e he,hraw e he,h2.get .v4,h1.v,
      keep3.get .v21 (by decide),hc.factor e he,keep3.get .v20 (by decide),hc.modulus e he,
      h3.get .v4 (by decide),h2.get .v4,h1.v,h3.get .v5 (by decide),h2.v,h1.mem,h1.gpr]
    rfl
  refine csub_ok fun f h5 hv5=>csub_ok fun u h6 hv6=>wp_vop (d:=r) rfl fun t h7=>?_
  have keep := ((keep4.trans h5).trans h6).trans h7.chg
  refine k t (keep.mono ?_) ?_
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind only
  · intro e he
    rw [h7.v]
    change vword (u.v .v6) e=_
    rw [hv6 e he,hv5 e he,vpre e he,h5.get .v20 (by decide),keep4.get .v20 (by decide),hc.modulus e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
