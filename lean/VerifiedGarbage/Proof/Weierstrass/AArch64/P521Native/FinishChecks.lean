module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishOutput
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Framework.Block

/-! Original ECDH security checks and masked serialization, independently of
how the affine shared coordinate was obtained. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ecdh.AArch64

 theorem checked_finish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64}
    (mn : wordsVal s.mem base (c.sl MN) c.n=c.C.n) (saved : Spill.Saved base g Cfg.saved s.mem)
    {V : Prop} [Decidable V] (hflag : word s.mem base (c.sl FLAG)=mask V) {out : Addr}
    (hx20 : s.gpr .x20=out) (hfit : out.toNat+c.C.len≤2^64)
    (hw : (⟨out,c.C.len⟩ : Region)∈s.wr) (hd : Region.Disjoint ⟨out,c.C.len⟩ ⟨base,size⟩) :
    WP isa (.block (c.checkRange (c.sl D)++c.checkNonzero (c.sl RZ)++VG.Impl.Ecdh.AArch64.Cfg.finish c)) s fun t =>
      VG.Spec.Ecdsa.bytesAt t.mem out c.C.len=
        (if ok c base s V then VG.Spec.Weierstrass.toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      (t.gpr .x0).setWidth 32=(if ok c base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hf : c.sl FLAG+8≤size := by have := sl_le c h7 (i:=FLAG) (by decide); omega_arith
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs h0 (sl_le c h7 (i:=D) (by decide)) (sl_le c h7 (i:=MN) (by decide))
    hf (sl_mod8 c D) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun u ⟨fu,ku,Ou⟩ => ?_
  have hsu := hs.of_keepRegs ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hsu h0 (sl_le c h7 (i:=RZ) (by decide)) hf
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun v ⟨fv,kv,Ov⟩ => ?_
  have hsv := hsu.of_keepRegs kv (by decide)
  have lowFlag : ∀w∈[(c.sl FLAG,8)],64≤w.1 := by
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact sl_ge64 c FLAG
  have savedV := Saved.unch (Saved.unch saved lowFlag Ou.unch) lowFlag Ov.unch
  have flagv : word v.mem base (c.sl FLAG)=if ok c base s V then BitVec.allOnes 64 else 0 := by
    rw [fv,fu,hflag,sv_flag Ou h0 h7 hn (i:=RZ) (by decide) (by decide),mn,mask_and,mask_and]
    simp only [mask,decide_eq_true_eq,and_assoc]
  have outv : v.gpr .x20=out := by rw [kv.gpr _ (by decide),ku.gpr _ (by decide),hx20]
  have wrv : (⟨out,c.C.len⟩ : Region)∈v.wr := by rw [kv.wr,ku.wr]; exact hw
  refine WP.mono (ecFinish_ok hc hsv outv hfit wrv hd savedV _ flagv) fun t ⟨bytes,ret,saved⟩ => ⟨?_,ret,saved⟩
  have xv : sv c base v X=sv c base s X :=
    (sv_flag Ov h0 h7 hn (i:=X) (by decide) (by decide)).trans
      (sv_flag Ou h0 h7 hn (i:=X) (by decide) (by decide))
  rw [bytes,xv]

/-- The exact emitted final block retains scalar/nonzero validation and the
original output/ABI contract, including every invalid-input path. -/
theorem native_finish_output_ok (hc : BaseCfgOk VG.Impl.Weierstrass.AArch64.P521Native.config)
    {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 64}
    (mn : wordsVal s.mem base 136 9=VG.Impl.Weierstrass.AArch64.P521Native.config.C.n)
    (saved : Spill.Saved base g Cfg.saved s.mem)
    {V : Prop} [Decidable V]
    (hflag : word s.mem base 3232=mask V) {out : Addr}
    (hx20 : s.gpr .x20=out) (hfit : out.toNat+66≤2^64)
    (hw : (⟨out,66⟩ : Region)∈s.wr) (hd : Region.Disjoint ⟨out,66⟩ ⟨base,size⟩) :
    WP isa (.block VG.Impl.Weierstrass.AArch64.P521Native.outerBlock171) s fun t =>
      VG.Spec.Ecdsa.bytesAt t.mem out 66=
        (if ok VG.Impl.Weierstrass.AArch64.P521Native.config base s V then
          VG.Spec.Weierstrass.toBytes 66 (wordsVal s.mem base 2584 9) else List.replicate 66 0) ∧
      (t.gpr .x0).setWidth 32=(if ok VG.Impl.Weierstrass.AArch64.P521Native.config base s V then 1 else 0) ∧
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=g r) := by
  apply finish_output_wp
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.AArch64.Mont.lr_ok s) fun u ⟨_,ku⟩ => ?_)
  have hsu := hs.of_keeps ku (by decide)
  have mnu : wordsVal u.mem base 136 9=VG.Impl.Weierstrass.AArch64.P521Native.config.C.n := by
    rw [ku.mem]; exact mn
  have savedU : Spill.Saved base g Cfg.saved u.mem := ku.mem.symm ▸ saved
  have flagu : word u.mem base 3232=mask V := by rw [ku.mem]; exact hflag
  have outu : u.gpr .x20=out := (ku.gpr .x20 (by decide)).trans hx20
  have wru : (⟨out,66⟩ : Region)∈u.wr := by rw [ku.wr]; exact hw
  refine WP.mono (checked_finish_ok hc hsu mnu savedU flagu outu hfit wru hd) fun t ht => ?_
  simpa only [ok,sv,ku.mem,
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.C.len=66 from rfl),
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.n=9 from rfl),
    (show VG.Impl.Weierstrass.AArch64.P521Native.config.sl X=2584 from rfl)] using ht

end VG.Proof.Weierstrass.AArch64.P521Native
