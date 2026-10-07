import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.ScalarState
import VerifiedGarbage.Proof.Ecdh.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.Window5

/-! The 256-bit scalar is recoded into five words and expanded into the secret window's bit table. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64

structure PrepPost (c : Cfg) (base : Addr) (k : Nat) (s t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs [.rax,.r8,.rdx,.rbx] s t
  unch : Unch base (winX c) s.mem t.mem
  bits : ScalarBits (cfg c) base (recoded (cfg c) k) t
  fit : recoded (cfg c) k<32^(cfg c).J

theorem prep_ok {c : Cfg} (hn : c.n=4) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (.seq (.block (WinCfg.addConst 4 (c.sl K) c.winK (16*((32^52-1)/31))))
      (bits c.winK c.winBits 40)) s
      (PrepPost c base (wordsVal s.mem base (c.sl K) 4) s) := by
  have hk : wordsVal s.mem base (c.sl K) 4<2^256 := wordsVal_lt _ _ _ _
  have hf := Window5.recode_lt hk
  have hoff := Window5.offset_eq
  have hsrc : c.sl K+32≤size := by rw [sl_eq,hn]; decide
  have hdst : c.winK+40≤size := by change c.sl WK+40≤size; rw [sl_eq,hn]; decide
  have hbits : c.winBits+320≤size := by change c.sl WB+320≤size; rw [sl_eq,hn]; decide
  have hsep : c.sl K+32≤c.winK := by change c.sl K+32≤c.sl WK; rw [sl_eq,sl_eq,hn]; decide
  have hsep' : c.winK+40≤c.winBits := by change c.sl WK+40≤c.sl WB; rw [sl_eq,sl_eq,hn]; decide
  apply WP.seq
  refine WP.mono (addConst_ok hs (n:=4) (src:=c.sl K) (dst:=c.winK)
    (c:=16*((32^52-1)/31)) (by decide) hsrc hdst (Or.inl hsep)
    (by rw [← hoff]; omega) (by rw [← hoff]; omega)) fun a ⟨ea,ka,oa⟩ => ?_
  have ha := hs.of_keepRegs ka (by decide)
  refine WP.mono (bits_ok ha (n:=5) (src:=c.winK) (dst:=c.winBits)
    (by decide) (by decide) hdst hbits (Or.inl hsep')) fun b ⟨bb,kb,ob⟩ => ?_
  rw [ea,← hoff] at bb
  refine ⟨ha.of_keepRegs kb (by decide),
    (ka.mono (by decide)).trans (kb.mono (by decide)),?_,?_,hf⟩
  · have oa' := (oa.mono (o':=c.winK) (n':=16*c.n) (Nat.le_refl _) (by rw [hn]; omega)).unch
    have ob' := (ob.mono (o':=c.winBits) (n':=80*c.n) (Nat.le_refl _) (by rw [hn])).unch
    exact (oa'.trans ob').mono (by intro w hw; simpa only [winX,List.singleton_append] using hw)
  · intro i hi
    exact bb i (by change i<5*52 at hi; omega)

end VG.Proof.Ecdh.X86_64.Secret
