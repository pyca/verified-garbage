import VerifiedGarbage.Proof.P256.X86_64.JointPrep

/-! The measured two-scalar multiplication, including both recoders. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

section
variable {c : Joint.Cfg} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G}
    {E : Nat → Fin Spec.P256.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hPrep : JointPrepLayout c size srcU srcV)
    (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n))) (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hn : (doubleSlots c.K.S c.K.R).Nodup)
    (hOne : c.K.one<Spec.P256.p) (hOneVal : toM Spec.P256.p (2^256) c.K.one=1)
    (hG : onCurve Spec.P256.curve G=true) (hQ : onCurve Spec.P256.curve Q=true)
    (hp : InvJ Spec.P256.curve (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hz : E c.K.zero=0)
    (hu : u<2^256) (hv : v<2^256)

include hL hInit hPrep hm hC ha hn hOne hOneVal hG hQ hp hz hu hv

theorem p256_jointMul_ok {s : State}
    (hi : Inv c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s)
    (he : JointGenerator c Spec.P256.curve base T size row s)
    (hU : wordsVal s.mem base srcU 4=u) (hV : wordsVal s.mem base srcV 4=v) :
    WP isa (.seq (Joint.prep c srcU srcV) (jointWindow c)) s fun t =>
      JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row)
        (add (mul u G) (mul v Q)) t ∧ t.gpr .rbx=0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Unch base (jointPrepRanges c++((jointInitWork c++jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)]))
        s.mem t.mem := by
  apply WP.seq
  refine WP.mono (p256_jointPrepInput_ok hPrep hInit.naf.lay hi hp hz he hU hV)
    fun a ⟨ia,pa,ka,ua⟩ => ?_
  refine WP.mono (p256_jointWindow_ok hL hInit hm hC ha hn hOne hOneVal hG hQ hu hv
    (ia.to_tmv (C:=Spec.P256.curve)) pa.point pa.zero pa.peer pa.generator pa.external) fun t ⟨kt,ct,tb⟩ => ?_
  exact ⟨ct,tb,kt.regs.rd.trans ka.rd,kt.regs.wr.trans ka.wr,ua.trans kt.unch⟩

theorem p256_jointMul_relCT
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hd : ScratchCT (doubleHalfPublic c.K.M c.K.S c.K.R))
    (ht : NafTableChecks c.K) (hcache : ScratchCT (Naf.cacheTable c.K.M c.K.tbl c.cache 8))
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (hcG : FastPrepChecks srcU c.gBits 7) (hcQ : FastPrepChecks srcV c.K.bits 5) :
    RelCT isa (fun s t => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointGenerator c Spec.P256.curve base T size row s ∧ JointGenerator c Spec.P256.curve base T size row t ∧
      wordsVal s.mem base srcU 4=u ∧ wordsVal s.mem base srcV 4=v ∧
      wordsVal t.mem base srcU 4=u ∧ wordsVal t.mem base srcV 4=v)
      (.seq (Joint.prep c srcU srcV) (jointWindow c))
      (JointPair c Spec.P256.curve base size
        (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row))
        (add (mul u G) (mul v Q)) 0) :=
  RelCT.seq (p256_jointPrepInput_relCT hPrep hInit.naf.lay hp hz hcG hcQ)
    (p256_jointWindow_relCT hL hInit hm hC ha hn hOne hOneVal hG hQ hc hf hd ht hcache hseed hu hv)

end
end VG.Proof.P256.X86_64
