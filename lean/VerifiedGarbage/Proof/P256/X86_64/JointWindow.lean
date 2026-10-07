import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
import VerifiedGarbage.Proof.P256.X86_64.JointLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed

/-! Complete table initialization and joint multiplication, ready for the verification tail. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem p256_jointWindow_ok {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G} {s : State}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hd : (doubleSlots c.K.S c.K.R).Nodup)
    (hOne : c.K.one<Spec.P256.p) (hOneVal : toM Spec.P256.p (2^256) c.K.one=1)
    (hG : onCurve Spec.P256.curve G=true) (hQ : onCurve Spec.P256.curve Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (hi : Inv c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K)
      (tmv Spec.P256.curve c.K.M.n base s) s)
    (hp : InvJ Spec.P256.curve (tmv Spec.P256.curve c.K.M.n base s c.K.P.x)
      (tmv Spec.P256.curve c.K.M.n base s c.K.P.y) (tmv Spec.P256.curve c.K.M.n base s c.K.P.z) Q)
    (hz : tmv Spec.P256.curve c.K.M.n base s c.K.zero=0)
    (hvBits : ∀ i<257,s.mem (off base (c.K.bits+i))=FastNaf.byte 5 v i)
    (huBits : ∀ i<257,s.mem (off base (c.gBits+i))=FastNaf.byte 7 u i)
    (he : JointGenerator c Spec.P256.curve base T size row s) :
    WP isa (jointWindow c) s fun t =>
      JointLoopKeep c.K.M base (jointInitWork c++jointWork c) s t ∧
      JointCore c Spec.P256.curve base size Q u v
        (JointGenerator c Spec.P256.curve base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  rw [jointWindow,Joint.window]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (jointTables_ok hInit hm hC ha hOne hQ hi hp hz hvBits huBits he)
    fun a ⟨ka,ia,sa,ea⟩ => ?_
  apply WP.seq
  refine WP.mono (jointSeed_ok hL.lookup.layout hOne ia sa ea) fun b ⟨kb,cb,bb⟩ => ?_
  refine WP.mono (p256_jointRun_ok hL hm hC ha hd hOne hOneVal hG hQ hu hv cb bb)
    fun t ⟨kt,ct,tb⟩ => ?_
  exact ⟨(ka.mono (fun _ h => List.mem_append_left _ h)).trans
    ((kb.trans kt).mono (fun _ h => List.mem_append_right _ h)),ct,tb⟩

end VG.Proof.P256.X86_64
