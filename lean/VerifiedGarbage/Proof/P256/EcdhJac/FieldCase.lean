import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.EcdhJac

structure FieldCase (ops : List FOp) where
  checked : Forward.OptChecked 8192 (fprog K.M ops) (Impl.Weierstrass.AArch64.Forward.optimize (fprog K.M ops))
  leftBound : ∀ i∈fprog K.M ops,Forward.instrBound i≤8192
  rightBound : ∀ i∈Impl.Weierstrass.AArch64.Forward.optimize (fprog K.M ops),Forward.instrBound i≤8192
  clob : ∀ r∈(Impl.Weierstrass.AArch64.Forward.optimize (fprog K.M ops)).flatMap Forward.instrClob,
    r∈VG.Proof.Mont.AArch64.clob 4

 theorem field_refinement {ops : List FOp} (cert : FieldCase ops)
    {base : Addr} {s : State} (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (fprogB K.M ops) s Q) :
    WP isa (arithmetic ops) s fun t =>
      ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (VG.Proof.Mont.AArch64.clob 4) s t := by
  have h := cert.checked.refine (by decide) (by decide) hs cert.leftBound cert.rightBound
    ((fprogB_wp _ _ (callOf_small (by decide))).mp hq)
  exact WP.mono h fun t ⟨u,hu,he,hk⟩ => ⟨u,hu,he,hk.mono cert.clob⟩

 theorem field_contract {ops : List FOp} (cert : FieldCase ops)
    {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop} {V W : List Nat}
    {E : Nat → Fin m} {s : State} {A : Prop} (hs : Scr s base 8192)
    (hb : WP isa (fprogB K.M ops) s fun t =>
      ProgKeep K.M base W s t ∧ Inv K.M base 8192 m Sl V E t ∧ A) :
    WP isa (arithmetic ops) s fun t =>
      ProgKeep K.M base W s t ∧ Inv K.M base 8192 m Sl V E t ∧ A := by
  exact WP.mono (field_refinement cert hs hb) fun _ ⟨_,⟨hk,hi,ha⟩,he,kt⟩ =>
    ⟨(Forward.transfer_post he kt hk hi).1,(Forward.transfer_post he kt hk hi).2,ha⟩

/-- The forwarded code realizes the ordinary field compiler contract. -/
theorem field_ok {ops : List FOp} (cert : FieldCase ops)
    {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M 8192 Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hi : Inv K.M base 8192 m Sl V E s)
    (hSl : ∀op∈ops,∀x∈op.out::op.ins,Sl x)
    (hLo : ∀op∈ops,Low K.M (op.out::op.ins)) (hV : readsOk ops V=true) :
    WP isa (arithmetic ops) s fun t =>
      ProgKeep K.M base (ops.map FOp.out) s t ∧
      Inv K.M base 8192 m Sl (validAfter ops V) (runOps ops E) t := by
  exact WP.mono (field_refinement cert hi.scr (fprogB_ok hL hAl hm ops hi hSl hLo hV))
    fun _ ⟨_,⟨hk,ht⟩,he,kt⟩ => Forward.transfer_post he kt hk ht

end VG.Proof.P256.EcdhJac
