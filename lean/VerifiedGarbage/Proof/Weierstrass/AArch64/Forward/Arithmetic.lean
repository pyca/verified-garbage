import VerifiedGarbage.Impl.P256.VerifyArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.P256.VerifyArithmetic

def original (k : Kind) := fprog VG.Impl.P256.VerifyDouble.M (operations k)
def optimized (k : Kind) := VG.Impl.Weierstrass.AArch64.Forward.optimize (original k)

structure Case (k : Kind) where
  checked : OptChecked 8192 (original k) (optimized k)
  leftBound : ∀ i∈original k,instrBound i≤8192
  rightBound : ∀ i∈optimized k,instrBound i≤8192
  clob : ∀ r∈(optimized k).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob 4

abbrev Cases := ∀ k, Case k

theorem refinement (certs : Cases) {M : Mod} {ops : List FOp}
    (sel : selected M ops)
    {base : Addr} {size : Nat} {s : State} (hs : Scr s base size) (hsize : 8192≤size)
    {Q : State → Prop} (hq : WP isa (fprogB M ops) s Q) :
    WP isa (program M ops) s fun t =>
      ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (VG.Proof.Mont.AArch64.clob M.n) s t := by
  rw [program,ite_eq_left sel]
  obtain ⟨rfl,hm⟩ := sel
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hm
  have c := certs k
  have h := c.checked.refine (by decide) (by decide) hs
    (fun i hi => Nat.le_trans (c.leftBound i hi) hsize)
    (fun i hi => Nat.le_trans (c.rightBound i hi) hsize) ((fprogB_wp _ _ (callOf_small (by decide))).mp hq)
  exact WP.mono h fun t ⟨u,hu,he,hk⟩ => ⟨u,hu,he,hk.mono c.clob⟩

/-- Lift a field contract, including algebraic facts independent of machine state. -/
theorem contract (certs : Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E : Nat → Fin m} {s : State} {ops : List FOp}
    {A : Prop} (hs : Scr s base size) (hsize : 8192≤size)
    (hb : WP isa (fprogB M ops) s fun t =>
      ProgKeep M base W s t ∧ Inv M base size m Sl V E t ∧ A) :
    WP isa (program M ops) s fun t =>
      ProgKeep M base W s t ∧ Inv M base size m Sl V E t ∧ A := by
  by_cases sel : selected M ops
  · exact WP.mono (refinement certs sel hs hsize hb)
      fun _ ⟨_,⟨hk,hi,ha⟩,he,kt⟩ => ⟨(transfer_post he kt hk hi).1,(transfer_post he kt hk hi).2,ha⟩
  · rw [program,ite_eq_right sel]
    exact hb

theorem field_ok (certs : Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) (hsize : 8192≤size) (ops : List FOp)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    (hSl : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x) (hLo : ∀ op∈ops, Low M (op.out::op.ins))
    (hV : readsOk ops V=true) :
    WP isa (program M ops) s fun t =>
      ProgKeep M base (ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) t := by
  have hb := fprogB_ok hL hAl hm ops hI hSl hLo hV
  by_cases sel : selected M ops
  · exact WP.mono (refinement certs sel hI.scr hsize hb)
      fun _ ⟨_,⟨hk,hi⟩,he,kt⟩ => transfer_post he kt hk hi
  · rw [program,ite_eq_right sel]
    exact hb

theorem field_relCT (certs : Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) (hsize : 8192≤size) (ops : List FOp)
    {V : List Nat} {E : Nat → Fin m}
    (hSl : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x) (hLo : ∀ op∈ops, Low M (op.out::op.ins))
    (hV : readsOk ops V=true)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (program M ops)) :
    RelCT isa (FieldPair M base size m Sl V E) (program M ops)
      (FieldPair M base size m Sl (validAfter ops V) (runOps ops E)) := by
  exact fieldWP_relCT hct fun _ hi => WP.mono (field_ok certs hL hAl hm hsize ops hi hSl hLo hV)
    fun _ ⟨hk,it⟩ => ⟨it,hk.sp⟩

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
