module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddField
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.Comb

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem magnitude_byte (v j : Nat) : nafMagnitude (FastNaf.byte 5 v j)=FastNaf.magnitude 5 v j :=
  FastNaf.byte_magnitude 5 v j

theorem negative_byte (v j : Nat) : nafNegative (FastNaf.byte 5 v j)=FastNaf.negative 5 v j :=
  FastNaf.byte_negative 5 v j

/-- Stable external generator data is framed by work writes and unchanged symbols. -/
def ExternalFrame (base : Addr) (External : State → Prop) : Prop :=
  ∀ {s t},ProgKeep K.M base (jointWork cfg) s t → t.syms=s.syms → External s → External t

theorem entry_core_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 6512≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hj : j<257)
    (hmag : 1≤nafMagnitude (FastNaf.byte 5 v j)) (hmag15 : nafMagnitude (FastNaf.byte 5 v j)≤15)
    (hodd : nafMagnitude (FastNaf.byte 5 v j)%2=1)
    {Q A : Point C} {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (h : JointCore cfg C base size Q u v External A s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (CachedJac.entry K) s fun t =>
      EntryPost C base size (FastNaf.point C Q 5 v j) (jointLive cfg) s t ∧
      JointCore cfg C base size Q u v External A t := by
  refine WP.mono_syms (entry_ok hL hsize hm hj hmag hmag15 hodd h.field h.stable h19 h2)
    fun t hp sy => ?_
  have pointEq : (if nafNegative (FastNaf.byte 5 v j) then negPt (mul (nafMagnitude (FastNaf.byte 5 v j)) Q)
      else mul (nafMagnitude (FastNaf.byte 5 v j)) Q)=FastNaf.point C Q 5 v j := by
    rw [negative_byte v j,magnitude_byte v j]; rfl
  rw [pointEq] at hp
  refine ⟨hp,h.of_write (E:=tmv C K.M.n base t) hL hp.1 entry_work entry_slots (by decide +kernel) ?_
    (hExt (hp.1.mono entry_work) sy h.external)⟩
  exact hp.2.1.sub (fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx))

end VG.Proof.Weierstrass.AArch64.CachedField
