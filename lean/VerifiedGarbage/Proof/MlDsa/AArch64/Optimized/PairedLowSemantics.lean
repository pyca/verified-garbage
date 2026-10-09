import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowModel

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high part for signed raw inverse outputs, before any memory framing. -/
theorem subHighReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (lowHighWord g (Inverse.signCorrected (Response.reduceWord (a-b)))).toNat=
      (highBits g (ofInt ((a.toNat:Int)-b.toInt))).toNat := by
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowHighWord_eq hg cb]
  exact Response.subHigh_word hg ha bl bh

/-- The paired rejection flag uses the same strict norm bound as the specification. -/
theorem subLowReduced_norm {g B : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    Response.normMask (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B then 0 else -1 := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_norm hg ha bl bh hB hB'

def lowInputField (m : Mem) (addr : Addr) (raw : BitVec 128) (e : Nat) : Zq :=
 ofInt (((vword (m.read addr 16) e).toNat:Int)-(vword raw e).toInt)

theorem lowInputValues_spec {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    (lowInputValues m addr raw e).toNat=(lowInputField m addr raw e).toNat :=
  Response.subInput_word ha bl bh

theorem lowInputValues_high {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    (lowHighWord g (lowInputValues m addr raw e)).toNat=(highBits g (lowInputField m addr raw e)).toNat :=
  subHighReduced_spec hg ha bl bh

theorem lowInputValues_low {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    let a := lowInputValues m addr raw e
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      lowBits g (lowInputField m addr raw e) :=
  subLowReduced_spec hg ha bl bh

theorem lowInputValues_norm {g B : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let a := lowInputValues m addr raw e
    Response.normMask (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (lowInputField m addr raw e)))<B then 0 else -1 :=
  subLowReduced_norm hg ha bl bh hB hB'
end VG.Proof.MlDsa.AArch64.Optimized.Paired
