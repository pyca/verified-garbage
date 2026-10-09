import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackOne

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

/-- The parser never consumes the output-vector temporaries as table data. -/
theorem gatherValue_congr {v w : VReg → BitVec 128} (h0 : v .v0=w .v0)
    (h1 : v .v1=w .v1) (h2 : v .v2=w .v2) (d g : Nat) :
    gatherValue v d g=gatherValue w d g := by
  unfold gatherValue
  congr 1
  funext e
  let ix := (vbyte (gatherIndex d g) e).toNat
  change (if ix<48 then tableByte v .v0 ix else 0) =
    (if ix<48 then tableByte w .v0 ix else 0)
  split
  · rename_i h
    unfold tableByte
    have hi : ix/16=0 ∨ ix/16=1 ∨ ix/16=2 := by omega
    rcases hi with hi | hi | hi
    · simp only [hi,show Nat.repeat VReg.succ 0 .v0=.v0 from rfl,h0]
    · simp only [hi,show Nat.repeat VReg.succ 1 .v0=.v1 from rfl,h1]
    · simp only [hi,show Nat.repeat VReg.succ 2 .v0=.v2 from rfl,h2]
  · rfl

theorem parsedVector_congr {s t : State}
    (h0 : t.v .v0=s.v .v0) (h1 : t.v .v1=s.v .v1) (h2 : t.v .v2=s.v .v2)
    (h20 : t.v .v20=s.v .v20) (h21 : t.v .v21=s.v .v21)
    (h22 : t.v .v22=s.v .v22) (h23 : t.v .v23=s.v .v23) (d g : Nat) :
    parsedVector t d g=parsedVector s d g := by
  simp only [parsedVector,gatherValue_congr h0 h1 h2,h20,h21,h22,h23]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
