module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Mgf
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSAES-OAEP on ARMv7: the label's hash

`argG`: an argument of the function, read from the frames, for the label's
hash (`LabelT.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32}

/-- An argument: its place, readable, and its value. -/
theorem argG (hg : Geo L scr) {σ s : State} (hs : L.St σ s) {j : Nat} (hj : j < L.argv.length) :
    State.addr (L.B + BitVec.ofNat 32 (arg j)) = L.fr (arg j) ∧ InRegions (s.rd ++ s.wr) (L.fr (arg j)) 4 ∧
    s.mem.readW (L.fr (arg j)) 32 = L.argv.getD j 0 := by
  have hn := hs.ok.nargs
  have ha := Lay.argOff_lt (L := L) (j := j) (by omega)
  have e : arg j = Impl.RsaPkcs1Sig.Arm.argOff L.F j := by rw [hg.F]
  rw [e]
  exact ⟨hs.ok.addrB (by omega), by rw [hs.rd, hs.wr]; exact hs.ok.arg_read hj, hs.arg hj⟩

end VG.Proof.RsaOaep.Arm
