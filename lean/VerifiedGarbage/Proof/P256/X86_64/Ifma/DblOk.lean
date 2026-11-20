module

-- separate module: its proofs (about 5 s, the doubling's stages) are not checked again when `AddOk` changes
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Step
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.Env

/-! ### `P256.X86_64.Ifma.StageFacts`, which only this module used -/

section

/-!
# P-256 on x86-64 with AVX512_IFMA: what the kernel checks of each stage

For each stage of each block, with the field vectors it starts from in
their places (`leaves`): its piece of code computes its terms (`…_chk`); the
terms have the bounds `…IV` (`…_iv`); and the bounds the next stage starts
from are those, but for the carried lanes (`…_ov`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The lanes of stage 0 of `dbl` that are known to be carried by their number. -/
def dblOv0 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 3)]

theorem dbl_chk0 : chkSeg (dblPieces.getD 0 []) stT (dbl1 tops) (dblLocs.getD 0 []) = true := by
  decide +kernel

theorem dbl_iv0 : ivWithin stB (segT (dbl1 tops) stT) dblIV0 = true := by
  decide +kernel

theorem dbl_ov0 : ovOk dblBT0 dblIV0 dblOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `dbl` that are known to be carried by their number. -/
def dblOv1 : List (Nat × Nat) := []

theorem dbl_chk1 : chkSeg (dblPieces.getD 1 []) (leaves (dblLocs.getD 0 [])) (dbl2 tops) (dblLocs.getD 1 []) = true := by
  decide +kernel

theorem dbl_iv1 : ivWithin (bndsOf (dblLocs.getD 0 []) dblBT0) (segT (dbl2 tops) (leaves (dblLocs.getD 0 []))) dblIV1 = true := by
  decide +kernel

theorem dbl_ov1 : ovOk dblBT1 dblIV1 dblOv1 = true := by decide +kernel

/-- The lanes of stage 2 of `dbl` that are known to be carried by their number. -/
def dblOv2 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2)]

theorem dbl_chk2 : chkSeg (dblPieces.getD 2 []) (leaves (dblLocs.getD 1 [])) (dbl3 tops) (dblLocs.getD 2 []) = true := by
  decide +kernel

theorem dbl_iv2 : ivWithin (bndsOf (dblLocs.getD 1 []) dblBT1) (segT (dbl3 tops) (leaves (dblLocs.getD 1 []))) dblIV2 = true := by
  decide +kernel

theorem dbl_ov2 : ovOk dblBT2 dblIV2 dblOv2 = true := by decide +kernel

/-- The lanes of stage 3 of `dbl` that are known to be carried by their number. -/
def dblOv3 : List (Nat × Nat) := []

theorem dbl_chk3 : chkSeg (dblPieces.getD 3 []) (leaves (dblLocs.getD 2 [])) (dbl4 tops) (dblLocs.getD 3 []) = true := by
  decide +kernel

theorem dbl_iv3 : ivWithin (bndsOf (dblLocs.getD 2 []) dblBT2) (segT (dbl4 tops) (leaves (dblLocs.getD 2 []))) dblIV3 = true := by
  decide +kernel

theorem dbl_ov3 : ovOk dblBT3 dblIV3 dblOv3 = true := by decide +kernel

/-- The lanes of stage 4 of `dbl` that are known to be carried by their number. -/
def dblOv4 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem dbl_chk4 : chkSeg (dblPieces.getD 4 []) (leaves (dblLocs.getD 3 [])) (dbl5 tops) (dblLocs.getD 4 []) = true := by
  decide +kernel

theorem dbl_iv4 : ivWithin (bndsOf (dblLocs.getD 3 []) dblBT3) (segT (dbl5 tops) (leaves (dblLocs.getD 3 []))) dblIV4 = true := by
  decide +kernel

theorem dbl_ov4 : ovOk dblBT4 dblIV4 dblOv4 = true := by decide +kernel

/-- The lanes of stage 5 of `dbl` that are known to be carried by their number. -/
def dblOv5 : List (Nat × Nat) := []

theorem dbl_chk5 : chkSeg (dblPieces.getD 5 []) (leaves (dblLocs.getD 4 [])) (dbl6 tops) regs20 = true := by
  decide +kernel

theorem dbl_iv5 : ivWithin (bndsOf (dblLocs.getD 4 []) dblBT4) (segT (dbl6 tops) (leaves (dblLocs.getD 4 []))) dblIV5 = true := by
  decide +kernel

theorem dbl_ov5 : ovOk stBT dblIV5 dblOv5 = true := by decide +kernel

/-- The lanes of stage 0 of `add` that are known to be carried by their number. -/
def addOv0 : List (Nat × Nat) := []

theorem add_chk0 : chkSeg (addPieces.getD 0 []) addT (add1 tops) (addLocs.getD 0 []) = true := by
  decide +kernel

theorem add_iv0 : ivWithin addB (segT (add1 tops) addT) addIV0 = true := by
  decide +kernel

theorem add_ov0 : ovOk addBT0 addIV0 addOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `add` that are known to be carried by their number. -/
def addOv1 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem add_chk1 : chkSeg (addPieces.getD 1 []) (leaves (addLocs.getD 0 [])) (add2 tops) (addLocs.getD 1 []) = true := by
  decide +kernel

theorem add_iv1 : ivWithin (bndsOf (addLocs.getD 0 []) addBT0) (segT (add2 tops) (leaves (addLocs.getD 0 []))) addIV1 = true := by
  decide +kernel

theorem add_ov1 : ovOk addBT1 addIV1 addOv1 = true := by decide +kernel

/-- The lanes of stage 2 of `add` that are known to be carried by their number. -/
def addOv2 : List (Nat × Nat) := []

theorem add_chk2 : chkSeg (addPieces.getD 2 []) (leaves (addLocs.getD 1 [])) (add3 tops) (addLocs.getD 2 []) = true := by
  decide +kernel

theorem add_iv2 : ivWithin (bndsOf (addLocs.getD 1 []) addBT1) (segT (add3 tops) (leaves (addLocs.getD 1 []))) addIV2 = true := by
  decide +kernel

theorem add_ov2 : ovOk addBT2 addIV2 addOv2 = true := by decide +kernel

/-- The lanes of stage 3 of `add` that are known to be carried by their number. -/
def addOv3 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)]

theorem add_chk3 : chkSeg (addPieces.getD 3 []) (leaves (addLocs.getD 2 [])) (add4 tops) (addLocs.getD 3 []) = true := by
  decide +kernel

theorem add_iv3 : ivWithin (bndsOf (addLocs.getD 2 []) addBT2) (segT (add4 tops) (leaves (addLocs.getD 2 []))) addIV3 = true := by
  decide +kernel

theorem add_ov3 : ovOk addBT3 addIV3 addOv3 = true := by decide +kernel

/-- The lanes of stage 4 of `add` that are known to be carried by their number. -/
def addOv4 : List (Nat × Nat) := []

theorem add_chk4 : chkSeg (addPieces.getD 4 []) (leaves (addLocs.getD 3 [])) (add5 tops) (addLocs.getD 4 []) = true := by
  decide +kernel

theorem add_iv4 : ivWithin (bndsOf (addLocs.getD 3 []) addBT3) (segT (add5 tops) (leaves (addLocs.getD 3 []))) addIV4 = true := by
  decide +kernel

theorem add_ov4 : ovOk addBT4 addIV4 addOv4 = true := by decide +kernel

/-- The lanes of stage 5 of `add` that are known to be carried by their number. -/
def addOv5 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem add_chk5 : chkSeg (addPieces.getD 5 []) (leaves (addLocs.getD 4 [])) (add6 tops) (addLocs.getD 5 []) = true := by
  decide +kernel

theorem add_iv5 : ivWithin (bndsOf (addLocs.getD 4 []) addBT4) (segT (add6 tops) (leaves (addLocs.getD 4 []))) addIV5 = true := by
  decide +kernel

theorem add_ov5 : ovOk addBT5 addIV5 addOv5 = true := by decide +kernel

/-- The lanes of stage 6 of `add` that are known to be carried by their number. -/
def addOv6 : List (Nat × Nat) := []

theorem add_chk6 : chkSeg (addPieces.getD 6 []) (leaves (addLocs.getD 5 [])) (add7 tops) regs20 = true := by
  decide +kernel

theorem add_iv6 : ivWithin (bndsOf (addLocs.getD 5 []) addBT5) (segT (add7 tops) (leaves (addLocs.getD 5 []))) addIV6 = true := by
  decide +kernel

theorem add_ov6 : ovOk stBT addIV6 addOv6 = true := by decide +kernel

/-- The lanes of stage 0 of `set` that are known to be carried by their number. -/
def setOv0 : List (Nat × Nat) := [(1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3)]

theorem set_chk0 : chkSeg (setPieces.getD 0 []) setT (set1 tops) (setLocs.getD 0 []) = true := by
  decide +kernel

theorem set_iv0 : ivWithin setB (segT (set1 tops) setT) setIV0 = true := by
  decide +kernel

theorem set_ov0 : ovOk setBT0 setIV0 setOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `set` that are known to be carried by their number. -/
def setOv1 : List (Nat × Nat) := []

theorem set_chk1 : chkSeg (setPieces.getD 1 []) (leaves (setLocs.getD 0 [])) (set2 tops) regs20 = true := by
  decide +kernel

theorem set_iv1 : ivWithin (bndsOf (setLocs.getD 0 []) setBT0) (segT (set2 tops) (leaves (setLocs.getD 0 []))) setIV1 = true := by
  decide +kernel

theorem set_ov1 : ovOk stBT setIV1 setOv1 = true := by decide +kernel

/-- The lanes of stage 0 of `out` that are known to be carried by their number. -/
def outOv0 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 3)]

theorem out_chk0 : chkSeg (outPieces.getD 0 []) stT (out1 tops) (outLocs.getD 0 []) = true := by
  decide +kernel

theorem out_iv0 : ivWithin stB (segT (out1 tops) stT) outIV0 = true := by
  decide +kernel

theorem out_ov0 : ovOk outBT0 outIV0 outOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `out` that are known to be carried by their number. -/
def outOv1 : List (Nat × Nat) := []

theorem out_chk1 : chkSeg (outPieces.getD 1 []) (leaves (outLocs.getD 0 [])) (out2 tops) (outLocs.getD 1 []) = true := by
  decide +kernel

theorem out_iv1 : ivWithin (bndsOf (outLocs.getD 0 []) outBT0) (segT (out2 tops) (leaves (outLocs.getD 0 []))) outIV1 = true := by
  decide +kernel

theorem out_ov1 : ovOk outBT1 outIV1 outOv1 = true := by decide +kernel

/-- The lanes of stage 2 of `out` that are known to be carried by their number. -/
def outOv2 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 3)]

theorem out_chk2 : chkSeg (outPieces.getD 2 []) (leaves (outLocs.getD 1 [])) (out3 tops) regs5 = true := by
  decide +kernel

theorem out_iv2 : ivWithin (bndsOf (outLocs.getD 1 []) outBT1) (segT (out3 tops) (leaves (outLocs.getD 1 []))) outIV2 = true := by
  decide +kernel

theorem out_ov2 : ovOk outBT2 outIV2 outOv2 = true := by decide +kernel

/-- The lanes of stage 0 of `convQ` that are known to be carried by their number. -/
def convQOv0 : List (Nat × Nat) := [(4, 0), (4, 1), (4, 2), (4, 3)]

theorem convQ_chk0 : chkSeg (convQPieces.getD 0 []) convQT (convQ tops) regs30 = true := by
  decide +kernel

theorem convQ_iv0 : ivWithin stB (segT (convQ tops) convQT) convQIV0 = true := by
  decide +kernel

theorem convQ_ov0 : ovOk (stBT ++ entBT) convQIV0 convQOv0 = true := by decide +kernel

/-- The lanes of stage 0 of `convG` that are known to be carried by their number. -/
def convGOv0 : List (Nat × Nat) := []

theorem convG_chk0 : chkSeg (convGPieces.getD 0 []) convGT (convG tops) regs30 = true := by
  decide +kernel

theorem convG_iv0 : ivWithin stB (segT (convG tops) convGT) convGIV0 = true := by
  decide +kernel

theorem convG_ov0 : ovOk (stBT ++ entBT) convGIV0 convGOv0 = true := by decide +kernel

/-- The lanes of stage 0 of `tabG` that are known to be carried by their number. -/
def tabGOv0 : List (Nat × Nat) := []

theorem tabG_chk0 : chkSeg (tabGPieces.getD 0 []) [rawPT] (tabG tops) regs10 = true := by
  decide +kernel

theorem tabG_iv0 : ivWithin stB (segT (tabG tops) [rawPT]) tabGIV0 = true := by
  decide +kernel

theorem tabG_ov0 : ovOk entBT tabGIV0 tabGOv0 = true := by decide +kernel

/-- The lanes of stage 0 of `dblu` that are known to be carried by their number. -/
def dbluOv0 : List (Nat × Nat) := []

theorem dblu_chk0 : chkSeg (dbluPieces.getD 0 []) [t5 0, t5 5] (dblu1 tops) (dbluLocs.getD 0 []) = true := by
  decide +kernel

theorem dblu_iv0 : ivWithin (bndsOf regs10 entBT) (segT (dblu1 tops) [t5 0, t5 5]) dbluIV0 = true := by
  decide +kernel

theorem dblu_ov0 : ovOk dbluBT0 dbluIV0 dbluOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `dblu` that are known to be carried by their number. -/
def dbluOv1 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem dblu_chk1 : chkSeg (dbluPieces.getD 1 []) (leaves (dbluLocs.getD 0 [])) (dblu2 tops) (dbluLocs.getD 1 []) = true := by
  decide +kernel

theorem dblu_iv1 : ivWithin (bndsOf (dbluLocs.getD 0 []) dbluBT0) (segT (dblu2 tops) (leaves (dbluLocs.getD 0 []))) dbluIV1 = true := by
  decide +kernel

theorem dblu_ov1 : ovOk dbluBT1 dbluIV1 dbluOv1 = true := by decide +kernel

/-- The lanes of stage 2 of `dblu` that are known to be carried by their number. -/
def dbluOv2 : List (Nat × Nat) := []

theorem dblu_chk2 : chkSeg (dbluPieces.getD 2 []) (leaves (dbluLocs.getD 1 [])) (dblu3 tops) (dbluLocs.getD 2 []) = true := by
  decide +kernel

theorem dblu_iv2 : ivWithin (bndsOf (dbluLocs.getD 1 []) dbluBT1) (segT (dblu3 tops) (leaves (dbluLocs.getD 1 []))) dbluIV2 = true := by
  decide +kernel

theorem dblu_ov2 : ovOk dbluBT2 dbluIV2 dbluOv2 = true := by decide +kernel

/-- The lanes of stage 3 of `dblu` that are known to be carried by their number. -/
def dbluOv3 : List (Nat × Nat) := [(0, 0), (0, 1)]

theorem dblu_chk3 : chkSeg (dbluPieces.getD 3 []) (leaves (dbluLocs.getD 2 [])) (dblu4 tops) (dbluLocs.getD 3 []) = true := by
  decide +kernel

theorem dblu_iv3 : ivWithin (bndsOf (dbluLocs.getD 2 []) dbluBT2) (segT (dblu4 tops) (leaves (dbluLocs.getD 2 []))) dbluIV3 = true := by
  decide +kernel

theorem dblu_ov3 : ovOk dbluBT3 dbluIV3 dbluOv3 = true := by decide +kernel

/-- The lanes of stage 4 of `dblu` that are known to be carried by their number. -/
def dbluOv4 : List (Nat × Nat) := []

theorem dblu_chk4 : chkSeg (dbluPieces.getD 4 []) (leaves (dbluLocs.getD 3 [])) (dblu5 tops) regs20 = true := by
  decide +kernel

theorem dblu_iv4 : ivWithin (bndsOf (dbluLocs.getD 3 []) dbluBT3) (segT (dblu5 tops) (leaves (dbluLocs.getD 3 []))) dbluIV4 = true := by
  decide +kernel

theorem dblu_ov4 : ovOk tabBT dbluIV4 dbluOv4 = true := by decide +kernel

/-- The lanes of stage 0 of `zaddu` that are known to be carried by their number. -/
def zadduOv0 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem zaddu_chk0 : chkSeg (zadduPieces.getD 0 []) tabT (zaddu1 tops) (zadduLocs.getD 0 []) = true := by
  decide +kernel

theorem zaddu_iv0 : ivWithin (bndsOf regs20 tabBT) (segT (zaddu1 tops) tabT) zadduIV0 = true := by
  decide +kernel

theorem zaddu_ov0 : ovOk zadduBT0 zadduIV0 zadduOv0 = true := by decide +kernel

/-- The lanes of stage 1 of `zaddu` that are known to be carried by their number. -/
def zadduOv1 : List (Nat × Nat) := []

theorem zaddu_chk1 : chkSeg (zadduPieces.getD 1 []) (leaves (zadduLocs.getD 0 [])) (zaddu2 tops) (zadduLocs.getD 1 []) = true := by
  decide +kernel

theorem zaddu_iv1 : ivWithin (bndsOf (zadduLocs.getD 0 []) zadduBT0) (segT (zaddu2 tops) (leaves (zadduLocs.getD 0 []))) zadduIV1 = true := by
  decide +kernel

theorem zaddu_ov1 : ovOk zadduBT1 zadduIV1 zadduOv1 = true := by decide +kernel

/-- The lanes of stage 2 of `zaddu` that are known to be carried by their number. -/
def zadduOv2 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem zaddu_chk2 : chkSeg (zadduPieces.getD 2 []) (leaves (zadduLocs.getD 1 [])) (zaddu3 tops) (zadduLocs.getD 2 []) = true := by
  decide +kernel

theorem zaddu_iv2 : ivWithin (bndsOf (zadduLocs.getD 1 []) zadduBT1) (segT (zaddu3 tops) (leaves (zadduLocs.getD 1 []))) zadduIV2 = true := by
  decide +kernel

theorem zaddu_ov2 : ovOk zadduBT2 zadduIV2 zadduOv2 = true := by decide +kernel

/-- The lanes of stage 3 of `zaddu` that are known to be carried by their number. -/
def zadduOv3 : List (Nat × Nat) := []

theorem zaddu_chk3 : chkSeg (zadduPieces.getD 3 []) (leaves (zadduLocs.getD 2 [])) (zaddu4 tops) (zadduLocs.getD 3 []) = true := by
  decide +kernel

theorem zaddu_iv3 : ivWithin (bndsOf (zadduLocs.getD 2 []) zadduBT2) (segT (zaddu4 tops) (leaves (zadduLocs.getD 2 []))) zadduIV3 = true := by
  decide +kernel

theorem zaddu_ov3 : ovOk zadduBT3 zadduIV3 zadduOv3 = true := by decide +kernel

/-- The lanes of stage 4 of `zaddu` that are known to be carried by their number. -/
def zadduOv4 : List (Nat × Nat) := [(0, 0), (0, 1), (0, 2), (0, 3)]

theorem zaddu_chk4 : chkSeg (zadduPieces.getD 4 []) (leaves (zadduLocs.getD 3 [])) (zaddu5 tops) (zadduLocs.getD 4 []) = true := by
  decide +kernel

theorem zaddu_iv4 : ivWithin (bndsOf (zadduLocs.getD 3 []) zadduBT3) (segT (zaddu5 tops) (leaves (zadduLocs.getD 3 []))) zadduIV4 = true := by
  decide +kernel

theorem zaddu_ov4 : ovOk zadduBT4 zadduIV4 zadduOv4 = true := by decide +kernel

/-- The lanes of stage 5 of `zaddu` that are known to be carried by their number. -/
def zadduOv5 : List (Nat × Nat) := []

theorem zaddu_chk5 : chkSeg (zadduPieces.getD 5 []) (leaves (zadduLocs.getD 4 [])) (zaddu6 tops) (zadduLocs.getD 5 []) = true := by
  decide +kernel

theorem zaddu_iv5 : ivWithin (bndsOf (zadduLocs.getD 4 []) zadduBT4) (segT (zaddu6 tops) (leaves (zadduLocs.getD 4 []))) zadduIV5 = true := by
  decide +kernel

theorem zaddu_ov5 : ovOk zadduBT5 zadduIV5 zadduOv5 = true := by decide +kernel

/-- The lanes of stage 6 of `zaddu` that are known to be carried by their number. -/
def zadduOv6 : List (Nat × Nat) := [(0, 3), (1, 0)]

theorem zaddu_chk6 : chkSeg (zadduPieces.getD 6 []) (leaves (zadduLocs.getD 5 [])) (zaddu7 tops) regs20 = true := by
  decide +kernel

theorem zaddu_iv6 : ivWithin (bndsOf (zadduLocs.getD 5 []) zadduBT5) (segT (zaddu7 tops) (leaves (zadduLocs.getD 5 []))) zadduIV6 = true := by
  decide +kernel

theorem zaddu_ov6 : ovOk tabBT zadduIV6 zadduOv6 = true := by decide +kernel

end VG.Proof.P256.X86_64.Ifma

end

end


/-!
# P-256 on x86-64 with AVX512_IFMA: the doubling

The accumulator's vectors stand for the Jacobian triple `(4 xn, 4 un, 2 z)`
(`AccOk`), and the doubling's code makes of them those of `(4 X3, 4 U3, 2 Z3)`
(`dbl_ok`): six pieces of code, each a stage of `Impl/…/Ifma/Point.lean`,
with what is known between them (`DblCut1`, …).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## Integers as field elements

The limbs of the vector code are signed, and the numbers they stand for may
be negative or above the modulus: `ofI` is an integer modulo `m`, a ring
homomorphism, and `dec` what it stands for in Montgomery's form with
`R = 2²⁶⁰`.
-/

section

open VG.Proof.Weierstrass

section
variable {m : Nat} [NeZero m]

/-- The residue of an integer modulo `m`, as a natural number. -/
def res (m : Nat) (v : Int) : Nat := (v % (m : Int)).toNat

theorem res_cast (v : Int) : (res m v : Int) = v % (m : Int) := by
  obtain hm : (0 : Int) < m := Int.natCast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))
  have := Int.emod_nonneg v (Int.ne_of_gt hm)
  unfold res; omega_using [this]

theorem res_lt (v : Int) : res m v < m := by
  obtain hm : (0 : Int) < m := Int.natCast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))
  obtain h1 := Int.emod_lt_of_pos v hm
  have := res_cast (m := m) v
  omega_using [h1, this]

theorem res_add (a b : Int) : res m (a + b) = (res m a + res m b) % m := by
  apply Int.ofNat.inj
  show ((res m (a + b) : Nat) : Int) = ((res m a + res m b) % m : Nat)
  rw [res_cast]; push_cast; rw [res_cast, res_cast, ← Int.add_emod]

theorem res_mul (a b : Int) : res m (a * b) = (res m a * res m b) % m := by
  apply Int.ofNat.inj
  show ((res m (a * b) : Nat) : Int) = ((res m a * res m b) % m : Nat)
  rw [res_cast]; push_cast; rw [res_cast, res_cast, ← Int.mul_emod]

theorem res_natCast (n : Nat) : res m (n : Int) = n % m := by
  apply Int.ofNat.inj
  show ((res m (n : Int) : Nat) : Int) = ((n % m : Nat) : Int)
  rw [res_cast]; push_cast; rfl

/-- An integer modulo `m`. -/
def ofI (m : Nat) [NeZero m] (v : Int) : Fin m := Fin.ofNat m (res m v)

theorem ofI_add (a b : Int) : ofI m (a + b) = ofI m a + ofI m b := by
  unfold ofI; rw [res_add, ofNat_mod, ofNat_add']

theorem ofI_mul (a b : Int) : ofI m (a * b) = ofI m a * ofI m b := by
  unfold ofI; rw [res_mul, ofNat_mod, ofNat_mul']

theorem ofI_natCast (n : Nat) : ofI m (n : Int) = Fin.ofNat m n := by
  unfold ofI; rw [res_natCast, ofNat_mod]

theorem ofI_self : ofI m (m : Int) = 0 := by
  rw [ofI_natCast]; apply Fin.ext; rw [Fin.val_ofNat, Nat.mod_self]; rfl

theorem ofI_sub (a b : Int) : ofI m (a - b) = ofI m a - ofI m b := by
  have := ofI_add (m := m) (a - b) b
  rw [show a - b + b = a by omega_using []] at this
  grind

/-- A multiple of `m` more is the same. -/
theorem ofI_add_mul (a q : Int) : ofI m (a + q * (m : Int)) = ofI m a := by
  rw [ofI_add, ofI_mul, ofI_self]; grind

/-- What an integer stands for in Montgomery's form with `R = 2²⁶⁰`. -/
def dec (m : Nat) [NeZero m] (v : Int) : Fin m := ofI m v * rinv m (2 ^ 260)

theorem dec_add (a b : Int) : dec m (a + b) = dec m a + dec m b := by
  unfold dec; rw [ofI_add]; grind

theorem dec_sub (a b : Int) : dec m (a - b) = dec m a - dec m b := by
  unfold dec; rw [ofI_sub]; grind

theorem dec_add_mul (a q : Int) : dec m (a + q * (m : Int)) = dec m a := by
  unfold dec; rw [ofI_add_mul]

theorem dec_sub_mul (a q : Int) : dec m (a - q * (m : Int)) = dec m a := by
  rw [show a - q * (m : Int) = a + (-q) * (m : Int) by grind, dec_add_mul]

/-- A multiple by a natural number. -/
theorem dec_nat_mul (n : Nat) (a : Int) : dec m ((n : Int) * a) = Fin.ofNat m n * dec m a := by
  unfold dec; rw [ofI_mul, ofI_natCast]; grind

/-- A Montgomery product. -/
theorem dec_mont (hR : UnitMod m (2 ^ 260)) {o a b M : Int} (h : o * 2 ^ 260 = a * b + M * (m : Int)) :
    dec m o = dec m a * dec m b := by
  obtain h1 := congrArg (ofI m) h
  rw [ofI_add_mul, ofI_mul, ofI_mul, show ((2 : Int) ^ 260) = ((2 ^ 260 : Nat) : Int) from (Int.natCast_pow 2 260).symm,
    ofI_natCast] at h1
  obtain hu := mul_rinv hR
  unfold dec
  grind

end

end

/-!
## The doubling's stages, as numbers
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

theorem dbl1g_v0 (u zn q3 : F5 T) (E : Env) :
    vI E 0 (Id.run (dbl1g tops u zn q3)) = 4 * vI E 0 u + 80 * pI := by
  glue_simp [dbl1g]
  omega_using []

theorem dbl1g_v1 (u zn q3 : F5 T) (E : Env) :
    vI E 1 (Id.run (dbl1g tops u zn q3)) = 4 * vI E 0 u + 2 * vI E 1 zn + 80 * pI := by
  glue_simp [dbl1g]
  omega_using []

theorem dbl1g_v3 (u zn q3 : F5 T) (E : Env) :
    vI E 3 (Id.run (dbl1g tops u zn q3)) = 48 * (vI E 3 q3 - vI E 1 q3) + 96 * pI := by
  glue_simp [dbl1g]
  omega_using []

theorem dbl3g_v0 (q1 n3 : F5 T) (E : Env) : vI E 0 (Id.run (dbl3g tops q1 n3)) = vI E 0 q1 := by
  glue_simp [dbl3g]
  omega_using []

theorem dbl3g_v1 (q1 n3 : F5 T) (E : Env) :
    vI E 1 (Id.run (dbl3g tops q1 n3)) = vI E 1 q1 - vI E 0 q1 - 4 * vI E 1 n3 + 10 * pI := by
  glue_simp [dbl3g]
  omega_using []

theorem dbl3g_v2 (q1 n3 : F5 T) (E : Env) :
    vI E 2 (Id.run (dbl3g tops q1 n3)) = vI E 0 q1 + 4 * vI E 3 n3 := by
  glue_simp [dbl3g]
  omega_using []

/-- `W = XB2 - BB - 16 XX'`, as the lanes of `dbl5g` have it. -/
def dblW (E : Env) (q2 q3 : F5 T) : Int := vI E 2 q2 - vI E 0 q2 - 16 * vI E 3 q3

theorem dbl5g_v0 (q2 q1 o1 q3 : F5 T) (E : Env) :
    vI E 0 (Id.run (dbl5g tops q2 q1 o1 q3)).1 = 6 * dblW E q2 q3 - vI E 3 q1 + 200 * pI := by
  glue_simp [dbl5g, dblW]
  omega_using []

theorem dbl5g_v1 (q2 q1 o1 q3 : F5 T) (E : Env) :
    vI E 1 (Id.run (dbl5g tops q2 q1 o1 q3)).1 = vI E 1 q2 := by
  glue_simp [dbl5g]
  omega_using []

theorem dbl5g_v2 (q2 q1 o1 q3 : F5 T) (E : Env) :
    vI E 2 (Id.run (dbl5g tops q2 q1 o1 q3)).1 = 6 * dblW E q2 q3 - vI E 3 q1 + vI E 3 o1 + 200 * pI := by
  glue_simp [dbl5g, dblW]
  omega_using []

theorem dbl5g_v3 (q2 q1 o1 q3 : F5 T) (E : Env) :
    vI E 3 (Id.run (dbl5g tops q2 q1 o1 q3)).1 = vI E 3 q1 - 4 * dblW E q2 q3 + 5 * pI := by
  glue_simp [dbl5g, dblW]
  omega_using []

theorem dbl5g_dd (q2 q1 o1 q3 : F5 T) (E : Env) : vI E 0 (Id.run (dbl5g tops q2 q1 o1 q3)).2.1 = vI E 3 q1 := by
  glue_simp [dbl5g]

theorem dbl5g_bb (q2 q1 o1 q3 : F5 T) (E : Env) : vI E 0 (Id.run (dbl5g tops q2 q1 o1 q3)).2.2 = vI E 0 q2 := by
  glue_simp [dbl5g]

theorem dbl6u_v0 (q3 pdd pbb : F5 T) (E : Env) :
    vI E 0 (Id.run (dbl6u tops q3 pdd pbb)) = vI E 2 q3 - vI E 0 q3 - vI E 0 pdd - 16 * vI E 0 pbb := by
  glue_simp [dbl6u]
  omega_using []

end

/-!
## What the stages' products and carries are

For lanes of field vectors as numbers (`vI`): a product of carried lanes is
below `p` and a little, and stands for the product (`mul_fact`, `sqr_fact`);
`norm` of a number in `[0, 2²⁶⁸)` is carried, below `Nb`, and stands for the
same (`norm_fact`).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Weierstrass (UnitMod unitMod_pow_two Unch)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

instance : NeZero pN := ⟨by decide⟩

theorem unitR : UnitMod pN (2 ^ 260) := unitMod_pow_two (by decide) 260

/-- What a number stands for. -/
abbrev D (v : Int) : Fin pN := dec pN v

theorem ofI_lit (n : Nat) : ofI pN (no_index (OfNat.ofNat n : Int)) = (OfNat.ofNat n : Fin pN) := ofI_natCast n

theorem ofI_pI : ofI pN pI = 0 := by rw [← pN_eq]; exact ofI_self

/-- A small number times. -/
theorem D_lit (n : Nat) (a : Int) : D (no_index (OfNat.ofNat n) * a) = (OfNat.ofNat n : Fin pN) * D a :=
  dec_nat_mul n a

theorem D_pI : D pI = 0 := by
  unfold D dec; rw [ofI_pI]; grind

theorem D_zero : D 0 = 0 := by
  have := D_lit 0 0
  rw [show ((0 : Int) * 0) = 0 from rfl] at this
  rw [this]; grind

/-- Closes an equation between what numbers stand for (`D`), given what their parts stand for (`hs`):
the numbers' sums, differences and small multiples are those of the field, and `p` is zero. -/
macro "d_ring" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [dec_add, dec_sub, D_lit, D_pI, D_zero, $hs,*] <;> grind))

/-- The bound of carried numbers. -/
abbrev Nb : Int := 2 ^ 256 + 2 ^ 238

/-- The bound of products of carried numbers. -/
abbrev Pb : Int := pI + 2 ^ 252 + 2 ^ 236

theorem Carried.nonneg {E : Env} {k : Nat} {v : F5 T} (h : Carried E k v) : 0 ≤ vI E k v := by
  unfold Carried at h
  simp only [vI, val5]
  omega_using [h]

/-- A product of carried lanes below `A` and `B`, with `A B ≤ 2²⁶⁰ Dd`. -/
theorem mul_fact {E : Env} {k : Nat} {a b : F5 T} (ha : Carried E k a) (hb : Carried E k b) {A B Dd : Int}
    (hA : vI E k a < A) (hB : vI E k b < B) (hAB : A * B ≤ 2 ^ 260 * Dd) :
    0 ≤ vI E k (Id.run (mulCore tops a b)) ∧ vI E k (Id.run (mulCore tops a b)) < pI + Dd ∧
      D (vI E k (Id.run (mulCore tops a b))) = D (vI E k a) * D (vI E k b) := by
  obtain ⟨M, h0, h1, h2⟩ := mulCore_val a b E k ha hb
  have a0 := ha.nonneg
  have b0 := hb.nonneg
  obtain hp : vI E k a * vI E k b ≤ A * B := Int.mul_le_mul (Int.le_of_lt hA) (Int.le_of_lt hB) b0 (by omega_using [hA, a0])
  refine ⟨?_, ?_, ?_⟩
  · have := Int.mul_nonneg a0 b0
    simp only [pI] at h2
    omega_using [h0, h2, this]
  · simp only [pI] at h2 ⊢
    omega_using [hAB, h1, h2, hp]
  · rw [← pN_eq] at h2
    exact dec_mont unitR h2

/-- A square of a carried lane below `Nb`. -/
theorem sqr_fact {E : Env} {k : Nat} {a : F5 T} (ha : Carried E k a) (hA : vI E k a < Nb) :
    0 ≤ vI E k (Id.run (sqrCore tops a)) ∧ vI E k (Id.run (sqrCore tops a)) < Pb ∧
      D (vI E k (Id.run (sqrCore tops a))) = D (vI E k a) * D (vI E k a) := by
  obtain ⟨M, h0, h1, h2⟩ := sqrCore_val a E k ha
  have a0 := ha.nonneg
  obtain hp : vI E k a * vI E k a ≤ Nb * Nb := Int.mul_le_mul (Int.le_of_lt hA) (Int.le_of_lt hA) a0 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · have := Int.mul_nonneg a0 a0
    simp only [pI] at h2
    omega_using [h0, h2, this]
  · simp only [pI, Pb, Nb] at h2 hp ⊢
    omega_using [h1, h2, hp]
  · rw [← pN_eq] at h2
    exact dec_mont unitR h2

/-- `norm` of a lane whose number is in `[0, 2²⁶⁸)`. -/
theorem norm_fact {s₀ : State} {B : Bnds} (hB : EnvOK s₀ B) (v : F5 T) {k : Nat} (hk : k < 4) {iv : Int × Int}
    (h : (Id.run (norm tops v)).l4.iv B k = some iv)
    (h0 : 0 ≤ vI (envOf s₀) k v) (h1 : vI (envOf s₀) k v < 2 ^ 268) :
    Carried (envOf s₀) k (Id.run (norm tops v)) ∧ vI (envOf s₀) k (Id.run (norm tops v)) < Nb ∧
      D (vI (envOf s₀) k (Id.run (norm tops v))) = D (vI (envOf s₀) k v) := by
  obtain ⟨c, e, -, lt⟩ := norm_carried hB v hk h h0 h1
  refine ⟨c, lt, ?_⟩
  rw [e, ← pN_eq]
  exact dec_sub_mul _ _

/-- Lane `k` of `v` is carried and below `bd`, and stands for `x`. -/
structure Lim (bd : Int) (E : Env) (k : Nat) (v : F5 T) (x : Fin pN) : Prop where
  c : Carried E k v
  hi : vI E k v < bd
  d : D (vI E k v) = x

/-- A carried lane, as `norm` leaves it. -/
abbrev Car := Lim Nb

/-- A lane of a table's entry. -/
abbrev Ent := Lim (2 ^ 259)

theorem Lim.lo {bd : Int} {E : Env} {k : Nat} {v : F5 T} {x : Fin pN} (h : Lim bd E k v x) : 0 ≤ vI E k v :=
  h.c.nonneg

/-- Lane `k` of `v` is in `[0, bd)`, and stands for `x`. -/
structure Val (bd : Int) (E : Env) (k : Nat) (v : F5 T) (x : Fin pN) : Prop where
  lo : 0 ≤ vI E k v
  hi : vI E k v < bd
  d : D (vI E k v) = x

/-- A lane of a product of carried lanes. -/
abbrev Raw := Val Pb

/-- The bound of products with an entry. -/
abbrev Wd : Int := pI + 2 ^ 255 + 2 ^ 238

/-- A lane of a product with an entry. -/
abbrev Wide := Val Wd

theorem Lim.mono {bd bd' : Int} {E : Env} {k : Nat} {v : F5 T} {x : Fin pN} (h : Lim bd E k v x) (hb : bd ≤ bd') :
    Lim bd' E k v x := ⟨h.c, Int.lt_of_lt_of_le h.hi hb, h.d⟩

theorem Lim.val {bd : Int} {E : Env} {k : Nat} {v : F5 T} {x : Fin pN} (h : Lim bd E k v x) : Val bd E k v x :=
  ⟨h.lo, h.hi, h.d⟩

theorem Raw.sqr {E : Env} {k : Nat} {a : F5 T} {x : Fin pN} (h : Car E k a x) :
    Raw E k (Id.run (sqrCore tops a)) (x * x) := by
  obtain ⟨l, u, e⟩ := sqr_fact h.c h.hi
  exact ⟨l, u, by rw [e, h.d]⟩

theorem Raw.mul {E : Env} {k : Nat} {a b : F5 T} {x y : Fin pN} (ha : Car E k a x) (hb : Car E k b y) :
    Raw E k (Id.run (mulCore tops a b)) (x * y) := by
  obtain ⟨l, u, e⟩ := mul_fact ha.c hb.c ha.hi hb.hi (Dd := 2 ^ 252 + 2 ^ 236) (by simp only [Nb]; omega_using [])
  exact ⟨l, u, by rw [e, ha.d, hb.d]⟩

theorem Wide.mul {E : Env} {k : Nat} {a b : F5 T} {x y : Fin pN} (ha : Car E k a x) (hb : Ent E k b y) :
    Wide E k (Id.run (mulCore tops a b)) (x * y) := by
  obtain ⟨l, u, e⟩ := mul_fact ha.c hb.c ha.hi hb.hi (Dd := 2 ^ 255 + 2 ^ 238) (by simp only [Nb]; omega_using [])
  exact ⟨l, u, by rw [e, ha.d, hb.d]⟩

theorem Car.norm {s₀ : State} {B : Bnds} (hB : EnvOK s₀ B) (v : F5 T) {k : Nat} (hk : k < 4) {iv : Int × Int}
    (h : (Id.run (norm tops v)).l4.iv B k = some iv)
    (h0 : 0 ≤ vI (envOf s₀) k v) (h1 : vI (envOf s₀) k v < 2 ^ 268) {x : Fin pN} (hd : D (vI (envOf s₀) k v) = x) :
    Car (envOf s₀) k (Id.run (norm tops v)) x := by
  obtain ⟨c, u, e⟩ := norm_fact hB v hk h h0 h1
  exact ⟨c, u, by rw [e, hd]⟩

/-! ### Lanes of permuted and blended vectors -/

theorem Carried.perm {E : Env} {k : Nat} {a : F5 T} (i0 i1 i2 i3 : Nat)
    (h : Carried E (sel4 (i0 + 4 * i1 + 16 * i2 + 64 * i3) k) a) : Carried E k (Id.run (fperm tops a i0 i1 i2 i3)) := by
  simp only [Carried, fperm, F5.mapM, Id.run, bind, pure, tops, T.int] at h ⊢
  exact h

theorem Carried.blend {E : Env} {k : Nat} {a b : F5 T} {m : Nat} (hm : m < 16)
    (h : if m.testBit k then Carried E k b else Carried E k a) : Carried E k (Id.run (fblend tops a b m)) := by
  simp only [Carried, fblend, F5.zipM, Id.run, bind, pure, tops_blend _ _ hm, T.int]
  split at h <;> rename_i hk <;> simp only [hk, ↓reduceIte] <;> exact h

theorem Lim.perm {bd : Int} {E : Env} {k k' : Nat} {a : F5 T} {x : Fin pN} (i0 i1 i2 i3 : Nat)
    (hk : sel4 (i0 + 4 * i1 + 16 * i2 + 64 * i3) k = k') (h : Lim bd E k' a x) :
    Lim bd E k (Id.run (fperm tops a i0 i1 i2 i3)) x := by
  subst hk
  obtain e := vI_fperm a i0 i1 i2 i3 E k
  exact ⟨Carried.perm _ _ _ _ h.c, by rw [Id.run, e]; exact h.hi, by rw [Id.run, e]; exact h.d⟩

theorem Lim.blendL {bd : Int} {E : Env} {k : Nat} {a b : F5 T} {m : Nat} {x : Fin pN} (hm : m < 16)
    (hk : m.testBit k = false) (h : Lim bd E k a x) : Lim bd E k (Id.run (fblend tops a b m)) x := by
  obtain e := vI_fblend a b hm E k
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at e
  exact ⟨Carried.blend hm (by simp only [hk, Bool.false_eq_true, ↓reduceIte]; exact h.c), by rw [Id.run, e]; exact h.hi,
    by rw [Id.run, e]; exact h.d⟩

theorem Lim.blendR {bd : Int} {E : Env} {k : Nat} {a b : F5 T} {m : Nat} {x : Fin pN} (hm : m < 16)
    (hk : m.testBit k = true) (h : Lim bd E k b x) : Lim bd E k (Id.run (fblend tops a b m)) x := by
  obtain e := vI_fblend a b hm E k
  simp only [hk, ↓reduceIte] at e
  exact ⟨Carried.blend hm (by simp only [hk, ↓reduceIte]; exact h.c), by rw [Id.run, e]; exact h.hi,
    by rw [Id.run, e]; exact h.d⟩

theorem Val.perm {bd : Int} {E : Env} {k k' : Nat} {a : F5 T} {x : Fin pN} (i0 i1 i2 i3 : Nat)
    (hk : sel4 (i0 + 4 * i1 + 16 * i2 + 64 * i3) k = k') (h : Val bd E k' a x) :
    Val bd E k (Id.run (fperm tops a i0 i1 i2 i3)) x := by
  subst hk
  obtain e := vI_fperm a i0 i1 i2 i3 E k
  exact ⟨by rw [Id.run, e]; exact h.lo, by rw [Id.run, e]; exact h.hi, by rw [Id.run, e]; exact h.d⟩

/-- The bounds of the top limb of a stage's carried vector, its first result. -/
theorem norm_iv {B : Bnds} {ts : List T} {bt : BT} (h : ivWithin B ts bt = true) {t : T} (ht : ts[4]? = some t)
    (k : Nat) (hk : k < 4) {b : Int × Int} (hb : bt.get 0 k = some b) : ∃ iv, t.iv B k = some iv := by
  obtain ⟨iv, e, -⟩ := ivWithin_get h (n := 4) ht hk hb
  exact ⟨iv, e⟩

/-- `norm_iv` for a stage's second result. -/
theorem norm_iv1 {B : Bnds} {ts : List T} {bt : BT} (h : ivWithin B ts bt = true) {t : T} (ht : ts[9]? = some t)
    (k : Nat) (hk : k < 4) {b : Int × Int} (hb : bt.get 1 k = some b) : ∃ iv, t.iv B k = some iv := by
  obtain ⟨iv, e, -⟩ := ivWithin_get h (n := 9) ht hk hb
  exact ⟨iv, e⟩

theorem Same.car {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) (j k : Nat) {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) {v : F5 T} (hv : xs.getD j zero5 = v) {bd : Int} {x : Fin pN}
    (hc : Lim bd E k v x) : Lim bd E' k (ys.getD j zero5) x := by
  subst hv
  obtain e := h.vI hk hb
  exact ⟨h.carried hk hb hc.c, by rw [e]; exact hc.hi, by rw [e]; exact hc.d⟩

theorem Same.raw {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) (j k : Nat) {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) {v : F5 T} (hv : xs.getD j zero5 = v) {bd : Int} {x : Fin pN}
    (hc : Val bd E k v x) : Val bd E' k (ys.getD j zero5) x := by
  subst hv
  obtain e := h.vI hk hb
  exact ⟨by rw [e]; exact hc.lo, by rw [e]; exact hc.hi, by rw [e]; exact hc.d⟩

/-- A limb of a lane. -/
theorem Same.limb {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) (j k i : Nat) {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) (hi : i < 5) {v : F5 T} (hv : xs.getD j zero5 = v) :
    ((ys.getD j zero5).get i).int E' k = (v.get i).int E k := by
  subst hv
  exact h j k b hk hb i hi

theorem Same.val {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) (j k : Nat) {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) {v : F5 T} (hv : xs.getD j zero5 = v) :
    Ifma.vI E' k (ys.getD j zero5) = Ifma.vI E k v := by
  subst hv
  exact h.vI hk hb

/-- A piece of the vector code changes only vector registers and the first `w` bytes of the slots. -/
structure KeptW (w : Nat) (s₀ s : State) : Prop where
  eq : vm s₀ s = s
  mem : Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem

/-- `KeptW`, for the first nine slots: what the blocks of the joint multiplication keep. -/
abbrev Kept (s₀ s : State) : Prop := KeptW slotsLen s₀ s

theorem KeptW.refl (w : Nat) (s : State) : KeptW w s s := ⟨rfl, Unch.refl _ _ _⟩

theorem Kept.refl (s : State) : Kept s s := KeptW.refl _ s

theorem KeptW.gpr {w : Nat} {s₀ s : State} (h : KeptW w s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl

theorem KeptW.rd {w : Nat} {s₀ s : State} (h : KeptW w s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl

theorem KeptW.wr {w : Nat} {s₀ s : State} (h : KeptW w s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl

theorem KeptW.trans {w : Nat} {s₀ s₁ s₂ : State} (h₁ : KeptW w s₀ s₁) (h₂ : KeptW w s₁ s₂) : KeptW w s₀ s₂ := by
  refine ⟨?_, ?_⟩
  · have e₁ := h₁.eq; have e₂ := h₂.eq
    rw [← e₂, ← e₁]; rfl
  · have := h₂.mem
    rw [h₁.gpr] at this
    exact (h₁.mem.trans this).mono fun _ hw => (List.mem_append.mp hw).elim id id

theorem KeptW.of {w : Nat} {σ : VSym} {s₀ s : State} (h : SRel par σ s₀ s)
    (hu : Unch (s₀.gpr .rdi) [(cfg.sbase, w)] s₀.mem s.mem) : KeptW w s₀ s := ⟨h.eq, hu⟩

/-- `cut_step`, with what the next piece needs of the state. -/
theorem cut_step' {w : Nat} {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSegW w c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B)
    {iv bt : BT} {ovs : List (Nat × Nat)} (hiv : ivWithin B (segT seg ins) iv = true) (hov : ovOk bt iv ovs = true)
    {rs : List (F5 T)} (hrs : Id.run (seg ins) = rs)
    (hlen : outs.length = 5 * rs.length) (hrows : iv.length ≤ rs.length)
    (hcar : ∀ j k, (j, k) ∈ ovs → Carried (envOf s₀) k (rs.getD j zero5)) :
    WP isa (.block c) s₀ fun s =>
      Ctx par s ∧ KeptW w s₀ s ∧ EnvOK s (bndsOf outs bt) ∧ Same iv (envOf s) (leaves outs) (envOf s₀) rs := by
  subst hrs
  exact WP.mono (cut_step h hc hB hiv hov hlen hrows hcar) fun s ⟨⟨σ, hσ⟩, hu, hE, hS⟩ =>
    ⟨ctx_step hc hσ, KeptW.of hσ hu, hE, hS⟩

theorem list3 {α : Type} (l : List α) (d : α) (h : l.length = 3) : l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [_, _, _], _ => rfl

theorem list4 {α : Type} (l : List α) (d : α) (h : l.length = 4) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d] := by
  match l, h with
  | [_, _, _, _], _ => rfl

theorem list5 {α : Type} (l : List α) (d : α) (h : l.length = 5) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d] := by
  match l, h with
  | [_, _, _, _, _], _ => rfl

/-- Closes a bound of a number from the bounds in the context. -/
macro "rng" : tactic => `(tactic| (simp only [Nb, Pb, Wd, pI] at *; omega))

end


open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The accumulator's vectors under `E` stand for `xn`, `un`, `z` (the
Jacobian triple `(4 xn, 4 un, 2 z)`), within the bounds a block starts from. -/
structure AccOk (E : Env) (u zn n3 q3 : F5 T) (xn un z : Fin pN) : Prop where
  ul : -20 * pI ≤ vI E 0 u
  uh : vI E 0 u ≤ 3 * pI
  du : D (vI E 0 u) = un
  zn : Car E 1 zn z
  a : Car E 1 n3 (z * z)
  x : Car E 3 n3 xn
  aa : Raw E 1 q3 (z * z * (z * z))
  xx : Raw E 3 q3 (xn * xn)

section
variable {F : Type} [Lean.Grind.CommRing F] (xn un z : F)

/-- `B = Y²`. -/
abbrev fB : F := 4 * un * (4 * un)
/-- `S = (Y + Z)²`. -/
abbrev fS : F := (4 * un + 2 * z) * (4 * un + 2 * z)
/-- `D = 3 (X² - Z⁴)`. -/
abbrev fD : F := 48 * (xn * xn - z * z * (z * z))
/-- `Z3 = S - B - Z²`. -/
abbrev fZ3 : F := fS un z - fB un - 4 * (z * z)
/-- `X + B`. -/
abbrev fXB : F := fB un + 4 * xn
/-- `W = (X + B)² - B² - X²`. -/
abbrev fW : F := fXB xn un * fXB xn un - fB un * fB un - 16 * (xn * xn)
/-- `X3 = D² - 4 W`. -/
abbrev fX3 : F := fD xn z * fD xn z - 4 * fW xn un
/-- `E = 2 W - X3`. -/
abbrev fE : F := 6 * fW xn un - fD xn z * fD xn z
/-- `U3 = (D + E)² - E² - D² - 16 B²`, twice `Y3`. -/
abbrev fU : F :=
  (fE xn un z + fD xn z) * (fE xn un z + fD xn z) - fE xn un z * fE xn un z - fD xn z * fD xn z -
    16 * (fB un * fB un)

end

/-- After the first stage: `o1 = [Y, Y + Z, _, D]`, carried. -/
structure DblCut1 (E : Env) (o1 q3 n3 : F5 T) (xn un z : Fin pN) : Prop where
  y : Car E 0 o1 (4 * un)
  yz : Car E 1 o1 (4 * un + 2 * z)
  d : Car E 3 o1 (fD xn z)
  a : Car E 1 n3 (z * z)
  x : Car E 3 n3 xn
  xx : Raw E 3 q3 (xn * xn)

/-- After the second: `q1 = [B, S, _, D²]`. -/
structure DblCut2 (E : Env) (q1 o1 q3 n3 : F5 T) (xn un z : Fin pN) : Prop where
  b : Raw E 0 q1 (fB un)
  s : Raw E 1 q1 (fS un z)
  dd : Raw E 3 q1 (fD xn z * fD xn z)
  d : Car E 3 o1 (fD xn z)
  a : Car E 1 n3 (z * z)
  x : Car E 3 n3 xn
  xx : Raw E 3 q3 (xn * xn)

/-- After the third: `o2 = [B, Z3, X + B, _]`, carried. -/
structure DblCut3 (E : Env) (o2 q1 o1 q3 : F5 T) (xn un z : Fin pN) : Prop where
  b : Car E 0 o2 (fB un)
  z3 : Car E 1 o2 (fZ3 un z)
  xb : Car E 2 o2 (fXB xn un)
  dd : Raw E 3 q1 (fD xn z * fD xn z)
  d : Car E 3 o1 (fD xn z)
  xx : Raw E 3 q3 (xn * xn)

/-- After the fourth: `q2 = [B², Z3², (X + B)², _]`. -/
structure DblCut4 (E : Env) (q2 o2 q1 o1 q3 : F5 T) (xn un z : Fin pN) : Prop where
  bb : Raw E 0 q2 (fB un * fB un)
  a3 : Raw E 1 q2 (fZ3 un z * fZ3 un z)
  xb2 : Raw E 2 q2 (fXB xn un * fXB xn un)
  z3 : Car E 1 o2 (fZ3 un z)
  dd : Raw E 3 q1 (fD xn z * fD xn z)
  d : Car E 3 o1 (fD xn z)
  xx : Raw E 3 q3 (xn * xn)

/-- After the fifth: `o3 = [E, Z3², D + E, X3]`, carried. -/
structure DblCut5 (E : Env) (o3 o2 pdd pbb : F5 T) (xn un z : Fin pN) : Prop where
  e : Car E 0 o3 (fE xn un z)
  a3 : Car E 1 o3 (fZ3 un z * fZ3 un z)
  de : Car E 2 o3 (fE xn un z + fD xn z)
  x3 : Car E 3 o3 (fX3 xn un z)
  z3 : Car E 1 o2 (fZ3 un z)
  dd : Raw E 0 pdd (fD xn z * fD xn z)
  bb : Raw E 0 pbb (fB un * fB un)

/-- The places of stage `j`'s results, as terms. -/
abbrev dL (j : Nat) : List (F5 T) := leaves (dblLocs.getD j [])

theorem dbl_s0 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) :
    WP isa (.block (dblPieces.getD 0 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dblLocs.getD 0 []) dblBT0) ∧
        DblCut1 (envOf s) ((dL 0).getD 0 zero5) ((dL 0).getD 1 zero5) ((dL 0).getD 2 zero5) xn un z := by
  obtain v0 := dbl1g_v0 (t5 0) (t5 5) (t5 15) (envOf s₀)
  obtain v1 := dbl1g_v1 (t5 0) (t5 5) (t5 15) (envOf s₀)
  obtain v3 := dbl1g_v3 (t5 0) (t5 5) (t5 15) (envOf s₀)
  obtain ⟨ul, uh, du, zn, a, x, aa, xx⟩ := h
  obtain zl := zn.lo; have zh := zn.hi; have aal := aa.lo; have aah := aa.hi; have xxl := xx.lo; have xxh := xx.hi
  obtain ⟨i0, hi0⟩ := norm_iv dbl_iv0 (t := (Id.run (norm tops (Id.run (dbl1g tops (t5 0) (t5 5) (t5 15))))).l4) rfl 0
    (by decide) (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv dbl_iv0 (t := (Id.run (norm tops (Id.run (dbl1g tops (t5 0) (t5 5) (t5 15))))).l4) rfl 1
    (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv dbl_iv0 (t := (Id.run (norm tops (Id.run (dbl1g tops (t5 0) (t5 5) (t5 15))))).l4) rfl 3
    (by decide) (b := _) rfl
  obtain c0 : Car (envOf s₀) 0 _ (4 * un) := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; d_ring [du])
  obtain c1 : Car (envOf s₀) 1 _ (4 * un + 2 * z) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; d_ring [du, zn.d])
  obtain c3 : Car (envOf s₀) 3 _ (fD xn z) := Car.norm hB _ (by decide) hi3 (by rw [v3]; rng) (by rw [v3]; rng)
    (by rw [v3]; d_ring [aa.d, xx.d])
  refine WP.mono (cut_step' dbl_chk0 hc hB dbl_iv0 dbl_ov0
    (rs := [Id.run (norm tops (Id.run (dbl1g tops (t5 0) (t5 5) (t5 15)))), t5 15, t5 10]) rfl rfl (by decide) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [dblOv0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 3 (by decide) rfl rfl c3,
      hS.car 2 1 (by decide) rfl rfl a, hS.car 2 3 (by decide) rfl rfl x, hS.raw 1 3 (by decide) rfl rfl xx⟩

theorem dbl_s1 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dblLocs.getD 0 []) dblBT0)) {xn un z : Fin pN}
    (h : DblCut1 (envOf s₀) ((dL 0).getD 0 zero5) ((dL 0).getD 1 zero5) ((dL 0).getD 2 zero5) xn un z) :
    WP isa (.block (dblPieces.getD 1 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dblLocs.getD 1 []) dblBT1) ∧
        DblCut2 (envOf s) ((dL 1).getD 0 zero5) ((dL 1).getD 1 zero5) ((dL 1).getD 2 zero5) ((dL 1).getD 3 zero5)
          xn un z := by
  obtain hchk := dbl_chk1; have hiv := dbl_iv1
  obtain hL := list3 (dL 0) zero5 (by decide +kernel)
  simp only [dL] at h hL
  generalize leaves (dblLocs.getD 0 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = o1, L.getD 1 zero5 = q3, L.getD 2 zero5 = n3 at h hL
  subst hL
  obtain ⟨y, yz, d, a, x, xx⟩ := h
  refine WP.mono (cut_step' hchk hc hB hiv dbl_ov1 (rs := [Id.run (sqrCore tops o1), o1, q3, n3]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.sqr y), hS.raw 0 1 (by decide) rfl rfl (Raw.sqr yz),
    hS.raw 0 3 (by decide) rfl rfl (Raw.sqr d), hS.car 1 3 (by decide) rfl rfl d, hS.car 3 1 (by decide) rfl rfl a,
    hS.car 3 3 (by decide) rfl rfl x, hS.raw 2 3 (by decide) rfl rfl xx⟩

theorem dbl_s2 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dblLocs.getD 1 []) dblBT1)) {xn un z : Fin pN}
    (h : DblCut2 (envOf s₀) ((dL 1).getD 0 zero5) ((dL 1).getD 1 zero5) ((dL 1).getD 2 zero5) ((dL 1).getD 3 zero5)
      xn un z) :
    WP isa (.block (dblPieces.getD 2 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dblLocs.getD 2 []) dblBT2) ∧
        DblCut3 (envOf s) ((dL 2).getD 0 zero5) ((dL 2).getD 1 zero5) ((dL 2).getD 2 zero5) ((dL 2).getD 3 zero5)
          xn un z := by
  obtain hchk := dbl_chk2; have hiv := dbl_iv2
  obtain hL := list4 (dL 1) zero5 (by decide +kernel)
  simp only [dL] at h hL
  generalize leaves (dblLocs.getD 1 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q1, L.getD 1 zero5 = o1, L.getD 2 zero5 = q3, L.getD 3 zero5 = n3 at h hL
  subst hL
  obtain ⟨b, s, dd, d, a, x, xx⟩ := h
  obtain v0 := dbl3g_v0 q1 n3 (envOf s₀)
  obtain v1 := dbl3g_v1 q1 n3 (envOf s₀)
  obtain v2 := dbl3g_v2 q1 n3 (envOf s₀)
  obtain bl := b.lo; have bh := b.hi; have sl := s.lo; have sh := s.hi
  obtain al := a.lo; have ah := a.hi; have xl := x.lo; have xh := x.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl3g tops q1 n3)))).l4) rfl 0 (by decide)
    (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl3g tops q1 n3)))).l4) rfl 1 (by decide)
    (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl3g tops q1 n3)))).l4) rfl 2 (by decide)
    (b := _) rfl
  obtain c0 : Car (envOf s₀) 0 _ (fB un) := Car.norm hB _ (by decide) hi0 (by rw [v0]; rng) (by rw [v0]; rng)
    (by rw [v0]; exact b.d)
  obtain c1 : Car (envOf s₀) 1 _ (fZ3 un z) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng) (by rw [v1]; rng)
    (by rw [v1]; d_ring [b.d, s.d, a.d])
  obtain c2 : Car (envOf s₀) 2 _ (fXB xn un) := Car.norm hB _ (by decide) hi2 (by rw [v2]; rng) (by rw [v2]; rng)
    (by rw [v2]; d_ring [b.d, x.d])
  refine WP.mono (cut_step' hchk hc hB hiv dbl_ov2
    (rs := [Id.run (norm tops (Id.run (dbl3g tops q1 n3))), q1, o1, q3]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [dblOv2, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.raw 1 3 (by decide) rfl rfl dd, hS.car 2 3 (by decide) rfl rfl d, hS.raw 3 3 (by decide) rfl rfl xx⟩

theorem dbl_s3 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dblLocs.getD 2 []) dblBT2)) {xn un z : Fin pN}
    (h : DblCut3 (envOf s₀) ((dL 2).getD 0 zero5) ((dL 2).getD 1 zero5) ((dL 2).getD 2 zero5) ((dL 2).getD 3 zero5)
      xn un z) :
    WP isa (.block (dblPieces.getD 3 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dblLocs.getD 3 []) dblBT3) ∧
        DblCut4 (envOf s) ((dL 3).getD 0 zero5) ((dL 3).getD 1 zero5) ((dL 3).getD 2 zero5) ((dL 3).getD 3 zero5)
          ((dL 3).getD 4 zero5) xn un z := by
  obtain hchk := dbl_chk3; have hiv := dbl_iv3
  obtain hL := list4 (dL 2) zero5 (by decide +kernel)
  simp only [dL] at h hL
  generalize leaves (dblLocs.getD 2 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = o2, L.getD 1 zero5 = q1, L.getD 2 zero5 = o1, L.getD 3 zero5 = q3 at h hL
  subst hL
  obtain ⟨b, z3, xb, dd, d, xx⟩ := h
  refine WP.mono (cut_step' hchk hc hB hiv dbl_ov3 (rs := [Id.run (sqrCore tops o2), o2, q1, o1, q3]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  exact ⟨hS.raw 0 0 (by decide) rfl rfl (Raw.sqr b), hS.raw 0 1 (by decide) rfl rfl (Raw.sqr z3),
    hS.raw 0 2 (by decide) rfl rfl (Raw.sqr xb), hS.car 1 1 (by decide) rfl rfl z3, hS.raw 2 3 (by decide) rfl rfl dd,
    hS.car 3 3 (by decide) rfl rfl d, hS.raw 4 3 (by decide) rfl rfl xx⟩

theorem dbl_s4 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dblLocs.getD 3 []) dblBT3)) {xn un z : Fin pN}
    (h : DblCut4 (envOf s₀) ((dL 3).getD 0 zero5) ((dL 3).getD 1 zero5) ((dL 3).getD 2 zero5) ((dL 3).getD 3 zero5)
      ((dL 3).getD 4 zero5) xn un z) :
    WP isa (.block (dblPieces.getD 4 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s (bndsOf (dblLocs.getD 4 []) dblBT4) ∧
        DblCut5 (envOf s) ((dL 4).getD 0 zero5) ((dL 4).getD 1 zero5) ((dL 4).getD 2 zero5) ((dL 4).getD 3 zero5)
          xn un z := by
  obtain hchk := dbl_chk4; have hiv := dbl_iv4
  obtain hL := list5 (dL 3) zero5 (by decide +kernel)
  simp only [dL] at h hL
  generalize leaves (dblLocs.getD 3 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = q2, L.getD 1 zero5 = o2, L.getD 2 zero5 = q1, L.getD 3 zero5 = o1,
    L.getD 4 zero5 = q3 at h hL
  subst hL
  obtain ⟨bb, a3, xb2, z3, dd, d, xx⟩ := h
  obtain v0 := dbl5g_v0 q2 q1 o1 q3 (envOf s₀)
  obtain v1 := dbl5g_v1 q2 q1 o1 q3 (envOf s₀)
  obtain v2 := dbl5g_v2 q2 q1 o1 q3 (envOf s₀)
  obtain v3 := dbl5g_v3 q2 q1 o1 q3 (envOf s₀)
  obtain vd := dbl5g_dd q2 q1 o1 q3 (envOf s₀)
  obtain vb := dbl5g_bb q2 q1 o1 q3 (envOf s₀)
  obtain bbl := bb.lo; have bbh := bb.hi; have a3l := a3.lo; have a3h := a3.hi; have xbl := xb2.lo; have xbh := xb2.hi
  obtain ddl := dd.lo; have ddh := dd.hi; have dl := d.lo; have dh := d.hi; have xxl := xx.lo; have xxh := xx.hi
  obtain ⟨i0, hi0⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl5g tops q2 q1 o1 q3)).1)).l4) rfl 0
    (by decide) (b := _) rfl
  obtain ⟨i1, hi1⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl5g tops q2 q1 o1 q3)).1)).l4) rfl 1
    (by decide) (b := _) rfl
  obtain ⟨i2, hi2⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl5g tops q2 q1 o1 q3)).1)).l4) rfl 2
    (by decide) (b := _) rfl
  obtain ⟨i3, hi3⟩ := norm_iv hiv (t := (Id.run (norm tops (Id.run (dbl5g tops q2 q1 o1 q3)).1)).l4) rfl 3
    (by decide) (b := _) rfl
  obtain c0 : Car (envOf s₀) 0 _ (fE xn un z) := Car.norm hB _ (by decide) hi0
    (by rw [v0]; simp only [dblW]; rng) (by rw [v0]; simp only [dblW]; rng)
    (by rw [v0]; simp only [dblW]; d_ring [bb.d, xb2.d, dd.d, xx.d])
  obtain c1 : Car (envOf s₀) 1 _ (fZ3 un z * fZ3 un z) := Car.norm hB _ (by decide) hi1 (by rw [v1]; rng)
    (by rw [v1]; rng) (by rw [v1]; exact a3.d)
  obtain c2 : Car (envOf s₀) 2 _ (fE xn un z + fD xn z) := Car.norm hB _ (by decide) hi2
    (by rw [v2]; simp only [dblW]; rng) (by rw [v2]; simp only [dblW]; rng)
    (by rw [v2]; simp only [dblW]; d_ring [bb.d, xb2.d, dd.d, xx.d, d.d])
  obtain c3 : Car (envOf s₀) 3 _ (fX3 xn un z) := Car.norm hB _ (by decide) hi3
    (by rw [v3]; simp only [dblW]; rng) (by rw [v3]; simp only [dblW]; rng)
    (by rw [v3]; simp only [dblW]; d_ring [bb.d, xb2.d, dd.d, xx.d])
  obtain pd : Raw (envOf s₀) 0 (Id.run (dbl5g tops q2 q1 o1 q3)).2.1 (fD xn z * fD xn z) :=
    ⟨by rw [vd]; exact dd.lo, by rw [vd]; exact dd.hi, by rw [vd]; exact dd.d⟩
  obtain pb : Raw (envOf s₀) 0 (Id.run (dbl5g tops q2 q1 o1 q3)).2.2 (fB un * fB un) :=
    ⟨by rw [vb]; exact bb.lo, by rw [vb]; exact bb.hi, by rw [vb]; exact bb.d⟩
  refine WP.mono (cut_step' hchk hc hB hiv dbl_ov4
    (rs := [Id.run (norm tops (Id.run (dbl5g tops q2 q1 o1 q3)).1), o2, (Id.run (dbl5g tops q2 q1 o1 q3)).2.1,
      (Id.run (dbl5g tops q2 q1 o1 q3)).2.2]) rfl rfl (Nat.le_of_eq rfl) ?_)
    fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  · intro j k hm
    simp only [dblOv4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact c0.c
    · exact c1.c
    · exact c2.c
    · exact c3.c
  · exact ⟨hS.car 0 0 (by decide) rfl rfl c0, hS.car 0 1 (by decide) rfl rfl c1, hS.car 0 2 (by decide) rfl rfl c2,
      hS.car 0 3 (by decide) rfl rfl c3, hS.car 1 1 (by decide) rfl rfl z3,
      hS.raw 2 0 (by decide) rfl rfl pd, hS.raw 3 0 (by decide) rfl rfl pb⟩

theorem dbl_s5 {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf (dblLocs.getD 4 []) dblBT4)) {xn un z : Fin pN}
    (h : DblCut5 (envOf s₀) ((dL 4).getD 0 zero5) ((dL 4).getD 1 zero5) ((dL 4).getD 2 zero5) ((dL 4).getD 3 zero5)
      xn un z) :
    WP isa (.block (dblPieces.getD 5 [])) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧
        AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) (fX3 xn un z) (fU xn un z) (fZ3 un z) := by
  obtain hchk := dbl_chk5; have hiv := dbl_iv5
  obtain hL := list4 (dL 4) zero5 (by decide +kernel)
  simp only [dL] at h hL
  generalize leaves (dblLocs.getD 4 []) = L at h hchk hiv hL
  generalize L.getD 0 zero5 = o3, L.getD 1 zero5 = o2, L.getD 2 zero5 = pdd, L.getD 3 zero5 = pbb at h hL
  subst hL
  obtain ⟨e, a3, de, x3, z3, dd, bb⟩ := h
  obtain vu := dbl6u_v0 (Id.run (sqrCore tops o3)) pdd pbb (envOf s₀)
  obtain ee := Raw.sqr e; have de2 := Raw.sqr de
  obtain eel := ee.lo; have eeh := ee.hi; have del := de2.lo; have deh := de2.hi
  obtain ddl := dd.lo; have ddh := dd.hi; have bbl := bb.lo; have bbh := bb.hi
  refine WP.mono (cut_step' hchk hc hB hiv dbl_ov5
    (rs := [Id.run (dbl6u tops (Id.run (sqrCore tops o3)) pdd pbb), o2, o3, Id.run (sqrCore tops o3)]) rfl rfl
    (Nat.le_of_eq rfl) (fun j k hm => absurd hm List.not_mem_nil)) fun s ⟨hc', hk, hE, hS⟩ => ⟨hc', hk, hE, ?_⟩
  obtain w : vI (envOf s) 0 (t5 0) = vI (envOf s₀) 0 (Id.run (dbl6u tops (Id.run (sqrCore tops o3)) pdd pbb)) :=
    hS.val 0 0 (by decide) rfl rfl
  exact ⟨by rw [w, vu]; rng, by rw [w, vu]; rng, by rw [w, vu]; d_ring [ee.d, de2.d, dd.d, bb.d],
    hS.car 1 1 (by decide) rfl rfl z3, hS.car 2 1 (by decide) rfl rfl a3, hS.car 2 3 (by decide) rfl rfl x3,
    hS.raw 3 1 (by decide) rfl rfl (Raw.sqr a3), hS.raw 3 3 (by decide) rfl rfl (Raw.sqr x3)⟩

private theorem flattenSix {α : Type} (a b c d e f : List α) :
    [a, b, c, d, e, f].flatten = a ++ (b ++ (c ++ (d ++ (e ++ f)))) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem dblPieces_flat : dblPieces.flatten = dblPieces.getD 0 [] ++ (dblPieces.getD 1 [] ++ (dblPieces.getD 2 [] ++
    (dblPieces.getD 3 [] ++ (dblPieces.getD 4 [] ++ dblPieces.getD 5 [])))) :=
  flattenSix _ _ _ _ _ _

/-- The doubling: the accumulator's vectors stand for the doubled triple's. -/
theorem dbl_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) :
    WP isa (.block dblPieces.flatten) s₀ fun s =>
      Ctx par s ∧ Kept s₀ s ∧ EnvOK s stB ∧
        AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) (fX3 xn un z) (fU xn un z) (fZ3 un z) := by
  rw [dblPieces_flat, WP.block_append_iff]
  refine WP.mono (dbl_s0 hc hB h) fun s₁ ⟨c₁, k₁, b₁, h₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_s1 c₁ b₁ h₁) fun s₂ ⟨c₂, k₂, b₂, h₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_s2 c₂ b₂ h₂) fun s₃ ⟨c₃, k₃, b₃, h₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_s3 c₃ b₃ h₃) fun s₄ ⟨c₄, k₄, b₄, h₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_s4 c₄ b₄ h₄) fun s₅ ⟨c₅, k₅, b₅, h₅⟩ => ?_
  exact WP.mono (dbl_s5 c₅ b₅ h₅) fun s ⟨c, k, b, h⟩ =>
    ⟨c, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k, b, h⟩

/-- The doubled triple is the textbook's, `(X3, Y3, Z3)`, as `(2² X3, 2³ Y3, 2 Z3)`. -/
theorem dbl_jac {F : Type} [Lean.Grind.CommRing F] (xn un z : F) :
    (4 * fX3 xn un z, 4 * fU xn un z, 2 * fZ3 un z) =
      (4 * (Weierstrass.dblJF (4 * xn) (4 * un) (2 * z)).1, 8 * (Weierstrass.dblJF (4 * xn) (4 * un) (2 * z)).2.1,
        2 * (Weierstrass.dblJF (4 * xn) (4 * un) (2 * z)).2.2) := by
  simp only [Weierstrass.dblJF, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

end VG.Proof.P256.X86_64.Ifma
