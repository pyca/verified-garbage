module

-- separate module: the kernel's evaluation of the stages' checks (about 11 s) is not repeated when `DblOk` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Step

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

end VG.Proof.P256.X86_64.Ifma
