import VerifiedGarbage.Spec.Cast5

/-!
# CAST5: the S-box tables of the scans

The implementations read the S-boxes by scanning a whole table of 256
entries of 16 bytes, entry `i` four S-box values at `i`: `VG_CAST5_S1234`
holds `S4[i], S3[i], S2[i], S1[i]` and `VG_CAST5_S5678` holds `S8[i], S7[i],
S6[i], S5[i]`, as 512 little-endian quadwords.
-/

namespace VG.Impl.Cast5

/-- The 512 quadwords of a table whose entry `i` holds the dwords `a i, b i,
c i, d i`, in that order. -/
def table (a b c d : Byte → Spec.Cast5.Word) : List (BitVec 64) :=
  (List.range 256).flatMap fun i =>
    let x := BitVec.ofNat 8 i
    [b x ++ a x, d x ++ c x]

/-- Entry `i`: `S4[i], S3[i], S2[i], S1[i]`. -/
def s1234 : List (BitVec 64) := table Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1

/-- Entry `i`: `S8[i], S7[i], S6[i], S5[i]`. -/
def s5678 : List (BitVec 64) := table Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5

def s1234Sym : String := "VG_CAST5_S1234"
def s5678Sym : String := "VG_CAST5_S5678"

/-- The tables the ECB functions read. -/
def ecbConsts : List (String × List (BitVec 64)) := [(s1234Sym, s1234)]

/-- The tables key expansion reads. -/
def keyConsts : List (String × List (BitVec 64)) := [(s5678Sym, s5678)]

end VG.Impl.Cast5
