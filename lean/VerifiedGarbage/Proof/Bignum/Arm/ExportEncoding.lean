module
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.ExportEncoding


@[expose] public section
namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (read_eq_wv wordsAt_two_reads wordsAt_zero_read)
end VG.Proof.Bignum.Arm
