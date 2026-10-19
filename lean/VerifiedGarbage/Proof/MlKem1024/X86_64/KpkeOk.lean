module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.Add16
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgMul16
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY16
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.Widen
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.MlKem1024.X86_64.Calls
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-! # ML-KEM-1024 on x86-64: the K-PKE functions, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64

theorem KpkeOk.k1024 : KpkeOk kem1024 where
  kg := ⟨kpkeKg1024Y_correct, kpkeKg1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  enc := ⟨kpkeEnc1024Y_correct, kpkeEnc1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩
  dec := ⟨kpkeDec1024Y_correct, kpkeDec1024Y_ct, nosp_of (by lit_decide), by lit_decide, by lit_decide,
    Code.all_of_allInstrs (by lit_decide)⟩

end VG.Proof.MlKem1024.X86_64
