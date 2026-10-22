module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcMask
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcTaint

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the body

The pieces in order (`body_vp`): `EM` (`Proof/RsaPkcs1Enc/X86/PcPieces.lean`),
the call (`PcCall.lean`) and the masks (`PcMask.lean`), and the body keeps
`esp` (`body_noSp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {P : EP}

theorem callArgs_vp : VP (G6 P) (.block callArgs) (G7 P) :=
  VP.taint [.esp] callArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => callArgs_wp h

theorem body_vp (c : Ver.PublicImpl) : VP (S P) (body c.name c.code) (G13 P) :=
  head_vp.seq (psLoop_vp.seq (sep_vp.seq (msgCopy_vp.seq (callArgs_vp.seq ((call_vp c).seq
    (maskArgs_vp.seq ((maskLoop_vp.mono (fun _ _ h => h) fun _ _ h => masked_g10 h).seq
      (wipeArgs_vp.seq (zero_vp.seq ret_vp)))))))))

theorem body_noSp (c : Ver.PublicImpl) : NoSp (body c.name c.code) :=
  noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel))
    (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel))
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_call c.noSp) (.of_all (by decide +kernel)))))))

end VG.Proof.RsaPkcs1Enc.X86.Pc
