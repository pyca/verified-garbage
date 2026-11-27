module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
public import VerifiedGarbage.Impl.Secp256k1.CombTable7

/-! # secp256k1's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def secp256k1d : CombData := ⟨7, Impl.Secp256k1.secp256k1Comb7, Impl.Secp256k1.secp256k1Comb7Start, "VG_SECP256K1_COMB", false⟩

def secp256k1Comb : Cfg := { secp256k1 with comb := some secp256k1d }

/-- `vg_ecdsa_secp256k1_sign_k`. -/
def signSecp256k1Comb : Prog isa := secp256k1Comb.signComb

end VG.Impl.Ecdsa.X86
