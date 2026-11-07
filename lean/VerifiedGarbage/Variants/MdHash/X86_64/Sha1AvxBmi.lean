module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1AvxBmi

/-! # SHA-1 on x86-64 with AVX and BMI -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha1AvxBmi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha1AvxBmi.variant

end VG.Variants.MdHash.X86_64.Sha1AvxBmi
