module

public import VerifiedGarbage.Impl.Idea.X86_64.Modes
public import VerifiedGarbage.Impl.Modes.X86_64.CfbFinal

/-!
# IDEA-CFB64 of a message's last piece: x86-64 implementation

`vg_idea_cfb64_encrypt_final(schedule = rdi, iv = rsi, data = rdx, len = rcx, scratch = r8)`
and `vg_idea_cfb64_decrypt_final` with the same arguments (see
`VG.Spec.Idea.cfbEncryptFinalContract`): the modes' final function
(`Impl/Modes/X86_64/CfbFinal.lean`) around IDEA's CFB64 functions, whose
arguments are the same but the number of 8-byte blocks in `rcx`.
-/

@[expose] public section

namespace VG.Impl.Idea.X86_64

open VG.X86_64

/-- Where IDEA's CFB64 functions take their arguments. -/
def finalArgs : Impl.Modes.X86_64.FinalArgs := ⟨[.rdi, .rsi, .rdx, .rcx, .r8], 2, 3, 3⟩

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := Impl.Modes.X86_64.cfbFinal finalArgs cfbEncrypt cfbEncrypt

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := Impl.Modes.X86_64.cfbFinal finalArgs cfbDecrypt cfbEncrypt

end VG.Impl.Idea.X86_64
