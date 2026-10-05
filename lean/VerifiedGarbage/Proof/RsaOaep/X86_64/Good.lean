import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core

/-!
# RSAES-OAEP on x86-64: the pieces that keep `rsp`, MXCSR and the stack

Each piece but the RSA operation's call is `Good` (`Stack.lean`): its
instructions, and those of the streaming hash functions it calls, never
write `rsp` or load MXCSR, and its calls nest at most two deep.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (seqs round mgfXor xorOut)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)

/-- What the pieces need of a hash function's streaming functions. -/
structure HGood (H : Hash) : Prop where
  init : H.initC.allInstrs okI = true
  upd : H.updC.allInstrs okI = true
  fin : H.finC.allInstrs okI = true
  initD : H.initC.depth ≤ 1
  updD : H.updC.depth ≤ 1
  finD : H.finC.depth ≤ 1

theorem HGood.of {H : Hash} (hH : HashOK H) (K : Callees H) : HGood H :=
  ⟨okI_all_of hH.initSp K.iMx, okI_all_of hH.updSp hH.updMx, okI_all_of hH.finSp hH.finMx, hH.initDepth,
    hH.updDepth, hH.finDepth⟩

variable {H : Hash} (g : HGood H)
include g

theorem hashLabel_good (o : Nat) : Good (hashLabel H.stream o) := by
  have := g.initD; have := g.updD; have := g.finD
  refine ⟨?_, ?_⟩
  · simp only [hashLabel, seqs, Code.allInstrs, Hash.stream, g.init, g.upd, g.fin, Bool.and_true, Bool.true_and]
    rfl
  · simp only [hashLabel, seqs, Code.depth, Hash.stream]; omega

theorem mgfXor_good : Good (mgfXor lay H.stream) := by
  have := g.initD; have := g.updD; have := g.finD
  refine ⟨?_, ?_⟩
  · simp only [mgfXor, round, xorOut, seqs, Code.allInstrs, Hash.stream, g.init, g.upd, g.fin, Bool.and_true,
      Bool.true_and]
    rfl
  · simp only [mgfXor, round, xorOut, seqs, Code.depth, Hash.stream, Impl.Mgf1.X86_64.byteLoop]; omega

end VG.Proof.RsaOaep.X86_64
