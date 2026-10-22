module

public import VerifiedGarbage.Proof.RsaOaep.X86.Base
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaPss.X86.NoSp

/-!
# RSAES-OAEP on x86: the calls write `esp` only through their frames

The calls of the streaming functions (`callInit_noSp`, …), MGF1's mask
(`mgfX_noSp`) and the label's hash (`hashLabel_noSp`), for both functions'
bodies.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (seqs countLoop)

variable (h g : OHash)

theorem callInit_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (callInit G) := noSp_pushCall hG.initSp
theorem callUpd_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (callUpd G) := noSp_pushCall hG.updSp
theorem callFin_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (hG : Proof.Pbkdf2.Stream.X86.HashOK G) :
    NoSp (callFin G) := noSp_pushCall hG.finSp

theorem mgfX_noSp : NoSp (mgfXor g.H) := by
  obtain ⟨p1, p2, -⟩ := g.certs.parts
  have i := callInit_noSp g.H g.ok
  have u := callUpd_noSp g.H g.ok
  have f := callFin_noSp g.H g.ok
  simp only [mgfXor, mgfRound, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_loop
    | exact i | exact u | exact f | exact p1 | exact p2
    | exact NoSp.of_all (by decide +kernel))

theorem hashLabel_noSp {j o : Nat} (hj : NoSp (.block (updLabArgs j) : Prog isa))
    (ho : NoSp (.block (finLabArgs j o) : Prog isa)) : NoSp (hashLabel h.H j o) := by
  have i := callInit_noSp h.H h.ok
  have u := callUpd_noSp h.H h.ok
  have f := callFin_noSp h.H h.ok
  simp only [hashLabel, seqs]
  repeat' (first
    | with_reducible apply noSp_seq
    | exact i | exact u | exact f | exact hj | exact ho
    | exact NoSp.of_all (by decide +kernel))

end VG.Proof.RsaOaep.X86
