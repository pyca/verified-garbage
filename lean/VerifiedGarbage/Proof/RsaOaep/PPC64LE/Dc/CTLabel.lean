module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-!
# RSAES-OAEP decryption on PPC64LE: the shared code's base state

Untrusted: everything here is checked by Lean. The arguments of the hash
functions' calls (`UpdArgs`, `FinArgs`) hold for the decoding's `Base` and so
for the shared code's (`UpdArgs.toX`, `FinArgs.toX`), whose base state has
the entry's public data (`pubX_bx`); the label's hash is through its table,
in two runs `hashLabelT_ct` (`Proof/RsaOaep/PPC64LE/CTMgfT.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_li wp_addi wp_mov wp_nil)

section
variable {s : State} (P : PreD s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

theorem UpdArgs.toX {H : Hash} {t : State} {d : Addr} {l : Nat} (A : UpdArgs (SD s) (VD s rc) H (withMem s m) t d l) :
    PreX (bx s m rc) ∧ UpdArgs SX VX H (bx s m rc) t d l := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h3.trans (e _), A.h5, A.h6, A.h7.trans (e _), A.hdc, by rw [← e]; exact A.hd₁,
    by rw [← e]; exact A.hd₂, A.hd₃⟩

theorem FinArgs.toX {t : State} (A : FinArgs (SD s) (VD s rc) (withMem s m) t) :
    PreX (bx s m rc) ∧ FinArgs SX VX (bx s m rc) t := by
  obtain ⟨pX, bX⟩ := Dec.toX P hm rc hrc A.b
  have h13 : SX (bx s m rc) = Sd s := stackArg_bx P hm rc (i := 13) (by decide)
  have e : ∀ o, off (SD s (withMem s m)) o = off (SX (bx s m rc)) o := fun o => by rw [h13]
  exact ⟨pX, pX, bX, A.h3.trans (e _), A.h5.trans (e _), A.h6.trans (e _)⟩

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

end VG.Proof.RsaOaep.PPC64LE.Dec
