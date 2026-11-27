module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.ScrubLocal
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
meta import VerifiedGarbage.Impl.Camellia.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.Spec.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Camellia on x86 (32-bit), without secret residue: what the implementations share

The functions' postconditions read the memory on return only within their
buffers, as on the other targets (`Proof/Camellia/ScrubLocal.lean`); a length
is the low 32 bits of its argument word. `SseEcb.lean`, `SseScrub.lean` and
the AES-NI files use these for the functions as emitted.

`vg_camellia_ctr_final` calls an implementation of `vg_camellia_ctr`'s code
(`CtrFinal.CtrImpl`), which states the doublewords of the stack it zeroes
with it, and that the residue analysis (`X86.rtaint`) finds it then returns
without secret residue (`X86.Scrub.verifiedScrubbedSel`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Spec.Camellia VG.Proof.Camellia.ScrubLocal

/-! ## Postconditions -/

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := len_le x 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86.abi d stack) (ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln], _ =>
      simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of hb.2 (len_le ln 16)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86.abi stack) (ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86.abi stack) (ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) : PostOut (ctrContract X86.abi stack) (ctrSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) : PostOut (ctrFinalContract X86.abi stack) (ctrFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## `vg_camellia_ctr_final` as emitted -/

/-- `Spec.Camellia.ctrFinalApi` as emitted (`Impl.Camellia.X86.Fn.ctrFinal`), calling the
implementation `c` of `vg_camellia_ctr`'s code, meets its contract in constant time and returns
without secret residue. -/
theorem ctrFinal_scrubbed (c : CtrFinal.CtrImpl) :
    VerifiedScrubbed X86.target (Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words)
      (Spec.Camellia.ctrFinalContract X86.abi 1660) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ctrFinalApi) (W := 1660)
    { code := Impl.StackScratch.X86.withStackScratchWiped 60 5 8 (Impl.Camellia.X86.ctrFinal c.name c.code)
      verified := Proof.Camellia.X86.CtrFinal.ctrFinal_framed c
      spSafe := Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe c }
    c.words (ctrFinalOut _) c.wordsOk c.residue

/-- `spSafe` of the function as emitted, which its registration states. -/
theorem ctrFinal_spSafeF (c : CtrFinal.CtrImpl) :
    (Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words).all (fun i => !isa.writesSp i) = true :=
  scrubSel_spSafe (Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe c)

end VG.Proof.Camellia.X86.Scrub
