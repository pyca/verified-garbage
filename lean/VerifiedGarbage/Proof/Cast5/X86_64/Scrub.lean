module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 on x86-64, without secret residue

The eleven CAST5 functions, each followed by `Impl.Scrub.X86_64.scrub` with
every granule of its stack wiped (`X86_64.RScrub.withScrubAllM`): none for
key expansion and ECB, whose working space is their caller's `scratch`, and
the 240-byte frame of the modes, which no longer zero its scratch words
themselves (`withStackScratchWiped 240 .r9 0`). Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
schedule, the data and the chaining block.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem blocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.blocksAt m₂ p n = Spec.Cast5.blocksAt m₁ p n := by
  simp only [Spec.Cast5.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  apply Vector.ext
  intro j hj
  simp only [Spec.Cast5.blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this, hj])

theorem cbcBlocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.cbcBlocksAt m₂ p n = Spec.Cast5.cbcBlocksAt m₁ p n := by
  simp only [Spec.Cast5.cbcBlocksAt, blocksAt_of0 h hn]

theorem scheduleAt_of (h : ∀ a, Region.Contains ⟨p, 128⟩ a 1 → m₁ a = m₂ a) :
    Spec.Cast5.scheduleAt m₂ p = Spec.Cast5.scheduleAt m₁ p :=
  Proof.Cast5.scheduleAt_congr (agree_le h (Nat.le_refl _))

end

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (X86_64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (X86_64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (X86_64.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub

def expandKeyReg : Registration Spec.Cast5.expandKeyApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.X86_64.expandKey
    stack := 0
    verified := Proof.Cast5.X86_64.expandKey_verified } (expandKeyOut _)

def ecbEncryptReg : Registration Spec.Cast5.ecbEncryptApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.X86_64.ecbEncrypt_verified } (ecbOut .encrypt _)

def ecbDecryptReg : Registration Spec.Cast5.ecbDecryptApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.X86_64.ecbDecrypt_verified } (ecbOut .decrypt _)

def cbcEncryptChainedReg : Registration Spec.Cast5.cbcEncryptChainedApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcEncryptChained
    stack := 240
    verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.X86_64.cbcEncryptChained_framed }
    (cbcEncryptOut _)

def cbcDecryptChainedReg : Registration Spec.Cast5.cbcDecryptChainedApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcDecryptChained
    stack := 240
    verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.X86_64.cbcDecryptChained_framed }
    (cbcDecryptOut _)

def cfbEncryptReg : Registration Spec.Cast5.cfbEncryptApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncrypt
    stack := 240
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.X86_64.cfbEncrypt_framed } (cfbEncryptOut _)

def cfbDecryptReg : Registration Spec.Cast5.cfbDecryptApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecrypt
    stack := 240
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.X86_64.cfbDecrypt_framed } (cfbDecryptOut _)

def cfbEncryptFinalReg : Registration Spec.Cast5.cfbEncryptFinalApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncryptFinal
    stack := 240
    verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.X86_64.cfbEncryptFinal_framed }
    (cfbEncryptFinalOut _)

def cfbDecryptFinalReg : Registration Spec.Cast5.cfbDecryptFinalApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecryptFinal
    stack := 240
    verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.X86_64.cfbDecryptFinal_framed }
    (cfbDecryptFinalOut _)

def ofbReg : Registration Spec.Cast5.ofbApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofb
    stack := 240
    verified := Proof.Cast5.ofb_keyed Proof.Cast5.X86_64.ofb_framed } (ofbOut _)

def ofbFinalReg : Registration Spec.Cast5.ofbFinalApi X86_64.target :=
  withScrubAllM {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofbFinal
    stack := 240
    verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.X86_64.ofbFinal_framed } (ofbFinalOut _)

end VG.Proof.Cast5.X86_64.Scrub
