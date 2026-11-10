module

public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.Verified
public import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Spec.Camellia.Cfb
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Spec.Camellia.Ofb
meta import VerifiedGarbage.Spec.Camellia.OfbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.Verified
meta import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Camellia.X86_64.Lit
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia on x86-64, without secret residue

Key expansion and the ECB, CBC, CFB128 and OFB functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`), as the
frames that keep their working space on the stack already show
(`X86_64.Verified.stackScratchWiped`'s `hpost`).

CTR is not here: `vg_camellia_ctr_final` calls `vg_camellia_ctr` by name with its code
as it is, and the analysis of `vg_camellia_ctr_final` does not succeed.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.Camellia

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) :=
  fun i hi => Proof.Camellia.agree_of h i (by omega)

theorem aesBytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => agree_le h hn i (List.mem_range.mp hi)

theorem cbcBlocksAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 16 ≤ L) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega)

theorem blocksAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 16 ≤ L) :
    blocksAt m₂ p n = blocksAt m₁ p n :=
  Proof.Camellia.blocksAt_congr fun i hi => agree_le h hn i (by omega)

end

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut : PostOut (expandKeyContract X86_64.abi 3216) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86_64.abi d stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln], _ =>
      simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of hb.2 (len_le ln 16)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (cbcEncryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (cbcDecryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86_64.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (cfbEncryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (cfbDecryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86_64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

/-- `vg_camellia_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey

def expandKeyKs : List Nat := keep_for% Spec.Camellia.expandKeyApi.sig 3216 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.expandKeyApi.sig 3216 []) expandKeyCode
      h).any (RScrub.resOkB · 3216 expandKeyKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_expand_key`. -/
def expandKeyReg : Registration Spec.Camellia.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 3216
    verified := Proof.Camellia.X86_64.expandKey_framed } expandKeyOut [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

/-- `vg_camellia_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .encrypt)

def ecbEncryptKs : List Nat := keep_for% Spec.Camellia.ecbEncryptApi.sig 3216 ecbEncryptCode []

theorem ecbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.ecbEncryptApi.sig 3216 []) ecbEncryptCode
      h).any (RScrub.resOkB · 3216 ecbEncryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of ecbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.Camellia.ecbEncryptApi X86_64.target :=
  withScrub {
    code := ecbEncryptCode
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .encrypt } (ecbOut .encrypt _) [] (pubOk_nil _) (some ⟨ecbEncryptKs, ecbEncryptOk⟩)

/-- `vg_camellia_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401 (Impl.Camellia.X86_64.ecb .decrypt)

def ecbDecryptKs : List Nat := keep_for% Spec.Camellia.ecbDecryptApi.sig 3216 ecbDecryptCode []

theorem ecbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.ecbDecryptApi.sig 3216 []) ecbDecryptCode
      h).any (RScrub.resOkB · 3216 ecbDecryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of ecbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.Camellia.ecbDecryptApi X86_64.target :=
  withScrub {
    code := ecbDecryptCode
    stack := 3216
    verified := Proof.Camellia.X86_64.ecb_framed .decrypt } (ecbOut .decrypt _) [] (pubOk_nil _) (some ⟨ecbDecryptKs, ecbDecryptOk⟩)

/-- `vg_camellia_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.Camellia.cbcEncryptChainedApi.sig 3288 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cbcEncryptChainedApi.sig 3288 []) cbcEncryptCode
      h).any (RScrub.resOkB · 3288 cbcEncryptKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.Camellia.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcEncryptChained_framed } (cbcEncryptOut _) [] (pubOk_nil _) (some ⟨cbcEncryptKs, cbcEncryptOk⟩)

/-- `vg_camellia_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained

def cbcDecryptKs : List Nat := keep_for% Spec.Camellia.cbcDecryptChainedApi.sig 3288 cbcDecryptCode []

theorem cbcDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cbcDecryptChainedApi.sig 3288 []) cbcDecryptCode
      h).any (RScrub.resOkB · 3288 cbcDecryptKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cbcDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptReg : Registration Spec.Camellia.cbcDecryptChainedApi X86_64.target :=
  withScrub {
    code := cbcDecryptCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcDecryptChained_framed } (cbcDecryptOut _) [] (pubOk_nil _) (some ⟨cbcDecryptKs, cbcDecryptOk⟩)

/-- `vg_camellia_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.Camellia.cfbEncryptApi.sig 3288 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cfbEncryptApi.sig 3288 []) cfbEncryptCode
      h).any (RScrub.resOkB · 3288 cfbEncryptKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncryptReg : Registration Spec.Camellia.cfbEncryptApi X86_64.target :=
  withScrub {
    code := cfbEncryptCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncrypt_framed } (cfbEncryptOut _) [] (pubOk_nil _) (some ⟨cfbEncryptKs, cfbEncryptOk⟩)

/-- `vg_camellia_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.Camellia.cfbEncryptFinalApi.sig 3288 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cfbEncryptFinalApi.sig 3288 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 3288 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Camellia.cfbEncryptFinalApi X86_64.target :=
  withScrub {
    code := cfbEncryptFinalCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncryptFinal_framed } (cfbEncryptFinalOut _) [] (pubOk_nil _) (some ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩)

/-- `vg_camellia_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt

def cfbDecryptKs : List Nat := keep_for% Spec.Camellia.cfbDecryptApi.sig 3288 cfbDecryptCode []

theorem cfbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cfbDecryptApi.sig 3288 []) cfbDecryptCode
      h).any (RScrub.resOkB · 3288 cfbDecryptKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cfbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecryptReg : Registration Spec.Camellia.cfbDecryptApi X86_64.target :=
  withScrub {
    code := cfbDecryptCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecrypt_framed } (cfbDecryptOut _) [] (pubOk_nil _) (some ⟨cfbDecryptKs, cfbDecryptOk⟩)

/-- `vg_camellia_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.Camellia.cfbDecryptFinalApi.sig 3288 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.cfbDecryptFinalApi.sig 3288 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 3288 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Camellia.cfbDecryptFinalApi X86_64.target :=
  withScrub {
    code := cfbDecryptFinalCode
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecryptFinal_framed } (cfbDecryptFinalOut _) [] (pubOk_nil _) (some ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩)

/-- `vg_camellia_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.Camellia.ofbApi.sig 3288 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.ofbApi.sig 3288 []) ofbCode
      h).any (RScrub.resOkB · 3288 ofbKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_ofb`. -/
def ofbReg : Registration Spec.Camellia.ofbApi X86_64.target :=
  withScrub {
    code := ofbCode
    stack := 3288
    verified := Proof.Camellia.X86_64.ofb_framed } (ofbOut _) [] (pubOk_nil _) (some ⟨ofbKs, ofbOk⟩)

/-- `vg_camellia_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.Camellia.ofbFinalApi.sig 3288 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Camellia.ofbFinalApi.sig 3288 []) ofbFinalCode
      h).any (RScrub.resOkB · 3288 ofbFinalKs (Impl.Scrub.X86_64.chunks 3288)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_camellia_ofb_final`. -/
def ofbFinalReg : Registration Spec.Camellia.ofbFinalApi X86_64.target :=
  withScrub {
    code := ofbFinalCode
    stack := 3288
    verified := Proof.Camellia.X86_64.ofbFinal_framed } (ofbFinalOut _) [] (pubOk_nil _) (some ⟨ofbFinalKs, ofbFinalOk⟩)

end VG.Proof.Camellia.X86_64.Scrub

