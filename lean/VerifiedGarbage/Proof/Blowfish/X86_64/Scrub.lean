module

public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.X86_64.Frame
public import VerifiedGarbage.Proof.Blowfish.X86_64.Verified
public import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Spec.Blowfish.Cbc
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Spec.Blowfish.Ofb
meta import VerifiedGarbage.Spec.Blowfish.OfbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Frame
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Verified
meta import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit

/-!
# Blowfish on x86-64, without secret residue

Key expansion and the ECB, CBC, CFB64 and OFB functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
schedule (`scheduleAt_congr`), the blocks or bytes of the data and the
chaining value.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64.Scrub

open VG.Spec.Blowfish VG.X86_64 VG.X86_64.Scrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem blocksAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n * 8 ≤ L) : blocksAt m₂ p n = blocksAt m₁ p n := by
  have h := agree_of h hn
  simp only [blocksAt, blockAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  congr 1
  funext j
  have : 8 * i + j.val < n * 8 := by have := j.isLt; omega_arith
  rw [VG.Offset.add_add]
  exact h _ this

theorem cbcBlocksAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n * 8 ≤ L) : cbcBlocksAt m₂ p n = cbcBlocksAt m₁ p n := by
  simp only [cbcBlocksAt, blocksAt_of h hn]

theorem bytesAt_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have h := agree_of h hn
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem scheduleAt_of {p : Addr} (h : ∀ a, Region.Contains ⟨p, 4168 * Elem.u8.size⟩ a 1 → m₁ a = m₂ a) :
    scheduleAt m₂ p = scheduleAt m₁ p :=
  scheduleAt_congr (agree_of h (Nat.le_refl _))

theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.le_refl _

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

end

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (expandKeyContract X86_64.abi stack) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ sc = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86_64.abi d stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show blocksAt m₂ dt _ = _
    rw [blocksAt_of hb.2 (len_le ln 8)]
    exact h

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract X86_64.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86_64.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86_64.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract X86_64.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86_64.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

/-! ## The registrations -/

/-- `vg_blowfish_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey

def expandKeyKs : List Nat := keep_for% Spec.Blowfish.expandKeyApi.sig 40 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.expandKeyApi.sig 40 []) expandKeyCode
      h).any (RScrub.resOkB · 40 expandKeyKs (Impl.Scrub.X86_64.chunks 40)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_expand_key`. -/
def expandKeyReg : Registration Spec.Blowfish.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 40
    verified := Proof.Blowfish.X86_64.expandKey_framed } (expandKeyOut _) [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

/-- `vg_blowfish_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.encrypt

def ecbEncryptKs : List Nat := keep_for% Spec.Blowfish.ecbEncryptApi.sig 264 ecbEncryptCode []

theorem ecbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.ecbEncryptApi.sig 264 []) ecbEncryptCode
      h).any (RScrub.resOkB · 264 ecbEncryptKs (Impl.Scrub.X86_64.chunks 264)) = true :=
  RScrub.Analysed.ok_of ecbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.Blowfish.ecbEncryptApi X86_64.target :=
  withScrub {
    code := ecbEncryptCode
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.encrypt_verified } (ecbOut .encrypt _) [] (pubOk_nil _) (some ⟨ecbEncryptKs, ecbEncryptOk⟩)

/-- `vg_blowfish_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.decrypt

def ecbDecryptKs : List Nat := keep_for% Spec.Blowfish.ecbDecryptApi.sig 264 ecbDecryptCode []

theorem ecbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.ecbDecryptApi.sig 264 []) ecbDecryptCode
      h).any (RScrub.resOkB · 264 ecbDecryptKs (Impl.Scrub.X86_64.chunks 264)) = true :=
  RScrub.Analysed.ok_of ecbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.Blowfish.ecbDecryptApi X86_64.target :=
  withScrub {
    code := ecbDecryptCode
    stack := 264
    verified := Proof.Blowfish.X86_64.ecb_framed Proof.Blowfish.X86_64.decrypt_verified } (ecbOut .decrypt _) [] (pubOk_nil _) (some ⟨ecbDecryptKs, ecbDecryptOk⟩)

/-- `vg_blowfish_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.Blowfish.cbcEncryptChainedApi.sig 96 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cbcEncryptChainedApi.sig 96 []) cbcEncryptCode
      h).any (RScrub.resOkB · 96 cbcEncryptKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.Blowfish.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcEncryptChained_framed } (cbcEncryptOut _) [] (pubOk_nil _) (some ⟨cbcEncryptKs, cbcEncryptOk⟩)

/-- `vg_blowfish_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecryptChained

def cbcDecryptKs : List Nat := keep_for% Spec.Blowfish.cbcDecryptChainedApi.sig 96 cbcDecryptCode []

theorem cbcDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cbcDecryptChainedApi.sig 96 []) cbcDecryptCode
      h).any (RScrub.resOkB · 96 cbcDecryptKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cbcDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptReg : Registration Spec.Blowfish.cbcDecryptChainedApi X86_64.target :=
  withScrub {
    code := cbcDecryptCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcDecryptChained_framed } (cbcDecryptOut _) [] (pubOk_nil _) (some ⟨cbcDecryptKs, cbcDecryptOk⟩)

/-- `vg_blowfish_cfb64_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.Blowfish.cfbEncryptApi.sig 96 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cfbEncryptApi.sig 96 []) cfbEncryptCode
      h).any (RScrub.resOkB · 96 cfbEncryptKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncryptReg : Registration Spec.Blowfish.cfbEncryptApi X86_64.target :=
  withScrub {
    code := cfbEncryptCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbEncrypt_framed } (cfbEncryptOut _) [] (pubOk_nil _) (some ⟨cfbEncryptKs, cfbEncryptOk⟩)

/-- `vg_blowfish_cfb64_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecrypt

def cfbDecryptKs : List Nat := keep_for% Spec.Blowfish.cfbDecryptApi.sig 96 cfbDecryptCode []

theorem cfbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cfbDecryptApi.sig 96 []) cfbDecryptCode
      h).any (RScrub.resOkB · 96 cfbDecryptKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cfbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecryptReg : Registration Spec.Blowfish.cfbDecryptApi X86_64.target :=
  withScrub {
    code := cfbDecryptCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbDecrypt_framed } (cfbDecryptOut _) [] (pubOk_nil _) (some ⟨cfbDecryptKs, cfbDecryptOk⟩)

/-- `vg_blowfish_cfb64_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.Blowfish.cfbEncryptFinalApi.sig 96 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cfbEncryptFinalApi.sig 96 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 96 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Blowfish.cfbEncryptFinalApi X86_64.target :=
  withScrub {
    code := cfbEncryptFinalCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbEncryptFinal_framed } (cfbEncryptFinalOut _) [] (pubOk_nil _) (some ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩)

/-- `vg_blowfish_cfb64_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.Blowfish.cfbDecryptFinalApi.sig 96 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.cfbDecryptFinalApi.sig 96 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 96 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Blowfish.cfbDecryptFinalApi X86_64.target :=
  withScrub {
    code := cfbDecryptFinalCode
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbDecryptFinal_framed } (cfbDecryptFinalOut _) [] (pubOk_nil _) (some ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩)

/-- `vg_blowfish_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.Blowfish.ofbApi.sig 96 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.ofbApi.sig 96 []) ofbCode
      h).any (RScrub.resOkB · 96 ofbKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_ofb`. -/
def ofbReg : Registration Spec.Blowfish.ofbApi X86_64.target :=
  withScrub {
    code := ofbCode
    stack := 96
    verified := Proof.Blowfish.X86_64.ofb_framed } (ofbOut _) [] (pubOk_nil _) (some ⟨ofbKs, ofbOk⟩)

/-- `vg_blowfish_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.Blowfish.ofbFinalApi.sig 96 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blowfish.ofbFinalApi.sig 96 []) ofbFinalCode
      h).any (RScrub.resOkB · 96 ofbFinalKs (Impl.Scrub.X86_64.chunks 96)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_blowfish_ofb_final`. -/
def ofbFinalReg : Registration Spec.Blowfish.ofbFinalApi X86_64.target :=
  withScrub {
    code := ofbFinalCode
    stack := 96
    verified := Proof.Blowfish.X86_64.ofbFinal_framed } (ofbFinalOut _) [] (pubOk_nil _) (some ⟨ofbFinalKs, ofbFinalOk⟩)

end VG.Proof.Blowfish.X86_64.Scrub
