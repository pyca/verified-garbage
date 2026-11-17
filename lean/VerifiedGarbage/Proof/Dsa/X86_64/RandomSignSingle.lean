module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI

/-! ### `Dsa.X86_64.RandomSignCallValue`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSignCallResult`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSignCallPre`, which this module and modules that import it used -/

section

/-! Establish the supplied-nonce contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_call_pre {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce) :
    (Spec.Dsa.signContract abi extra).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hE (i : Nat) (hi : i < 5) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ hi).trans (hw i hi)
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide),
    hE 3 (by decide), hE 4 (by decide)]
  simp only [randomCallArg, randomCallRd, randomCallWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_using [hh]
  have hk := randomStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, randomStack_offset_toNat h (by omega_using [])]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 208) := by
    rw [random_nonceBase extra s, randomStack_offset_toNat h (by omega_using [])]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩
      (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_using [hq])
  have sA : Region.Sub ⟨randomBase s, 40⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have sR : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have sK : Region.Sub (below (randomBase s - 8) extra) (below (s.gpr .rsp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega_using [])
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hl]) (by omega_using [hl, hq])
  have dRA : (⟨randomBase s - 8, 8⟩ : Region).Disjoint ⟨randomBase s, 40⟩ := by
    rw [random_callBase extra s, random_frameBase extra s]
    exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hl]) (by omega_using [hl])
  have dKM : (below (randomBase s - 8) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl, hq])
  have dKA : (below (randomBase s - 8) extra).Disjoint ⟨randomBase s, 40⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])
  refine ⟨?_, by omega_using [hl, hk, hR], trivial, trivial, h.outKey, (h.stackOut.sub_left sM).symm,
    h.outDigest, h.outScratch, (h.stackOut.sub_left sA).symm, h.keyScratch,
    h.stackScratch.sub_left sM, h.digestScratch, (h.stackScratch.sub_left sA).symm,
    h.stackOut.sub_left sR, h.stackKey.sub_left sR, dRM, h.stackDigest.sub_left sR,
    h.stackScratch.sub_left sR, ?_, h.outBound, h.keyBound, by omega_using [hl, hq, hk, hN], h.digestBound,
    h.scratchBound, h.lengths, h.outLength, h.keyLength, ?_⟩
  · cases extra <;> simp only <;> omega_using [hR]
  · cases extra with
    | zero => exact dRA
    | succ n => exact ⟨dRA, h.stackOut.sub_left sK, h.stackKey.sub_left sK, dKM,
        h.stackDigest.sub_left sK, h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.randomSignScratchWords at hh
    omega_using [hh]

end VG.Proof.Dsa.X86_64

end

end

/-! The supplied-nonce call's result, with the wrapper's argument mapping. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomCallResult (s t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .r9).toNat (stackArg s 0).toNat
    (Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt t.callEntry.mem (stackArg s 1) (stackArg s 2).toNat)

/-- The signer's validity of the wrapper's key, which the signer's contract
asks of the key it is called with. -/
def RandomValid (S : Signer) (s : State) : Prop :=
  S.valid (randomInput s).pLen (randomInput s).qLen (randomInput s).key = true

/-- Writing the return address leaves the key unchanged. -/
theorem random_callEntry_key {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat := by
  have hsub : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  exact random_callEntry_bytes hsp
    (((h.stackKey.sub_left hsub).symm).sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .r8).isLt

/-- The signer's contract at the wrapper's call boundary, for a key the
signer accepts. -/
theorem random_call_pre_with (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    (signContractWith S.valid abi S.stack).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hpre := random_call_pre h hsp hw hdi hsi hdx hcx h8 h9
  have hE0 : stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) 0 = randomCallArg s 0 :=
    (random_call_stackArg hsp _ _ (by decide)).trans (hw 0 (by decide))
  refine signWith_of_pre hpre ?_
  simp only [hE0, State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (r := .r8) (by decide),
    State.callEntry_gpr _ (r := .rdx) (by decide), State.callEntry_gpr _ (r := .rcx) (by decide),
    h8, hdx, hcx]
  rw [random_callEntry_key h hsp, hkey]
  exact hv

theorem random_signer_outcome (S : Signer) {s t : State} (h : RandomSignABI S.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.call S.name S.code) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (randomCallWr s ++ [below (randomBase s) (S.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat = Spec.Dsa.signStatus (randomCallResult s t) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (randomCallResult s t).getD (List.replicate (s.gpr .rsi).toNat 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := random_call_covers h hrd hwr
  have hpre := random_call_pre_with S h hsp hw hdi hsi hdx hcx h8 h9 hkey hv
  refine WP.mono (random_signer_call S hpre hc hcw)
    fun u ⟨hur, huw, huc, hf, ⟨w, hwm, hwg, hp⟩, hmx⟩ => ?_
  have hE (i : Nat) (hi : i < 5) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ hi).trans (hw i hi)
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp
  sig_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide),
    randomCallArg, hwm, hwg .rax (by decide)] at hp
  refine ⟨hur, huw, huc, ?_, hp.1, hp.2, hmx⟩
  rw [hsp] at hf
  exact VG.X86_64.Frame.below_mono hf (by have := S.depth; omega_using [this]) (by have := S.stackBound; omega_using [this])

end VG.Proof.Dsa.X86_64

end

end

/-! The call instruction's return-address write does not change signing inputs. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_callResult_plain {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    randomCallResult s t = Spec.Dsa.signBytes (s.gpr .r9).toNat (stackArg s 0).toNat
      (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt t.mem (stackArg s 1) (stackArg s 2).toNat) := by
  have sR : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have retain (p : Addr) (n : Nat) (hn : n < 2 ^ 64)
      (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) :
      Spec.Rsa.bytesAt t.callEntry.mem p n = Spec.Rsa.bytesAt t.mem p n :=
    random_callEntry_bytes hsp
      ((hd.sub_left sR).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) hn
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  have hn : (⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ : Region).Disjoint
      ⟨randomBase s - 8, 8⟩ :=
    Offset.disjoint_below _ (by change 8 + 200 + (stackArg s 0).toNat ≤ 2 ^ 64; omega_using [hq])
  unfold randomCallResult
  rw [retain _ _ (s.gpr .r8).isLt h.stackKey, retain _ _ (stackArg s 2).isLt h.stackDigest,
    random_callEntry_bytes hsp (hn.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega_using [])]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignArgsSaved`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSignArgs`, which only this module used -/

section

/-! Set up the supplied-nonce signer's register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSignOutgoing : List (Nat × Nat) :=
  [(Random.oQLen, 0), (Random.oDigest, 8), (Random.oDigestLen, 16),
    (Random.oScratch, 24), (Random.oScratchLen, 32)]

theorem random_signCallArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block RandomSign.callArgs) s fun t =>
      t.gpr .rdi = word s.mem B Random.oOut ∧
      t.gpr .rsi = word s.mem B Random.oOutLen ∧
      t.gpr .rdx = word s.mem B Random.oKey ∧
      t.gpr .rcx = word s.mem B Random.oKeyLen ∧
      t.gpr .r8 = word s.mem B Random.oPLen ∧ t.gpr .r9 = off B Random.oNonce ∧
      t.mem = randomSlotsMem B s.mem randomSignOutgoing ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] s t := by
  unfold RandomSign.callArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u =>
      u.gpr .rdi = word s.mem B Random.oOut ∧ u.gpr .rsi = word s.mem B Random.oOutLen ∧
      u.gpr .rdx = word s.mem B Random.oKey ∧ u.gpr .rcx = word s.mem B Random.oKeyLen ∧
      u.gpr .r8 = word s.mem B Random.oPLen ∧ u.mem = s.mem)
      (by xrun [random_ea_sp, hsp, hs.ld (d := Random.oOut) (by decide),
        hs.ld (d := Random.oOutLen) (by decide), hs.ld (d := Random.oKey) (by decide),
        hs.ld (d := Random.oKeyLen) (by decide), hs.ld (d := Random.oPLen) (by decide)]) rfl)
    fun u ⟨⟨hud, hus, hux, huc, hu8, hum⟩, hku⟩ => ?_
  have husp := (hku.gpr (by decide)).trans hsp
  refine WP.mono (WP.keep [.r9] (Q := fun v => v.gpr .r9 = off B Random.oNonce ∧ v.mem = u.mem)
      (by unfold Random.address; xrun [husp]; rfl) rfl)
    fun v ⟨⟨hv9, hvm⟩, hkv⟩ => ?_
  have hvk := hku.trans hkv
  have hvs := hs.congr hvk.2.2
  refine WP.mono (random_copySlots_ok randomSignOutgoing ((hvk.gpr (by decide)).trans hsp)
      (fun p hp => hvs.ld (by
        simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide))
      (fun p hp => hvs.st (by
        simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ?_
  have hk := hkv.trans hkt
  exact ⟨(hk.gpr (by decide)).trans hud, (hk.gpr (by decide)).trans hus,
    (hk.gpr (by decide)).trans hux, (hk.gpr (by decide)).trans huc,
    (hk.gpr (by decide)).trans hu8, (hkt.gpr (by decide)).trans hv9,
    by rw [htm, hvm, hum], (hku.trans hk).mono (by decide)⟩

theorem random_signOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 40 m (randomSlotsMem B m randomSignOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Each outgoing stack word has the original saved argument value. -/
theorem random_signOutgoing_words (m : Mem) (B : Addr) :
    ∀ p ∈ randomSignOutgoing,
      word (randomSlotsMem B m randomSignOutgoing) B p.2 = word m B p.1 := by
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp only [randomSignOutgoing, randomSlotsMem, Random.oQLen, Random.oDigest,
      Random.oDigestLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

end VG.Proof.Dsa.X86_64

end

end


/-! Map the wrapper's saved arguments to the supplied-nonce signing ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_saved_outgoing {s : State} {m : Mem} (h : RandomSaved s m) :
    ∀ i < 5, word (randomSlotsMem (randomBase s) m randomSignOutgoing) (randomBase s) (8 * i) = randomCallArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact (random_signOutgoing_words m _ (88, 0) (by decide)).trans
      (h (88, stackArg s 0) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (96, 8) (by decide)).trans
      (h (96, stackArg s 1) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (104, 16) (by decide)).trans
      (h (104, stackArg s 2) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (128, 24) (by decide)).trans
      (h (128, stackArg s 5) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (136, 32) (by decide)).trans
      (h (136, stackArg s 6) (by simp [randomSavedValues]))

theorem random_callArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : RandomSaved s t.mem) :
    WP isa (.block RandomSign.callArgs) t fun u =>
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧
      u.gpr .rdx = s.gpr .rcx ∧ u.gpr .rcx = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = off (randomBase s) Random.oNonce ∧
      (∀ i < 5, word u.mem (randomBase s) (8 * i) = randomCallArg s i) ∧
      RandomSaved s u.mem ∧ Outside (randomBase s) 0 40 t.mem u.mem ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (random_signCallArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 40 t.mem u.mem := by rw [hm]; exact random_signOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .rdi) (by simp [randomSavedValues])),
    hsi.trans (hv (48, s.gpr .rsi) (by simp [randomSavedValues])),
    hdx.trans (hv (64, s.gpr .rcx) (by simp [randomSavedValues])),
    hcx.trans (hv (72, s.gpr .r8) (by simp [randomSavedValues])),
    h8.trans (hv (80, s.gpr .r9) (by simp [randomSavedValues])), h9,
    fun i hi => by rw [hm]; exact random_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr hd) (by omega_using [hd'])), hf, hk⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignRetry`, which only this module used -/

section

/-! Update the bounded signing-attempt counter after a supplied-nonce call. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomRetryMem (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) : Mem :=
  if success then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := (m.writeW (off B Random.oStatus) (0 : BitVec 64)).writeW
      (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1))
    if attempts = 1 then m' else m'.writeW (off B Random.oStatus) (4 : BitVec 64)

theorem random_callFinish_ok {s : State} {B : Addr} {attempts : Nat} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (ha : (s.gpr .rax).setWidth 32 = if success then 1 else 0)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa RandomSign.callFinish s fun t =>
      t.mem = randomRetryMem s.mem B success attempts ∧ Keep [.rax] s t := by
  unfold RandomSign.callFinish
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
      u.zf = some (!success)) ?_ rfl) fun u ⟨⟨hum, huz⟩, hku⟩ => ?_)
  · cases success <;> xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide), ha] <;> rfl
  · cases success with
    | true =>
      refine WP.ite false (by simp only [eval, huz]; rfl) (fun h => Bool.noConfusion h)
        (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hum]; rfl, hku⟩
    | false =>
      refine WP.ite true (by simp only [eval, huz]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
      have hus := hs.congr hku.2.2
      have husp := (hku.gpr (by decide)).trans hsp
      have hun : word u.mem B Random.oAttempts = BitVec.ofNat 64 attempts := by
        rw [hum, (writeW_outside _ B _ (by decide)).word (by decide) (by decide), hn]
      have hz : (BitVec.ofNat 64 (attempts - 1) == 0) = decide (attempts = 1) := by
        rw [ofNat64_beq_zero (by omega_using [hbound])]
        exact decide_eq_decide.mpr (by omega_using [hpos])
      refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v =>
          v.mem = u.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
          v.zf = some (decide (attempts = 1))) (by
        xrun [random_ea_sp, husp, hus.ld (d := Random.oAttempts) (by decide),
          hus.st (d := Random.oAttempts) (by decide), hun, ofNat64_pred hpos hbound, hz]) rfl)
        fun v ⟨⟨hvm, hvz⟩, hkv⟩ => ?_)
      by_cases h1 : attempts = 1
      · refine WP.ite false (by simp only [eval, hvz, h1, decide_true]; rfl)
          (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
        exact ⟨by rw [hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1, ite_true],
          (hku.trans hkv).mono (by decide)⟩
      · refine WP.ite true (by simp only [eval, hvz, h1, decide_false]; rfl)
          (fun _ => ?_) (fun h => Bool.noConfusion h)
        refine WP.mono (random_status_ok 4 (hus.congr hkv.2.2)
          ((hkv.gpr (by decide)).trans husp)) fun t ⟨_, htm, hkt⟩ => ?_
        exact ⟨by rw [htm, hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1]; rfl,
          ((hku.trans hkv).trans hkt).mono (by decide)⟩

theorem random_retry_outside (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    Outside B 152 48 m (randomRetryMem m B success attempts) := by
  have step (m : Mem) (d : Nat) (v : BitVec 64) (hd : 152 ≤ d ∧ d + 8 ≤ 200) :
      Outside B 152 48 m (m.writeW (off B d) v) :=
    (writeW_outside _ _ _ (by omega_using [hd])).mono hd.1 hd.2
  cases success with
  | true => exact step _ _ _ (by decide)
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split
    · exact (step _ _ _ (by decide)).trans (step _ _ _ (by decide))
    · exact ((step _ _ _ (by decide)).trans (step _ _ _ (by decide))).trans (step _ _ _ (by decide))

theorem random_retry_status (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oStatus =
      if success then 1 else if attempts = 1 then 0 else 4 := by
  cases success with
  | true => exact word_writeW_self _ _ _ _
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]
    · exact word_writeW_self _ _ _ _

theorem random_retry_attempts (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oAttempts =
      if success then word m B Random.oAttempts else BitVec.ofNat 64 (attempts - 1) := by
  cases success with
  | true => exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · exact word_writeW_self _ _ _ _
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_retry_word (m : Mem) (B : Addr) (success : Bool) (attempts d : Nat)
    (hd : d + 8 ≤ 2 ^ 64) (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hs : d + 8 ≤ 192 ∨ 200 ≤ d) :
    word (randomRetryMem m B success attempts) B d = word m B d := by
  have wa (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oAttempts) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word ha hd
  have ws (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oStatus) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word hs hd
  cases success with
  | true => exact ws _ _
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split <;> simp only [wa, ws]

end VG.Proof.Dsa.X86_64

end

end

/-! One complete supplied-nonce signing step, including arguments and retry state. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomRestore.lean`, which only this module imported.
section

/-! Resume sampling after a signer call that preserves its inputs and private state. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomReadySlots : List Nat := [112, 120, 144, 176, 88, 184, 168, 160]

/-- Each sampling invocation tracks its own exact memory effects. The outer
signing loop separately tracks output and arithmetic-scratch writes. -/
theorem RandomReady.restore {C : RandomContext} {used draws : Nat} {s t : State}
    (h : RandomReady C used draws s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.gpr .rsp = s.gpr .rsp)
    (hwords : ∀ d ∈ randomReadySlots, word t.mem C.B d = word s.mem C.B d)
    (hrand : ∀ i < C.rand.length, t.mem (C.R + BitVec.ofNat 64 i) = s.mem (C.R + BitVec.ofNat 64 i))
    (hq : ∀ i < C.qBytes.length, t.mem (C.Q + BitVec.ofNat 64 i) = s.mem (C.Q + BitVec.ofNat 64 i))
    (hpad : ∀ i < C.qBytes.length - (VG.Proof.Dsa.significant C.qBytes).1,
      t.mem (off C.B (200 + i)) = s.mem (off C.B (200 + i))) :
    RandomReady { C with initialMem := t.mem } used draws t := by
  refine ⟨h.scr.congr hwr, hsp.trans h.sp,
    (hwords _ (by decide)).trans h.rand,
    (hwords _ (by decide)).trans h.randLen,
    (hwords _ (by decide)).trans h.usedWord,
    (hwords _ (by decide)).trans h.width,
    (hwords _ (by decide)).trans h.qLen,
    (hwords _ (by decide)).trans h.mask,
    (hwords _ (by decide)).trans h.q,
    (hwords _ (by decide)).trans h.draws,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.randSrc.rd i hi,
      fun i hi => (hrand i hi).trans (h.randSrc.val i hi), h.randSrc.out⟩,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.qSrc.rd i hi,
      fun i hi => (hq i hi).trans (h.qSrc.val i hi), h.qSrc.out⟩,
    h.usedBound, Frm.refl _ _ _, fun i hi => (hpad i hi).trans (h.padding i hi)⟩

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomSignResume.lean`, which only this module imported.
section

/-! Restore the complete signing-loop invariant after a supplied-nonce call. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem RandomSignRunning.after_signer {extra : Nat} {s t a u : State} {m : Mem}
    {h : RandomSignABI extra s} {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (success : Bool)
    (hargs : Outside (randomBase s) 0 40 t.mem a.mem) (hka : Keep randomVolatile t a)
    (hf : Frame (randomCallWr s ++ [below (randomBase s) (extra + 8)]) a.mem m)
    (hm : u.mem = randomRetryMem m (randomBase s) success fuel)
    (hrd : u.rd = a.rd) (hwr : u.wr = a.wr)
    (hcs : ∀ r ∈ calleeSaved, u.gpr r = a.gpr r)
    (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    RandomSignRunning h hq used (if success then fuel else fuel - 1) u := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  have hargsF := InScr.of_outside hargs (show 0 + 40 ≤ Random.frameBytes by decide)
  have hpostF : InScr (randomBase s) Random.frameBytes m u.mem := by
    rw [hm]
    exact InScr.of_outside (random_retry_outside _ _ _ _) (by decide)
  have hkeyA := hr.key.congrK hargsF hka
  have hdigestA := hr.digest.congrK hargsF hka
  have hrandA := hready.randSrc.congrK hargsF hka
  have hkeyU := random_call_source hkeyA hf hpostF hrd hwr
    (by simpa only [randomInput, bytesAt_length] using h.outKey.symm)
    (by simpa only [randomInput, bytesAt_length] using h.keyScratch)
    (by simpa only [randomInput, bytesAt_length] using h.stackKey)
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (s.gpr .r8).isLt)
  have hdigestU := random_call_source hdigestA hf hpostF hrd hwr
    (by simpa only [randomInput, bytesAt_length] using h.outDigest.symm)
    (by simpa only [randomInput, bytesAt_length] using h.digestScratch)
    (by simpa only [randomInput, bytesAt_length] using h.stackDigest)
    (by simp only [randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 2).isLt)
  have hrandU := random_call_source hrandA hf hpostF hrd hwr
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.outRand.symm)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.randScratch)
    (by simpa only [randomContextOf, randomInput, bytesAt_length] using h.stackRand)
    (by simp only [randomContextOf, randomInput, bytesAt_length]; exact Nat.le_of_lt (stackArg s 4).isLt)
  have hqU : Src u (randomBase s) Random.frameBytes (s.gpr .rcx + s.gpr .r9) (randomQBytes s) := by
    have hx := random_src_take (random_src_drop hkeyU (randomInput s).pLen) (randomInput s).qLen
    simpa only [randomQBytes, randomInput, ofNat_toNat64] using hx
  have hword (d : Nat) (hd : 40 ≤ d) (hb : d + 8 ≤ Random.frameBytes)
      (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hz : d + 8 ≤ 192 ∨ 200 ≤ d) :
      word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hm, random_retry_word _ _ _ _ d (by unfold Random.frameBytes at hb; omega) ha hz,
      random_frame_words (random_call_frameBytes h hf) hb, hargs.word (Or.inr hd) (by unfold Random.frameBytes at hb; omega)]
  have hkeepSp : u.gpr .rsp = t.gpr .rsp :=
    (hcs .rsp (by simp [calleeSaved])).trans (hka.gpr (by decide))
  have hnew := hready.restore (hrd.trans hka.2.1) (hwr.trans hka.2.2) hkeepSp
    (by
      intro d hd
      simp only [randomReadySlots, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hword _ (by decide) (by decide) (by decide) (by decide))
    (fun i hi => (hrandU.val i hi).trans (hready.randSrc.val i hi).symm)
    (fun i hi => (hqU.val i hi).trans (hready.qSrc.val i hi).symm)
    (by
      intro i hi
      have hlen := (randomContextOf h cm hq).qlen
      change u.mem (off (randomBase s) (200 + i)) = t.mem (off (randomBase s) (200 + i))
      rw [hm, random_outside_offset (random_retry_outside _ _ _ _) (by omega) (Or.inr (by omega)),
        random_call_frameBytes h hf _ (by unfold Random.frameBytes; omega),
        random_outside_offset hargs (by omega) (Or.inr (by omega))])
  refine ⟨⟨u.mem, draws, hnew⟩, hr.saved.congr (fun d hd hb => hword d hd (by unfold Random.frameBytes; omega)
    (Or.inl (by omega)) (Or.inl (by omega))), ?_, (hrd.trans hka.2.1).trans hr.rd,
    (hwr.trans hka.2.2).trans hr.wr, hkeyU, hdigestU,
    fun r hc hn => ((hcs r hc).trans (hka.gpr (random_saved_not_volatile hc))).trans (hr.callee r hc hn),
    hmx.trans hr.mxcsr⟩
  rw [hm, random_retry_attempts, random_frame_words (random_call_frameBytes h hf) (by decide),
    hargs.word (by decide) (by decide), hr.attempts]
  cases success <;> rfl

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomSignCallRetry.lean`, which only this module imported.
section

/-! Compose supplied-nonce signing with the bounded-retry update. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_signer_retry (S : Signer) {s t : State} {attempts : Nat} (h : RandomSignABI S.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hn : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64)
    (hkey : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key)
    (hv : RandomValid S s) :
    WP isa (.seq (.call S.name S.code) RandomSign.callFinish) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      (∃ m : Mem,
        Frame (randomCallWr s ++ [below (randomBase s) (S.stack + 8)]) t.mem m ∧
        Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat =
          (randomCallResult s t).getD (List.replicate (s.gpr .rsi).toNat 0) ∧
        u.mem = randomRetryMem m (randomBase s) (randomCallResult s t).isSome attempts) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  refine WP.seq (WP.mono (random_signer_outcome S h hsp hw hdi hsi hdx hcx h8 h9 hrd hwr hkey hv)
    fun u ⟨hur, huw, huc, hf, hstatus, hout, hmx⟩ => ?_)
  have hus : Scr u (randomBase s) Random.frameBytes :=
    (random_alloc_scr h).congr (huw.trans hwr)
  have husp : u.gpr .rsp = randomBase s := (huc .rsp (by simp [calleeSaved])).trans hsp
  have hun : word u.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 attempts :=
    (random_frame_words (random_call_frameBytes h hf) (by decide)).trans hn
  have hra : (u.gpr .rax).setWidth 32 = if (randomCallResult s t).isSome then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hstatus]
    cases randomCallResult s t <;> rfl
  refine WP.mono_mx (by decide) (random_callFinish_ok (randomCallResult s t).isSome hus husp hra hun hpos hbound)
    fun w ⟨hwm, hkw⟩ hmxw => ?_
  exact ⟨hkw.2.1.trans hur, hkw.2.2.trans huw, fun r hr =>
    (hkw.gpr (by simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (huc r hr),
    ⟨u.mem, hf, hout, hwm⟩, by rw [hmxw]; exact hmx⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSingleResult (s : State) (k : Nat) : Option (List Byte) :=
  Spec.Dsa.signBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
    (Spec.Dsa.encodeBE (randomInput s).qLen k) (randomInput s).digest

theorem random_sign_single (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel k : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel < 2 ^ 64)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k) (hv : RandomValid S s) :
    WP isa (.seq (.block RandomSign.callArgs)
      (.seq (.call S.name S.code) RandomSign.callFinish)) t fun u =>
      RandomSignRunning h hq used (if (randomSingleResult s k).isSome then fuel else fuel - 1) u ∧
      word u.mem (randomBase s) Random.oStatus =
        (if (randomSingleResult s k).isSome then 1 else if fuel = 1 then 0 else 4) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        (randomSingleResult s k).getD (List.replicate (s.gpr .rsi).toNat 0) := by
  obtain ⟨cm, draws, hready⟩ := hr.ready
  refine WP.seq (WP.mono_mx (by decide) (random_callArgs_saved hready.scr hready.sp hr.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ hmxa => ?_)
  have hspA := (hka.gpr (by decide)).trans hready.sp
  have hargsF := InScr.of_outside hargs (show 0 + 40 ≤ Random.frameBytes by decide)
  have hkeyA := hr.key.congrK hargsF hka
  have hdigestA := hr.digest.congrK hargsF hka
  have hqbound : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  have hkey : Spec.Rsa.bytesAt a.mem (s.gpr .rcx) (s.gpr .r8).toNat = (randomInput s).key := by
    simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hkeyA
  have hres : randomCallResult s a = randomSingleResult s k := by
    rw [random_callResult_plain h hspA]
    have hdigest : Spec.Rsa.bytesAt a.mem (stackArg s 1) (stackArg s 2).toNat = (randomInput s).digest := by
      simpa only [randomInput, bytesAt_length] using FoldedPublic.src_bytesAt hdigestA
    have hnonceA := (random_outside_bytes hargs
      (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hqbound])
      (Or.inr (show 0 + 40 ≤ Random.oNonce by decide))).trans hnonce
    rw [hkey, hdigest, hnonceA]
    rfl
  have hna : word a.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel :=
    (hargs.word (by decide) (by decide)).trans hr.attempts
  refine WP.mono (random_signer_retry S h hspA hw hdi hsi hdx hcx h8 h9
    (hka.2.1.trans hr.rd) (hka.2.2.trans hr.wr) hna hpos hbound hkey hv)
    fun u ⟨hur, huw, huc, ⟨m, hf, hout, hum⟩, hmx⟩ => ?_
  rw [hres] at hout hum
  have hpostF : InScr (randomBase s) Random.frameBytes m u.mem := by
    rw [hum]; exact InScr.of_outside (random_retry_outside _ _ _ _) (by decide)
  refine ⟨hr.after_signer (randomSingleResult s k).isSome hargs (hka.mono (by decide)) hf hum hur huw huc
    (by rw [hmx, hmxa]), ?_, ?_⟩
  · rw [hum, random_retry_status]
  · exact (random_private_bytes hpostF ((h.stackOut.sub_left (random_frame_sub h)).symm)
      (Nat.le_of_lt (s.gpr .rsi).isLt)).trans hout

end VG.Proof.Dsa.X86_64
