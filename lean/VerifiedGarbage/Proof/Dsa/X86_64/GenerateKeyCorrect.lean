module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeySample
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishResult
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedVerified
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! ### `Dsa.X86_64.GenerateKeyBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeySampled`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyGenerate`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.GenerateKeyDerive`, which this module and modules that import it used -/

section

/-! # Key generation's call of key derivation, with the sampled x -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenDeriveOutgoing : List (Nat × Nat) :=
  [(Random.oQLen, 0), (Random.oScratch, 8), (Random.oScratchLen, 16)]

theorem keygen_deriveArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B) :
    WP isa (.block GenerateKey.deriveArgs) s fun t =>
      t.gpr .rdi = word s.mem B Random.oOut ∧
      t.gpr .rsi = word s.mem B Random.oOutLen ∧
      t.gpr .rdx = word s.mem B Random.oKey ∧
      t.gpr .rcx = word s.mem B Random.oKeyLen ∧
      t.gpr .r8 = word s.mem B Random.oPLen ∧ t.gpr .r9 = off B Random.oNonce ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] s t := by
  unfold GenerateKey.deriveArgs
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
  refine WP.mono (random_copySlots_ok keygenDeriveOutgoing ((hvk.gpr (by decide)).trans hsp)
      (fun p hp => hvs.ld (by
        simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> decide))
      (fun p hp => hvs.st (by
        simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> decide)))
    fun t ⟨htm, hkt⟩ => ?_
  have hk := hkv.trans hkt
  exact ⟨(hk.gpr (by decide)).trans hud, (hk.gpr (by decide)).trans hus,
    (hk.gpr (by decide)).trans hux, (hk.gpr (by decide)).trans huc,
    (hk.gpr (by decide)).trans hu8, (hkt.gpr (by decide)).trans hv9,
    by rw [htm, hvm, hum], (hku.trans hk).mono (by decide)⟩

theorem keygen_deriveOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 24 m (randomSlotsMem B m keygenDeriveOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem keygen_deriveOutgoing_words (m : Mem) (B : Addr) :
    ∀ p ∈ keygenDeriveOutgoing,
      word (randomSlotsMem B m keygenDeriveOutgoing) B p.2 = word m B p.1 := by
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [keygenDeriveOutgoing, randomSlotsMem, Random.oQLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := decide) only [word_writeW_self, random_word_write_other]

def keygenDeriveArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => stackArg s 0
  | 1 => stackArg s 3
  | _ => stackArg s 4

theorem keygen_saved_outgoing {s : State} {m : Mem} (h : KeygenSaved s m) :
    ∀ i < 3, word (randomSlotsMem (randomBase s) m keygenDeriveOutgoing) (randomBase s) (8 * i) =
      keygenDeriveArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_arith
  rcases cases with rfl | rfl | rfl
  · exact (keygen_deriveOutgoing_words m _ (88, 0) (by decide)).trans
      (h (88, stackArg s 0) (by simp [keygenSavedValues]))
  · exact (keygen_deriveOutgoing_words m _ (128, 8) (by decide)).trans
      (h (128, stackArg s 3) (by simp [keygenSavedValues]))
  · exact (keygen_deriveOutgoing_words m _ (136, 16) (by decide)).trans
      (h (136, stackArg s 4) (by simp [keygenSavedValues]))

theorem keygen_deriveArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.deriveArgs) t fun u =>
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧
      u.gpr .rdx = s.gpr .rcx ∧ u.gpr .rcx = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = off (randomBase s) Random.oNonce ∧
      (∀ i < 3, word u.mem (randomBase s) (8 * i) = keygenDeriveArg s i) ∧
      KeygenSaved s u.mem ∧ Outside (randomBase s) 0 24 t.mem u.mem ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (keygen_deriveArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 24 t.mem u.mem := by rw [hm]; exact keygen_deriveOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .rdi) (by simp [keygenSavedValues])),
    hsi.trans (hv (48, s.gpr .rsi) (by simp [keygenSavedValues])),
    hdx.trans (hv (64, s.gpr .rcx) (by simp [keygenSavedValues])),
    hcx.trans (hv (72, s.gpr .r8) (by simp [keygenSavedValues])),
    h8.trans (hv (80, s.gpr .r9) (by simp [keygenSavedValues])), h9,
    fun i hi => by rw [hm]; exact keygen_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr (by omega_arith)) (by omega_arith)), hf, hk⟩

def keygenDeriveRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩,
    ⟨randomBase s, 24⟩]

def keygenDeriveWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]

theorem keygen_derive_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenDeriveRd s ++ keygenDeriveWr s) (t.rd ++ t.wr) ∧ Covers (keygenDeriveWr s) t.wr := by
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_arith
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (keygenDeriveWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, ho, 0, zero _, by simp⟩
    · exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [keygenDeriveRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (stackArg s 0).toNat ≤ 248; omega_arith⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 24 ≤ 248; decide⟩

theorem keygen_derive_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce) :
    (Spec.Dsa.deriveKeyContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw i hi)
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide)]
  simp only [keygenDeriveArg, keygenDeriveRd, keygenDeriveWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_arith
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 208) := by
    rw [random_nonceBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩
      (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_arith)
  have sA : Region.Sub ⟨randomBase s, 24⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_arith)
  have sR := keygen_ret_sub h
  have sK := keygen_callee_sub h
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have dRA : (⟨randomBase s - 8, 8⟩ : Region).Disjoint ⟨randomBase s, 24⟩ := by
    rw [random_callBase extra s, random_frameBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have dKM : (below (randomBase s - 8) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  have dKA : (below (randomBase s - 8) extra).Disjoint ⟨randomBase s, 24⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  refine ⟨?_, by omega_arith, trivial, trivial, h.outParams, (h.stackOut.sub_left sM).symm,
    h.outScratch, (h.stackOut.sub_left sA).symm, h.paramsScratch,
    h.stackScratch.sub_left sM, (h.stackScratch.sub_left sA).symm,
    h.stackOut.sub_left sR, h.stackParams.sub_left sR, dRM, h.stackScratch.sub_left sR,
    ?_, h.outBound, h.paramsBound, by omega_arith, h.scratchBound, h.lengths, h.outLength, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_arith
  · cases extra with
    | zero => exact dRA
    | succ n => exact ⟨dRA, h.stackOut.sub_left sK, h.stackParams.sub_left sK, dKM,
        h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_arith

/-- The sampled x, as the callee reads it. -/
theorem keygen_callEntry_nonce {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_arith
  have hk := keygenStackBase_toNat h
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  exact random_callEntry_bytes hsp (dRM.symm.sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by omega_arith)

/-- The checked derivation's contract at key generation's call, once the
domain check has passed. -/
theorem keygen_derive_checked_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  refine deriveChecked_of_pre (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9) ?_
  have hE0 : stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = keygenDeriveArg s 0 :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw 0 (by decide))
  simp only [hE0, State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (r := .r8) (by decide),
    State.callEntry_gpr _ (r := .rdx) (by decide), State.callEntry_gpr _ (r := .rcx) (by decide),
    h8, hdx, hcx, keygenDeriveArg]
  rw [keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt, hparams]
  exact hc

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        res.getD (List.replicate (s.gpr .rsi).toNat 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc', hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveCheckedDepth
  have hb := v.stackBound
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw i hi)
  refine WP.call_sp_mx v.deriveCheckedVerified.1 (SpSafe.of_all v.deriveCheckedSp) (by omega_arith)
    (keygen_derive_checked_pre h hsp hw hdi hsi hdx hcx h8 h9 hparams hc) hc' hcw
    (fun u hur huw huc hf _ ⟨w, hwm, hwg, hp⟩ hmx => ?_)
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), keygenDeriveArg, hwm, hwg .rax (by decide)] at hp
  rw [show t.mem.writeW (t.gpr .rsp - 8) (t.unknowns 0) = t.callEntry.mem from rfl,
    keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt, keygen_callEntry_nonce h hsp] at hp
  refine ⟨hur, huw, huc, ?_, hp.1, hp.2, hmx⟩
  rw [hsp] at hf
  exact VG.X86_64.Frame.below_mono hf (by omega_arith) (by omega_arith)

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)]) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧ u.zf = some (t.gpr .rax == 1) ∧
      Keep [.rax] t u := by
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .rax) ∧
    u.zf = some (t.gpr .rax == 1)) ?_ rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]
  exact sub_beq_zero _ _

theorem keygen_keepStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.gpr .rsp = B) :
    WP isa (.block GenerateKey.keepStatus) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64) ∧
      Keep [.rax] t u := by
  refine WP.keep [.rax] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) ((t.gpr .rax).setWidth 32 |>.setWidth 64)) ?_ rfl
  unfold GenerateKey.keepStatus
  xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega_using [hd'])) (by omega_using [hd'])) hk (by rw [hmx])

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 24 t.mem u.mem)
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr = t.mxcsr) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega_using [hd])) (by omega_arith)) hk
    (by rw [hmx])

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
  simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .rsi).toNat 0))

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k)
      KeygenState h used u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat = res.getD (List.replicate (s.gpr .rsi).toNat 0) := by
  refine WP.seq (WP.mono_mx (by decide) (keygen_deriveArgs_saved ht.scr ht.sp ht.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hka⟩ hmxa => ?_)
  have ha := ht.of_outgoing hargs (hka.mono (by decide)) hmxa
  have hnA : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat k := by
    have hq : (stackArg s 0).toNat ≤ 32 := by
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega_using [hl]
    exact (random_outside_bytes hargs (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega_using [hq]) (Or.inr (show 0 + 24 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 ha.rd ha.wr (keygen_bytes_params ha) hc)
    fun b ⟨hbr, hbw, hbc, hf, hst, hout, hmxb⟩ => ?_)
  rw [keygen_bytes_params ha, hnA] at hst hout
  have hoF : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackOut.sub_left (keygen_frame_sub h)).symm
  have hsF : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hb, _⟩ := ha.after_call (wr := keygenDeriveWr s)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hoF
      · exact hsF)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outParams
      · exact h.paramsScratch.symm)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outRand
      · exact h.randScratch.symm)
    hf hbr hbw hbc hmxb
  refine WP.mono_mx (by decide) (keygen_keepStatus_ok hb.scr hb.sp) fun u ⟨hum, hku⟩ hmxu => ?_
  refine ⟨hb.write_status hum (hku.mono (by decide)) hmxu, ?_, ?_⟩
  · rw [hum, word_writeW_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using []), ← BitVec.toNat_setWidth, hst]
    exact (Nat.mod_eq_of_lt (by unfold Spec.Dsa.signStatus; split <;> decide)).symm
  · rw [hum, random_writeW_bytes _ (hoF.sep (Region.contains_self _ _)
      (Offset.contains_base (randomBase s) (d := Random.oStatus) (n := 8) (by decide) (by decide)))
      (s.gpr .rsi).isLt]
    exact hout

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation after an accepted domain: the sampler, then the derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

/-- The sampler's state once prepared and past the test of its status. -/
theorem keygen_prepared {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) :
    WP isa (.seq Random.prepare (.block [.alu .cmp .rax (.imm 0)])) t fun b =>
      b.zf = some false ∧ (∃ draws, RandomReady (keygenContextOf h t.mem hq) 0 draws b) ∧
      Keep randomVolatile t b ∧ b.mxcsr = t.mxcsr := by
  refine WP.seq (WP.mono (keygen_prepare ht hQ hq) fun a ⟨hax, ⟨draws, hra⟩, hka, hmxa⟩ => ?_)
  refine WP.mono_mx (by decide) (random_sign_test_zero (t := a)) fun b ⟨⟨hbm, hbz⟩, hkb⟩ hmxb => ?_
  have hkb' : Keep randomVolatile a b := hkb.mono (by decide)
  exact ⟨by rw [hbz, hax]; rfl, ⟨draws, hra.congr hbm hkb⟩, (hka.trans hkb').mono (by decide),
    hmxb.trans hmxa⟩

/-- The draw and its status stored: the frame state, the flag for success, and x. -/
theorem keygen_sampled {extra : Nat} {s t b : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {draws : Nat} (ht : KeygenState h 0 t)
    (hrb : RandomReady (keygenContextOf h t.mem hq) 0 draws b) (hkb : Keep randomVolatile t b)
    (hmxb : b.mxcsr = t.mxcsr) :
    WP isa (.seq Random.sample (.block [.store (Random.sp Random.oStatus) .rax, .alu .cmp .rax (.imm 1)])) b
      fun d =>
        KeygenState h (keygenDraw s).used d ∧
        d.zf = some (BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) == 1) ∧
        word d.mem (randomBase s) Random.oStatus =
          BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) ∧
        (∀ k, (keygenDraw s).scalar = some k →
          Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
            Spec.Dsa.encodeBE (stackArg s 0).toNat k) := by
  have hd : randomRemaining (keygenContextOf h t.mem hq) 0 128 = keygenDraw s := by
    unfold randomRemaining; rfl
  refine WP.seq (WP.mono_mx (by decide) (random_sample_encoded hq hrb)
    fun c ⟨hcax, _, _, hnonce, _, ⟨draws', hrc⟩, hkc⟩ hmxc => ?_)
  rw [hd, Nat.zero_add] at hrc
  rw [hd] at hcax hnonce
  have hkc' : Keep randomVolatile b c := hkc.mono (by decide)
  have hkt : Keep randomVolatile t c := (hkb.trans hkc').mono (by decide)
  have hsc : KeygenState h (keygenDraw s).used c :=
    ht.of_ready hrc hkt (by rw [hmxc, hmxb])
  refine WP.mono_mx (by decide) (keygen_storeStatus_ok hsc.scr hsc.sp) fun d ⟨hdm, hdz, hkd⟩ hmxd => ?_
  have hsd := hsc.write_status hdm (hkd.mono (by decide)) hmxd
  rw [hcax] at hdm hdz
  refine ⟨hsd, hdz, by rw [hdm, word_writeW_self], fun k hk => ?_⟩
  have hn := hnonce k hk
  simp only [keygenContextOf, keygen_q_length h] at hn
  have hql : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  rw [hdm]
  exact (random_outside_bytes (writeW_outside _ _ _ (by decide))
    (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hql])
    (Or.inr (by decide))).trans hn

theorem keygen_generate (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hc : keygenChecked s = true) :
    WP isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.sq v.mul)) t
      (KeygenGenerated h) := by
  have hq := keygen_q_valid h hc
  have hres := keygen_result_checked h hc
  unfold GenerateKey.generate
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_prepared ht hQ hq) fun b ⟨hbz, ⟨draws, hrb⟩, hkb, hmxb⟩ => ?_)
  refine WP.ite false (by simp only [eval, hbz]) (fun he => Bool.noConfusion he) fun _ => ?_
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_sampled ht hrb hkb hmxb) fun d ⟨hsd, hdz, hdw, hnd⟩ => ?_)
  have hlt : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (keygen_sampleStatus_le _) (by decide)
  cases hx : (keygenDraw s).scalar with
  | none =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]; split <;> decide
    refine WP.ite false (by
      simp only [eval, hdz]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      apply hs1
      have := congrArg BitVec.toNat he
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this)
      (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.block_nil ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hsd, hdw, fun h1 => absurd h1 hs1⟩
  | some k =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
    rw [hs1] at hdz
    refine WP.ite true (by simp only [eval, hdz]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (keygen_derive_step v hsd (hnd k hx) hc) fun u ⟨hu, hw, hb⟩ => ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hu, hw, fun _ => hb⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.GenerateKeyFinish`, which only this module used -/

section

/-! # Key generation's finish: the status, the key or zeros, and the draws used -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure KeygenBodyPost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem keygen_finish_result {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    {result : Spec.Dsa.GenerateKeyResult} (hr : KeygenState h result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      result.key.getD (List.replicate (s.gpr .rsi).toNat 0))
    (hbound : result.status ≤ 2) (hkey : result.status ≠ 1 → result.key = none) :
    WP isa RandomSign.finish t (KeygenBodyPost s result) := by
  have houtlen : 0 < (s.gpr .rsi).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .rdx :=
    hr.saved (56, s.gpr .rdx) (by simp [keygenSavedValues])
  have hframeOut := h.stackOut.sub_left (keygen_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (keygen_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .rdi) (s.gpr .rsi).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono_mx (by decide) (random_finish_ok (B := randomBase s) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat)
    hr.scr hr.sp
    (hr.saved (40, s.gpr .rdi) (by simp [keygenSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .rsi) (by simp [keygenSavedValues]))
    houtlen (s.gpr .rsi).isLt
    (fun j hj => ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .rsi).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ hmx => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .rdx := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨(hk.gpr (by decide)).trans hr.sp, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc hn => (hkv.gpr (random_saved_not_volatile hc)).trans (hr.callee r hc hn),
    by rw [hmx]; exact hr.mxcsr, ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .rsi).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hkey hs]
      exact keygen_bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- Key generation's status is at most 2, and only success returns a key. -/
theorem keygen_result_bounds {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenResult s).status ≤ 2 ∧ ((keygenResult s).status ≠ 1 → (keygenResult s).key = none) := by
  by_cases hc : keygenChecked s = true
  · rw [keygen_result_checked h hc]
    cases hx : (keygenDraw s).scalar with
    | none => exact ⟨keygen_sampleStatus_le _, fun _ => rfl⟩
    | some k =>
      dsimp only
      unfold Spec.Dsa.signStatus
      cases hd : Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k) with
      | none => exact ⟨by decide, fun _ => rfl⟩
      | some key => exact ⟨by simp, fun hn => absurd (by simp) hn⟩
  · have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
      simp only [keygenInput, bytesAt_length]; exact h.paramsLength
    unfold keygenResult
    rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
      h.lengths hpl]
    simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
      = false from Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, fun _ => trivial⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Key generation's body: entry, the domain check, generation, the finish -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_test_check {t : State} :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (((t.gpr .rax).setWidth 32).toNat == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  rw [sub_beq_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  have hz : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  rw [hz]
  constructor
  · intro he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_setWidth] at hn ⊢
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 32 ≤ 2 ^ 64))] at hn
    exact hn
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, he, Nat.zero_mod]
    rfl

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveChecked v.sq v.mul))
      (allocState Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (keygen_test_check (t := u)) fun w ⟨⟨hwm, hwz⟩, hkw⟩ hmxw => ?_)
  have hsw : KeygenState h 0 w :=
    hu.of_frame (by rw [hwm]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hwm]) (hkw.mono (by decide))
      (by rw [hmxw])
  have hword (d : Nat) (hd : d + 8 ≤ Random.frameBytes) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm]; exact hw d hd
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp only [eval, hwz, hax]; rfl) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hsw (by rw [hword _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp only [eval, hwz, hax]; rfl) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hsw (by rw [hword _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's functional correctness against its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)).all (fun i => !isa.writesSp i) = true := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.all, Bool.and_eq_true]
  repeat' constructor
  all_goals first | with_reducible exact v.parametersSp | with_reducible exact v.deriveCheckedSp | decide

theorem keygen_depth (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)).x86_64Depth ≤ v.stack + 256 := by
  simp only [GenerateKey.code, GenerateKey.body, GenerateKey.generate, Code.x86_64Depth,
    show Random.prepare.x86_64Depth = 0 from rfl,
    show Random.sample.x86_64Depth = 0 from rfl,
    show RandomSign.finish.x86_64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  have hm := Nat.max_le.mpr ⟨Nat.add_le_add_right v.parametersDepth 8, Nat.add_le_add_right v.deriveCheckedDepth 8⟩
  exact Nat.add_le_add_right hm 248

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
      (Generate.deriveChecked v.sq v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht => ⟨ht.sp, ht.wr, fun m _ fm => ?_⟩
  -- The frame's bytes, once released, hold anything: the key and `used` lie apart from them.
  have hl := h.stackLower
  have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩
      (below (s.gpr .rsp) (v.stack + 256)) :=
    Offset.sub_below _ (by unfold Random.frameBytes; omega_using []) (by unfold Random.frameBytes; omega_using [])
  have sep : ∀ {B : Region}, (below (s.gpr .rsp) (v.stack + 256)).Disjoint B →
      ∀ q ∈ [(⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩ : Region)], B.Disjoint q :=
    fun hB q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact fun x h₁ h₂ => hB x (hR x h₂) h₁
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ?_, ?_, ?_, ht.mxcsr⟩
  · show Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = _
    rw [Proof.Rsa.rsa_bytes_frame fm (s.gpr .rsi).isLt (sep h.stackOut)]
    exact ht.output
  · show m.readW (s.gpr .rdx) 64 = _
    rw [fm.readW (r := ⟨s.gpr .rdx, 8⟩) (Region.contains_self _ _) (sep h.stackUsed) (by decide)]
    exact ht.used
  intro r hr
  by_cases he : r = .rsp
  · subst r
    change t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes = s.gpr .rsp
    rw [ht.sp, randomBase, BitVec.sub_add_cancel]
  · change (t.setReg .rsp (t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes)).gpr r = _
    simp only [State.setReg, ite_eq_right he]
    exact ht.callee r hr he

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, stackArgs_five']
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.sq v.mul) (Generate.deriveChecked v.sq v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  refine ⟨trace, t, he, ⟨hp.callee, ?_, hp.mxcsr⟩, keygen_shared_post h hp⟩
  have hd := keygen_depth v
  have hb := v.stackBound
  have hf := Exec.stackFrame (SpSafe.of_all (keygen_sp v)) he (by omega_using [hd, hb])
  have hfb := VG.X86_64.Frame.below_mono hf hd (by omega_using [hb])
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.retOut
    · exact h.retUsed
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by omega_using [hb])

end VG.Proof.Dsa.X86_64
