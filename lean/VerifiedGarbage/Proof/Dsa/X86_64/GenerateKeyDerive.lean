module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.Offset

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

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = keygenDeriveArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveKey v.sq v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        res.getD (List.replicate (s.gpr .rsi).toNat 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveDepth
  have hb := v.stackBound
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) i = keygenDeriveArg s i :=
    (random_call_stackArg hsp _ _ (by omega_arith)).trans (hw i hi)
  refine WP.call_sp_mx v.deriveVerified.1 (SpSafe.of_all v.deriveSp) (by omega_arith)
    (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9) hc hcw
    (fun u hur huw huc hf _ ⟨w, hwm, hwg, hp⟩ hmx => ?_)
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), keygenDeriveArg, hwm, hwg .rax (by decide)] at hp
  rw [show t.mem.writeW (t.gpr .rsp - 8) (t.unknowns 0) = t.callEntry.mem from rfl,
    keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt, keygen_callEntry_nonce h hsp] at hp
  refine ⟨hur, huw, huc, ?_, hp.1, hp.2, hmx⟩
  rw [hsp] at hf
  exact VG.X86_64.Frame.below_mono hf (by omega_arith) (by omega_arith)

end VG.Proof.Dsa.X86_64
