module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyABI
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyEntry

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Key generation's call of key derivation, with the sampled x -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenDeriveOutgoing : List (Nat × Nat) := [(Random.oScratchLen, 0)]

theorem keygen_deriveArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block GenerateKey.deriveArgs) s fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] s t := by
  unfold GenerateKey.deriveArgs
  rw [WP.block_append_iff]
  refine WP.mono (random_copySlot_ok Random.oScratchLen 0 hsp (by decide) (by decide)
    (hs.ld (by decide)) (hs.st (by decide))) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧ t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧ t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing) ?_ rfl rfl rfl)
    fun t ⟨ht, hkt⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
      ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.2, (hku.trans hkt).mono (by decide)⟩
  brun [exec_ldrSp_x', exec_addSp (show Random.oNonce < 4096 by decide), husp, hus.ld (d := Random.oOut) (by decide),
    hus.ld (d := Random.oOutLen) (by decide), hus.ld (d := Random.oKey) (by decide),
    hus.ld (d := Random.oKeyLen) (by decide), hus.ld (d := Random.oPLen) (by decide),
    hus.ld (d := Random.oQLen) (by decide), hus.ld (d := Random.oScratch) (by decide)]
  simp only [hum, keygenDeriveOutgoing, randomSlotsMem]
  simp (disch := decide) only [random_word_write_other]
  trivial

theorem keygen_deriveOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 8 m (randomSlotsMem B m keygenDeriveOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  decide

theorem keygen_deriveOutgoing_words (m : Mem) (B : Addr) :
    word (randomSlotsMem B m keygenDeriveOutgoing) B 0 = word m B Random.oScratchLen := by
  exact word_writeW_self _ _ _ _

theorem keygen_deriveArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.deriveArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = stackArg s 1 ∧
      word u.mem (randomBase s) 0 = stackArg s 2 ∧
      KeygenSaved s u.mem ∧ Outside (randomBase s) 0 8 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (keygen_deriveArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 8 t.mem u.mem := by rw [hm]; exact keygen_deriveOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .x0) (by simp [keygenSavedValues])),
    hsi.trans (hv (48, s.gpr .x1) (by simp [keygenSavedValues])),
    hdx.trans (hv (64, s.gpr .x3) (by simp [keygenSavedValues])),
    hcx.trans (hv (72, s.gpr .x4) (by simp [keygenSavedValues])),
    h8.trans (hv (80, s.gpr .x5) (by simp [keygenSavedValues])), h9,
    h6.trans (hv (88, s.gpr .x6) (by simp [keygenSavedValues])),
    h7.trans (hv (128, stackArg s 1) (by simp [keygenSavedValues])),
    by rw [hm, keygen_deriveOutgoing_words]; exact hv (136, stackArg s 2) (by simp [keygenSavedValues]),
    hv.congr (fun d hd hd' => hf.word (Or.inr (by omega)) (by omega)), hf, hk⟩

def keygenDeriveRd (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩,
    ⟨randomBase s, 8⟩]

def keygenDeriveWr (s : State) : List Region :=
  [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

theorem keygen_derive_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenDeriveRd s ++ keygenDeriveWr s) (t.rd ++ t.wr) ∧ Covers (keygenDeriveWr s) t.wr := by
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
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
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (s.gpr .x6).toNat ≤ 256; omega⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 8 ≤ 256; decide⟩

end VG.Proof.Dsa.AArch64
