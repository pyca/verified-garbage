module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

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
