module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.RandomSignArgs`, which only this module used -/

section

/-! Set up the supplied-nonce signer's register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSignOutgoing : List (Nat × Nat) :=
  [(Random.oDigestLen, 0), (Random.oScratch, 8), (Random.oScratchLen, 16)]

theorem random_signOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 40 m (randomSlotsMem B m randomSignOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-- Each outgoing stack word has the original saved argument value. -/
theorem random_signOutgoing_words (m : Mem) (B : Addr) :
    ∀ p ∈ randomSignOutgoing,
      word (randomSlotsMem B m randomSignOutgoing) B p.2 = word m B p.1 := by
  intro p hp
  simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [randomSignOutgoing, randomSlotsMem, Random.oDigestLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := omega_using []) only [word_writeW_self, random_word_write_other]

theorem random_signCallArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block RandomSign.callArgs) s fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oDigest ∧
      t.mem = randomSlotsMem B s.mem randomSignOutgoing ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] s t := by
  unfold RandomSign.callArgs
  rw [WP.block_append_iff]
  refine WP.mono (random_copySlots_ok randomSignOutgoing hsp
    (by intro p hp; simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp;
        rcases hp with rfl | rfl | rfl <;> decide)
    (fun p hp => hs.ld (by
      simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide))
    (fun p hp => hs.st (by
      simp only [randomSignOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide))) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have hw (d : Nat) (hd : 40 ≤ d) (hb : d + 8 ≤ 2 ^ 64) : word u.mem B d = word s.mem B d := by
    rw [hum]
    exact (random_signOutgoing_frame _ _).word (Or.inr hd) hb
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oDigest ∧
      t.mem = u.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hm⟩, hkt⟩ =>
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm.trans hum, (hku.trans hkt).mono (by decide)⟩
  brun [husp, exec_addSp (show Random.oNonce < 4096 by decide),
    exec_ldrSp (show Random.oOut % 8 = 0 ∧ Random.oOut < 32768 by decide),
    hus.ld (d := Random.oOut) (by decide), hw Random.oOut (by decide) (by decide),
    exec_ldrSp (show Random.oOutLen % 8 = 0 ∧ Random.oOutLen < 32768 by decide),
    hus.ld (d := Random.oOutLen) (by decide), hw Random.oOutLen (by decide) (by decide),
    exec_ldrSp (show Random.oKey % 8 = 0 ∧ Random.oKey < 32768 by decide),
    hus.ld (d := Random.oKey) (by decide), hw Random.oKey (by decide) (by decide),
    exec_ldrSp (show Random.oKeyLen % 8 = 0 ∧ Random.oKeyLen < 32768 by decide),
    hus.ld (d := Random.oKeyLen) (by decide), hw Random.oKeyLen (by decide) (by decide),
    exec_ldrSp (show Random.oPLen % 8 = 0 ∧ Random.oPLen < 32768 by decide),
    hus.ld (d := Random.oPLen) (by decide), hw Random.oPLen (by decide) (by decide),
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    hus.ld (d := Random.oQLen) (by decide), hw Random.oQLen (by decide) (by decide),
    exec_ldrSp (show Random.oDigest % 8 = 0 ∧ Random.oDigest < 32768 by decide),
    hus.ld (d := Random.oDigest) (by decide), hw Random.oDigest (by decide) (by decide)]

end VG.Proof.Dsa.AArch64

end

end


/-! Map the wrapper's saved arguments to the supplied-nonce signing ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_saved_outgoing {s : State} {m : Mem} (h : RandomSaved s m) :
    ∀ i < 3, word (randomSlotsMem (randomBase s) m randomSignOutgoing) (randomBase s) (8 * i) = randomCallArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
  rcases cases with rfl | rfl | rfl
  · exact (random_signOutgoing_words m _ (104, 0) (by decide)).trans
      (h (104, stackArg s 0) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (128, 8) (by decide)).trans
      (h (128, stackArg s 3) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (136, 16) (by decide)).trans
      (h (136, stackArg s 4) (by simp [randomSavedValues]))

theorem random_callArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : RandomSaved s t.mem) :
    WP isa (.block RandomSign.callArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = s.gpr .x7 ∧
      (∀ i < 3, word u.mem (randomBase s) (8 * i) = randomCallArg s i) ∧
      RandomSaved s u.mem ∧ Outside (randomBase s) 0 40 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (random_signCallArgs_ok hs hsp) fun u ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 40 t.mem u.mem := by rw [hm]; exact random_signOutgoing_frame _ _
  exact ⟨h0.trans (hv (40, s.gpr .x0) (by simp [randomSavedValues])),
    h1.trans (hv (48, s.gpr .x1) (by simp [randomSavedValues])),
    h2.trans (hv (64, s.gpr .x3) (by simp [randomSavedValues])),
    h3.trans (hv (72, s.gpr .x4) (by simp [randomSavedValues])),
    h4.trans (hv (80, s.gpr .x5) (by simp [randomSavedValues])), h5,
    h6.trans (hv (88, s.gpr .x6) (by simp [randomSavedValues])),
    h7.trans (hv (96, s.gpr .x7) (by simp [randomSavedValues])),
    fun i hi => by rw [hm]; exact random_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr hd) (by omega_using [hd'])), hf, hk⟩

end VG.Proof.Dsa.AArch64
