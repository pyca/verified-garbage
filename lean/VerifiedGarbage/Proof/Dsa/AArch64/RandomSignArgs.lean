module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
    simp (disch := omega) only [word_writeW_self, random_word_write_other]

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
