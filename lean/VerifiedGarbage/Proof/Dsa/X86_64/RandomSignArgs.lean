module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSlots
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

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
