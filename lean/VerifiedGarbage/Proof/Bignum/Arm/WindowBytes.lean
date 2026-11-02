module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowBit
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteLoad
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # The exponent's bytes in the windowed exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_str wp_mov op2_imm)

/-- The exponent's pointer and count are kept. -/
def KeepsPtr (base : BitVec 32) (m m' : Mem) : Prop :=
  ∀ e ∈ [128, 132], m'.readW (off (State.addr base) e) 32 = m.readW (off (State.addr base) e) 32

theorem KeepsPtr.refl (base : BitVec 32) (m : Mem) : KeepsPtr base m m := fun _ _ => rfl

theorem KeepsPtr.trans {base : BitVec 32} {m₁ m₂ m₃ : Mem} (h₁ : KeepsPtr base m₁ m₂)
    (h₂ : KeepsPtr base m₂ m₃) : KeepsPtr base m₁ m₃ := fun e he => (h₂ e he).trans (h₁ e he)

theorem KeepsExp.ptr {base : BitVec 32} {m m' : Mem} (h : KeepsExp base m m') : KeepsPtr base m m' :=
  fun e he => h e (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; omega)

theorem KeepsPtr.of_write (m : Mem) (base : BitVec 32) {d : Nat} (v : BitVec 32) (hd : 136 ≤ d)
    (hd' : d + 4 ≤ 256) : KeepsPtr base m (m.writeW (off (State.addr base) d) v) := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have outside := writeW32_outside m (State.addr base) (d := d) v (by omega)
  exact outside_read32 outside (by omega) (by omega)

/-- The byte and the count of its bits, two header writes. -/
theorem windowByteSave_ok (s : State) {base : BitVec 32} {len w : Nat} {v : BitVec 32}
    (h : ArithmeticReady base len w s) (value : s.gpr .r1 = v) :
    WP isa (.block expByteSave) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 200) v).writeW (off (State.addr base) 192)
        (BitVec.ofNat 32 8) ∧ Rest [.r1] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have addr (d : Nat) (hd : d ≤ 252) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold expByteSave
  refine wp_str (a := off (State.addr base) 200) (by decide) (addr 200 (by decide))
    (h.workspace.write (by omega)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun z b => ?_
  refine wp_str (a := off (State.addr base) 192) (by decide)
    (by rw [b.other .r0 (by decide), a.gpr]; exact addr 192 (by decide))
    (by rw [b.wr, a.wr]; exact h.workspace.write (by omega)) fun t c => WP.block_nil ?_
  refine ⟨?_, (a.rest _).trans ((b.rest (by simp)).trans (c.rest _))⟩
  rw [c.mem, b.mem, a.mem, b.gpr, value]
  rfl

/-- The next exponent byte `v`: the state kept, the byte at 200 and its 8 bits
at 192. -/
theorem windowByteHead_ok (s : State) {base ep : BitVec 32} {len w M x A p q : Nat}
    (h : WinState base len w M x A p q s)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa expByteHead s fun t => WinState base len w M x A p q t ∧
      t.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (s.mem (State.addr ep)).toNat ∧
      t.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 8 ∧
      KeepsPtr base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [expByteHead, WP.block_append_iff]
  refine WP.mono (expByteLoad_ok s h.power.ready.workspace (by omega) h.power.ready.ptr pointer read) ?_
  rintro u ⟨byte, mem, rest⟩
  have readyU := h.power.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.power.ready.ptr)
  refine WP.mono (windowByteSave_ok u readyU (v := BitVec.ofNat 32 (s.mem (State.addr ep)).toNat)
    (by rw [byte, BitVec.ofNat_toNat])) ?_
  rintro t ⟨memT, restT⟩
  rw [mem] at memT
  have ctl : CtlOnly base s.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have restST : Rest roundClobbers s t := (rest_round rest).trans (rest_round restT)
  obtain ⟨powerT, frameT⟩ := h.power.after_ctl ctl restST ((restT.gpr .r0 (by simp)).trans readyU.ptr)
  obtain ⟨byteT, countT⟩ := two_writes s.mem base (d := 200) (e := 192)
    (BitVec.ofNat 32 (s.mem (State.addr ep)).toNat) (BitVec.ofNat 32 8) (by decide) (by decide) (by decide)
  rw [← memT] at byteT countT
  have keep (a : Nat) (ha : a + 4 ≤ 192 ∨ 204 ≤ a) (ha' : a + 4 ≤ 256) :
      t.mem.readW (off (State.addr base) a) 32 = s.mem.readW (off (State.addr base) a) 32 := by
    rw [memT]; exact read_after_writes _ _ _ _ (by omega) (by omega) (by decide) (by decide) ha'
  refine ⟨⟨powerT, h.table.after_ctl ctl fits nowrap (by decide), fits, ?_, ?_, h.bound, h.short⟩,
    byteT, countT, ?_, frameT, restST⟩
  · rw [memT, read_after_writes _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h.digit
  · rw [keep 204 (by decide) (by decide)]; exact h.pending
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact keep 128 (by decide) (by decide)
    · exact keep 132 (by decide) (by decide)

/-- An exponent bit, then the byte shifted and its count decremented. -/
theorem windowRound_ok (s : State) {base : BitVec 32} {len w M x A p q V c : Nat}
    (h : WinState base len w M x A p q s) (hv : V < 2 ^ 32) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V)
    (count : s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 c) :
    WP isa windowRound s fun t => (∃ A' p', WinState base len w M x A' p' ((q + 1) % 3) t ∧
      A' + p' = 2 * (A + p) + V / 128 % 2) ∧
      t.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) ∧
      t.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ KeepsPtr base s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [windowRound, WP.seq_iff]
  refine WP.mono (windowBit_ok s h hv byte) ?_
  rintro u ⟨⟨A', p', stateU, sum⟩, keepsU, frameU, restU⟩
  have byteU := (keepsU 200 (by simp)).trans byte
  have countU := (keepsU 192 (by simp)).trans count
  rw [WP.seq_iff]
  refine WP.mono (expShift_ok u stateU.power.ready.workspace (by omega) stateU.power.ready.ptr byteU) ?_
  rintro v ⟨memV, restV⟩
  have readyV := stateU.power.ready
  refine WP.mono (expDecrement_ok v (readyV.workspace.congr restV.wr) (by omega)
    ((restV.gpr .r0 (by simp)).trans readyV.ptr) hc hc' (by
      have outside := writeW32_outside u.mem (State.addr base) (d := 200) (BitVec.ofNat 32 (V + V)) (by decide)
      rw [← memV] at outside
      rw [outside_read32 outside (d := 192) (by decide) (by decide)]; exact countU)) ?_
  rintro t ⟨memT, flag, restT⟩
  rw [memV] at memT
  have ctl : CtlOnly base u.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have restUT : Rest roundClobbers u t := (rest_round restV).trans (rest_round restT)
  obtain ⟨powerT, frameT⟩ := stateU.power.after_ctl ctl restUT
    ((restT.gpr .r0 (by simp)).trans ((restV.gpr .r0 (by simp)).trans readyV.ptr))
  obtain ⟨byteT, countT⟩ := two_writes u.mem base (d := 200) (e := 192)
    (BitVec.ofNat 32 (V + V)) (BitVec.ofNat 32 (c - 1)) (by decide) (by decide) (by decide)
  rw [← memT] at byteT countT
  have keep (a : Nat) (ha : a + 4 ≤ 192 ∨ 204 ≤ a) (ha' : a + 4 ≤ 256) :
      t.mem.readW (off (State.addr base) a) 32 = u.mem.readW (off (State.addr base) a) 32 := by
    rw [memT]; exact read_after_writes _ _ _ _ (by omega) (by omega) (by decide) (by decide) ha'
  refine ⟨⟨A', p', ⟨powerT, stateU.table.after_ctl ctl fits nowrap (by decide), fits, ?_, ?_,
    stateU.bound, stateU.short⟩, sum⟩, byteT, countT, flag, ?_, frameU.trans frameT, restU.trans restUT⟩
  · rw [memT, read_after_writes _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact stateU.digit
  · rw [keep 204 (by decide) (by decide)]; exact stateU.pending
  · refine keepsU.ptr.trans ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact keep 128 (by decide) (by decide)
    · exact keep 132 (by decide) (by decide)

/-- After `j` bits of the byte `v`, with `E` the earlier bytes: the bits read
are `E 2^j + v / 2^(8 - j)`, and `n + j` of them, `n` before the byte. -/
structure WinBitState (base : BitVec 32) (len w M x E v n j : Nat) (s : State) : Prop where
  state : ∃ A p, WinState base len w M x A p ((n + j) % 3) s ∧ A + p = E * 2 ^ j + v / 2 ^ (8 - j)
  byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (v * 2 ^ j)
  count : s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 (8 - j)

theorem windowBits_ok (s : State) {base : BitVec 32} {len w M x E v n : Nat}
    (h : WinBitState base len w M x E v n 0 s) (hv : v < 256) :
    WP isa windowBits s fun t => (∃ A p, WinState base len w M x A p ((n + 8) % 3) t ∧ A + p = 256 * E + v) ∧
      KeepsPtr base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ WinBitState base len w M x E v n j t ∧
    KeepsPtr base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  unfold windowBits
  refine WP.loop (M := isa) I ?_ 8 s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, ⟨⟨A, p, state, sum⟩, byte, count⟩, keeps, frame, rest⟩ := inv
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
    have valueFit : v * 2 ^ j < 2 ^ 32 := by
      have := Nat.mul_le_mul_left v hp
      omega
    refine WP.mono (windowRound_ok t state valueFit (by omega) (by omega) byte count) ?_
    rintro u ⟨⟨A', p', stateU, sumU⟩, byteU, countU, zero, keepsU, frameU, restU⟩
    rw [Nat.mod_add_mod] at stateU
    have expEq : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
        E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
      rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
        Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
    rw [sum, expEq] at sumU
    have next : WinBitState base len w M x E v n (j + 1) u := by
      refine ⟨⟨A', p', stateU, sumU⟩, ?_, ?_⟩
      · rw [byteU, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countU]; congr 1
    by_cases last : j + 1 = 8
    · left
      refine ⟨?_, ?_, keeps.trans keepsU, frame.trans frameU, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, show 8 - j = 1 by omega, decide_true, Bool.not_true]
      · refine ⟨A', p', by rw [show n + 8 = n + j + 1 by omega]; exact stateU, ?_⟩
        simpa only [last, Nat.sub_self, Nat.pow_zero, Nat.div_one, show 2 ^ 8 = 256 from rfl,
          Nat.mul_comm E 256] using sumU
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, next, keeps.trans keepsU, frame.trans frameU,
        rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, show (8 - j = 1) = False by simp; omega, decide_false, Bool.not_false]
  · exact ⟨0, by decide, by decide, h, KeepsPtr.refl _ _, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm
