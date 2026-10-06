import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow

/-! The carry and cancellation steps for reducing the unreduced square. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def redcU (x inv : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * inv.toNat)

theorem redcHead_ok {s : State} {B : Addr} {Z e w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (h8 : s.gpr .r8 = off B e) (he : e + 8 ≤ Z) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxSquare.redcHead) s fun t =>
      t.gpr .rdx = redcU (word s.mem B e) minv ∧ t.mem = s.mem ∧ Keep [.rdx, .rax] s t := by
  have hn := hs.nowrap
  have hh : 8 * sMinv + 8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sMinv < 32 by decide)
    omega
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun t =>
    t.gpr .rdx = redcU (word s.mem B e) minv ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold AdxSquare.redcHead
  xrun [State.ea, at0, hdr, h8, hdi, hdrOff, hs.ld he, hs.ld hh, hH.hminv,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, execMulx, redcU]

/-- A top-word addition with an explicit high carry. -/
theorem redcTail_ok {s : State} {B : Addr} {Z e w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 w)
    (hZ : e + 8 * w + 8 ≤ Z) :
    WP isa (.block AdxSquare.redcTail) s fun t => ∃ lo : BitVec 64,
      t.mem = s.mem.writeW (off B (e + 8 * w)) lo ∧
      lo.toNat + 2 ^ 64 * (t.gpr .r10).toNat =
        (word s.mem B (e + 8 * w)).toNat + (s.gpr .rcx).toNat + (s.gpr .r10).toNat ∧
      ((s.gpr .r10).toNat ≤ 1 → (t.gpr .r10).toNat ≤ 1) ∧
      t.gpr .r8 = off B (e + 8) ∧ Keep [.rax, .rsi, .r10, .r8] s t := by
  generalize hTw : word s.mem B (e + 8 * w) = Tw
  generalize hc : s.gpr .rcx = c
  generalize hp : s.gpr .r10 = p
  let hi1 := (0 : BitVec 64) + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ Tw.toNat + c.toNat))).setWidth 64
  let hi2 := hi1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ (Tw + c).toNat + p.toNat))).setWidth 64
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  have eq1 : (Tw + c).toNat + 2 ^ 64 * hi1.toNat = Tw.toNat + c.toNat := by
    have he := addc_toNat Tw (0 : BitVec 64) c (by
      rw [hz]; have := Tw.isLt; have := c.isLt; omega)
    simpa only [hi1, hz, Nat.mul_zero, Nat.add_zero] using he
  have eq2 : (Tw + c + p).toNat + 2 ^ 64 * hi2.toNat =
      (Tw + c).toNat + p.toNat + 2 ^ 64 * hi1.toNat :=
    addc_toNat (Tw + c) hi1 p (by have := Tw.isLt; have := c.isLt; have := p.isLt; omega)
  have val : (Tw + c + p).toNat + 2 ^ 64 * hi2.toNat = Tw.toNat + c.toNat + p.toNat := by
    omega
  refine WP.mono (WP.keep [.rax, .rsi, .r10, .r8] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * w)) (Tw + c + p) ∧
      t.gpr .r10 = hi2 ∧ t.gpr .r8 = off B (e + 8)) ?_ rfl)
    fun t ⟨⟨hm, h10, h8'⟩, k⟩ => ⟨_, hm, by rw [h10]; exact val, ?_, h8', k⟩
  · unfold AdxSquare.redcTail
    xrun [State.ea, ix, addr0 h8 h14, hs.ld hZ, hs.st hZ, hTw, hc, hp, sx0, hi1, hi2,
      show s.gpr .r8 + 8 = off B (e + 8) by rw [h8, off_add8]]
    rfl
  · intro h
    rw [h10]
    have := Tw.isLt; have := c.isLt
    omega

end VG.Proof.Bignum.X86_64.AdxSquare
