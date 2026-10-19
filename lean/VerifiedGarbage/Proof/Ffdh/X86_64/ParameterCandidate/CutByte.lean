module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape

/-! # FFDH parameter candidates on x86-64: the witness's high-byte mask -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

private theorem fullMask {j : Nat} (hj : j < 8) :
    BitVec.ofNat 64 (2 ^ j - 1) ||| BitVec.ofNat 64 (2 ^ j) = BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem cutMasks_ok {s : State} {bits : Nat} (hb : 1 ≤ bits) (hk : bits < 2 ^ 31)
    (hd : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa (.block cutMasks) s fun t => t.gpr .r8 = BitVec.ofNat 64 (2 ^ ((bits - 1) % 8 + 1) - 1) ∧
      t.gpr .r9 = 0 ∧ t.mem = s.mem ∧ Keep [.rdx, .r8, .r9, .r10] s t := by
  unfold cutMasks
  rw [WP.block_append_iff]
  refine WP.mono (shapeMasks_ok hb hk hd) fun u ⟨h8, h9, hm, k⟩ => ?_
  exact WP.mono (WP.keep [.r8, .r9] (Q := fun t =>
    t.gpr .r8 = BitVec.ofNat 64 (2 ^ ((bits - 1) % 8 + 1) - 1) ∧ t.gpr .r9 = 0 ∧ t.mem = u.mem)
    (by xrun [h8, h9, fullMask (Nat.mod_lt _ (by decide))]) rfl)
    fun t ⟨⟨hr8, hr9, hm'⟩, k'⟩ => ⟨hr8, hr9, hm'.trans hm, (k.trans k').mono (by decide)⟩

/-- Copy and mask the first byte, without forcing its high or low bits. -/
theorem firstByte_cut_ok {s : State} {rp op : Addr} {len j : Nat} {b : Byte}
    (hl : 2 ≤ len) (hk : len < 2 ^ 31)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op) (hn : s.gpr .rcx = BitVec.ofNat 64 len)
    (hm : s.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1)) (hh : s.gpr .r9 = 0)
    (hrd : InRegions (s.rd ++ s.wr) rp 1) (hwr : InRegions s.wr op 1) (hb : s.mem rp = b) :
    WP isa (.block firstByte) s fun t =>
      t.mem = s.mem.writeW op (b &&& BitVec.ofNat 8 (2 ^ (j + 1) - 1)) ∧
      t.gpr .r10 = off rp 1 ∧ t.gpr .r11 = off op 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (len - 1) ∧
      Keep [.rax, .r10, .r11, .rcx] s t := by
  have hbyte : (b.setWidth 64 &&& BitVec.ofNat 64 (2 ^ (j + 1) - 1)).setWidth 8 =
      b &&& BitVec.ofNat 8 (2 ^ (j + 1) - 1) := by simp [BitVec.setWidth_and]
  refine WP.mono (WP.keep [.rax, .r10, .r11, .rcx] (Q := fun t =>
    t.mem = s.mem.writeW op (b &&& BitVec.ofNat 8 (2 ^ (j + 1) - 1)) ∧
      t.gpr .r10 = off rp 1 ∧ t.gpr .r11 = off op 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (len - 1))
    (by
      unfold firstByte
      xrun [State.ea, at0, hrp, hop, hn, hm, hh,
      show rp + BitVec.ofInt 64 0 = rp from by simp,
      show op + BitVec.ofInt 64 0 = op from by simp, hrd, hwr, hb, hbyte,
      ofNat64_pred (show 1 ≤ len from by omega) (by omega), off]
      refine ⟨?_, rfl, rfl⟩
      change s.mem.writeW op (((b.setWidth 64 &&& BitVec.ofNat 64 (2 ^ (j + 1) - 1)) ||| (0#64)).setWidth 8) = _
      rw [BitVec.or_zero, hbyte]) rfl) fun _ ⟨⟨hm', hp, ho, hc⟩, k⟩ => ⟨hm', hp, ho, hc, k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
