module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-! # FFDH parameter generation on x86-64: random-tape header operations -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Rsa.X86_64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem drawHead_ok {s : State} {B O : Addr} {Z left len : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hle : word s.mem O (8 * oRandLeft) = BitVec.ofNat 64 left)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len)
    (hleft : left < 2 ^ 64) (hln : len < 2 ^ 64) :
    WP isa (.block drawHead) s fun t => t.cf = some (decide (left < len)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega)
  refine WP.mono (WP.keep [.rax, .rcx]
    (Q := fun t => t.cf = some (decide (left < len)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, k⟩
  xrun [drawHead, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oRandLeft (by decide), hrd oWitnessLen (by decide), hle, hlen]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hln]

theorem drawShort_ok {s : State} {B O : Addr} {Z : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O) :
    WP isa (.block drawShort) s fun t =>
      t.mem = s.mem.writeW (off O (8 * oStatus)) (0#64) ∧
      t.zf = some false ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off O (8 * oStatus)) (0#64) ∧ t.zf = some false) ?_ rfl)
    fun t ⟨⟨hm, hf⟩, k⟩ => ⟨hm, hf, k⟩
  xrun [drawShort, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    ho.st (d := 8 * oStatus) (by unfold oStatus; omega)]
  rfl

theorem drawFinish_ok {s : State} {B O : Addr} {Z : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O) :
    WP isa (.block drawFinish) s fun t =>
      t.mem = s.mem.writeW (off O (8 * oStatus)) (1#64) ∧
      t.zf = s.zf ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off O (8 * oStatus)) (1#64) ∧ t.zf = s.zf) ?_ rfl)
    fun t ⟨⟨hm, hf⟩, k⟩ => ⟨hm, hf, k⟩
  xrun [drawFinish, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    ho.st (d := 8 * oStatus) (by unfold oStatus; omega)]
  rfl

theorem drawLoad_ok {s : State} {B O op : Addr} {Z len : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hbp : s.gpr .rbp = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hop : word s.mem O (8 * oOut) = op)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len) :
    WP isa (.block drawLoad) s fun t => t.gpr .rdi = B ∧ t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.mem = s.mem ∧ Keep [.rdi, .rax, .rsi, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega)
  refine WP.mono (WP.keep [.rdi, .rax, .rsi, .rcx] (Q := fun t => t.gpr .rdi = B ∧ t.gpr .rsi = op ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hd, hr, hc, hm⟩, k⟩ => ⟨hd, hr, hc, hm, k⟩
  xrun [drawLoad, State.ea, hdr, hbp, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oOut (by decide), hrd oWitnessLen (by decide), hop, hlen]

/-- Advancing a draw keeps the old pointer in RSI for the masked copy. -/
theorem drawSetup_ok {s : State} {B O op rp : Addr} {Z len bits left used : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hop : word s.mem O (8 * oOut) = op)
    (hp : word s.mem O (8 * oRandPtr) = rp)
    (hle : word s.mem O (8 * oRandLeft) = BitVec.ofNat 64 left)
    (hu : word s.mem O (8 * oUsed) = BitVec.ofNat 64 used)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len)
    (hb : word s.mem O (8 * oWitnessBits) = BitVec.ofNat 64 bits)
    (hln : len < 2 ^ 64) (hleft : len ≤ left) :
    WP isa (.block drawSetup) s fun t =>
      t.mem = ((s.mem.writeW (off O (8 * oRandPtr)) (off rp len)).writeW
        (off O (8 * oRandLeft)) (BitVec.ofNat 64 (left - len))).writeW
        (off O (8 * oUsed)) (BitVec.ofNat 64 (used + len)) ∧
      t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rbp = B ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 bits ∧
      Keep [.rax, .rsi, .rcx, .rdx, .r8, .rbp, .rdi] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega)
  have hwr : ∀ j < 32, InRegions s.wr (off O (8 * j)) 8 := fun j hj => ho.st (by omega)
  have hskip (m : Mem) (v : BitVec 64) {i j : Nat} (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
      word (m.writeW (off O (8 * i)) v) O (8 * j) = word m O (8 * j) :=
    hdrStore_hdr m O v hi hj hne
  have hsub : BitVec.ofNat 64 left - BitVec.ofNat 64 len = BitVec.ofNat 64 (left - len) :=
    BitVec.ofNat_sub_ofNat_of_le left len hln hleft
  refine WP.mono (WP.keep [.rax, .rsi, .rcx, .rdx, .r8, .rbp, .rdi] (Q := fun t =>
    t.mem = ((s.mem.writeW (off O (8 * oRandPtr)) (off rp len)).writeW
      (off O (8 * oRandLeft)) (BitVec.ofNat 64 (left - len))).writeW
      (off O (8 * oUsed)) (BitVec.ofNat 64 (used + len)) ∧
    t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rbp = B ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 bits) ?_ rfl)
    fun t ⟨⟨hm, hp', ho', hb', hc, hd⟩, k⟩ => ⟨hm, hp', ho', hb', hc, hd, k⟩
  xrun [drawSetup, State.ea, hdr, hdi, hdrOff, ws, hl,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oRandPtr (by decide), hrd oWitnessLen (by decide), hrd oWitnessBits (by decide),
    hrd oRandLeft (by decide), hrd oUsed (by decide), hrd oOut (by decide),
    hwr oRandPtr (by decide), hwr oRandLeft (by decide), hwr oUsed (by decide),
    hp, hlen, hb, hle, hu, hop,
    hskip (i := oRandPtr) (j := oRandLeft) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandPtr) (j := oUsed) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandLeft) (j := oUsed) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandPtr) (j := oOut) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandLeft) (j := oOut) _ _ (by decide) (by decide) (by decide),
    hskip (i := oUsed) (j := oOut) _ _ (by decide) (by decide) (by decide), hsub,
    BitVec.ofNat_add_ofNat]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
