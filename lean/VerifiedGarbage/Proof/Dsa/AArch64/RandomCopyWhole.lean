module
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Compose the masked first byte and unmasked suffix of a random draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.WriteBytes (writeW8_apply)

private theorem zero_addr (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

private theorem shift_addr (p : Addr) (i : Nat) : p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
  change p + BitVec.ofNat 64 1 + BitVec.ofNat 64 i = _
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm 1]

/-- Composition rule used with `random_copyInit_ok`. Every write is confined
to the draw's destination; the only altered byte value is the masked head. -/
theorem random_copy_of_init {s : State} {src dst : Addr} {n : Nat} {head : Byte}
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (hinit : WP isa (.block Random.copyInit) s fun u =>
      u.gpr .x12 = src + 1#64 ∧ u.gpr .x2 = dst + 1#64 ∧ u.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      u.mem = s.mem.writeW dst head ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s u) :
    WP isa Random.copy s fun t =>
      (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) = if i = 0 then head else s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  unfold Random.copy
  refine WP.seq (WP.mono hinit fun u ⟨hup, hud, hun, hum, hku⟩ => ?_)
  refine WP.mono (random_copyRest_ok hup hud hun (by omega)
    (fun i hi => by rw [hku.rd, hku.wr, shift_addr]; exact hr (i + 1) (by omega))
    (fun i hi => by rw [hku.wr, shift_addr]; exact hw (i + 1) (by omega))
    (fun i hi j hj => by rw [shift_addr, shift_addr]; exact hsep (i + 1) (by omega) (j + 1) (by omega)))
    fun t ⟨htb, htf, hkt⟩ => ?_
  refine ⟨?_, ?_, (hku.trans hkt).mono (by decide)⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp only [zero_addr, ite_true]
      have hstay : t.mem dst = u.mem dst := htf dst fun j hj => by
        rw [shift_addr]
        have hn := out_ne (out := dst) (i := 0) (j := j + 1) (by decide) (by omega) (by omega)
        simpa only [zero_addr] using hn
      rw [hstay, hum, writeW8_apply, ite_eq_left rfl]
    · have hj : i - 1 < n - 1 := by omega
      have hb := htb (i - 1) hj
      rw [shift_addr, shift_addr, Nat.sub_add_cancel (by omega)] at hb
      rw [hb, ite_eq_right hi0, hum, writeW8_apply]
      have hne : src + BitVec.ofNat 64 i ≠ dst := by
        have h := hsep i hi 0 hpos
        simpa only [zero_addr] using h
      exact ite_eq_right hne
  · intro x hx
    have hstay := htf x fun j hj => by rw [shift_addr]; exact hx (j + 1) (by omega)
    rw [hstay, hum, writeW8_apply]
    have hne : x ≠ dst := by simpa only [zero_addr] using hx 0 hpos
    exact ite_eq_right hne

/-- A complete draw copy, from the caller-owned frame to the nonce buffer. -/
theorem random_copy_ok {s : State} {B R src dst : Addr} {l n used : Nat} {mask : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = mask)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst)
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    WP isa Random.copy s fun t =>
      (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) =
        if i = 0 then (((s.mem src).setWidth 64 &&& mask).setWidth 8)
        else s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  exact random_copy_of_init hpos hbound hr hw hsep
    (random_copyInit_ok hs hsp hR hu hn hl hm hsrc hdst hpos hbound
      (by simpa only [zero_addr] using hr 0 hpos)
      (by simpa only [zero_addr] using hw 0 hpos))

end VG.Proof.Dsa.AArch64
