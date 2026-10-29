module

public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Impl.Dsa.X86_64.Random
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.RandomEncoding
/-! A complete draw from the random tape, with derived memory permissions. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomCopyWhole.lean`, which only this module imported.
section

/-! Compose the masked first byte and unmasked suffix of a random draw. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
open VG.WriteBytes (writeW8_apply)

private theorem zero_addr (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

private theorem shift_addr (p : Addr) (i : Nat) : p + 1 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, BitVec.add_comm 1, ofNat_add_one]

/-- Composition rule used with `random_copyInit_ok`. Every write is confined
to the draw's destination; the only altered byte value is the masked head. -/
theorem random_copy_of_init {s : State} {src dst : Addr} {n : Nat} {head : Byte}
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (hinit : WP isa (.block Random.copyInit) s fun u =>
      u.gpr .r10 = src + 1 ∧ u.gpr .rdx = dst + 1 ∧ u.gpr .r11 = BitVec.ofNat 64 (n - 1) ∧
      u.zf = some (decide (n = 1)) ∧ u.mem = s.mem.writeW dst head ∧
      Keep [.rax, .r10, .rdx, .r11] s u) :
    WP isa Random.copy s fun t =>
      (∀ i < n, t.mem (dst + BitVec.ofNat 64 i) = if i = 0 then head else s.mem (src + BitVec.ofNat 64 i)) ∧
      (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .r10, .rdx, .r11] s t := by
  unfold Random.copy
  refine WP.seq (WP.mono hinit fun u ⟨hup, hud, hun, huz, hum, hku⟩ => ?_)
  have hz : u.zf = some (decide (n - 1 = 0)) := by
    rw [huz]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (random_copyRest_ok hup hud hun hz (by omega)
    (fun i hi => by rw [hku.2.1, hku.2.2, shift_addr]; exact hr (i + 1) (by omega))
    (fun i hi => by rw [hku.2.2, shift_addr]; exact hw (i + 1) (by omega))
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
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
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
      Keep [.rax, .r10, .rdx, .r11] s t := by
  exact random_copy_of_init hpos hbound hr hw hsep
    (random_copyInit_ok hs hsp hR hu hn hl hm hsrc hdst hpos hbound
      (by simpa only [zero_addr] using hr 0 hpos)
      (by simpa only [zero_addr] using hw 0 hpos))

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomCopyCandidate.lean`, which only this module imported.
section

/-! The copied ISA bytes encode precisely the specification's candidate. -/
section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

private theorem masked_head (qBytes : List Byte) (b : Byte)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1) :
    ((b.setWidth 64 &&& randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat).setWidth 8) =
      b &&& BitVec.ofNat 8 (2 ^ ((VG.Proof.Dsa.significant qBytes).2.toNat.log2 + 1) - 1) := by
  have hb : 0 < (VG.Proof.Dsa.significant qBytes).2.toNat := by
    have hn := VG.Proof.Dsa.significant_nonzero qBytes
    have hz : (VG.Proof.Dsa.significant qBytes).2.toNat ≠ 0 := by
      intro he
      have := hn.mpr (BitVec.eq_of_toNat_eq he)
      omega
    omega
  rw [randomMaskValue_eq _ hb (VG.Proof.Dsa.significant qBytes).2.isLt, BitVec.setWidth_and,
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

theorem random_copy_candidate_ok {s : State} {B R src dst : Addr} {l used : Nat}
    {qBytes tail : List Byte} {b : Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (tail.length + 1))
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 (tail.length + 1) = dst)
    (hwidth : tail.length + 1 = (VG.Proof.Dsa.significant qBytes).1)
    (hbound : tail.length + 1 < 2 ^ 64)
    (hr : ∀ i < tail.length + 1, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < tail.length + 1, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < tail.length + 1, ∀ j < tail.length + 1,
      src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (hv : ∀ i (hi : i < (b :: tail).length), s.mem (src + BitVec.ofNat 64 i) = (b :: tail)[i]) :
    WP isa Random.copy s fun t => ∃ copied : List Byte,
      copied.length = tail.length + 1 ∧
      (∀ i (hi : i < copied.length), t.mem (dst + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes) (b :: tail) ∧
      (∀ x, (∀ i < tail.length + 1, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .r10, .rdx, .r11] s t := by
  refine WP.mono (random_copy_ok hs hsp hR hu hn hl hm hsrc hdst (by omega) hbound hr hw hsep)
    fun t ⟨htv, htf, htk⟩ => ?_
  let head := b &&& BitVec.ofNat 8 (2 ^ ((VG.Proof.Dsa.significant qBytes).2.toNat.log2 + 1) - 1)
  refine ⟨head :: tail, rfl, ?_, (VG.Proof.Dsa.random_candidate_mask qBytes b tail hwidth).symm,
    htf, htk⟩
  intro i hi
  rw [htv i hi]
  cases i with
  | zero =>
    have hb : s.mem src = b := by
      have h := hv 0 (by simp)
      change s.mem (src + 0#64) = b at h
      simpa only [BitVec.add_zero] using h
    simp only [ite_true, hb, List.getElem_cons_zero]
    exact masked_head qBytes b (by omega)
  | succ i =>
    rw [ite_eq_right (Nat.succ_ne_zero i), hv (i + 1) hi]
    rfl

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_copy_draw_ok {s : State} {B R : Addr} {used : Nat} {qBytes rand : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hrand : Src s B Random.frameBytes R rand)
    (hqlen : qBytes.length ≤ 32)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hfull : used + (VG.Proof.Dsa.significant qBytes).1 ≤ rand.length) :
    WP isa Random.copy s fun t => ∃ copied : List Byte,
      copied.length = (VG.Proof.Dsa.significant qBytes).1 ∧
      (∀ i (hi : i < copied.length), t.mem
        (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes)
        ((rand.drop used).take (VG.Proof.Dsa.significant qBytes).1) ∧
      Outside B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1)
        (VG.Proof.Dsa.significant qBytes).1 s.mem t.mem ∧ Keep [.rax, .r10, .rdx, .r11] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  have hlen : ((rand.drop used).take n).length = n := by
    rw [List.length_take, List.length_drop]
    omega
  have hslice := random_src_take (random_src_drop hrand used) n
  have hne : (rand.drop used).take n ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    omega
  obtain ⟨b, tail, he⟩ := List.exists_cons_of_ne_nil hne
  rw [he] at hlen hslice
  have htlen : tail.length + 1 = n := hlen
  have hbound : tail.length + 1 < 2 ^ 64 := by omega
  have hdst : off B Random.oNonce + BitVec.ofNat 64 qBytes.length - BitVec.ofNat 64 (tail.length + 1) =
      off B (200 + qBytes.length - n) := by rw [htlen]; exact random_nonce_addr B hnfit
  have hwrite : ∀ i < tail.length + 1,
      InRegions s.wr (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    have headdr : off B (200 + qBytes.length - n) + BitVec.ofNat 64 i =
        off B (200 + qBytes.length - n + i) := by simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
    rw [headdr]
    exact hs.st8 (by unfold Random.frameBytes; omega)
  have hsep : ∀ i < tail.length + 1, ∀ j < tail.length + 1,
      R + BitVec.ofNat 64 used + BitVec.ofNat 64 i ≠
        off B (200 + qBytes.length - n) + BitVec.ofNat 64 j := by
    intro i hi j hj headdr
    have ho := hslice.out i hi
    rw [headdr, random_nonce_offset B hnfit hqlen (by omega)] at ho
    unfold Random.frameBytes at ho
    omega
  refine WP.mono (random_copy_candidate_ok hs hsp hR hu
    (by rw [htlen]; exact hn) hl hm rfl hdst htlen hbound hslice.rd hwrite hsep hslice.val)
    fun t ⟨copied, hclen, hcv, hcdec, hcf, hck⟩ => ?_
  refine ⟨copied, hclen.trans htlen, hcv, ?_, ?_, hck⟩
  · rw [he]; exact hcdec
  · exact random_copy_outside hnfit hqlen (by simpa only [htlen] using hcf)

end VG.Proof.Dsa.X86_64
