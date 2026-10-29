module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeSlice
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Framework.AddrArith
/-! # A whole tape draw supplies the sampler and preserves all loop arguments -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/DrawCopy.lean`, which only this module imported.
section

/-! Copy a complete draw's significant suffix, preserving the advanced cursor frame. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem drawCopy_ok {s : State} {B rp op : Addr} {Z w used len drawBytes : Nat}
    (h : Ws s B Z w) (hlen : len ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr)
      (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsrc : ∀ i < len, Z ≤ ofs B (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i))
    (hsep : ∀ i < len, ∀ j < len,
      off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy len drawBytes) s fun t =>
      t.gpr .x0 = B ∧
      (∀ i < len, t.mem (off op i) = s.mem (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i)) ∧
      (∀ a, (∀ i < len, a ≠ off op i) →
        t.mem a = (s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) a) ∧
      Keep [.x0, .x2, .x3, .x9, .x12, .x17] s t := by
  unfold Impl.Dsa.AArch64.Generation.drawCopy
  refine WP.seq (WP.mono (drawCopyArgs_ok h hlen hmax hp hu ho)
    fun u ⟨hu17, hu12, hu2, hu9, hum, ku⟩ => ?_)
  have hur : ∀ i < len, InRegions (u.rd ++ u.wr)
      (off (rp + BitVec.ofNat 64 (used + (drawBytes - len))) i) 1 := by
    intro i hi; rw [ku.rd, ku.wr]; exact hrd i hi
  have huw : ∀ i < len, InRegions u.wr (off op i) 1 := by
    intro i hi; rw [ku.wr]; exact hwr i hi
  refine WP.seq (WP.mono (random_copyRest_ok hu12 hu2 hu9 (by omega) hur huw hsep)
    fun v ⟨hb, hf, kv⟩ => ?_)
  have hv17 := (kv.gpr .x17 (by decide)).trans hu17
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = v.mem)
    (by brun [hv17]) rfl rfl rfl) fun t ⟨⟨ht0, htm⟩, kt⟩ => ?_
  refine ⟨ht0, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · intro i hi
    rw [htm, hb i hi, hum]
    apply writeW_outside _ B _ (d := 8 * kUsed) (by decide)
    have h256 := h.h256
    have hx := hsrc i hi
    simp only [off] at hx
    exact Or.inr (by simp only [kUsed, sFn]; omega)
  · intro a ha
    rw [htm, hf a ha, hum]

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/DrawPrepared.lean`, which only this module imported.
section

/-! Drawing witness bytes preserves the modulus and advances only the entropy cursor. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem drawPrepared_ok {s : State} {B rp op : Addr} {Z w N used drawBytes : Nat} {bs : List Byte}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hlen : bs.length ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op)
    (hsrc : Src s B Z (off rp (used + (drawBytes - bs.length))) bs)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hout : ∀ i < bs.length, Z ≤ ofs B (off op i))
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off rp (used + (drawBytes - bs.length))) i ≠ off op j) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy bs.length drawBytes) s fun t =>
      ModulusReady t B Z w N ∧ Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + drawBytes) ∧
      WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (drawCopy_ok h.ws hlen hmax hp hu ho hsrc.rd hwr hsrc.out hsep)
    fun t ⟨ht0, htbytes, hframe, hk⟩ => ?_
  let mid : State := {s with mem := s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))}
  have hmid : ModulusReady mid B Z w N := h.write_header _ hEZ (by decide)
  have hwords : ∀ d, d + 8 ≤ Z → word t.mem B d = word mid.mem B d :=
    words_outside_bytes (by have := h.ws.scr.nowrap; omega) hframe hout
  have kt : Keep mmRegs s t := by
    refine ⟨?_, hk.rd, hk.wr, hk.sp, hk.vcs⟩
    intro r hr
    by_cases he : r = .x0
    · subst r; exact ht0.trans h.ws.x0.symm
    · apply hk.gpr r
      intro bad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at bad
      rcases bad with rfl | rfl | rfl | rfl | rfl | rfl
      · exact he rfl
      all_goals exact hr (by decide)
  refine ⟨hmid.of_words hEZ hwords hk.wr ht0, ?_, ?_, ?_, kt⟩
  · apply List.ext_getElem
    · exact bytesAt_length _ _ _
    · intro i hi hi'
      have he := htbytes i hi'
      exact (by simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using he.trans (hsrc.val i hi'))
  · rw [hwords _ (by have := h.ws.h256; simp only [kUsed, sFn]; omega)]
    exact word_writeW_self _ _ _ _
  · intro x hx hr
    rw [hframe x (fun i hi he => ?_)]
    · exact writeW_outside _ B _ (by decide) x (hr (8 * kUsed, 8) (by simp))
    · subst x
      apply hx ⟨op, bs.length⟩ (by simp)
      apply (Region.contains_self op bs.length).byte
      simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact hi

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64

theorem drawBuffer_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.drawCopy P.len P.drawBytes) s fun t =>
      PrimeState P (used + P.drawBytes) t ∧
      SampleState P.B P.p P.Z P.w P.N (P.drawSlice used) t ∧
      WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlen := P.slice_length hroom
  have hs : Src s P.B P.Z (off P.rp (used + (P.drawBytes - (P.drawSlice used).length))) (P.drawSlice used) := by
    rw [hlen]; exact h.slice_source hroom
  have hw : ∀ i < (P.drawSlice used).length, InRegions s.wr (off P.p i) 1 := by
    rw [hlen]; exact h.writable
  have hd := drawPrepared_ok h.ready P.exponentRoom
    (by rw [hlen]; exact P.lenDraw) (by have := P.drawMax; omega)
    h.rand h.used h.ptr hs hw (by rw [hlen]; exact P.bufferOutside)
    (by simpa only [hlen, PrimeParams.drawStart] using P.slice_separate hroom)
  rw [hlen] at hd
  refine WP.mono hd fun t ⟨ht, hbytes, hused, hf, hk⟩ => ?_
  have hft : WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact hf x (fun r hmem => hx r (by
      simp only [List.mem_singleton] at hmem; subst r; simp [primeExtras])) hr
  have hzt : 256 ≤ P.Z := P.z256
  have hpt : PrimeState P (used + P.drawBytes) t := h.advance ht hused hft hk
    (by simp only [List.mem_singleton, forall_eq]; change 224 ≤ P.Z; omega)
    (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨hpt, ⟨ht, hpt.ptr, ?_, ?_, ?_⟩, hft, hk⟩
  · rw [hlen]; exact hpt.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => P.bufferOutside i (by rwa [hlen] at hi)⟩
    · obtain ⟨r, hr, hc⟩ := hpt.writable i (by rwa [hlen] at hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have hb : t.mem (off P.p i) = (Spec.Rsa.bytesAt t.mem P.p P.len)[i]'(by rw [bytesAt_length]; rwa [hlen] at hi) := by
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, off]
      simpa only [hbytes] using hb
  · rw [hlen]; exact hpt.writable

end VG.Proof.Dsa.AArch64.Generation
