module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Bignum.ExternalWords
/-! The forced branch changes the draw and preserves its nonuniform flag. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ForceWitness.lean`, which only this module imported.
section

/-! # Native forced-witness byte transformation -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem forceWitness_ok {s : State} {op : Addr} {len : Nat}
    (hlen : 2 ≤ len) (hmax : len < 4096) (hop : s.gpr .x1 = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off op i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) s fun t =>
      t.mem = (s.mem.writeW op (s.mem op &&& (127 : Byte))).writeW
        (off op (len - 1)) (s.mem (off op (len - 1)) ||| (2 : Byte)) ∧ Keep [.x3, .x4] s t := by
  have hne : off op (len - 1) ≠ op := by
    intro he
    have hv : BitVec.ofNat 64 (len - 1) = 0#64 := by
      have he' := congrArg (fun x => x - op) he
      simpa only [off, Offset.add_sub_cancel_left, BitVec.sub_self] using he'
    have := congrArg BitVec.toNat hv
    change (len - 1) % 2 ^ 64 = 0 at this
    omega
  have hr0 := hrd 0 (by omega)
  have hw0 := hwr 0 (by omega)
  have hrn := hrd (len - 1) (by omega)
  have hwn := hwr (len - 1) (by omega)
  simp only [off, BitVec.add_zero] at hr0 hw0 hrn hwn hne
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  unfold Impl.Dsa.AArch64.Generation.forceWitness
  brun [hop, hr0, hw0, hrn, hwn, show len - 1 < 4096 by omega, read_one,
    BitVec.setWidth_and, BitVec.setWidth_or,
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
  change (s.mem.writeW op (s.mem op &&& (127#8))).writeW _
    ((s.mem.writeW op (s.mem op &&& (127#8))) _ ||| (2#8)) = _
  rw [WriteBytes.writeW8_apply, ite_eq_right hne]
  rfl

/-- The native transformation implements the forced branch of the shared
RSA sampler, with all memory outside the witness buffer preserved. -/
theorem forceWitness_spec {s : State} {op : Addr} {len w : Nat}
    (hlen : 2 ≤ len) (hmax : len < 4096) (hop : s.gpr .x1 = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off op i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hbits : Spec.RsaKeyGen.bitLength (w - 1) = 8 * len)
    (hbad : ¬ (2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len) < w - 1)) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) s fun t =>
      Spec.RsaKeyGen.witness (w - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len)) =
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op len), false) ∧
      (∀ a, (∀ i < len, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (forceWitness_ok hlen hmax hop hrd hwr) fun t ⟨hm, hk⟩ => ?_
  refine ⟨?_, ?_, hk⟩
  · rw [hm, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem op hlen (by omega)]
    exact VG.Proof.Dsa.Generation.forcedWitnessBytes_spec
      (by simpa only [bytesAt_length] using hlen) (by simpa only [bytesAt_length] using hbits) hbad
  · intro a ha
    have hzero : a ≠ op := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/StoredWitness.lean`, which only this module imported.
section

/-! Force a stored witness while retaining every prepared modulus word. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem forceStoredWitness_ok {s : State} {B p : Addr} {Z w N len : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hp : word s.mem B (8 * kOut) = p) (hlen : 2 ≤ len) (hmax : len < 4096)
    (hwr : ∀ i < len, InRegions s.wr (off p i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (off p i)) :
    WP isa (Impl.Dsa.AArch64.Generation.forceStoredWitness len) s fun t =>
      ModulusReady t B Z w N ∧
      Spec.Rsa.bytesAt t.mem p len = VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem p len) ∧
      (∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧ Keep [.x1, .x3, .x4] s t := by
  unfold Impl.Dsa.AArch64.Generation.forceStoredWitness
  apply WP.block_append_iff.mpr
  refine WP.mono (WP.keep [.x1] (Q := fun u => u.gpr .x1 = p ∧ u.mem = s.mem)
    (by
      brun [h.ws.x0, hdr_enc (show kOut < 32 by decide), hp,
        h.ws.scr.ld (d := 8 * kOut) (by have := h.ws.h256; simp only [kOut, sFn]; omega)])
    rfl rfl rfl) fun u ⟨⟨hu1, hum⟩, ku⟩ => ?_
  have hwu : ∀ i < len, InRegions u.wr (off p i) 1 := by
    intro i hi; rw [ku.wr]; exact hwr i hi
  have hru : ∀ i < len, InRegions (u.rd ++ u.wr) (off p i) 1 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hwu i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (forceWitness_ok hlen hmax hu1 hru hwu) fun t ⟨htm, kt⟩ => ?_
  have hmfinal : t.mem = (s.mem.writeW p (s.mem p &&& (127 : Byte))).writeW
      (off p (len - 1)) (s.mem (off p (len - 1)) ||| (2 : Byte)) := by rw [htm, hum]
  have hf : ∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a := by
    intro a ha
    have hzero : a ≠ p := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hmfinal, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]
  have hwords := words_outside_bytes (by have := h.ws.scr.nowrap; omega : Z ≤ 2 ^ 64) hf hsep
  have k := ku.trans kt
  refine ⟨h.of_words hEZ hwords k.wr ((k.gpr .x0 (by decide)).trans h.ws.x0), ?_, hf, hwords,
    k.mono (by decide)⟩
  rw [hmfinal, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem p hlen (by omega)]

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.Dsa.Generation

theorem forceSample_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096) :
    WP isa (Impl.Dsa.AArch64.Generation.forceStoredWitness bs.length) s fun t =>
      SampleState B p Z w N (forcedWitnessBytes bs) t ∧
      word t.mem B (8 * kU) = word s.mem B (8 * kU) ∧
      WorkFrame B [] [⟨p, bs.length⟩] s.mem t.mem ∧ Keep [.x1, .x3, .x4] s t := by
  have hz := h.ready.ws.h256
  have hfl := forcedWitnessBytes_length hlen
  refine WP.mono (forceStoredWitness_ok h.ready hEZ h.ptr hlen hmax h.writable h.source.out)
    fun t ⟨ht, hbytes, hf, hwords, hk⟩ => ?_
  rw [h.bytes] at hbytes
  refine ⟨⟨ht, (hwords _ (by simp only [kOut, sFn]; omega)).trans h.ptr,
    ?_, ?_, ?_⟩, hwords _ (by simp only [kU]; omega), ?_, hk⟩
  · rw [hfl, hwords _ (by simp only [kUsedP, sFn]; omega)]; exact h.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => h.source.out i (by rwa [hfl] at hi)⟩
    · rw [hk.rd, hk.wr]
      exact h.source.rd i (by rwa [hfl] at hi)
    · have hi' : i < bs.length := by rwa [hfl] at hi
      have hb : t.mem (off p i) = (Spec.Rsa.bytesAt t.mem p bs.length)[i]'(by simpa only [bytesAt_length] using hi') := by
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, off]
      simpa only [hbytes] using hb
  · intro i hi
    rw [hk.wr]
    exact h.writable i (by rwa [hfl] at hi)
  · intro x hx _
    apply hf
    intro i hi he
    subst x
    apply hx ⟨p, bs.length⟩ (by simp)
    apply (Region.contains_self p bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
    exact hi

end VG.Proof.Dsa.AArch64.Generation
