module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Dsa.X86_64.Generation.ForceWitness`, which only this module used -/

section

/-! # Native forced-witness byte transformation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem forceWitness_ok {s : State} {op : Addr} {len : Nat}
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 32) (hop : s.gpr .rdi = op)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off op i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.block Impl.Dsa.X86_64.Generation.forceWitness) s fun t =>
      t.mem = (s.mem.writeW op (s.mem op &&& (127 : Byte))).writeW
        (off op (len - 1)) (s.mem (off op (len - 1)) ||| (2 : Byte)) ∧ Keep [.rax] s t := by
  have hne : off op (len - 1) ≠ op := by
    intro he
    have hv : BitVec.ofNat 64 (len - 1) = 0#64 := by
      have he' := congrArg (fun x => x - op) he
      simpa only [off, Offset.add_sub_cancel_left, BitVec.sub_self] using he'
    have := congrArg BitVec.toNat hv
    change (len - 1) % 2 ^ 64 = 0 at this
    omega_using [hlen, hmax, this]
  have hlast : op + BitVec.ofNat 64 len * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = off op (len - 1) := by
    have h1 : BitVec.ofNat 64 len = BitVec.ofNat 64 (len - 1) + BitVec.ofNat 64 1 := by
      rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel (by omega_using [hlen])]
    rw [BitVec.mul_one, BitVec.add_assoc, h1, BitVec.add_assoc,
      show BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = 0#64 by decide, BitVec.add_zero]
  have hr0 := hrd 0 (by omega_using [hlen])
  have hw0 := hwr 0 (by omega_using [hlen])
  have hrn := hrd (len - 1) (by omega_using [hlen])
  have hwn := hwr (len - 1) (by omega_using [hlen])
  simp only [off, BitVec.add_zero] at hr0 hw0 hrn hwn hne hlast
  refine WP.keep [.rax] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.forceWitness, State.ea, hop, hcx, hlast, off,
    show BitVec.ofInt 64 0 = 0#64 by rfl, BitVec.add_zero, hr0, hw0, hrn, hwn, WriteBytes.writeW8_apply, hne]

  simp [BitVec.setWidth_and, BitVec.setWidth_or]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The forced branch replaces the draw while preserving the uniform flag -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/StoredWitness.lean`, which only this module imported.
section

/-! # A forced witness preserves all prepared modulus data -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem forceStoredWitness_ok {s : State} {B p : Addr} {Z w N sp lp len : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hsp : sp < 32) (hp : word s.mem B (8 * sp) = p)
    (hlp : lp < 32) (hlw : word s.mem B (8 * lp) = BitVec.ofNat 64 len)
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 32)
    (hwr : ∀ i < len, InRegions s.wr (off p i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (off p i)) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness sp lp) s fun t =>
      ModulusReady t B Z w mi N ∧
      Spec.Rsa.bytesAt t.mem p len = VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem p len) ∧
      (∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧ Keep [.rax, .rbx, .rcx] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sp)) 8 :=
    h.good.scr.ld (by have := hdr_lt_slot w 8 hsp; have := hd.z; omega)
  have hll : InRegions (s.rd ++ s.wr) (off B (8 * lp)) 8 :=
    h.good.scr.ld (by have := hdr_lt_slot w 8 hlp; have := hd.z; omega)
  unfold Impl.Dsa.X86_64.Generation.forceStoredWitness
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx, .rcx, .rdi] (Q := fun u =>
      u.gpr .rbx = B ∧ u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .rdi = p ∧ u.mem = s.mem) (by
        xrun [State.ea, hdr, hdrOff, h.good.rdi, hl, hp, hll, hlw]) rfl)
    fun u ⟨⟨hbx, hcx, hdi, hm⟩, ku⟩ => ?_)
  have hwu : ∀ i < len, InRegions u.wr (off p i) 1 := fun i hi => by rw [ku.2.2]; exact hwr i hi
  have hru : ∀ i < len, InRegions (u.rd ++ u.wr) (off p i) 1 := fun i hi => by
    obtain ⟨r, hr, hc⟩ := hwu i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (forceWitness_ok hlen hmax hdi hcx hru hwu) fun v ⟨hmv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = v.mem) (by
    xrun [(kv.gpr (by decide) : v.gpr .rbx = u.gpr .rbx).trans hbx]) rfl) fun t ⟨⟨hdit, hmt⟩, kt⟩ => ?_
  have k := (ku.trans kv).trans kt
  have hmfinal : t.mem = (s.mem.writeW p (s.mem p &&& (127 : Byte))).writeW
      (off p (len - 1)) (s.mem (off p (len - 1)) ||| (2 : Byte)) := by rw [hmt, hmv, hm]
  have hf : ∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a := by
    intro a ha
    have hzero : a ≠ p := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hmfinal, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]
  have hwords := VG.Proof.Bignum.words_outside_bytes (by have := h.good.scr.nowrap; omega : Z ≤ 2 ^ 64) hf hsep
  refine ⟨h.of_words hd hwords k.2.2 hdit, ?_, hf, hwords, ?_⟩
  · rw [hmfinal, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem p hlen (by omega)]
  · refine ⟨fun r hr => ?_, k.2⟩
    by_cases he : r = .rdi
    · subst r; exact hdit.trans h.good.rdi.symm
    · exact k.gpr (by revert hr he; cases r <;> decide)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Dsa.Generation

theorem forceSample_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 2 ^ 32) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut kUsedP) s fun t =>
      SampleState B p Z w N mi (forcedWitnessBytes bs) t ∧
      word t.mem B (8 * kU) = word s.mem B (8 * kU) ∧
      WorkFrame B [] [⟨p, bs.length⟩] s.mem t.mem ∧ Keep [.rax, .rbx, .rcx] s t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_using [this]
  have hfl := forcedWitnessBytes_length hlen
  refine WP.mono (forceStoredWitness_ok h.ready hd (by decide) h.ptr (by decide) h.len hlen hmax h.writable h.source.out)
    fun t ⟨ht, hbytes, hf, hwords, hk⟩ => ?_
  rw [h.bytes] at hbytes
  refine ⟨⟨ht, (hwords _ (by change 136 ≤ Z; omega_using [hz])).trans h.ptr,
    ?_, ?_, ?_⟩, hwords _ (by change 248 ≤ Z; omega_using [hz]), ?_, hk⟩
  · rw [hfl, hwords _ (by change 152 ≤ Z; omega_using [hz])]; exact h.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => h.source.out i (by rwa [hfl] at hi)⟩
    · rw [hk.2.1, hk.2.2]
      exact h.source.rd i (by rwa [hfl] at hi)
    · have hi' : i < bs.length := by rwa [hfl] at hi
      have hb := bytesAt_read t.mem p hi'
      simpa only [hbytes] using hb
  · intro i hi
    rw [hk.2.2]
    exact h.writable i (by rwa [hfl] at hi)
  · intro x hx _
    apply hf
    intro i hi he
    subst x
    apply hx ⟨p, bs.length⟩ (by simp)
    apply (Region.contains_self p bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hmax, hi] : i < 2 ^ 64)]
    exact hi

end VG.Proof.Dsa.X86_64.Generation
