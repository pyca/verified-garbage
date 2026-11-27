module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Uniform
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.CrtRedc
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Bignum.ExternalWords

/-! ### `Dsa.X86_64.Generation.Sample`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.ForceSample`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86_64.Generation.TestWitness`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.LoadWitness`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.Load`, which this module and modules that import it used -/

section

/-! # Padded candidate and witness loads for the shared primality workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadPadded_ok {s : State} {B p : Addr} {Z w a sp sl : Nat} {mi : BitVec 64} {bs : List Byte}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw31 : w < 2 ^ 31)
    (ha : a < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded a sp sl) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Outside B (slot w a) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hJ := slot_le (w := w) ha
  have hn := hg.scr.nowrap
  have hhdr : 256 ≤ slot w a := by simp only [slot, hdrBytes]; omega_using []
  unfold Impl.Dsa.X86_64.Generation.loadPadded
  simp only [seqs]
  refine WP.seq (WP.mono (zeroArr_ok hg hZ hw hw31 ha) fun u ⟨hz, ho, ku⟩ => ?_)
  have hgu : Good u B Z w mi := ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside ho hhdr⟩
  have hhu : ∀ i < 32, word u.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by omega_using [hhdr, hi])) (by omega_using [hi])
  have hld : ∀ i < 32, InRegions (u.rd ++ u.wr) (off B (8 * i)) 8 := fun i hi =>
    hgu.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun v =>
      v.gpr .rsi = p ∧ v.gpr .rcx = BitVec.ofNat 64 bs.length ∧
      v.gpr .rbx = off B (slot w a) ∧ v.mem = u.mem) (by
        xrun [State.ea, hdr, hgu.rdi, hdrOff, hld sp hsp, hld sl hsl,
          hld (sArr a) (by unfold sArr; omega_using [ha]), hhu sp hsp, hhu sl hsl, hp, hl, hgu.hdr.harr a ha]) rfl)
    fun v ⟨⟨hsi, hcx, hbx, hm⟩, kv⟩ => ?_)
  have hrd : ∀ i < bs.length, InRegions (v.rd ++ v.wr) (off p i) 1 := fun i hi => by
    rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact hsrc.rd i hi
  have hbytes : ∀ i (hi : i < bs.length), v.mem (off p i) = bs[i] := by
    intro i hi
    rw [hm, ho _ (Or.inr (by have h := hsrc.out i hi; change Z ≤ ofs B (off p i) at h; omega_using [hZ, hJ, h]))]
    exact hsrc.val i hi
  refine WP.mono (loadBE_ok (hgu.scr.congr kv.2.2) hsi hcx hbx rfl hk1 hk31 rfl (by omega_using [hZ, hkw, hJ])
    hrd hbytes (fun i hi => Or.inr (by have h := hsrc.out i hi; omega_using [hZ, hkw, hJ, h]))) fun t ⟨hv, hot, kt⟩ => ?_
  have hout : Outside B (slot w a) (8 * (w + 2)) s.mem t.mem := by
    intro x hx
    rw [hot x (by omega_using [hkw, hx]), hm, ho x hx]
  refine ⟨⟨hg.scr.congr (kt.2.2.trans (kv.2.2.trans ku.2.2)),
    ((ku.trans kv).trans kt).gpr (by decide) |>.trans hg.rdi, hg.hdr.outside hout hhdr⟩,
    ?_, hout, ((ku.trans kv).trans kt).mono (by decide)⟩
  have hzero : wv t.mem B (slot w a + 8 * ((bs.length + 7) / 8)) (w - (bs.length + 7) / 8) = 0 :=
    (wv_eq_zero_iff _ _ _ _).mpr fun j hj => by
      rw [hot.word (by omega_using []) (by omega_using [hZ, hJ, hn, hj]), hm,
        show slot w a + 8 * ((bs.length + 7) / 8) + 8 * j =
          slot w a + 8 * ((bs.length + 7) / 8 + j) by omega_using []]
      exact (wv_eq_zero_iff _ _ _ _).mp hz _ (by omega_using [hj])
  rw [wv_split _ _ _ (show (bs.length + 7) / 8 + (w - (bs.length + 7) / 8) = w by omega_using [hkw]),
    hv, hzero, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Preserve the prepared Miller–Rabin modulus when loading a DSA witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem loadWitness_ok {s : State} {B p : Addr} {Z w N sp sl : Nat} {mi : BitVec 64} {bs : List Byte}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31)
    (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded aXm sp sl) s fun t =>
      ModulusReady t B Z w mi N ∧ wv t.mem B (slot w aXm) w = Spec.Rsa.os2ip bs ∧
      Frm B [(slot w aXm, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadPadded_ok h.good hd.z (by have := hd.w4; omega_using [this])
    (by have := hd.w128; omega_using [this]) (by decide : aXm < 8) hsp hsl hp hl hsrc hk1 hk31 hkw)
    fun t ⟨hg, hv, ho, hk⟩ => ?_
  have hf : Frm B [(slot w aXm, 8 * (w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨h.of_frm hd hf hk hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), hv, hf, hk⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The complete native uniform-range test preserves the original draw -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Uniform.lean`, which only this module imported.
section

/-! # The stored uniform mask agrees with the branch condition -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem saveUniform_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64} {u : Bool}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hax : s.gpr .rax = BitVec.ofNat 64 u.toNat) :
    WP isa (.block Impl.Dsa.X86_64.Generation.saveUniform) s fun t =>
      ModulusReady t B Z w mi N ∧ word t.mem B (8 * kU) = mask u ∧ t.zf = some (!u) ∧
      Frm B [(8 * kU, 8)] s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  have hst : InRegions s.wr (off B (8 * kU)) 8 :=
    h.good.scr.st (by have := hdr_lt_slot w 8 (show kU < 32 by decide); have := hd.z; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.mem = s.mem.writeW (off B (8 * kU)) (mask u) ∧ t.zf = some (!u)) (by
    xrun [Impl.Dsa.X86_64.Generation.saveUniform, State.ea, hdr, hdrOff, h.good.rdi, hst, hax,
      BitVec.and_self]
    cases u <;> exact ⟨rfl, by decide⟩) rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  have hf : Frm B [(8 * kU, 8)] s.mem t.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kU) (by decide)) (by simp)
  refine ⟨h.of_frm hd hf hk ((hk.gpr (by decide)).trans h.good.rdi)
    (by simp; decide) (by rng_disj) (by rng_disj), ?_, hz, hf, hk⟩
  rw [hm, word_writeW_self]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

def testRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aXm, 8 * (w + 2)), (slot w aTmp, 8 * w), (8 * kU, 8)]

theorem testWitness_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w) (hodd : N % 2 = 1)
    (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa Impl.Dsa.X86_64.Generation.testWitness s fun t =>
      SampleState B p Z w N mi bs t ∧ wv t.mem B (slot w aXm) w = Spec.Rsa.os2ip bs ∧
      word t.mem B (8 * kU) = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      t.zf = some (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      Frm B (testRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hXm := slot_le (w := w) (show aXm < 8 by decide)
  have hTmp := slot_le (w := w) (show aTmp < 8 by decide)
  have hz := hd.z
  have hhdr : 256 ≤ Z := by simp only [slot, hdrBytes] at hz; omega_using [hz]
  unfold Impl.Dsa.X86_64.Generation.testWitness
  simp only [seqs]
  refine WP.seq (WP.mono (loadWitness_ok h.ready hd (by decide) (by decide) h.ptr h.len h.source hk1 hk31 hkw)
    fun u ⟨hu, hxu, hfu, ku⟩ => ?_)
  have hsu := h.of_frm hd hu hfu ku (by rng_disj) (by rng_disj)
    (by simp only [List.mem_singleton, forall_eq]; omega_using [hXm, hz])
  refine WP.seq (WP.mono (witnessRange_ok hu hd hodd hxu) fun v ⟨hax, _, hv, hxv, hfv, kv⟩ => ?_)
  have hsv := hsu.of_frm hd hv hfv kv
    (by simp only [Impl.Ffdh.X86_64.Domain.sF]; rng_disj)
    (by simp only [Impl.Ffdh.X86_64.Domain.sF]; rng_disj)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · omega_using [hTmp, hz]
      · change 248 ≤ Z; omega_using [hhdr])
  have hax' : v.gpr .rax = BitVec.ofNat 64 (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)).toNat := by
    by_cases hp : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 <;>
      simpa [VG.Proof.Ffdh.X86_64.bit, hp] using hax
  refine WP.mono (saveUniform_ok hv hd hax') fun t ⟨ht, hut, hzt, hft, kt⟩ => ?_
  have hst := hsv.of_frm hd ht hft kt (by rng_disj) (by rng_disj)
    (by simp only [List.mem_singleton, forall_eq]; change 248 ≤ Z; omega_using [hhdr])
  refine ⟨hst, ?_, hut, hzt, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [hft.wv_eq (by rng_disj) (by have := h.ready.good.scr.nowrap; omega_using [hXm, hz, this])]
    exact hxv
  · exact ((hfu.mono (by simp [testRanges])).trans
      (hfv.mono (by simp [testRanges, Impl.Ffdh.X86_64.Domain.sF, kU]))).trans
        (hft.mono (by simp [testRanges]))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.Round`, which the modules that import this one used -/

section

/-! # DSA invokes the same verified windowed Miller–Rabin round as RSA -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem round_ok (M : Mont) (K : Kernel) {s : State} {B : Addr} {Z w N a : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (hr : Caller.Room s B Z)
    (ho : N % 2 = 1) (hN : 3 ≤ N) (ha : wv s.mem B (slot w aXm) w = a) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.witnessRound M.mm K.run) s fun t =>
      ModulusReady t B Z w mi N ∧
      word t.mem B (8 * kFlag) = mask (Spec.RsaKeyGen.mrIteration N
        (Spec.Rsa.splitTwos (N - 1)).1 (Spec.Rsa.splitTwos (N - 1)).2 a) ∧
      WorkFrame B (witnessRoundRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hd ho (by omega_using [hN]) ha) fun u ⟨hu, hxm, hf, hk⟩ => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hru : Caller.Room u B Z := ⟨by rw [hsp]; exact hr.size, by rw [hsp]; exact hr.disjoint⟩
  refine WP.mono (sharedRound_ok K hu hd hZ hru ho hN hxm) fun t ⟨ht, hflag, hft, kt⟩ => ?_
  rw [hsp] at hft
  exact ⟨ht, hflag, (hf.work.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.mono (fun r hr => List.mem_append_right _ hr)), (hk.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Native DSA witness selection implements RSA's exact sampler -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Dsa.Generation

theorem sampleWitness_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w) (hodd : N % 2 = 1)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ w)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length) :
    WP isa (Impl.Dsa.X86_64.Generation.sampleWitness) s fun t =>
      ModulusReady t B Z w mi N ∧
      wv t.mem B (slot w aXm) w = (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).2 ∧
      WorkFrame B (testRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.sampleWitness
  refine WP.seq (WP.mono (testWitness_ok h hd hodd (by omega_using [hlen]) hmax hkw)
    fun u ⟨hu, hxu, huu, hzu, hfu, ku⟩ => ?_)
  refine WP.ite (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1))
    (by simp [eval, hzu]) (fun hbad => ?_) (fun hgood => ?_)
  · have hb : ¬ (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hbad
    have hspec := forcedWitnessBytes_spec hlen hbits hb
    have hfl := forcedWitnessBytes_length hlen
    refine WP.seq (WP.mono (forceSample_ok hu hd hlen (by omega_using [hmax])) fun v ⟨hv, huv, hfv, kv⟩ => ?_)
    refine WP.mono (loadWitness_ok hv.ready hd (by decide) (by decide) hv.ptr hv.len hv.source
      (by rw [hfl]; omega_using [hlen]) (by rwa [hfl]) (by rwa [hfl])) fun t ⟨ht, hxt, hft, kt⟩ => ?_
    refine ⟨ht, ?_, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    · simpa only [hspec] using hxt
    · rw [hft.word_eq (by rng_disj) (by change 248 ≤ 2 ^ 64; decide), huv, huu, hspec]
      simp [hb]
    · exact ((hfu.work).trans (hfv.mono (by simp))).trans
        (hft.work.mono (by simp [testRanges]))
  · have hg : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 := by simpa using hgood
    have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
      rw [← VG.Proof.Bignum.pow256_eq]
      exact VG.Proof.Rsa.lt_of_os2ip bs
    have hspec : Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs) = (Spec.Rsa.os2ip bs, true) := by
      simp only [Spec.RsaKeyGen.witness, hbits, Nat.mod_eq_of_lt hfit, ite_eq_left hg]
    refine WP.block_nil ⟨hu.ready, ?_, ?_, hfu.work, ku⟩
    · simpa only [hspec] using hxu
    · rw [huu, hspec]; simp [hg]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.TapeSlice`, which this module and modules that import it used -/

section

/-! # The next significant witness bytes are a disjoint slice of the random tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def PrimeParams.drawStart (P : PrimeParams) (used : Nat) : Nat := used + (P.drawBytes - P.len)
def PrimeParams.drawSlice (P : PrimeParams) (used : Nat) : List Byte := (P.rand.drop (P.drawStart used)).take P.len

theorem PrimeParams.slice_length (P : PrimeParams) {used : Nat} (h : used + P.drawBytes ≤ P.rand.length) :
    (P.drawSlice used).length = P.len := by
  simp only [PrimeParams.drawSlice, PrimeParams.drawStart, List.length_take, List.length_drop]
  have := P.lenDraw
  omega_using [h, this]

theorem PrimeState.slice_source {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : Src s P.B P.Z (off P.rp (P.drawStart used)) (P.drawSlice used) :=
  source_take (source_drop h.source (P.drawStart used)) P.len

theorem PrimeParams.slice_separate (P : PrimeParams) {used : Nat}
    (hroom : used + P.drawBytes ≤ P.rand.length) :
    ∀ i < (P.drawSlice used).length, ∀ j < (P.drawSlice used).length,
      off (off P.rp (P.drawStart used)) i ≠ off P.p j := by
  intro i hi j hj he
  rw [P.slice_length hroom] at hi hj
  have hs : P.drawStart used + i < P.rand.length := by
    dsimp only [PrimeParams.drawStart]; have := P.lenDraw; omega_using [hroom, hi, this]
  have ha : off (off P.rp (P.drawStart used)) i = off P.rp (P.drawStart used + i) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  apply P.tapeBuffer (off P.p j)
  · rw [← he, ha]
    apply (Region.contains_self P.rp P.rand.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.randMax; omega_using [hs, this])]
    exact hs
  · apply (Region.contains_self P.p P.len).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := P.lenDraw; have := P.drawMax; omega_arith)]
    exact hj

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.DrawCopy`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.PreparedFrame`, which only this module used -/

section

/-! # Preserve a prepared modulus across writes to separate byte buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem ready_of_work {s t : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} {extra : List Region}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hf : WorkFrame B rs extra s.mem t.mem)
    (hx : ∀ r ∈ extra, Region.Disjoint ⟨B, Z⟩ r)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = B)
    (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (ha : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], ∀ r ∈ rs,
      slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (he : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE) :
    ModulusReady t B Z w mi N := by
  have hn := h.good.scr.nowrap
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_using [this]
  have hword : ∀ d, d + 8 ≤ 128 → word t.mem B d = word s.mem B d := by
    intro d hd'
    exact hf.word_eq (fun r hr => Or.inl (Nat.le_trans hd' (hh r hr))) (by omega_using [hz, hd']) hn hx
  have hhdr : Hdr t.mem B w mi := by
    refine ⟨(hword _ (by decide)).trans h.good.hdr.hw,
      (hword _ (by decide)).trans h.good.hdr.hminv, ?_⟩
    intro j hj
    exact (hword _ (by unfold sArr; omega_using [hj])).trans (h.good.hdr.harr j hj)
  have hread : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], slot w j + 8 * w ≤ Z := by
    intro j hj
    have hj' : j ≤ aRm1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hs := VG.Proof.Rsa.slot_mono (w := w) hj'
    omega_using [hs, hd.x]
  have hval : ∀ j ∈ [aN, aOne, aR2, aR1, aRm1], wv t.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => hf.wv_eq (ha j hj) (hread j hj) hn hx
  refine ⟨⟨h.good.scr.congr hwr, hdi, hhdr⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.word_eq (fun r hr => by have := ha aN (by simp) r hr; have := hd.w4; omega_arith)
      (by have := hread aN (by simp); have := hd.w4; omega_arith) hn hx]
    exact h.inv
  · rw [hval aN (by simp)]; exact h.n
  · rw [hval aOne (by simp)]; exact h.one
  · rw [hval aR2 (by simp)]; exact h.r2
  · rw [hval aR1 (by simp)]; exact h.r1
  · rw [hval aRm1 (by simp)]; exact h.rm1
  · have hE := aE_fits hd
    refine ⟨?_, ?_⟩
    · rw [hf.wv_eq (fun r hr => by have := he r hr; omega_using [this]) (by omega_using [hE]) hn hx]
      exact h.exponent.e
    · rw [hf.word_eq (fun r hr => by have := he r hr; omega_using [this]) (by omega_using [hE]) hn hx]
      exact h.exponent.l

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Copy a complete draw and advance its tape cursor in verified code -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawCopy_ok {s : State} {B rp op : Addr} {Z w N drawBytes used : Nat} {mi : BitVec 64} {bs : List Byte}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hlen : 2 ≤ bs.length) (hld : bs.length ≤ drawBytes) (hmax : drawBytes ≤ 1024)
    (hrp : word s.mem B (8 * kRand) = rp) (hop : word s.mem B (8 * kOut) = op)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hdl : word s.mem B (8 * kLen) = BitVec.ofNat 64 drawBytes)
    (hll : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z (off rp (used + (drawBytes - bs.length))) bs)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hout : Region.Disjoint ⟨B, Z⟩ ⟨op, bs.length⟩)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off rp (used + (drawBytes - bs.length))) i ≠ off op j) :
    WP isa Impl.Dsa.X86_64.Generation.drawCopy s fun t =>
      ModulusReady t B Z w mi N ∧ Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + drawBytes) ∧
      WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_arith
  unfold Impl.Dsa.X86_64.Generation.drawCopy
  simp only [seqs]
  refine WP.seq (WP.mono (drawCopyArgs_ok h.good hd.z hld hrp hop hus hdl hll)
    fun u ⟨h15, hsi, hdi, hcx, hdx, hmu, ku⟩ => ?_)
  have hfu : Frm B [(8 * kUsed, 8)] s.mem u.mem := by
    rw [hmu]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kUsed) (by decide)) (by simp)
  have hsrcu := hsrc.congrK (fun x hx => hfu x (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    right; change 208 ≤ ofs B x; omega_arith)) ku
  have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := fun i hi => by rw [ku.2.2]; exact hwr i hi
  have hbu : ∀ i < bs.length, u.mem (off (off rp (used + (drawBytes - bs.length))) i) = bs.getD i 0 := by
    intro i hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hsrcu.val i hi
  refine WP.seq (WP.mono (copyBytes_ok ⟨hlen, by omega_arith⟩ hsi hdi hcx hdx hsrcu.rd hwu hbu hsep)
    fun v ⟨hbv, hfv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = v.mem) (by
    xrun [(kv.gpr (by decide) : v.gpr .r15 = u.gpr .r15).trans h15]) rfl)
    fun t ⟨⟨hdit, hmt⟩, kt⟩ => ?_
  have k := (ku.trans kv).trans kt
  have hfvt : WorkFrame B [] [⟨op, bs.length⟩] u.mem t.mem := by
    intro x hx _
    rw [hmt]
    apply hfv
    intro i hi he
    subst x
    apply hx ⟨op, bs.length⟩ (by simp)
    apply (Region.contains_self op bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64)]
    exact hi
  have hft : WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem :=
    hfu.work.trans (hfvt.mono (by simp))
  have hex : ∀ r ∈ [⟨op, bs.length⟩], Region.Disjoint ⟨B, Z⟩ r := by simpa using hout
  refine ⟨ready_of_work h hd hft hex k.2.2 hdit (by simp; decide) (by rng_disj) (by rng_disj),
    by rw [hmt]; exact hbv, ?_, hft, ?_⟩
  · rw [hfvt.word_eq (by simp) (by change 208 ≤ Z; omega_arith) h.good.scr.nowrap hex,
      hmu, word_writeW_self]
  · refine ⟨fun r hr => ?_, k.2⟩
    by_cases he : r = .rdi
    · subst r; exact hdit.trans h.good.rdi.symm
    · exact k.gpr (by revert hr he; cases r <;> decide)

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # A whole tape draw supplies the sampler and preserves all loop arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawBuffer_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) (hroom : used + P.drawBytes ≤ P.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.drawCopy) s fun t =>
      PrimeState P mi (used + P.drawBytes) t ∧
      SampleState P.B P.p P.Z P.w P.N mi (P.drawSlice used) t ∧
      WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlen := P.slice_length hroom
  have hs : Src s P.B P.Z (off P.rp (used + (P.drawBytes - (P.drawSlice used).length))) (P.drawSlice used) := by
    rw [hlen]; exact h.slice_source
  have hw : ∀ i < (P.drawSlice used).length, InRegions s.wr (off P.p i) 1 := by
    rw [hlen]; exact h.writable
  have hout : Region.Disjoint ⟨P.B, P.Z⟩ ⟨P.p, (P.drawSlice used).length⟩ := by
    rw [hlen]; exact P.bufferSeparate
  have hd := drawCopy_ok h.ready P.dims (by rw [hlen]; exact P.len2)
    (by rw [hlen]; exact P.lenDraw) P.drawMax h.rand h.ptr h.used h.draw (by rw [hlen]; exact h.len) hs hw hout (by simpa only [hlen, PrimeParams.drawStart] using P.slice_separate hroom)
  rw [hlen] at hd
  refine WP.mono hd fun t ⟨ht, hbytes, hused, hf, hk⟩ => ?_
  have hft : WorkFrame P.B [(8 * kUsed, 8)] (primeExtras P) s.mem t.mem := by
    intro x hx hr
    exact hf x (fun r hmem => hx r (by
      simp only [List.mem_singleton] at hmem; subst r; simp [primeExtras])) hr
  have hzt : 256 ≤ P.Z := P.z256
  have hpt : PrimeState P mi (used + P.drawBytes) t := h.advance ht hused hft hk
    (by simp only [List.mem_singleton, forall_eq]; change 208 ≤ P.Z; omega_using [hzt])
    (by
      intro k hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  refine ⟨hpt, ⟨ht, hpt.ptr, ?_, ?_, ?_⟩, hft, hk⟩
  · rw [hlen]; exact hpt.len
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => P.bufferOutside i (by rwa [hlen] at hi)⟩
    · obtain ⟨r, hr, hc⟩ := hpt.writable i (by rwa [hlen] at hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have hb := bytesAt_read t.mem P.p (n := P.len) (i := i) (by rwa [hlen] at hi)
      simpa only [hbytes] using hb
  · rw [hlen]; exact hpt.writable

end VG.Proof.Dsa.X86_64.Generation
