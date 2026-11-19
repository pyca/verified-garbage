module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SampleRound
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.WitnessRange
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep: its symbolic execution names RegUpd lemmas by path, which shake does not see
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Bignum.ExternalWords
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
meta import VerifiedGarbage.Proof.MillerRabin.Representation
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices

/-! ### `Dsa.AArch64.Generation.DrawRound`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.DrawBuffer`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.DrawCopyArgs`, which this module and modules that import it used -/

section

/-! Advance the entropy cursor exactly once before copying the draw's suffix. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem drawCopyArgs_ok {s : State} {B rp op : Addr} {Z w used len drawBytes : Nat}
    (h : Ws s B Z w) (hlen : len ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) s fun t =>
      t.gpr .x17 = B ∧ t.gpr .x12 = rp + BitVec.ofNat 64 (used + (drawBytes - len)) ∧
      t.gpr .x2 = op ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧
      t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes)) ∧
      Keep [.x2, .x3, .x9, .x12, .x17] s t := by
  refine WP.mono (WP.keep [.x2, .x3, .x9, .x12, .x17] (Q := fun t =>
    t.gpr .x17 = B ∧ t.gpr .x12 = rp + BitVec.ofNat 64 (used + (drawBytes - len)) ∧
    t.gpr .x2 = op ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧
    t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) ?_ rfl rfl rfl)
    fun t ⟨ht, hk⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, hk⟩
  have hz := h.scr.nowrap
  have h256 := h.h256
  have hout (v : BitVec 64) : (s.mem.writeW (off B (8 * kUsed)) v).readW (off B (8 * kOut)) 64 = op :=
    ((writeW_outside _ B v (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_using [])).word
      (by decide) (by simp only [kOut, sFn]; omega_using [])).trans ho
  unfold Impl.Dsa.AArch64.Generation.drawCopyArgs
  brun [h.x0, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
    hdr_enc (show kOut < 32 by decide), hp, hu, hout,
    h.scr.ld (d := 8 * kRand) (by simp only [kRand, sFn]; omega_using [h256]),
    h.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_using [h256]),
    h.scr.ld (d := 8 * kOut) (by simp only [kOut, sFn]; omega_using [h256]),
    h.scr.st (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_using [h256]),
    hmax, show drawBytes - len < 4096 by omega_using [hmax]]
  simp only [BitVec.ofNat_add_ofNat]
  have hv : (BitVec.ofNat 16 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hlen, hmax]
  simp [hv]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.ModulusHeader`, which this module and modules that import it used -/

section

/-! Policy-header writes leave the prepared modulus and exponent intact. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem ModulusReady.write_header {s : State} {B : Addr} {Z w N i : Nat} (v : BitVec 64)
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hi : i ∈ [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 31]) :
    ModulusReady {s with mem := s.mem.writeW (off B (8 * i)) v} B Z w N := by
  have hi32 : i < 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega_using [hi]
  have hf : Frm B [(8 * i, 8)] s.mem (s.mem.writeW (off B (8 * i)) v) :=
    Frm.of_outside (writeW_outside _ B v (by omega_using [hi32])) (by simp)
  have hk : Keep [] s {s with mem := s.mem.writeW (off B (8 * i)) v} :=
    ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_
  · intro r hr; rw [List.mem_singleton.mp hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact KMut.hdr (by decide)
  · intro a ha r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes]; omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes, aE]; omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.TapeSlice`, which this module and modules that import it used -/

section

/-! # The next significant witness bytes are a disjoint slice of the random tape -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.AArch64

def PrimeParams.drawStart (P : PrimeParams) (used : Nat) : Nat := used + (P.drawBytes - P.len)
def PrimeParams.drawSlice (P : PrimeParams) (used : Nat) : List Byte := (P.rand.drop (P.drawStart used)).take P.len

theorem PrimeParams.slice_length (P : PrimeParams) {used : Nat} (h : used + P.drawBytes ≤ P.rand.length) :
    (P.drawSlice used).length = P.len := by
  simp only [PrimeParams.drawSlice, PrimeParams.drawStart, List.length_take, List.length_drop]
  have := P.lenDraw
  omega_using [h, this]

theorem PrimeState.slice_source {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hroom : used + P.drawBytes ≤ P.rand.length) : Src s P.B P.Z (off P.rp (P.drawStart used)) (P.drawSlice used) :=
  source_slice h.source (by have := P.lenDraw; dsimp only [PrimeParams.drawStart]; omega_using [hroom, this])

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

end VG.Proof.Dsa.AArch64.Generation

end

end

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
    (by rw [hlen]; exact P.lenDraw) (by have := P.drawMax; omega_using [this])
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
    (by simp only [List.mem_singleton, forall_eq]; change 224 ≤ P.Z; omega_using [hzt])
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

end

end

/-! ### `Dsa.AArch64.Generation.Sample`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.PublicKernel`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.PublicRoundCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PublicRound`, which only this module used -/

section

/-!
# DSA parameter generation on AArch64: the round for public candidates

`publicSel` does what the masked selection does (`publicSel_selOK`), so the
round with it is the shared round's (`publicRound_correct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aXm)

/-- The base of entry `d`, from `T_0`'s and `d` strides. -/
theorem entry_base (B : Addr) (w d : Nat) :
    off B (slot w aT0) + BitVec.ofNat 64 d * BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (aT0 + d)) := by
  rw [← BitVec.ofNat_mul, off_add]
  congr 1
  unfold slot
  rw [Nat.add_mul]
  omega_using []

/-- The selection's head: the bases of `aXm` and of entry `d`. -/
theorem publicSelHead_ok {s : State} {B : Addr} {Z w d : Nat} (h : Ws s B Z w)
    (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 d) :
    WP isa (.block (ws ++ base aXm .x17 ++ base aT0 .x16 ++
      ([ldh .x9 kG, .mul .x .x9 .x9 .x11, .add .x .x16 .x16 .x9] : List Instr))) s fun t =>
      (t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.gpr .x17 = off B (slot w aXm) ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.x9, .x11, .x12, .x16, .x17] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aXm .x17 h0₁ h11) fun s₂ ⟨⟨h17, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aT0 .x16 ((k₂.gpr .x0 (by decide)).trans h0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (WP.keep [.x9, .x16] (Q := fun t => t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kG < 32 by decide),
      (hs.congr k13.wr).ld (d := 8 * kG) (by simp only [kG]; omega_using [h256]), (by rw [m₃, m₂, m₁]; exact hG :
        word s₃.mem B (8 * kG) = BitVec.ofNat 64 d), h16, (k₂.trans k₃ |>.gpr .x11 (by decide)).trans h11,
      entry_base])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16t, hm⟩, k⟩ => ?_
  exact ⟨⟨h16t, (k₃.trans k |>.gpr .x17 (by decide)).trans h17,
    (k₂.trans k₃ |>.trans k |>.gpr .x12 (by decide)).trans h12, by rw [hm, m₃, m₂, m₁]⟩,
    (k13.trans k).mono (by decide)⟩

/-- `publicSel`: `[aXm] := T_d` for the digit `d` in `kG`, as `mrSel_ok`. -/
theorem publicSel_selOK : SelOK publicSel := by
  intro s B Z w d h hEZ hd hG
  have hn := h.scr.nowrap
  have hT := tab_fits (w := w) hEZ hd
  have hX := tab_sep_xm w (j := d)
  have hXZ := h.sl (show aXm < 16 by decide)
  simp only [publicSel, seqs]
  refine WP.seq (WP.mono (publicSelHead_ok h hG) fun s₁ ⟨⟨h16, h17, h12, m₁⟩, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.wr
  refine WP.mono (copyWords_ok h16 h17 h12 (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [hn, hXZ])
    (fun i hi => hs₁.ld (by omega_using [hT, hi])) (fun i hi => hs₁.st (by omega_using [hXZ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hn, hT, hi, hb])]; omega_using [hX, hi, hb]))
    fun t ⟨hv, _, o, _, _, k₂⟩ => ?_
  rw [m₁] at hv o
  exact ⟨hv, o, h.scr.congr (k₁.trans k₂).wr, (k₁.trans k₂).mono (by decide)⟩

theorem publicSel_ne : publicSel ≠ [] := by unfold publicSel; exact List.cons_ne_nil _ _

theorem publicWin_winOK (M : Mont) : WinOK (publicWin M.mm) := mrWinS_winOK publicSel_ne publicSel_selOK M

/-- The round for public candidates meets the shared round's contract. -/
theorem publicRound_correct (M : Mont) (s : State) (h : roundContract.pre s) :
    ∃ tr t, Exec isa (publicRound M.mm) s tr t ∧ abiPreserved s t ∧ roundContract.post s t :=
  roundW_correct (publicWin_winOK M) M s h

end VG.Proof.Dsa.AArch64.Generation

end

end

/-!
# DSA parameter generation on AArch64: constant time of the round for public candidates

Runs of `publicRound` leak the same when they agree on the working space
and on the candidate: the exponent's windows are then the same, and with
them the table entry each window reads (`publicSel_ct`, its address pinned
by correctness). Everything else is the shared round's, piece by piece
(`Proof/RsaKeyGen/AArch64/CTMrTab.lean`, `CTMrExp.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The public data: the working space, and the candidate. -/
abbrev CPub := WsP × Nat

/-- Word `w − 1 − j` of the candidate's exponent. -/
def pubWord (c w j : Nat) : BitVec 64 := BitVec.ofNat 64 (mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64)

theorem pubWord_toNat (c w j : Nat) : (pubWord c w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
  rw [pubWord, BitVec.toNat_ofNat, Nat.mod_mod]

/-- After `i` windows of word `w − 1 − j` (`WinP`), for the candidate of the public data. -/
def WinPc (q : CPub × Nat) (i : Nat) (s : State) : Prop :=
  4 ≤ q.1.1.w ∧ q.1.1.w ≤ 128 ∧ slot q.1.1.w aE + 8 * (q.1.1.w + 2) ≤ q.1.1.Z ∧ q.2 < q.1.1.w ∧ ∃ bm b s₀,
    WinInv q.1.1.B q.1.1.Z q.1.1.w q.1.2 bm b (q.1.1.w - q.2) (pubWord q.1.2 q.1.1.w q.2) s₀ i s ∧
    ECtx s₀.mem q.1.1.B q.1.1.w q.1.2 ∧ q.1.2 % 2 = 1 ∧ 1 < q.1.2

theorem WinPc.winP {q : CPub × Nat} {i : Nat} {s : State} (h : WinPc q i s) : WinP (q.1.1, q.2) i s := by
  obtain ⟨h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  exact ⟨h4, h128, hEZ, hj, _, bm, b, s₀, _, hI, pubWord_toNat _ _ _, hE, hodd, hc1⟩

/-- The digit of window `i` of word `w − 1 − j`. -/
def pubDigit (r : (CPub × Nat) × Nat) : Nat :=
  ((pubWord r.1.1.2 r.1.1.1.w r.1.2 <<< (4 * r.2)) >>> 60).toNat

/-- After a window's squarings: `WW`, and the word in `kV`. -/
def WVc (r : (CPub × Nat) × Nat) (s : State) : Prop :=
  WW r.1.1.1 s ∧ word s.mem r.1.1.1.B (8 * kV) = pubWord r.1.1.2 r.1.1.1.w r.1.2 <<< (4 * r.2)

/-- After the digit: `WW`, and the public digit in `kG`. -/
def WDc (r : (CPub × Nat) × Nat) (s : State) : Prop :=
  WW r.1.1.1 s ∧ word s.mem r.1.1.1.B (8 * kG) = BitVec.ofNat 64 (pubDigit r)

theorem winSq_ok (M : Mont) {r : (CPub × Nat) × Nat} {s : State} (h : r.2 < 16 ∧ WinPc r.1 r.2 s) :
    WP isa (seqs (mrSq M.mm ++ (mrSq M.mm ++ (mrSq M.mm ++ mrSq M.mm)))) s (WVc r) := by
  obtain ⟨-, h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  have hn := hI.ctx.ws.scr.nowrap
  refine WP.mono (sq4_ok M h128 hI.ctx hodd hc1 (st := (_, _)) hI.y hI.flag) fun t ⟨hct, hYt, _, hf, k⟩ => ?_
  have hT : TabOK t.mem r.1.1.1.B r.1.1.1.w r.1.1.2 b :=
    hI.tab.of_low (hf.mono (sqRanges_win _)) (winRanges_low _) hEZ hn
  refine ⟨⟨h4, h128, hEZ, _, bm, hct, hodd, hc1, tab_lt hT (by omega_using [hc1]),
    by rw [hYt]; exact Nat.mod_lt _ (by omega_using [hc1])⟩, ?_⟩
  rw [hf.word_eq (by unfold sqRanges; w_disj) (by simp only [kV, kT0, sCnt, sFn]; omega_arith)]
  exact hI.v

theorem winDigitC_ok {r : (CPub × Nat) × Nat} {s : State} (h : WVc r s) :
    WP isa (.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]) s (WDc r) :=
  WP.mono (winDigit_ok h.1.ws h.2) fun t ⟨hm, k⟩ =>
    ⟨h.1.of_frm (rs := [(8 * kG, 8)]) (by rw [hm]; exact frm_hdr (show kG < 32 by decide) _ (by simp))
      (by simp [wkRanges]) k (by decide), by rw [hm, word_writeW_self]; rfl⟩

/-- The selection's registers, after its first block. -/
def selValC (r : (CPub × Nat) × Nat) : Reg → BitVec 64
  | .x0 => r.1.1.1.B
  | .x12 => BitVec.ofNat 64 r.1.1.1.w
  | .x16 => off r.1.1.1.B (slot r.1.1.1.w (aT0 + pubDigit r))
  | _ => off r.1.1.1.B (slot r.1.1.1.w aXm)

/-- The selection: its first block pins the entry's base, by the public digit. -/
theorem publicSel_ct : RelCT isa (Two WDc) (seqs publicSel) (Two WWX) := by
  have e : seqs publicSel = Code.seq _ _ := rfl
  rw [e]
  refine (pin_ct (Ψ := fun r s => WWX r.1.1.1 s) [.x0] [.x0, .x12, .x16, .x17] selValC
    (pins_ws' (fun r : (CPub × Nat) × Nat => r.1.1.1.B) (fun r => r.1.1.1.Z) (fun r => r.1.1.1.w)
      fun _ _ h => h.1.ws)
    (by taint_decide) (fun r s h => ?_) (by taint_decide) fun r s h => ?_).mono (fun _ _ h => h)
      (fun _ _ ⟨r, h₁, h₂, hsp⟩ => ⟨r.1.1.1, h₁, h₂, hsp⟩)
  · refine WP.mono (publicSelHead_ok h.1.ws h.2) fun t ⟨⟨h16, h17, h12, _⟩, k⟩ x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans h.1.ws.x0
    · exact h12
    · exact h16
    · exact h17
  · rw [← e]
    obtain ⟨⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩, hG⟩ := h
    have hd : pubDigit r < 16 := top_nibble _
    have hn := hc.ws.scr.nowrap
    refine WP.mono (publicSel_selOK hc.ws hEZ hd hG) fun t ⟨hv, ho, _, k⟩ => ?_
    have hf : Frm r.1.1.1.B [(slot r.1.1.1.w aXm, 8 * (r.1.1.1.w + 2))] s.mem t.mem :=
      Frm.of_outside (ho.mono (o' := slot r.1.1.1.w aXm) (n' := 8 * (r.1.1.1.w + 2)) (Nat.le_refl _)
        (by omega_arith)) (by simp)
    obtain ⟨-, -, -, c', bm', hc', hodd', hc1', hT', hY'⟩ :=
      WW.of_frm ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ hf (by simp [wkRanges]) k (by decide)
    have hN := hc.ws.sl (show aN < 16 by decide)
    have hn' : c' = c := by rw [← hc'.n, ← hc.n, hf.wv_eq (by w_disj) (by omega_arith)]
    subst hn'
    exact ⟨h4, h128, hEZ, c', bm', hc', hodd', hc1', hT', hY', by rw [hv]; exact hT _ hd⟩

/-- A window leaks the same in runs that agree on the working space and the
candidate. -/
theorem publicWin_ct (M : Mont) :
    RelCT isa (Two fun (r : (CPub × Nat) × Nat) s => r.2 < 16 ∧ WinPc r.1 r.2 s) (seqs (publicWin M.mm))
      fun _ _ => True := by
  rw [publicWin, mrWinS_eq]
  refine RelCT.seqs_append (by simp [mrSq]) (by simp) (RelCT.seq (two_post (Ψ := WVc)
    (two_map (fun r : (CPub × Nat) × Nat => r.1.1.1) (fun r _ h => winP_ww (p := (r.1.1.1, r.1.2)) h.2.winP)
      ((sq4_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun _ _ h => winSq_ok M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [publicSel_ne]) (RelCT.seq (two_post (Ψ := WDc)
    (two_map (fun r : (CPub × Nat) × Nat => r.1.1.1) (fun _ _ h => h.1)
      (digit_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) fun _ _ h => winDigitC_ok h) ?_)
  exact RelCT.seqs_append publicSel_ne (by simp) (RelCT.seq publicSel_ct (winRest_ct M))

/-! ## The exponentiation -/

/-- Before the exponentiation (`E0`), for the candidate of the public data. -/
def E0c (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧ ∃ bm b, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧
    TabOK s.mem p.1.B p.1.w p.2 b ∧ ECtx s.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2 ∧
    wv s.mem p.1.B (slot p.1.w aY) p.1.w = 2 ^ (64 * p.1.w) % p.2

/-- After `j` words (`WI`), for the candidate of the public data. -/
def WIc (p : CPub) (j : Nat) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧ ∃ bm b s₀,
    WordInv p.1.B p.1.Z p.1.w p.2 bm b s₀ j s ∧ ECtx s₀.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2

theorem WIc.wi {p : CPub} {j : Nat} {s : State} (h : WIc p j s) : WI p.1 j s := by
  obtain ⟨h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  exact ⟨h4, h128, hEZ, _, bm, b, s₀, hI, hE, hodd, hc1⟩

/-- The start of a word: its word is the public data's. -/
theorem pubWordHead_ct : RelCT isa (Two fun (q : CPub × Nat) s => q.2 < q.1.1.w ∧ WIc q.1 q.2 s)
    (.block (ws ++ base aE .x16 ++ wordHead)) (Two fun q s => 0 < 16 ∧ WinPc q 0 s) :=
  two_post (two_map (fun q : CPub × Nat => (q.1.1, q.2)) (fun _ _ h => ⟨h.1, h.2.wi⟩)
      (wordHead_ct.mono (fun _ _ h => h) fun _ _ _ => trivial))
    fun q s ⟨hj, h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩ => by
      have hW : (wordE s.mem q.1.1.B q.1.1.w q.2).toNat =
          mrE q.1.2 / 2 ^ (64 * (q.1.1.w - q.2 - 1)) % 2 ^ 64 := by
        have hE' : ECtx s.mem q.1.1.B q.1.1.w q.1.2 :=
          hE.of_low hI.frm (expRanges_low q.1.1.w) hEZ hI.ctx.ws.scr.nowrap
        rw [← hE'.e]; exact word_of_wv s.mem q.1.1.B (slot q.1.1.w aE) q.1.1.w (by omega_using [hj])
      have e : wordE s.mem q.1.1.B q.1.1.w q.2 = pubWord q.1.2 q.1.1.w q.2 :=
        BitVec.eq_of_toNat_eq (by rw [hW, pubWord_toNat])
      refine WP.mono (wordStart_ok hEZ hj hI) fun t hB => ?_
      rw [e] at hB
      exact ⟨by decide, h4, h128, hEZ, hj, bm, b, s₀, hB, hE, hodd, hc1⟩

/-- The windows of a word. -/
theorem pubWins_ct (M : Mont) : RelCT isa (Two fun (q : CPub × Nat) s => 0 < 16 ∧ WinPc q 0 s)
    (.loop (seqs (publicWin M.mm)) (.nonzero .x .x3)) (Two fun q s => WinPc q 16 s) := by
  refine two_loop (Φ := WinPc) (fun _ => 16) (publicWin_ct M) ?_
  rintro q i s hi ⟨h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩
  exact WP.mono (mrWinStepW_ok (publicWin_winOK M) h128 hEZ hodd hc1 (by omega_using [hj]) (by omega_using [])
    (pubWord_toNat _ _ _) hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h128, hEZ, hj, bm, b, s₀, hI', hE, hodd, hc1⟩,
      fun e => e ▸ ⟨h4, h128, hEZ, hj, bm, b, s₀, hI', hE, hodd, hc1⟩⟩

/-- One word. -/
theorem pubWordLoop_ct (M : Mont) : RelCT isa (Two fun (q : CPub × Nat) s => q.2 < q.1.1.w ∧ WIc q.1 q.2 s)
    (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (publicWin M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) fun _ _ => True :=
  RelCT.seq pubWordHead_ct (RelCT.seq (pubWins_ct M) (two_taint [.x0]
    (pins_ws' (fun q : CPub × Nat => q.1.1.B) (fun q => q.1.1.Z) (fun q => q.1.1.w)
      fun q _ h => (winP_ww (p := (q.1.1, q.2)) h.winP).ws) (by taint_decide)))

/-- The exponentiation leaks the same in runs that agree on the working
space and the candidate. -/
theorem publicExpLoop_ct (M : Mont) :
    RelCT isa (Two E0c) (seqs (mrExpLoopW (publicWin M.mm) M.mm)) fun _ _ => True := by
  rw [mrExpLoopW_eq]
  refine RelCT.seqs_append (by simp) (by simp [mrLast]) (RelCT.seq (?_ : RelCT isa (Two E0c) _ (Two WLast))
    (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (j := 1) (by decide))
      (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (j := 2) (by decide))
        ((mrLast_ct M (j := 3) (by decide)).mono (fun _ _ h => h) fun _ _ _ => trivial))))
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.1.w ∧ WIc p 0 s) [.x0]
    (pins_ws' (fun p : CPub => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide)
    fun p s ⟨h4, h128, hEZ, bm, b, hc, hT, hE, hodd, hc1, hY⟩ => WP.mono (expStart_ok hEZ hc hT hY) fun t hI =>
      ⟨by omega_using [h4], h4, h128, hEZ, bm, b, s, hI, hE, hodd, hc1⟩) ?_
  refine (two_loop (Φ := WIc) (Ψ := fun p s => WLast p.1 s) (fun p => p.1.w) (pubWordLoop_ct M) ?_).mono
    (fun _ _ h => h) (fun _ _ ⟨p, h₁, h₂, hsp⟩ => ⟨p.1, h₁, h₂, hsp⟩)
  rintro p j s hj ⟨h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩
  refine WP.mono (mrWordW_ok (publicWin_winOK M) h128 hEZ
    (hE.of_low hI.frm (expRanges_low p.1.w) hEZ hI.ctx.ws.scr.nowrap) hodd hc1 hj hI)
    fun t ⟨hI', hz⟩ => ⟨eval_cnt .x3 hj hz, fun _ => ⟨h4, h128, hEZ, bm, b, s₀, hI', hE, hodd, hc1⟩, fun _ => ?_⟩
  have hn := hI'.ctx.ws.scr.nowrap
  exact ⟨⟨h4, h128, hEZ, _, bm, hI'.ctx, hodd, hc1, tab_lt hI'.tab (by omega_using [hodd]),
    by rw [hI'.y]; exact Nat.mod_lt _ (by omega_using [hodd])⟩,
    by rw [hI'.ctx.n]; exact hE.of_low hI'.frm (expRanges_low p.1.w) hEZ hn, _, hI'.flag⟩

/-! ## The round -/

/-- A prepared input (`CorePre`), for the candidate of the public data. -/
def CorePreC (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧
    ∃ bm b, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧ ECtx s.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2 ∧
      wv s.mem p.1.B (slot p.1.w aXm) p.1.w = Spec.Rsa.powMod b 1 p.2 * 2 ^ (64 * p.1.w) % p.2

theorem publicCore_ct (M : Mont) :
    RelCT isa (Two CorePreC) (seqs (preparedRoundW (publicWin M.mm) M.mm)) fun _ _ => True := by
  unfold preparedRoundW
  refine RelCT.seqs_append (by simp [tabBuild]) (by simp [mrExpLoopW]) (RelCT.seq (two_post (Ψ := E0c)
    (two_map (fun p : CPub => p.1) (fun p s h => ?_)
      ((tabBuild_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) ?_) (publicExpLoop_ct M))
  · obtain ⟨h4, hw, hEZ, bm, b, hc, hE, hodd, hc1, hX⟩ := h
    exact ⟨h4, hw, hEZ, _, bm, b, hc, hodd, hc1, hX⟩
  · rintro p s ⟨h4, hw, hEZ, bm, b, hc, hE, hodd, hc1, hX⟩
    have hEn : p.1.B.toNat + slot p.1.w aE + 8 * (p.1.w + 1) ≤ 2 ^ 64 := by
      have := hc.ws.scr.nowrap
      omega_arith
    exact WP.mono (tabBuild_ok M hw hEZ hc hodd hc1 hX) fun t ⟨ht, htab, hy, hf, hk⟩ =>
      ⟨h4, hw, hEZ, bm, b, ht, htab,
        hE.of_frm hf (fun r hr => Or.inr (VG.Proof.MillerRabin.AArch64.tab_below_exp p.1.w r hr)) hEn, hodd, hc1, hy⟩

theorem publicCore_base (M : Mont) (p : CPub) (s : State) (h : CorePreC p s) :
    WP isa (seqs (preparedRoundW (publicWin M.mm) M.mm)) s fun t => t.gpr .x0 = p.1.B := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, hE, hodd, h1, hX⟩ := h
  have hfit : mrE p.2 < 16 ^ (16 * p.1.w) := by
    change mrE p.2 < (2 ^ 4) ^ (16 * p.1.w)
    rw [← Nat.pow_mul, show 4 * (16 * p.1.w) = 64 * p.1.w by omega_arith]
    have hn : p.2 < 2 ^ (64 * p.1.w) := hc.n ▸ wv_lt s.mem p.1.B (slot p.1.w aN) p.1.w
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)
  exact WP.mono (VG.Proof.MillerRabin.AArch64.coreW_ok (publicWin_winOK M) M h128 hEZ hc hE hodd
    (by omega_arith) hfit hX) fun t ⟨ht, _⟩ => ht.ws.x0

theorem publicRound_rel (M : Mont) : RelCT isa (Two CorePreC) (publicRound M.mm) fun _ _ => True := by
  change RelCT isa _ (.seq (seqs (preparedRoundW (publicWin M.mm) M.mm))
    (.block VG.Impl.MillerRabin.AArch64.returnFlag)) _
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = p.1.B) (publicCore_ct M) (publicCore_base M)) ?_
  exact two_taint [.x0] (fun p s t hs ht r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hs.trans ht.symm) (by unfold VG.Impl.MillerRabin.AArch64.returnFlag; taint_decide)

/-- The candidate of a prepared workspace. -/
def candidateOf (s : State) : Nat :=
  Proof.Rsa.Mont.numAt s.mem (s.gpr .x0) (Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)) 0

/-- What runs of the round for public candidates may agree on: the shared
round's (`roundPub`), and the candidate. -/
def publicRoundPub (s t : State) : Prop :=
  VG.Proof.MillerRabin.AArch64.roundPub s t ∧ candidateOf s = candidateOf t

/-- The shared round's contract, with the candidate public too. -/
def publicRoundContract : Contract isa where
  pre := VG.Proof.MillerRabin.AArch64.roundPre
  post := VG.Proof.MillerRabin.AArch64.roundPost
  pub := publicRoundPub

private def coreSpace (s : State) : VG.Proof.Bignum.AArch64.Ws :=
  ⟨s.gpr .x0, (s.gpr .x1).toNat * 8, Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)⟩

private theorem initial_core {s : State} (h : VG.Proof.MillerRabin.AArch64.roundPre s) :
    CorePreC (coreSpace s, candidateOf s) s := by
  unfold candidateOf
  obtain ⟨h4, h128, hEZ, bm, hc, hE, hodd, h3, hx⟩ := VG.Proof.MillerRabin.AArch64.initial_ctx h
  obtain ⟨b, -, hb⟩ := VG.Proof.MillerRabin.witness_exists (coprime_pow2 hodd _) hx
  refine ⟨h4, h128, hEZ, bm, b, hc, hE, hodd, by omega_arith, ?_⟩
  simpa only [coreSpace, VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb

/-- The round for public candidates leaks only the working space's place and
size, and the candidate. -/
theorem publicRound_ct (M : Mont) :
    ConstantTime isa VG.Proof.MillerRabin.AArch64.roundPre publicRoundPub (publicRound M.mm) := by
  apply RelCT.constantTime
  refine (publicRound_rel M).mono (fun s t ⟨hs, ht, hp⟩ => ?_) (fun _ _ h => h)
  obtain ⟨⟨hsp, h0, h1, hw⟩, hc⟩ := hp
  have hL : (coreSpace s, candidateOf s) = (coreSpace t, candidateOf t) := by
    unfold coreSpace
    rw [hw, h0, h1, hc]
  exact ⟨(coreSpace s, candidateOf s), initial_core hs, hL.symm ▸ initial_core ht, hsp⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-!
# DSA parameter generation on AArch64: the kernel of its round

`PublicKernel` is `MillerRabin.AArch64.Kernel` for a public candidate: its
runs leak the same when they agree on the working space and the candidate
(`BeforeC`), not on the working space alone. `PublicKernel.called` calls
`publicRound` as `Kernel.called` calls the shared round.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Proof.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)

/-- Before the call (`Caller.Before`), for the candidate of the public data. -/
def BeforeC (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧
    ∃ bm b : Nat, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧ ECtx s.mem p.1.B p.1.w p.2 ∧
      p.2 % 2 = 1 ∧ 3 ≤ p.2 ∧ wv s.mem p.1.B (slot p.1.w aXm) p.1.w = b % p.2 * 2 ^ (64 * p.1.w) % p.2

theorem BeforeC.before {p : CPub} {s : State} (h : BeforeC p s) : Before p.1 s := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  exact ⟨h4, h128, hEZ, _, bm, b, hc, he, ho, h3, hx⟩

/-- After the registers are saved (`Caller.Ready`). -/
def ReadyC (p : CPub) (s : State) : Prop :=
  BeforeC p s ∧ s.gpr .x19 = p.1.B ∧ s.gpr .x1 = BitVec.ofNat 64 (callWords p.1.w)

theorem ReadyC.ready {p : CPub} {s : State} (h : ReadyC p s) : Ready p.1 s := ⟨h.1.before, h.2⟩

theorem save_readyC {p : CPub} {s : State} (h : BeforeC p s) : WP isa (.block save) s (ReadyC p) := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good.1 hc.good.2 h128) ?_
  rintro t ⟨hm, h19, h1, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hEZ hm hk
  refine ⟨⟨h4, h128, hEZ, bm, b, hct, het, ho, h3, ?_⟩, h19, h1⟩
  rw [hm, (saved_outside s p.1.B p.1.w (by
    have hz : slot p.1.w 16 ≤ p.1.Z := hc.ws.hZ
    have hn := hc.ws.scr.nowrap
    simp only [pad, slot, hdrBytes, aOne] at hz ⊢
    omega_arith)).wv (Or.inl (by simp only [pad, slot, hdrBytes, aOne, aXm]; omega_arith))
      (by
        have hsX := slot_le (w := p.1.w) (show aXm < 8 by decide)
        have hsZ := hc.good.2
        have hsN := hc.ws.scr.nowrap
        omega_arith)]
  exact hx

/-- The candidate the call's callee sees. -/
theorem ready_candidate {p : CPub} {s : State} (h : ReadyC p s) :
    candidateOf (narrowed s p.1.B p.1.w) = p.2 := by
  have h0 : (narrowed s p.1.B p.1.w).gpr .x0 = p.1.B := (s.callEntry_gpr (by decide)).trans (ready_base h.ready)
  obtain ⟨⟨_, _, _, bm, b, hc, _⟩, _⟩ := h
  have hw : Proof.Rsa.Mont.wOf s.mem p.1.B = p.1.w := ctx_width hc
  unfold candidateOf
  rw [h0]
  change Proof.Rsa.Mont.numAt s.mem p.1.B (Proof.Rsa.Mont.wOf s.mem p.1.B) 0 = p.2
  rw [hw, VG.Proof.Bignum.AArch64.MontFn.numAt_eq]
  exact hc.n

theorem publicPrepared_call_ct (M : Mont) (name : String) :
    RelCT isa (Two ReadyC) (.call name (publicRound M.mm)) fun _ _ => True := by
  apply RelCT.callEx (k := publicRoundContract) (publicRound_correct M) (publicRound_ct M)
  rintro s t ⟨p, hs, ht, hsp⟩
  have hcs := ready_covers hs.ready
  have hct := ready_covers ht.ready
  exact ⟨[], [⟨p.1.B, 8 * callWords p.1.w⟩], [], [⟨p.1.B, 8 * callWords p.1.w⟩],
    ready_pre hs.ready, ready_pre ht.ready,
    ⟨ready_pub hs.ready ht.ready hsp, (ready_candidate hs).trans (ready_candidate ht).symm⟩,
    Covers.right hcs, hcs, Covers.right hct, hct⟩

/-- A call of the round for public candidates leaks the same in runs that
agree on the working space and the candidate. -/
theorem publicCall_ct (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    RelCT isa (Two BeforeC) (call name (publicRound M.mm)) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.AArch64.Caller.call
  refine RelCT.seq (two_post (Ψ := ReadyC) ?_ (fun _ _ h => save_readyC h)) ?_
  · exact save_ct.mono (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p.1, before_good hs.before, before_good ht.before, hsp⟩)
      (fun _ _ h => h)
  · exact RelCT.seq (two_post (Ψ := fun p s => RestorePre p.1 s) (publicPrepared_call_ct M name)
      (fun _ _ h => call_restore_pre (publicRound_correct M) name hnf h.ready))
      (two_map (fun p : CPub => p.1) (fun _ _ h => h) restore_ct)

/-- The round for public candidates has no frames where the shared round has none:
they differ in the selection, which is blocks and a loop. -/
theorem publicRound_noFrames {mul : Nat → Nat → Nat → Prog isa}
    (h : (VG.Impl.MillerRabin.AArch64.round mul).noFrames = true) : (publicRound mul).noFrames = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self]
  exact h

/-- A prepared round for a public candidate: `Kernel`, but its runs agree on
the candidate too. -/
structure PublicKernel where
  run : List (Prog isa)
  nonempty : run ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat},
    MrCtx s B Z w c bm → ECtx s.mem B w c → 4 ≤ w → w ≤ 128 →
    slot w aE + 8 * (w + 2) ≤ Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa (seqs run) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two BeforeC) (seqs run) fun _ _ => True

/-- A call of the round for public candidates, keeping its workspace for the policy. -/
def PublicKernel.called (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    PublicKernel where
  run := [call name (publicRound M.mm)]
  nonempty := by simp
  ok := by exact Caller.call_result_ok (publicRound_correct M) name hnf
  ct := by exact publicCall_ct M name hnf

/-- The name of the round for public candidates that goes with a shared round. -/
def publicRoundName (v : RoundImpl) : String := "vg_dsa_miller_rabin_round" ++ v.suffix

/-- The kernel of DSA's parameter search for an implementation of the shared
round: the round for public candidates over the same multiplication. -/
def publicKernel (v : RoundImpl) : PublicKernel :=
  PublicKernel.called v.roundMont (publicRoundName v) (publicRound_noFrames v.noFrames)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.ForceSample`, which this module and modules that import it used -/

section

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
  refine ⟨⟨ht, (hwords _ (by simp only [kOut, sFn]; omega_using [hz])).trans h.ptr,
    ?_, ?_, ?_⟩, hwords _ (by simp only [kU]; omega_using [hEZ]), ?_, hk⟩
  · rw [hfl, hwords _ (by simp only [kUsedP, sFn]; omega_using [hz])]; exact h.len
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
    rw [Nat.mod_eq_of_lt (by omega_using [hmax, hi] : i < 2 ^ 64)]
    exact hi

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.TestWitness`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.LoadWitness`, which this module and modules that import it used -/

section

/-! Loading a padded witness preserves the prepared modulus and exponent. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem loadWitness_ok {s : State} {B p : Addr} {Z w N : Nat} {bs : List Byte}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hp : word s.mem B (8 * kOut) = p)
    (hl : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (h1 : 1 ≤ bs.length) (hw : bs.length ≤ 8 * w) :
    WP isa Impl.Dsa.AArch64.Generation.loadWitness s fun t =>
      ModulusReady t B Z w N ∧ wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧
      Frm B [(slot w aX, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h.ws (by decide) (by decide) (by decide) hp hl hsrc rfl h1 hw)
    fun t ⟨hv, ho, _, _, hk⟩ => ?_
  have hf : Frm B [(slot w aX, 8 * (w + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, hv, hf, hk.mono (by decide)⟩
  · intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.ofSlot w aX _
  · intro a ha r hr
    rw [List.mem_singleton.mp hr]
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aN, aOne, aR2, aR1, aRm1, aX] <;> omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    left; simp only [slot, hdrBytes, aX, sMinv]; omega_arith
  · intro r hr; rw [List.mem_singleton.mp hr]
    right; simp only [slot, hdrBytes, aX, aE]; omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Classify the complete truncated draw while preserving its original bytes. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/WitnessRange.lean`, which only this module imported.
section

/-! The uniform flag agrees with the shared RSA sampler, without changing the draw. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MlKem.AArch64

theorem testRange_ok {s : State} {B : Addr} {Z w X N : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w aX) w = X)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) :
    WP isa Impl.Dsa.AArch64.Generation.testRange s fun t =>
      t.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) ∧
      t.mem = s.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))) ∧
      Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.testRange
  refine WP.seq (WP.mono (drawRange_ok h hx) fun u ⟨hu9, hum, ku⟩ => ?_)
  have hu9' : u.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) := by
    simpa only [hn, or1_lt_iff hodd, Bool.decide_and] using hu9
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = u.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))))
      (by
        brun [(ku.gpr .x0 (by decide)).trans h.x0, hu9', hdr_enc (show kU < 32 by decide),
          (h.scr.congr ku.wr).st (d := 8 * kU) (by have := h.h256; simp only [kU]; omega)])
      rfl rfl rfl) fun t ⟨htm, kt⟩ => ?_
  exact ⟨(kt.gpr .x9 (by decide)).trans hu9', by rw [htm, hum], (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def testRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kU, 8)]

theorem testWitness_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (h1 : 1 ≤ bs.length) (hw : bs.length ≤ 8 * w) :
    WP isa Impl.Dsa.AArch64.Generation.testWitness s fun t =>
      SampleState B p Z w N bs t ∧ wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧
      word t.mem B (8 * kU) = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      t.gpr .x9 = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      Frm B (testRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := h.ready.ws.scr.nowrap
  have hZ := h.ready.ws.hZ
  have h256 := h.ready.ws.h256
  have hX := h.ready.ws.sl (show aX < 16 by decide)
  unfold Impl.Dsa.AArch64.Generation.testWitness
  refine WP.seq (WP.mono (loadWitness_ok h.ready hEZ h.ptr h.len h.source h1 hw)
    fun u ⟨hu, hxu, fu, ku⟩ => ?_)
  have hsu := h.of_frm hu fu ku
    (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aX, kOut, sFn]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aX, kUsedP, sFn]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact hX)
  refine WP.mono (testRange_ok hu.ws hxu hu.modulus hodd) fun t ⟨ht9, htm, kt⟩ => ?_
  have ft : Frm B [(8 * kU, 8)] u.mem t.mem := by
    rw [htm]; exact Frm.of_outside (writeW_outside _ B _ (by decide)) (by simp)
  have ht : ModulusReady t B Z w N := hu.of_frm hEZ ft
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.hdr (.inl (by decide))) kt (by decide)
    (by
      intro a ha r hr; rw [List.mem_singleton.mp hr]
      right; simp only [slot, hdrBytes, kU]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aE, kU]; omega_arith)
  have hst := hsu.of_frm ht ft kt
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [kU]; omega_using [hEZ])
  refine ⟨hst, ?_, ?_, ht9, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aX, kU]; omega_arith)
      (by omega_using [hz, hX])]
    exact hxu
  · rw [htm, word_writeW_self]
  · exact (fu.mono (by simp [testRanges])).trans (ft.mono (by simp [testRanges]))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.WitnessRound`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.Generation.WitnessMont`, which only this module used -/

section

/-! Convert a sampled witness to Montgomery form using the shared arithmetic. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def witnessMontRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

theorem witnessMont_ok (M : Mont) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (M.mm aXm aX aR2) s fun t =>
      ModulusReady t B Z w N ∧ wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N ∧
      Frm B (witnessMontRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw := h.ws.w2
  have hn := h.ws.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  refine WP.mono (M.mm_ok h.ws.good.1 h.ws.good.2 h.ws.w1 (by omega)
    (o := aXm) (a := aX) (b := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h.inverse
    (by rw [h.r2, h.modulus]; exact Nat.mod_lt _ (by omega))) fun t ⟨_, hlt, hy, ha, hk⟩ => ?_
  rw [h.modulus] at hlt hy
  rw [hx, h.r2] at hy
  have hXm : wv t.mem B (slot w aXm) w = b * 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hf : Frm B (witnessMontRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [witnessMontRanges])
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, hXm, hf, hk⟩
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.ofSlot w _ _
  · intro a ha r hr
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aN, aOne, aR2, aR1, aRm1, aAcc, aTmp, aXm] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      left <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, sMinv] <;> omega_arith
  · intro r hr
    simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, aAcc, aTmp, aXm, aE] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.KernelFrame`, which only this module used -/

section

/-! The callable round retains every constant needed for the next witness. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin

theorem kernel_preserves_modulus {s t : State} {B : Addr} {Z w N : Nat}
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hf : Frm B (VG.Proof.MillerRabin.AArch64.Caller.callRanges w) s.mem t.mem)
    (hk : Keep mmRegs s t) : ModulusReady t B Z w N := by
  apply h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      KMut, VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, sW, sMinv, sArr, sStride, sFn]
    and_intros <;> omega_arith
  · intro a ha
    simp only [modulusArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
        Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aN, aOne, aR2, aR1, aRm1,
        Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
      and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, sMinv,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith
  · simp only [VG.Proof.MillerRabin.AArch64.Caller.callRanges, mutRanges,
      Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      VG.Proof.MillerRabin.AArch64.Caller.pad, slot, hdrBytes, aOne, aE,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! The chosen witness is tested by the shared callable windowed round. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64

def witnessRoundRanges (w : Nat) : List (Nat × Nat) := witnessMontRanges w ++ Caller.callRanges w

theorem witnessRound_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {s : State} {B : Addr} {Z w N b : Nat}
    (h : ModulusReady s B Z w N) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : N % 2 = 1) (h3 : 3 ≤ N)
    (hx : wv s.mem B (slot w aX) w = b) :
    WP isa (Impl.Dsa.AArch64.Generation.witnessRound M.mm K.run) s fun t =>
      ModulusReady t B Z w N ∧ word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round N b) ∧
      Frm B (witnessRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.witnessRound
  refine WP.seq (WP.mono (witnessMont_ok M h hEZ hodd (by omega_using [h3]) hx)
    fun u ⟨hu, hxu, fu, ku⟩ => ?_)
  have hcu : MrCtx u B Z w N (wv u.mem B (slot w aB) w) :=
    ⟨hu.ws, hu.inverse, hu.modulus, rfl, hu.r1, hu.rm1⟩
  refine WP.mono (K.ok (b := b) hcu hu.exponent h4 h128 hEZ hodd h3
    (by simpa only [Nat.mod_mul_mod] using hxu))
    fun t ⟨_, _, hflag, ft, kt⟩ => ?_
  exact ⟨kernel_preserves_modulus hu hEZ ft kt, hflag,
    (fu.mono fun r hr => List.mem_append_left _ hr).trans
      (ft.mono fun r hr => List.mem_append_right _ hr), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Native witness selection agrees exactly with RSA's shared sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.Dsa.Generation

theorem sampleWitness_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096)
    (hw : bs.length ≤ 8 * w) (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length) :
    WP isa (Impl.Dsa.AArch64.Generation.sampleWitness bs.length) s fun t =>
      ModulusReady t B Z w N ∧
      wv t.mem B (slot w aX) w = (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)).2 ∧
      WorkFrame B (testRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := h.ready.ws.scr.nowrap
  have hX := h.ready.ws.sl (show aX < 16 by decide)
  unfold Impl.Dsa.AArch64.Generation.sampleWitness
  refine WP.seq (WP.mono (testWitness_ok h hEZ hodd (by omega_using [hlen]) hw)
    fun u ⟨hu, hxu, huu, hu9, fu, ku⟩ => ?_)
  refine WP.ite (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1))
    (by rw [VG.Proof.MlKem.AArch64.eval_zero, hu9]; cases decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) <;> decide)
    (fun hbad => ?_) (fun hgood => ?_)
  · have hb : ¬ (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1) := by
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hbad
    have hspec := forcedWitnessBytes_spec hlen hbits hb
    have hfl := forcedWitnessBytes_length hlen
    refine WP.seq (WP.mono (forceSample_ok hu hEZ hlen hmax) fun v ⟨hv, huv, fv, kv⟩ => ?_)
    refine WP.mono (loadWitness_ok hv.ready hEZ hv.ptr hv.len hv.source
      (by rw [hfl]; omega_using [hlen]) (by rwa [hfl])) fun t ⟨ht, hxt, ft, kt⟩ => ?_
    refine ⟨ht, ?_, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    · simpa only [hspec] using hxt
    · rw [ft.word_eq (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [kU, slot, hdrBytes, aX]; omega_arith)
        (by decide), huv, huu, hspec]
      simp [hb]
    · exact (fu.work.trans (fv.mono (by simp))).trans (ft.work.mono (by simp [testRanges]))
  · have hg : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 := by simpa using hgood
    have hfit : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
      rw [← VG.Proof.Bignum.pow256_eq]
      exact VG.Proof.Rsa.lt_of_os2ip bs
    have hspec : Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs) = (Spec.Rsa.os2ip bs, true) := by
      simp only [Spec.RsaKeyGen.witness, hbits, Nat.mod_eq_of_lt hfit, ite_eq_left hg]
    refine WP.block_nil ⟨hu.ready, ?_, ?_, fu.work, ku⟩
    · simpa only [hspec] using hxu
    · rw [huu, hspec]; simp [hg]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.RoundHeader`, which only this module used -/

section

/-! The shared round preserves the caller's entropy and policy header words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem round_header_ranges (w j : Nat) (hj : j ∈ [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27]) :
    ∀ r ∈ witnessRoundRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  intro r hr
  rcases List.mem_append.mp hr with hm | hk
  · simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hj32 : j < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega_using [hj]
    rcases hm with rfl | rfl | rfl <;> left <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aXm] <;> omega_arith
  · exact sharedKernel_hdr w j hj r hk

theorem witnessRoundRanges_lt (w : Nat) : ∀ r ∈ witnessRoundRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  rcases List.mem_append.mp hr with hm | hk
  · simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aXm, aE] <;> omega_arith
  · apply sharedRoundRanges_lt w r
    simp only [sharedRoundRanges, sharedMidRanges, List.mem_append]
    exact Or.inl (Or.inr hk)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SampleRound`, which only this module used -/

section

/-! A complete native witness iteration through the shared windowed round. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/RoundTailResult.lean`, which only this module imported.
section

/-! The round completion policy retains the prepared modulus for retries. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem roundTail_result {s : State} {B : Addr} {Z w N : Nat} 
    (h : ModulusReady s B Z w N) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    {f u : Bool} {i uni ch : Nat}
    (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa Impl.Dsa.AArch64.Generation.roundTail s fun t =>
      ModulusReady t B Z w N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + u.toNat)) ∧
      Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.roundTail
  refine WP.mono (VG.Proof.RsaKeyGen.AArch64.roundTail_ok h.ws hF hI hU hUni hC hi huni hch)
    fun t ⟨hm, hk⟩ => ?_
  have hf : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by decide)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by decide)) (by simp))).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨h.of_frm hEZ hf ?_ hk (by decide) ?_ ?_ ?_, ?_, ?_, hf, hk⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.hdr (by decide)
  · intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> left <;> decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      right <;> simp only [slot, hdrBytes, aE, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro htrue
    rw [hm, htrue]
    simp only [↓reduceIte]
    constructor
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]


end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 VG.Proof.MillerRabin.AArch64

def sampleRoundRanges (w : Nat) : List (Nat × Nat) :=
  testRanges w ++ witnessRoundRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

theorem sampleRound_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {B p : Addr} {Z w N i uni ch : Nat}
    {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hout : Region.Disjoint ⟨B, Z⟩ ⟨p, bs.length⟩)
    (hodd : N % 2 = 1) (hN : 3 ≤ N)
    (hlen : 2 ≤ bs.length) (hmax : bs.length < 4096) (hw : bs.length ≤ 8 * w)
    (hbits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * bs.length)
    (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (Impl.Dsa.AArch64.Generation.sampleRound M.mm K.run bs.length) s fun t =>
      let wt := Spec.RsaKeyGen.witness (N - 1) (Spec.Rsa.os2ip bs)
      let f := Proof.MillerRabin.Round.round N wt.1
      ModulusReady t B Z w N ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3) ∧
      (f = true → word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame B (sampleRoundRanges w) [⟨p, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  have hz := h.ready.ws.h256
  have hn := h.ready.ws.scr.nowrap
  unfold Impl.Dsa.AArch64.Generation.sampleRound
  refine WP.seq (WP.mono (sampleWitness_ok h hEZ hodd hlen hmax hw hbits)
    fun u ⟨hu, hxu, huu, fu, ku⟩ => ?_)
  have hhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks → word u.mem B (8 * k) = word s.mem B (8 * k) := by
    intro k hk
    apply fu.word_eq (Z := Z)
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rcases hk with rfl | rfl | rfl <;> constructor
      all_goals simp only [slot, hdrBytes, aX, kI, kElen, kUni, kP, kChecks, kE, kU, sFn] <;> omega_arith
    · rcases hk with rfl | rfl | rfl <;> simp only [kI, kElen, kUni, kP, kChecks, kE, sFn] <;> omega_using [hz]
    · exact hn
    · simpa using hout
  refine WP.seq (WP.mono (witnessRound_ok M K hu h4 h128 hEZ hodd hN hxu)
    fun v ⟨hv, hflag, fv, kv⟩ => ?_)
  have hvhdr : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks ∨ k = kU →
      word v.mem B (8 * k) = word u.mem B (8 * k) := by
    intro k hk
    apply fv.word_eq
    · apply round_header_ranges
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    · rcases hk with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (roundTail_result hv hEZ hflag
    ((hvhdr kI (by simp)).trans ((hhdr kI (by simp)).trans hI))
    ((hvhdr kU (by simp)).trans huu)
    ((hvhdr kUni (by simp)).trans ((hhdr kUni (by simp)).trans hUni))
    ((hvhdr kChecks (by simp)).trans ((hhdr kChecks (by simp)).trans hC)) hi huni hch)
    fun t ⟨ht, hstat, hcount, ft, kt⟩ => ?_
  have fuv : WorkFrame B (testRanges w ++ witnessRoundRanges w) [⟨p, bs.length⟩] s.mem v.mem :=
    (fu.mono fun r hr => List.mem_append_left _ hr).trans
      (fv.work.mono fun r hr => List.mem_append_right _ hr)
  refine ⟨ht, hstat, hcount, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  exact (fuv.mono fun r hr => List.mem_append_left _ hr).trans
    (ft.work.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # One consumed draw, the shared round, and DSA's next loop state -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SampleRoundHeader.lean`, which only this module imported.
section

/-! A complete witness iteration retains its immutable generation arguments. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem sampleRound_header_ranges {w j : Nat} (hj : j ∈ [16, 17, 18, 19, 24, 25, 27]) :
    ∀ r ∈ sampleRoundRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      have hj32 : j < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      have hj1 : 1 ≤ j := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      rcases htest with rfl | rfl
      · left; simp only [slot, hdrBytes, aX]; omega_arith
      · right; simp only [kU]; omega
    · apply round_header_ranges w j ?_ r hrnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ht
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl <;> decide

theorem sampleRoundRanges_le (w : Nat) : ∀ r ∈ sampleRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      rcases htest with rfl | rfl <;> simp only [slot, hdrBytes, aX, kU] <;> omega_arith
    · have hh := witnessRoundRanges_lt w r hrnd
      simp only [slot, hdrBytes, aE] at hh ⊢
      omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.Dsa.Generation

def drawRoundRanges (w : Nat) : List (Nat × Nat) := [(8 * kUsed, 8)] ++ sampleRoundRanges w

theorem drawRound_ok (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {P : PrimeParams} {used i uni : Nat} {s : State}
    (h : PrimeState P used s) (hroom : used + P.drawBytes ≤ P.rand.length)
    (hI : word s.mem P.B (8 * kI) = BitVec.ofNat 64 i)
    (hUni : word s.mem P.B (8 * kUni) = BitVec.ofNat 64 uni)
    (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) :
    WP isa (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run P.len P.drawBytes) s fun t =>
      let wt := Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes))
      let f := Proof.MillerRabin.Round.round P.N wt.1
      PrimeState P (used + P.drawBytes) t ∧
      word t.mem P.B (8 * kStat) = BitVec.ofNat 64 (if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < P.checks then 4 else 1) else 3) ∧
      (f = true → word t.mem P.B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem P.B (8 * kUni) = BitVec.ofNat 64 (uni + wt.2.toNat)) ∧
      WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  unfold Impl.Dsa.AArch64.Generation.drawRound
  refine WP.seq (WP.mono (drawBuffer_ok h hroom) fun u ⟨hu, hsample, hfu, ku⟩ => ?_)
  have hIu : word u.mem P.B (8 * kI) = BitVec.ofNat 64 i :=
    (prime_frame_word h.ready.ws.scr.nowrap hfu (by decide : kI < 32) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)).trans hI
  have hUniu : word u.mem P.B (8 * kUni) = BitVec.ofNat 64 uni :=
    (prime_frame_word h.ready.ws.scr.nowrap hfu (by decide : kUni < 32) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)).trans hUni
  have hlen := P.slice_length hroom
  have hsamp := sampleRound_ok M K hsample P.w4 P.w128 P.exponentRoom
    (by rw [hlen]; exact P.bufferSeparate) P.odd P.n3 (by rw [hlen]; exact P.len2)
    (by rw [hlen]; have := P.lenDraw; have := P.drawMax; omega_arith) (by rw [hlen]; exact P.lenWords)
    (by rw [hlen]; exact P.predBits) hIu hUniu hu.checks hi huni P.checksMax
  rw [hlen] at hsamp
  refine WP.mono hsamp fun t ⟨ht, hstat, hcount, hft, kt⟩ => ?_
  change WorkFrame P.B (sampleRoundRanges P.w) (primeExtras P) u.mem t.mem at hft
  have hused : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 (used + P.drawBytes) :=
    (prime_frame_word hu.ready.ws.scr.nowrap hft (by decide : kUsed < 32)
      (sampleRound_header_ranges (by decide : kUsed ∈ [16, 17, 18, 19, 24, 25, 27]))).trans hu.used
  have hpt := hu.advance ht hused hft kt
    (fun r hr => Nat.le_trans (sampleRoundRanges_le P.w r hr) P.room) (by
      intro k hk
      apply sampleRound_header_ranges
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwt := witness_slice (r := P.rand) (used := used) P.lenDraw hroom P.predBits
  change Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip ((P.rand.drop used).take P.drawBytes)) =
    Spec.RsaKeyGen.witness (P.N - 1) (Spec.Rsa.os2ip (P.drawSlice used)) at hwt
  rw [← hwt] at hstat hcount
  exact ⟨hpt, hstat, hcount, (hfu.mono (fun r hr => List.mem_append_left _ hr)).trans
    (hft.mono (fun r hr => List.mem_append_right _ hr)), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The invariant and result of DSA's finite blinded witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure PrimeLoopState (P : PrimeParams) (s₀ : State)
    (res : Option (Bool × List Byte)) (i uni used : Nat) (s : State) : Prop where
  state : PrimeState P used s
  ki : word s.mem P.B (8 * kI) = BitVec.ofNat 64 i
  kuni : word s.mem P.B (8 * kUni) = BitVec.ofNat 64 uni
  usedBound : used ≤ P.rand.length
  i1 : 1 ≤ i
  countBound : P.drawBytes * (i - 1) ≤ used
  uniformBound : uni ≤ i
  go : i ≤ Spec.RsaKeyGen.blindedChecks ∨ uni < P.checks
  rest : primeRest P i uni used = res
  frame : WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

def PrimeLoopEnd (P : PrimeParams) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  ∃ used, PrimeState P used s ∧ used ≤ P.rand.length ∧
    (res = none → word s.mem P.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) →
      word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧ used = P.rand.length - rest.length) ∧
    WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem ∧ Keep mmRegs s₀ s

theorem PrimeLoopState.counter_bound {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} (h : PrimeLoopState P s₀ res i uni used s) :
    i < 2 ^ 62 ∧ uni < 2 ^ 62 := by
  have hb := Nat.le_trans (Nat.mul_le_mul_right (i - 1) P.drawMin) h.countBound
  have hr := P.randMax
  have hu := h.usedBound
  have hi := h.i1
  have hn := h.uniformBound
  omega_using [hb, hr, hu, hn]

theorem PrimeLoopState.of_mem {P : PrimeParams} {s₀ s t : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} (h : PrimeLoopState P s₀ res i uni used s)
    (hm : t.mem = s.mem) (hk : Keep mmRegs s t) : PrimeLoopState P s₀ res i uni used t := by
  exact ⟨h.state.of_mem hm hk, by rw [hm]; exact h.ki, by rw [hm]; exact h.kuni,
    h.usedBound, h.i1, h.countBound, h.uniformBound, h.go, h.rest,
    by rw [hm]; exact h.frame, (h.keep.trans hk).mono (by decide)⟩

theorem PrimeLoopEnd.of_mem {P : PrimeParams} {s₀ s t : State}
    {res : Option (Bool × List Byte)} (h : PrimeLoopEnd P s₀ res s)
    (hm : t.mem = s.mem) (hk : Keep mmRegs s t) : PrimeLoopEnd P s₀ res t := by
  obtain ⟨used, hs, hu, he, hr, hf, hkeep⟩ := h
  refine ⟨used, hs.of_mem hm hk, hu, ?_, ?_, ?_, (hkeep.trans hk).mono (by decide)⟩
  · intro hn; rw [hm]; exact he hn
  · intro b rest hr'; rw [hm]; exact hr b rest hr'
  · rw [hm]; exact hf

theorem primeLoopEnd_some {P : PrimeParams} {s₀ s : State}
    {res : Option (Bool × List Byte)} {used : Nat} {b : Bool}
    (h : PrimeState P used s) (hu : used ≤ P.rand.length)
    (hres : res = some (b, P.rand.drop used))
    (hstat : word s.mem P.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3))
    (hf : WorkFrame P.B (drawRoundRanges P.w) (primeExtras P) s₀.mem s.mem)
    (hk : Keep mmRegs s₀ s) : PrimeLoopEnd P s₀ res s := by
  refine ⟨used, h, hu, ?_, ?_, hf, hk⟩
  · intro hn; rw [hres] at hn; cases hn
  · intro b' rest he
    have hpair := Option.some.inj (hres.symm.trans he)
    obtain ⟨hb, hr⟩ := Prod.mk.inj hpair
    subst b' rest
    exact ⟨hstat, by rw [List.length_drop]; omega_using [hu]⟩

end VG.Proof.Dsa.AArch64.Generation
