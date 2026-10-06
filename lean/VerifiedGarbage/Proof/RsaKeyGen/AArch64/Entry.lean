import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-!
# A candidate on AArch64: the entry

`kEntry` stores the arguments in the header of the working space, whose
base (the second stack argument) it leaves in `x0` (`kEntry_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem kEntry_eq : kEntry = ([.ldrSp .x8 8, .str .x .x0 .x8 (8 * kOut), .str .x .x1 .x8 (8 * kLen),
    .str .x .x2 .x8 (8 * kUsedP), .str .x .x3 .x8 (8 * kE), .str .x .x4 .x8 (8 * kElen), .str .x .x5 .x8 (8 * kP),
    .str .x .x6 .x8 (8 * kPlen), .str .x .x7 .x8 (8 * kRand)] : List Instr) ++
    (hdrPairs [(0, kRandLen)] ++ ([mov .x0 .x8] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def entryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) : Mem :=
  (((((((m.writeW (off B (8 * kOut)) v0).writeW (off B (8 * kLen)) v1).writeW (off B (8 * kUsedP)) v2).writeW
    (off B (8 * kE)) v3).writeW (off B (8 * kElen)) v4).writeW (off B (8 * kP)) v5).writeW
    (off B (8 * kPlen)) v6).writeW (off B (8 * kRand)) v7

/-- The header after the entry's stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 v7 vr : BitVec 64) : Mem :=
  (entryMemA m B v0 v1 v2 v3 v4 v5 v6 v7).writeW (off B (8 * kRandLen)) vr

theorem entryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    Outside B 0 (8 * 32) m (entryMemA m B v0 v1 v2 v3 v4 v5 v6 v7) := by
  unfold entryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

/-- The header words the entry stores. -/
structure KArgs (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 v7 vr : BitVec 64) : Prop where
  out : word m B (8 * kOut) = v0
  len : word m B (8 * kLen) = v1
  usedP : word m B (8 * kUsedP) = v2
  e : word m B (8 * kE) = v3
  elen : word m B (8 * kElen) = v4
  p : word m B (8 * kP) = v5
  plen : word m B (8 * kPlen) = v6
  rand : word m B (8 * kRand) = v7
  rlen : word m B (8 * kRandLen) = vr

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 v6 v7 vr : BitVec 64) :
    KArgs (entryMem m B v0 v1 v2 v3 v4 v5 v6 v7 vr) B v0 v1 v2 v3 v4 v5 v6 v7 vr ∧
      Outside B 0 (8 * 32) m (entryMem m B v0 v1 v2 v3 v4 v5 v6 v7 vr) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> unfold entryMem entryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `kEntry`: the header, from the arguments, and the working space's base
(stack argument 1) in `x0`. -/
theorem kEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 3, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block kEntry) s fun t => t.gpr .x0 = B ∧
      KArgs t.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
        (s.gpr .x7) (stackArg s 0) ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = B := hB
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := ha 1 (by decide)
  have ho : 8 % 8 = 0 ∧ 8 < 32768 := ⟨rfl, by decide⟩
  rw [kEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = entryMemA s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
        (s.gpr .x6) (s.gpr .x7)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha1, hB', hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide),
      hdr_enc (show kUsedP < 32 by decide), hdr_enc (show kE < 32 by decide), hdr_enc (show kElen < 32 by decide),
      hdr_enc (show kP < 32 by decide), hdr_enc (show kPlen < 32 by decide), hdr_enc (show kRand < 32 by decide),
      hw kOut (by decide), hw kLen (by decide), hw kUsedP (by decide), hw kE (by decide), hw kElen (by decide),
      hw kP (by decide), hw kPlen (by decide), hw kRand (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact entryMemA_outside _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = t₂.mem) (by brun [h8₂])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = entryMem s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
      (s.gpr .x6) (s.gpr .x7) (stackArg s 0) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hA, ho'⟩ := entryMem_facts s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)
    (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (stackArg s 0)
  exact ⟨h0, hA, ho', (k12.trans k₃).mono (by decide)⟩

end VG.Proof.RsaKeyGen.AArch64
