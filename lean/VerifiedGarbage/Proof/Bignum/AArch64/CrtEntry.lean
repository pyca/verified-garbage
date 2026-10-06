import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs

/-!
# RSA with the CRT on AArch64: the entry

`entry` stores the arguments (the pointers and lengths among them that
`main` reads, some from the stack) in the header of the working space, and
leaves its base in `x0` (`crtEntry_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem crtEntry_eq : entry = ([.ldrSp .x8 64, stw .x0 .x8 Public.sOut, stw .x2 .x8 Public.sN,
    stw .x3 .x8 Public.sK, stw .x4 .x8 Public.sIn, stw .x6 .x8 sP, stw .x7 .x8 sPlen] : List Instr) ++
    (hdrPairs [(0, sQ), (1, sQlen), (2, sDp), (4, sDq), (6, sQinv)] ++ ([mov .x0 .x8] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def crtEntryMemA (m : Mem) (B : Addr) (vo vn vk vi vp vpl : BitVec 64) : Mem :=
  (((((m.writeW (off B (8 * Public.sOut)) vo).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk).writeW (off B (8 * Public.sIn)) vi).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sPlen)) vpl

/-- The header after the entry's stores. -/
def crtEntryMem (m : Mem) (B : Addr) (vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((((crtEntryMemA m B vo vn vk vi vp vpl).writeW (off B (8 * sQ)) vq).writeW
    (off B (8 * sQlen)) vql).writeW (off B (8 * sDp)) vdp).writeW (off B (8 * sDq)) vdq).writeW
    (off B (8 * sQinv)) vqi

theorem crtEntryMemA_outside (m : Mem) (B : Addr) (vo vn vk vi vp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (crtEntryMemA m B vo vn vk vi vp vpl) := by
  unfold crtEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem crtEntryMem_facts (m : Mem) (B : Addr) (vo vn vk vi vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := crtEntryMem m B vo vn vk vi vp vpl vq vql vdp vdq vqi
    word m' B (8 * Public.sOut) = vo ∧ word m' B (8 * Public.sN) = vn ∧ word m' B (8 * Public.sK) = vk ∧
    word m' B (8 * Public.sIn) = vi ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vdp ∧
    word m' B (8 * sDq) = vdq ∧ word m' B (8 * sQinv) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' crtEntryMem crtEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 8) in `x0`. -/
theorem crtEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 10, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * Public.sOut) = s.gpr .x0 ∧ word t.mem B (8 * Public.sN) = s.gpr .x2 ∧
      word t.mem B (8 * Public.sK) = s.gpr .x3 ∧ word t.mem B (8 * Public.sIn) = s.gpr .x4 ∧
      word t.mem B (8 * sP) = s.gpr .x6 ∧ word t.mem B (8 * sPlen) = s.gpr .x7 ∧
      word t.mem B (8 * sQ) = stackArg s 0 ∧ word t.mem B (8 * sQlen) = stackArg s 1 ∧
      word t.mem B (8 * sDp) = stackArg s 2 ∧ word t.mem B (8 * sDq) = stackArg s 4 ∧
      word t.mem B (8 * sQinv) = stackArg s 6 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = B := hB
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  rw [crtEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = crtEntryMemA s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7)) ?_
      (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [stw, exec_ldrSp ho ha8, hB', hdr_enc (show Public.sOut < 32 by decide),
      hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show sP < 32 by decide),
      hdr_enc (show sPlen < 32 by decide), hw Public.sOut (by decide), hw Public.sN (by decide),
      hw Public.sK (by decide), hw Public.sIn (by decide), hw sP (by decide), hw sPlen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact crtEntryMemA_outside _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = t₂.mem) (by brun [h8₂])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = crtEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6)
      (s.gpr .x7) (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho'⟩ :=
    crtEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7)
      (stackArg s 0) (stackArg s 1) (stackArg s 2) (stackArg s 4) (stackArg s 6)
  exact ⟨h0, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Bignum.AArch64
