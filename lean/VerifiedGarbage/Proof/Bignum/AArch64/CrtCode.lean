module

public import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.SigEval

/-! ### `Bignum.AArch64.CrtEntry`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: the entry

`entry` stores the arguments (the pointers and lengths among them that
`main` reads, some from the stack) in the header of the working space, and
leaves its base in `x0` (`crtEntry_ok`).
-/

@[expose] public section

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

end

end


/-!
# RSA with the CRT on AArch64: correctness

`code`, from a state its contract allows, writes `privateCrt` of its inputs,
against `crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA)

/-! ## The precondition, as `main` uses it -/

theorem stackArgAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

/-- What `code` uses of its contract's precondition, for the working space
`B` (stack argument 8) of `Z` bytes, `n`'s length `k` and the primes'
lengths (`x7` and stack argument 1). -/
structure CrtCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x3).toNat
  hk2 : (s.gpr .x3).toNat ≤ 1024
  hpl1 : 1 ≤ (s.gpr .x7).toNat
  hpl2 : (s.gpr .x7).toNat < (s.gpr .x3).toNat
  hql1 : 1 ≤ (stackArg s 1).toNat
  hql2 : (stackArg s 1).toNat < (s.gpr .x3).toNat
  hZ : 128 * (s.gpr .x3).toNat + 256 ≤ (stackArg s 9).toNat * 8
  hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 10, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 10, ∀ m', Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  hnb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x2)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  hxb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x4)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)
  hpb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x6)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
  hqb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hdpb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
  hdqb : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  hqib : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat)
  hout : ∀ j < (s.gpr .x3).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .x3).toNat,
    (stackArg s 9).toNat * 8 ≤ ofs (stackArg s 8) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem crtCtx_of {s : State} (h : crtA.pre s) : CrtCtx s := by
  simp only [crtA] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOs dOa dns dis dps dqs ddps ddqs dqis dsa wO
    wN wI wP wQ wDp wDq wQi wS hk hol hil hpl1 hpl2 hql1 hql2 hdpl hqil hdql
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega_arith, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega_arith) (by omega_arith))
      rw [← stackArgAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega_arith) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega_arith) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega_arith) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega_arith) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega_arith) (by omega_arith)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega_arith) (by omega_arith))⟩

/-- After `entry`, from `s`. -/
structure CrtHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 8) ((stackArg s 9).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 8
  hO : word t.mem (stackArg s 8) (8 * Public.sOut) = s.gpr .x0
  hN : word t.mem (stackArg s 8) (8 * Public.sN) = s.gpr .x2
  hK : word t.mem (stackArg s 8) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x3).toNat
  hIn : word t.mem (stackArg s 8) (8 * Public.sIn) = s.gpr .x4
  hP : word t.mem (stackArg s 8) (8 * sP) = s.gpr .x6
  hPl : word t.mem (stackArg s 8) (8 * sPlen) = BitVec.ofNat 64 (s.gpr .x7).toNat
  hQ : word t.mem (stackArg s 8) (8 * sQ) = stackArg s 0
  hQl : word t.mem (stackArg s 8) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hDp : word t.mem (stackArg s 8) (8 * sDp) = stackArg s 2
  hDq : word t.mem (stackArg s 8) (8 * sDq) = stackArg s 4
  hQi : word t.mem (stackArg s 8) (8 * sQinv) = stackArg s 6
  inScr : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x8, .x9] s t

/-- `entry`. -/
theorem crtHead_ok {s : State} (c : CrtCtx s) : WP isa (.block entry) s (CrtHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (crtEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq,
    hQi, ho, k⟩ => ?_
  exact ⟨c.hs.congr k.wr, h0, hO, hN, by rw [hK, ofNat_toNat64], hI, hP, by rw [hPl, ofNat_toNat64], hQ,
    by rw [hQl, ofNat_toNat64], hDp, hDq, hQi, InScr.of_outside ho (by omega_arith), k⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem crtPre_of {s t₁ t : State} (c : CrtCtx s) (h : CrtHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t) :
    CrtPre t (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x3).toNat (s.gpr .x0) (s.gpr .x2)
      (s.gpr .x4) (s.gpr .x6) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6)
      (s.gpr .x7).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have h0 : t.gpr .x0 = stackArg s 8 := (k.gpr .x0 (by decide)).trans h.x0
  have hz : offQ (((s.gpr .x3).toNat + 7) / 8) (s.gpr .x7).toNat + slot (wsWords (stackArg s 1).toNat) 8 +
      wsTab (wsWords (stackArg s 1).toNat) ≤ (stackArg s 9).toNat * 8 :=
    crt_room hk1 hpl2 hql2 hZ
  exact
    { scr := h.scr.congr k.wr, x0 := h0, z := hz, zk := (by omega_arith), k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hIn := (by rw [hm]; exact h.hIn),
      hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl), hQ := (by rw [hm]; exact h.hQ),
      hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp), hDq := (by rw [hm]; exact h.hDq),
      hQi := (by rw [hm]; exact h.hQi), n := c.hnb.congrK hi kk, x := c.hxb.congrK hi kk,
      p := c.hpb.congrK hi kk, q := c.hqb.congrK hi kk, dp := c.hdpb.congrK hi kk, dq := c.hdqb.congrK hi kk,
      qi := c.hqib.congrK hi kk, nl := bytesAt_length _ _ _, xl := bytesAt_length _ _ _,
      pbl := bytesAt_length _ _ _, qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _,
      dql := bytesAt_length _ _ _, qil := bytesAt_length _ _ _, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.wr]; exact c.hout j hj), outSep := c.houts }

/-- `fail`: zeros to `out`, and 0 returned. -/
theorem crtFail_ok {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib) :
    WP isa Precomputed.fail s fun t => MainPost s t B Z k op 0 false := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have h8 : 8 * 32 ≤ Z := by
    have := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
    unfold offQ at hZq; omega_arith
  refine WP.mono (pdFail_ok h.scr h.x0 h8 (by omega_arith) (by omega_arith) h.hO h.hK h.out)
    fun t ⟨hb, hx, hfr, k⟩ => ⟨by rw [i2osp_zero']; exact hb, hx, fun x _ hx' => hfr x hx', k⟩

/-- What `code` leaves, from what `fail` or `main` leaves. -/
theorem crtCode_fin {s t₁ t₂ t : State} (h : CrtHeadPost s t₁)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .x3).toNat (s.gpr .x0) r cb)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true →
      (cb = true ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) ∧
      r = if cb then crtResult (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false → cb = false ∧ r = 0) :
    abiPreserved s t ∧ crtA.post s t :=
  ⟨abiPreserved_of_keep (((h.keep.trans k).trans hp.keep).mono (by decide)),
    crtWritten_of (bytesAt_length _ _ _) hp.bytes hp.x0 hc hf⟩

end VG.Proof.Bignum.AArch64
