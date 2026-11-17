module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRound
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundCall
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions

/-! ### `RsaKeyGen.X86.WitnessInput`, which this module and modules that import it used -/

section

/-! # Each remaining entropy block is a disjoint, readable native import source -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessInput
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

/-- The `count` native words at offset `used` of the entropy, into the witness array. -/
def geometryAt (g : Geometry) (rand : BitVec 32) (used count : Nat) : Import.Geometry :=
  ⟨rand + BitVec.ofNat 32 used, BitVec.ofNat 32 (g.W.toNat + g.array 6), count⟩

theorem source_address {rand : BitVec 32} {used : Nat} (fit : rand.toNat + used < 2 ^ 32) :
    (rand + BitVec.ofNat 32 used).setWidth 64 = off (rand.setWidth 64) used := by
  change addr rand used = _
  exact addr_eq fit

theorem destination_pointer {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst = s.gpr .edi + BitVec.ofNat 32 (g.array 6) := by
  have arrBound : g.array 6 < 2 ^ 32 := by
    have := S.nowrap
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega_arith
  apply BitVec.eq_of_toNat_eq
  simp only [geometryAt, BitVec.toNat_ofNat, BitVec.toNat_add, S.edi_toNat, Nat.mod_eq_of_lt arrBound]

theorem destination_address {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst.setWidth 64 = off g.W (g.array 6) := by
  rw [destination_pointer v S]
  have fit : g.array 6 < g.L := by
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega_using [a, this]
  exact S.ea fit

theorem context_okAt {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used length count : Nat} (noWrap : rand.toNat + length ≤ 2 ^ 32)
    (positive : 0 < count) (wide : count ≤ g.words) (enough : used + 4 * count ≤ length)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) length)
    (separate : (⟨rand.setWidth 64, length⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    Import.Context (geometryAt g rand used count) s := by
  have sourceFit : rand.toNat + used < 2 ^ 32 := by omega_using [noWrap, positive, enough]
  have sourceAddr := source_address sourceFit
  have destAddr := destination_address v S (rand := rand) (used := used) (count := count)
  have destPtr := destination_pointer v S (rand := rand) (used := used) (count := count)
  have hw : g.words = 2 * g.w := rfl
  apply Import.context_of_regions
  · exact positive
  · change (rand + BitVec.ofNat 32 used).toNat + 4 * count ≤ 2 ^ 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := used) (by omega_using [sourceFit]), Nat.mod_eq_of_lt sourceFit]
    omega_using [noWrap, enough]
  · change (geometryAt g rand used count).dst.toNat + 4 * count ≤ 2 ^ 32
    rw [destPtr, BitVec.toNat_add, S.edi_toNat, BitVec.toNat_ofNat]
    have bound : g.W.toNat + g.array 6 < 2 ^ 32 := by
      have := S.nowrap; have := v.arrayFit (j := 6) (by decide); have := v.minWidth; omega_arith
    rw [Nat.mod_eq_of_lt (a := g.array 6) (by omega_using [bound]), Nat.mod_eq_of_lt bound]
    have := S.nowrap
    have := v.arrayFit (j := 6) (by decide)
    omega_arith
  · change InRegions (s.rd ++ s.wr) ((rand + BitVec.ofNat 32 used).setWidth 64) (4 * count)
    rw [sourceAddr]
    obtain ⟨r, member, access⟩ := readable
    exact ⟨r, member, Import.contains_offset access enough⟩
  · change InRegions s.wr ((geometryAt g rand used count).dst.setWidth 64) (4 * count)
    rw [destAddr]
    exact S.write (by have := v.arrayFit (j := 6) (by decide); omega_using [wide, this])
  · change (⟨(rand + BitVec.ofNat 32 used).setWidth 64, 4 * count⟩ : Region).Disjoint
      ⟨(geometryAt g rand used count).dst.setWidth 64, 4 * count⟩
    rw [sourceAddr, destAddr]
    exact (separate.sub_left (Offset.sub_base _ enough)).sub_right
      (Offset.sub_base _ (by have := v.arrayFit (j := 6) (by decide); omega_using [wide, this]))

end VG.Proof.RsaKeyGen.X86.WitnessInput

end

end

/-! ### `RsaKeyGen.X86.WitnessAdvance`, which this module and modules that import it used -/

section

/-! # Advancing entropy retains preparation and accounts for exactly one witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessAdvance
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessAdvance

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity used step : Nat} {p rand : BitVec 32}
    (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand)
    (consumed : w32 s.mem g.W usedOffset = used) (fit : used + step < 2 ^ 32) :
    WP isa (.block (codeAt step)) s fun t =>
      Prepare.Data g c capacity p t ∧ t.gpr .esi = rand + BitVec.ofNat 32 used ∧
      w32 t.mem g.W usedOffset = used + step ∧
      Outside g.W usedOffset 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  have head := v.headerFit
  unfold codeAt
  refine wp_movS (readSrc_sc S.ready.scratch (by omega_using [head])) fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (d := usedOffset) (by unfold usedOffset; omega_using [head])) fun b B _ =>
    wp_addS rfl fun d D _ => wp_addS rfl fun e E _ => ?_
  have K : Keeps [.eax, .esi] s e := (((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps
  have Se := S.ready.scratch.of_keeps K (by decide)
  refine wp_storeS (Se.ea (by unfold usedOffset; omega_using [head])) (Se.write (by unfold usedOffset; omega_using [head])) fun t T => WP.block_nil ?_
  have Ot : Outside g.W usedOffset 4 s.mem t.mem := by
    rw [T.mem, E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold usedOffset; decide)
  have Kt := K.widen (T.keeps [])
  refine ⟨S.keepGap v (by unfold usedOffset; decide) (by unfold usedOffset; decide) Ot Kt (by decide) (by decide), ?_, ?_, Ot, Kt⟩
  · rw [T.gpr, E.other .esi (by decide), D.gpr, B.other .esi (by decide), A.gpr, source,
      B.gpr, A.mem]
    have wordEq : s.mem.readW (off g.W usedOffset) 32 = BitVec.ofNat 32 used := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← consumed, Nat.mod_eq_of_lt (by change w32 s.mem g.W usedOffset < 2 ^ 32; exact (s.mem.readW _ 32).isLt)]
    rw [wordEq]
  · rw [T.mem, w32_write_self, E.gpr, D.other .eax (by decide), B.gpr, A.mem,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W usedOffset + step % 2 ^ 32) % 2 ^ 32 = _
    rw [consumed, Nat.mod_eq_of_lt (a := step) (by omega_using [fit]), Nat.mod_eq_of_lt fit]

end VG.Proof.RsaKeyGen.X86.WitnessAdvance

end

end

/-! ### `RsaKeyGen.X86.WitnessCount`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessCountNext`, which this module and modules that import it used -/

section

/-! # Accumulate one witness and its exact uniform-sampling bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessCount

def nextClob : List Reg := [.eax, .ebx, .edx, .esi]
def nextRanges : List (Nat × Nat) := [(roundsOffset, 4), (uniformOffset, 4)]

theorem mask_bit (uniform : Bool) : cmask uniform &&& 1 = BitVec.ofNat 32 uniform.toNat := by
  cases uniform <;> decide

theorem next_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {uniform : Bool}
    (S : Prepare.Data g c capacity p s) (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa (.block next) s fun t =>
      Prepare.Data g c capacity p t ∧
      t.gpr .esi = s.gpr .eax ∧
      t.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) ∧
      t.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) ∧
      t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      Outs g.W nextRanges s.mem t.mem ∧ Keeps nextClob s t := by
  have head := v.headerFit
  unfold next
  refine wp_movS rfl fun a A _ => ?_
  obtain Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by unfold roundsOffset; omega_using [head])) fun b B _ =>
    wp_addS rfl fun d D _ => ?_
  obtain Kd : Keeps nextClob s d := ((A.keeps.mono (by unfold nextClob; decide)).widen B.keeps).widen D.keeps
  obtain Sd := S.ready.scratch.of_keeps Kd (by unfold nextClob; decide)
  obtain valueD : d.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) := by
    rw [D.gpr, B.gpr, A.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32 = (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32
    rfl
  refine wp_storeS (Sd.ea (by unfold roundsOffset; omega_using [head])) (Sd.write (by unfold roundsOffset; omega_using [head])) fun e E => ?_
  obtain Ke := Kd.widen (E.keeps [])
  obtain Se := S.ready.scratch.of_keeps Ke (by unfold nextClob; decide)
  obtain Oe : Outside g.W roundsOffset 4 s.mem e.mem := by
    rw [E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold roundsOffset; decide)
  obtain sampleE : e.mem.readW (off g.W 144) 32 = cmask uniform := by
    exact (BitVec.eq_of_toNat_eq (Oe.w32 (d := 144)
      (by unfold roundsOffset; decide) (by decide))).trans mask
  refine wp_movS (readSrc_sc Se (d := 144) (by omega_using [head])) fun f F _ => wp_andi fun h H => ?_
  obtain Kh := (Ke.widen F.keeps).widen H.keeps
  obtain Sh := S.ready.scratch.of_keeps Kh (by unfold nextClob; decide)
  obtain uRead := readSrc_sc Sh (d := uniformOffset) (by unfold uniformOffset; omega_using [head])
  refine wp_addS uRead fun i I _ => ?_
  obtain Ki := Kh.widen I.keeps
  obtain Si := S.ready.scratch.of_keeps Ki (by unfold nextClob; decide)
  obtain valueI : i.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) := by
    obtain same : h.mem.readW (off g.W uniformOffset) 32 = s.mem.readW (off g.W uniformOffset) 32 := by
      rw [H.mem, F.mem]
      exact BitVec.eq_of_toNat_eq (Oe.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold uniformOffset; decide))
    rw [I.gpr, H.gpr, F.gpr, sampleE, mask_bit, same]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := uniform.toNat) (by have := Bool.toNat_le uniform; omega_using [uniformFit])]
    change (uniform.toNat + w32 s.mem g.W uniformOffset) % 2 ^ 32 = (w32 s.mem g.W uniformOffset + uniform.toNat) % 2 ^ 32
    rw [Nat.add_comm]
  refine wp_storeS (Si.ea (by unfold uniformOffset; omega_using [head])) (Si.write (by unfold uniformOffset; omega_using [head])) fun j J => ?_
  obtain Kj := Ki.widen (J.keeps [])
  obtain Sj := S.ready.scratch.of_keeps Kj (by unfold nextClob; decide)
  refine wp_movS (readSrc_sc Sj (d := checksOffset) (by unfold checksOffset; omega_using [head])) fun t T _ => WP.block_nil ?_
  obtain K := Kj.widen T.keeps
  obtain Oj : Outside g.W uniformOffset 4 e.mem j.mem := by
    rw [J.mem, I.mem, H.mem, F.mem]
    exact writeW32_outside _ _ _ (by unfold uniformOffset; decide)
  obtain O : Outs g.W nextRanges s.mem t.mem := by
    rw [T.mem]
    exact (Outs.of_outside Oe (by simp [nextRanges])).trans (Outs.of_outside Oj (by simp [nextRanges]))
  obtain gap : Outside g.W 128 96 s.mem t.mem := by
    rw [T.mem]
    exact (Oe.mono (by unfold roundsOffset; decide) (by unfold roundsOffset; decide)).trans
      (Oj.mono (by unfold uniformOffset; decide) (by unfold uniformOffset; decide))
  obtain roundT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [T.mem, Oj.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold roundsOffset; decide),
      E.mem, w32_write_self, valueD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt roundsFit]
  obtain uniformT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [T.mem, J.mem, w32_write_self, valueI, BitVec.toNat_ofNat, Nat.mod_eq_of_lt uniformFit]
  obtain checksT : t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 := by
    rw [T.gpr]
    exact BitVec.eq_of_toNat_eq ((Oj.w32 (by unfold uniformOffset checksOffset; decide) (by unfold checksOffset; decide)).trans
      (Oe.w32 (by unfold roundsOffset checksOffset; decide) (by unfold checksOffset; decide)))
  refine ⟨S.keepHeader v (by decide) (by decide) gap K (by unfold nextClob; decide) (by unfold nextClob; decide),
    ?_, ?_, ?_, checksT, roundT, uniformT, O, K⟩
  · rw [T.other .esi (by decide), J.gpr, I.other .esi (by decide), H.other .esi (by decide),
      F.other .esi (by decide), E.gpr, D.other .esi (by decide), B.other .esi (by decide)]
    exact A.gpr
  · rw [T.other .eax (by decide), J.gpr, I.other .eax (by decide), H.other .eax (by decide), F.other .eax (by decide), E.gpr]
    exact valueD
  · rw [T.other .ebx (by decide), J.gpr]; exact valueI

end VG.Proof.RsaKeyGen.X86.WitnessCount

end

end

/-! # The complete masked counting policy retains candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessCount

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
def ranges : List (Nat × Nat) := nextRanges ++ [(statusOffset, 4)]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {passed uniform : Bool}
    (S : Prepare.Data g c capacity p s) (flag : s.gpr .eax = BitVec.ofNat 32 passed.toNat)
    (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa code s fun t =>
      Prepare.Data g c capacity p t ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
        (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) ∧
      Outs g.W ranges s.mem t.mem ∧ Keeps clob s t := by
  unfold code
  refine WP.seq (WP.mono (next_ok v S mask roundsFit uniformFit)
    fun a ⟨A, flagA, roundsA, uniformA, checksA, countA, uniA, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessStatus.code_ok (flagA.trans flag)) fun b ⟨statusB, memB, Kb⟩ => ?_)
  rw [roundsA, uniformA, checksA, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt roundsFit, Nat.mod_eq_of_lt uniformFit] at statusB
  have B : Prepare.Data g c capacity p b :=
    A.keepHeader v (d := 128) (bytes := 0) (by decide) (by decide)
      (by rw [memB]; exact Outside.refl _ _ _ _) Kb (by decide) (by decide)
  refine wp_storeS (B.ready.scratch.ea (by have := v.headerFit; unfold statusOffset; omega_using [this]))
    (B.ready.scratch.write (by have := v.headerFit; unfold statusOffset; omega_using [this])) fun t T => WP.block_nil ?_
  have Ot : Outside g.W statusOffset 4 b.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by unfold statusOffset; decide)
  have statusBound : WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) < 2 ^ 32 := by
    unfold WitnessStatus.status
    split <;> first | decide | (split <;> decide)
  have statusT : w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) := by
    rw [T.mem, w32_write_self, statusB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusBound]
  have countT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [Ot.w32 (by unfold statusOffset roundsOffset; decide) (by unfold roundsOffset; decide), memB]
    exact countA
  have uniT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [Ot.w32 (by unfold statusOffset uniformOffset; decide) (by unfold uniformOffset; decide), memB]
    exact uniA
  have Oab : Outs g.W ranges s.mem b.mem := by
    rw [memB]
    exact Oa.mono (fun r mem => List.mem_append_left _ mem)
  exact ⟨B.keepGap v (by unfold statusOffset; decide) (by unfold statusOffset; decide) Ot (T.keeps []) (by decide) (by decide),
    countT, uniT, statusT, Oab.trans (Outs.of_outside Ot (by simp [ranges])),
    ((Ka.mono (by unfold clob nextClob; decide)).widen Kb).widen (T.keeps [])⟩

end VG.Proof.RsaKeyGen.X86.WitnessCount

end

end

/-! ### `RsaKeyGen.X86.WitnessRoundFrame`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessRound`, which this module and modules that import it used -/

section

/-! # Each witness iteration computes the exact sampled Miller–Rabin test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRound

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
def ranges (g : Geometry) : List (Nat × Nat) := WitnessMont.ranges g ++ roundWrites g ++ [(uniformOffset, 4)]

theorem codeAt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) {draw k : Nat} (width : 4 * input.count = draw) (two : 2 ≤ k)
    (narrow : k ≤ input.count) (wide : input.count ≤ g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (codeAt draw k g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) draw))
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c sampled.1 then 1 else 0) ∧
      t.mem.readW (off g.W uniformOffset) 32 = cmask sampled.2 ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t := by
  unfold codeAt
  refine WP.seq (WP.mono (WitnessLoad.codeAt_ok v S C width two narrow wide source destination odd shape)
    fun a ⟨A, Va, uniform, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Prepare.storeGap_ok v A (d := uniformOffset) (by decide) (by decide))
    fun b ⟨B, uniformB, Ob, Kb⟩ => ?_)
  rw [uniform] at uniformB
  have Vb := (Ob.val32 (Or.inr (by have := v.arrayHeader 6; unfold uniformOffset; omega_using [this]))
    (by have := A.ready.scratch.nowrap; have := v.arrayFit (j := 6) (by decide); omega_arith)).trans Va
  refine WP.seq (WP.mono (WitnessMont.code_ok montVerified montNoSp montStack v length B odd (by omega_using [odd]))
    fun d ⟨D, Vd, Wd, Fd, Kd⟩ => ?_)
  rw [Vb] at Vd
  have uniformD : d.mem.readW (off g.W uniformOffset) 32 = b.mem.readW (off g.W uniformOffset) 32 :=
    Wd.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [WitnessMont.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | rfl <;>
        exact Or.inl (by simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))
  refine WP.mono (RoundCall.code_ok (b := (Spec.RsaKeyGen.witness (c - 1)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) draw))).1)
    roundVerified roundNoSp roundStack v length D odd large
    (by rw [Nat.mod_mul_mod]; exact Vd) fit far lengthFar) fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have uniformT : t.mem.readW (off g.W uniformOffset) 32 = d.mem.readW (off g.W uniformOffset) 32 :=
    Wt.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.ready.scratch.nowrap (Outs.of_outside
      (Oa.mono (o' := g.array 6) (n' := 8 * (g.w + 2)) (Nat.le_refl _) (by unfold Geometry.words; omega_using []))
      (by simp [ranges, WitnessMont.ranges, montWrites]))
  have Wb : WorkspaceFrame g (ranges g) a.mem b.mem :=
    WorkspaceFrame.of_outs A.ready.scratch.nowrap (Outs.of_outside Ob (by simp [ranges]))
  have Wd' := Wd.mono (fun r mem => List.mem_append_left _ (List.mem_append_left _ mem) : ∀ r ∈ WitnessMont.ranges g, r ∈ ranges g)
  have Wt' := Wt.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ roundWrites g, r ∈ ranges g)
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fb : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) a.mem b.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ob (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold uniformOffset; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd' := VG.X86.Frame.below_mono Fd (by decide : 80 ≤ 108) fit
  exact ⟨T, result, (uniformT.trans uniformD).trans uniformB,
    ((Wa.trans Wb).trans Wd').trans Wt', ((Fa.trans Fb).trans Fd').trans Ft,
    (((Ka.mono (by unfold clob WitnessLoad.clob; decide)).widen Kb).widen Kd).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRound

end

end

/-! # Witness tests retain entropy bookkeeping and the two outer round counters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def safeHeader (d : Nat) : Prop :=
  d + 4 ≤ 8 ∨ 16 ≤ d ∧ d + 4 ≤ 144 ∨ 148 ≤ d ∧ d + 4 ≤ 184 ∨
    192 ≤ d ∧ d + 4 ≤ 208 ∨ 216 ≤ d ∧ d + 4 ≤ 232 ∨ 248 ≤ d ∧ d + 4 ≤ 256

theorem ranges_apart32 {g : Geometry} {d : Nat} (safe : safeHeader d) :
    ∀ r ∈ ranges g, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r mem
  simp only [ranges, WitnessMont.ranges, montWrites, roundWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with (((rfl | rfl | rfl) | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset] <;> unfold safeHeader at safe <;> omega_using [safe]

theorem header32 {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {d : Nat} (safe : safeHeader d) : w32 t g.W d = w32 s g.W d :=
  congrArg BitVec.toNat (F.read32 (by have := v.headerFit; unfold safeHeader at safe; omega_using [safe, this]) (ranges_apart32 safe))

end VG.Proof.RsaKeyGen.X86.WitnessRound

end

end

/-! # A complete loop step accounts for entropy and both witness counters exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStep
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessStep

def ranges (g : Geometry) : List (Nat × Nat) :=
  [(152, 4)] ++ WitnessRound.ranges g ++ WitnessCount.ranges

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem flag_value {x : BitVec 32} {b : Bool} (h : x.toNat = if b then 1 else 0) :
    x = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> simpa using h

theorem codeAt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity used randLen draw k : Nat} {p rand : BitVec 32}
    (two : 2 ≤ k) (narrow : 4 * k ≤ draw) (wide : draw ≤ 8 * g.w) (four : draw % 4 = 0)
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand) (consumed : w32 s.mem g.W 152 = used)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + draw ≤ randLen)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (roundsFit : w32 s.mem g.W 176 + 1 < 2 ^ 32) (uniformFit : w32 s.mem g.W 192 + 1 < 2 ^ 32)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (codeAt draw k g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 152 = used + draw ∧
      w32 t.mem g.W 176 = w32 s.mem g.W 176 + 1 ∧
      w32 t.mem g.W 192 = w32 s.mem g.W 192 + sampled.2.toNat ∧
      w32 t.mem g.W 168 = WitnessStatus.status (Proof.MillerRabin.Round.round c sampled.1)
        (w32 s.mem g.W 176 + 1) (w32 s.mem g.W 192 + sampled.2.toNat) (w32 s.mem g.W 200) ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t := by
  unfold codeAt
  refine WP.seq (WP.mono (WitnessAdvance.codeAt_ok (step := draw) v S source consumed (by omega_using [randLenFit, enough]))
    fun a ⟨A, sourceA, usedA, Oa, Ka⟩ => ?_)
  let input := WitnessInput.geometryAt g rand used (draw / 4)
  have readA : InRegions (a.rd ++ a.wr) (rand.setWidth 64) randLen := by
    rw [Ka.2.1, Ka.2.2]; exact readable
  have C := WitnessInput.context_okAt (used := used) (count := draw / 4) v A.ready.scratch randFit (by omega_using [two, narrow])
    (by unfold Geometry.words; omega_using [wide]) (by omega_using [enough]) readA separate
  have inputSource : input.src.setWidth 64 = off (rand.setWidth 64) used :=
    WitnessInput.source_address (by omega_using [two, narrow, randFit, enough])
  have bytesA : Spec.Rsa.bytesAt a.mem (input.src.setWidth 64) draw =
      Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw := by
    rw [inputSource]
    apply VG.Proof.Bignum.scratch_bytes
      (Oa.mono (o' := 0) (n' := g.L) (by decide) (by have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega_using [this]))
      (by have := randLenFit; omega_using [randFit, enough])
    exact separate.sub_left (Offset.sub_base _ enough)
  refine WP.seq (WP.mono (WitnessRound.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v length A
    C (by change 4 * (draw / 4) = draw; omega_using [four]) two (by change k ≤ draw / 4; omega_using [narrow])
    (by change draw / 4 ≤ g.words; unfold Geometry.words; omega_using [wide]) sourceA
    (WitnessInput.destination_pointer v A.ready.scratch).symm odd large shape fit far lengthFar)
    fun b ⟨B, resultB, uniformB, Wb, Fb, Kb⟩ => ?_)
  rw [bytesA] at resultB uniformB
  have roundB : w32 b.mem g.W 176 = w32 s.mem g.W 176 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have uniB : w32 b.mem g.W 192 = w32 s.mem g.W 192 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have checksB : w32 b.mem g.W 200 = w32 s.mem g.W 200 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have flagB : b.gpr .eax = BitVec.ofNat 32 (Proof.MillerRabin.Round.round c
      (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).1).toNat := by
    exact flag_value resultB
  refine WP.mono (WitnessCount.code_ok v B flagB uniformB (by change w32 b.mem g.W 176 + 1 < 2 ^ 32; rw [roundB]; exact roundsFit)
    (by change w32 b.mem g.W 192 + _ < 2 ^ 32; rw [uniB]; have := Bool.toNat_le (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).2; omega_using [uniformFit, this]))
    fun t ⟨T, countT, uniT, statusT, Ot, Kt⟩ => ?_
  dsimp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.checksOffset] at countT uniT statusT
  rw [roundB] at countT
  rw [uniB] at uniT
  rw [roundB, uniB, checksB] at statusT
  have usedB := (WitnessRound.header32 v Wb (d := 152) (by unfold WitnessRound.safeHeader; decide)).trans usedA
  have usedT : w32 t.mem g.W 152 = used + draw := by
    have same := (WorkspaceFrame.of_outs B.ready.scratch.nowrap Ot).read32
      (d := 152) (by have := v.headerFit; omega_using [this]) (by
        intro r mem
        simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with (rfl | rfl) | rfl <;> left <;> decide)
    rw [show w32 t.mem g.W 152 = w32 b.mem g.W 152 from congrArg BitVec.toNat same]
    exact usedB
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem := WorkspaceFrame.of_outs S.ready.scratch.nowrap
    (Outs.of_outside Oa (by simp [ranges, VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset]))
  have Wb' := Wb.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ WitnessRound.ranges g, r ∈ ranges g)
  have Wt : WorkspaceFrame g (ranges g) b.mem t.mem := WorkspaceFrame.of_outs B.ready.scratch.nowrap
    (Ot.mono (fun r mem => List.mem_append_right _ mem))
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) b.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl) | rfl <;> have := v.headerFit <;>
        simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
          VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T, usedT, countT, uniT, statusT, (Wa.trans Wb').trans Wt, (Fa.trans Fb).trans Ft,
    ((Ka.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessStep
