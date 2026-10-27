module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Feistel
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# The round function on RISC-V, on the machine

The three checks of `Feistel.lean` on the machine, and their composition,
`feistel_ok`: `feistel` XORs the round function of R and the round key at
`a3` into L, keeps memory and the registers `feistelKept`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (inputTable roundChunk roundChunk_bit)

/-- The words of constants in the frame at `sb`, in slots 15–69. -/
def ConstsAt (s : State) : Prop :=
  ∀ c < 55, s.mem.readW (wordAddr (s.gpr sb) (15 + c)) 64 = roundConsts.getD c 0

/-- What the round function needs of the frame: its first 70 words, aligned
and writable (so readable), with the constants. -/
structure FeiReady (s : State) : Prop where
  al : (s.gpr sb).toNat % 8 = 0
  wr : ∀ o < 70, InRegions s.wr (wordAddr (s.gpr sb) o) 8
  consts : ConstsAt s

theorem FeiReady.congr {s t : State} (h : FeiReady s) (hb : t.gpr sb = s.gpr sb)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) : FeiReady t :=
  ⟨by rw [hb]; exact h.al, by rw [hb, hwr]; exact h.wr, by
    intro c hc; rw [hb, hm]; exact h.consts c hc⟩

theorem feiCfg_ok {s : State} (h : FeiReady s) : Ok feiCfg s where
  slotIn k hk := by simp [feiCfg] at hk
  extIn k hk := by
    obtain ⟨r, hr, hc⟩ := h.wr k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  baseAl h0 := by simp [feiCfg] at h0
  extAl _ := h.al
  slots := by decide
  sep k hk := by simp [feiCfg] at hk

theorem constKs_rel {s : State} (h : ConstsAt s) :
    ∀ j v, (j, v) ∈ constKs → s.mem.readW (wordAddr (s.gpr feiCfg.ext) j) 64 = v := by
  intro j v hm
  simp only [constKs, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  obtain ⟨c, hc, rfl, rfl⟩ := hm
  exact h c hc

theorem mem_of_frame_fei {s s' : State} (h : Frame [slotRegion feiCfg s] s.mem s'.mem) :
    s'.mem = s.mem := by
  funext a
  apply h a
  intro r hr hc
  simp only [slotRegion, feiCfg, List.mem_singleton] at hr
  subst r
  simp [Region.Contains] at hc

/-! ## The three parts -/

/-- R and the round key, as input words. -/
def inWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .a2 else s.gpr .t4

theorem feistelIn_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa (ePart ++ kPart ++ maskPart) s = some s' ∧
      (∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((ePart ++ kPart ++ maskPart).all fun i => dst i != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := feistelIn_check
  rw [← feistelIn.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk (feiCfg_ok h) (inWords s)
    (fun r i hri => by
      simp only [inRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun k hk p hp => out (m k) (maskBits k)
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) p hp, rd, wr, sp,
    mem_of_frame_fei frame, keep⟩

/-- Lane `p`'s six input bits. -/
def laneInput (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun k => (s.gpr (m k)).getLsbD p

theorem testBit_laneTables {p c : Nat} (hp : p < 64) (hc : c < 64) :
    laneTables.testBit (64 * p + c) = laneBit p c := by
  rw [laneTables, testBit_blocks (fun p => tableOf_lt _ 64) 64 p c hc, testBit_tableOf]
  simp [hp, hc]

theorem feistelTree_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa treePart s = some s' ∧
      (∀ p < 64, (s'.gpr .t0).getLsbD p = laneBit p (laneInput s p).toNat) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (treePart.all fun i => dst i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelTree_check
  rw [← feistelTree.lit_eq] at hchk
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let cs : Nat → Nat := fun p => (laneInput s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (laneInput s p).isLt
  have hrel : Rel (PosRel 64 cs) feiCfg treeExt treeEnv s := by
    refine ⟨fun r a hr => ?_, fun _ _ hk _ => by simp [feiCfg] at hk, fun j a hj hja => ?_⟩
    · simp only [treeEnv, Option.map_eq_some_iff] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      have hqr := List.find?_some hk
      have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hqr
      subst hqr
      intro p hp
      have hc : (ofBits 6 fun k => (s.gpr (m k)).getLsbD p).toNat < 64 := BitVec.isLt _
      rw [inputTable, testBit_everywhere (tableOf_lt _ 64) hp (hcs p hp), testBit_tableOf]
      simp only [cs, laneInput, hc, decide_true, Bool.true_and, BitVec.testBit_toNat,
        getLsbD_ofBits, hk6]
    · simp only [treeExt] at hja
      split at hja
      · cases hja
        intro p hp
        have hc : j - 15 < 55 := by simp only [feiCfg] at hj; omega
        have hw := h.consts (j - 15) hc
        rw [show 15 + (j - 15) = j by omega] at hw
        rw [testBit_spreadConst hp (hcs p hp), BitVec.testBit_toNat]
        exact congrArg (fun x : BitVec 64 => x.getLsbD p) hw.symm
      · cases hja
  obtain ⟨s', hs', p₀⟩ := run (posTables_sound hcs) posRel_fun (feiCfg_ok h) hrel he
  have hout : e'.reg .t0 = some (.v laneTables) := by
    simp only [treePost, beq_iff_eq] at hpost
    cases hr : e'.reg .t0 with
    | none => rw [hr] at hpost; cases hpost
    | some v => cases v <;> rw [hr] at hpost <;> simp_all [word]
  refine ⟨s', hs', fun p hp => ?_, p₀.rd, p₀.wr, p₀.sp, mem_of_frame_fei p₀.frame,
    fun r hr => p₀.other r (by
      intro hw
      rw [show instrs (Code.block treePart) = treePart from rfl, hr] at hw
      cases hw)⟩
  have hb := p₀.rel.reg .t0 _ hout p hp
  rw [← hb, testBit_laneTables hp (hcs p hp)]

/-- The lanes' tables and L, as input words. -/
def outWords (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .t0 else s.gpr .a1

theorem feistelOut_ok (s : State) (h : FeiReady s) :
    ∃ s', runBlock isa pPart s = some s' ∧
      (∀ q < 64, (s'.gpr .a1).getLsbD q = xorBits (outWords s) (outBits q)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (pPart.all fun i => dst i != some r) = true → s'.gpr r = s.gpr r) := by
  have hchk := feistelOut_check
  rw [← feistelOut.lit_eq] at hchk
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk (feiCfg_ok h) (outWords s)
    (fun r i hri => by
      simp only [outRegs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (kExt_rel (constKs_rel h.consts))
  exact ⟨s', hs', fun q hq => out .a1 outBits (by simp) q hq, rd, wr, sp,
    mem_of_frame_fei frame, keep⟩

/-! ## The round function -/

theorem bitOf_lo (W : Nat → BitVec 64) {a : Nat} (ha : a < 64) : bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

theorem bitOf_hi (W : Nat → BitVec 64) {a : Nat} (ha : a < 64) :
    bitOf W (64 + a) = (W 1).getLsbD a := by
  have hd : (64 + a) / 64 = 1 := by omega
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

theorem maskBits_bounds : ∀ p < 64, ∀ k < 6,
    32 - Spec.TripleDes.expansion.getD (6 * (7 - p / 8) + 5 - k) 1 < 64 ∧
    47 - (6 * (7 - p / 8) + 5 - k) < 64 := by
  intro p _ k _; omega

/-- Each lane's input bits are its S-box's six bits of E of R XORed with
the round key. -/
theorem laneInput_eq {s s' : State}
    (hm : ∀ k < 6, ∀ p < 64, (s'.gpr (m k)).getLsbD p = xorBits (inWords s) (maskBits k p))
    (p : Nat) (hp : p < 64) :
    laneInput s' p = roundChunk (7 - p / 8) ((s.gpr .a2).setWidth 32) ((s.gpr .t4).setWidth 48) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [laneInput, getLsbD_ofBits, roundChunk_bit (7 - p / 8) k (by omega) hk, hm k hk p hp]
  obtain ⟨h1, h2⟩ := maskBits_bounds p hp k hk
  simp only [hk, decide_true, Bool.true_and, maskBits, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_lo _ h1, bitOf_hi _ h2, inWords, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]

/-- The two lanes of an output, in the two halves of its byte, XOR to the
output on every input. -/
theorem lane_pair (b l x : Nat) (hl : l < 4) (hx : x < 64) :
    (laneBit (8 * b + l) x ^^ laneBit (8 * b + l + 4) x) =
      (Spec.TripleDes.sBox (7 - b) (BitVec.ofNat 6 x)).getLsbD (laneOut b l) := by
  have h1 : (8 * b + l) / 8 = b := by omega
  have h2 : (8 * b + l) % 8 = l := by omega
  have h3 : (8 * b + l + 4) / 8 = b := by omega
  have h4 : (8 * b + l + 4) % 8 = l + 4 := by omega
  have h5 : laneOut b (l + 4) = laneOut b l := by
    simp only [laneOut, show (l + 4) % 4 = l % 4 by omega]
  simp only [laneBit, h1, h2, h3, h4, h5, show l / 4 = 0 by omega, show (l + 4) / 4 = 1 by omega]
  rcases (show x / 32 = 0 ∨ x / 32 = 1 by omega) with hx' | hx' <;> simp [hx']

theorem pSrc_shape : ∀ q < 32,
    let t := 32 - Spec.TripleDes.p.getD (31 - q) 1
    t / 4 < 8 ∧ outLane (t / 4) (t % 4) < 4 ∧ laneOut (t / 4) (outLane (t / 4) (t % 4)) = t % 4 := by
  decide +kernel

/-- The registers the round function keeps. -/
def feistelKept : List Reg :=
  [.ra, .s0, .s1, .s2, .s3, .s4, .s11, .a0, .a2, .a3, .a4, .a5, .a6, .a7]

theorem feistelIn_keeps : (.a1 :: feistelKept).all
    (fun r => (instrs feistelIn.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelTree_keeps : (.a1 :: feistelKept).all
    (fun r => (instrs feistelTree.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelOut_keeps : feistelKept.all
    (fun r => (instrs feistelOut.lit).all fun i => dst i != some r) = true := by
  decide +kernel

theorem feistelIn_keep {r : Reg} (hr : r ∈ .a1 :: feistelKept) :
    ((ePart ++ kPart ++ maskPart).all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelIn_keeps r hr
  rw [← feistelIn.lit_eq] at h
  exact h

theorem feistelTree_keep {r : Reg} (hr : r ∈ .a1 :: feistelKept) :
    (treePart.all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelTree_keeps r hr
  rw [← feistelTree.lit_eq] at h
  exact h

theorem feistelOut_keep {r : Reg} (hr : r ∈ feistelKept) :
    (pPart.all fun i => dst i != some r) = true := by
  have h := List.all_eq_true.mp feistelOut_keeps r hr
  rw [← feistelOut.lit_eq] at h
  exact h

theorem runBlock_append' (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem all_append_dst {a b : List Instr} {r : Reg}
    (h : ((a ++ b).all fun i => dst i != some r) = true) :
    (a.all fun i => dst i != some r) = true ∧ (b.all fun i => dst i != some r) = true := by
  simpa only [List.all_append, Bool.and_eq_true] using h

/-- The round function: L XORed with the round function of R and the round
key at `a3`. -/
theorem feistel_ok (s : State) (h : FeiReady s) (l r : BitVec 32)
    (hl : s.gpr .a1 = l.setWidth 64) (hr : s.gpr .a2 = r.setWidth 64)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .a3) 8) (hal : (s.gpr .a3).toNat % 8 = 0) :
    ∃ s', runBlock isa feistel s = some s' ∧
      s'.gpr .a1 = (l ^^^ Spec.TripleDes.roundFunction r
        ((s.mem.readW (s.gpr .a3) 64).setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ feistelKept, s'.gpr q = s.gpr q) := by
  have ha3 : s.gpr .a3 + BitVec.ofNat 64 0 = s.gpr .a3 := BitVec.add_zero _
  let s₀ := s.write .t4 (s.mem.readW (s.gpr .a3) 64)
  have run₀ : runBlock isa keyLoad s = some s₀ := by
    rw [keyLoad, runBlock_cons, exec_load_d (by decide) (by rw [ha3]; exact hal)
      (by rw [ha3]; exact hread), ha3, runStep_some, runBlock_nil]
  have hready₀ : FeiReady s₀ := h.congr (gpr_write_of_ne _ _ (by decide)) rfl rfl
  obtain ⟨s₁, run₁, masks, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := feistelIn_ok s₀ hready₀
  have hready₁ := hready₀.congr (keep₁ sb (feistelIn_keep (by decide))) wr₁ mem₁
  obtain ⟨s₂, run₂, tabs, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := feistelTree_ok s₁ hready₁
  have hready₂ := hready₁.congr (keep₂ sb (feistelTree_keep (by decide))) wr₂ mem₂
  obtain ⟨s₃, run₃, outs, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := feistelOut_ok s₂ hready₂
  have hL₂ : s₂.gpr .a1 = l.setWidth 64 := by
    rw [keep₂ .a1 (feistelTree_keep (by decide)), keep₁ .a1 (feistelIn_keep (by decide)),
      gpr_write_of_ne _ _ (by decide), hl]
  have hR₀ : (s₀.gpr .a2).setWidth 32 = r := by
    rw [gpr_write_of_ne _ _ (by decide), hr]; simp
  have hK₀ : s₀.gpr .t4 = s.mem.readW (s.gpr .a3) 64 := gpr_write_self _ _ _
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    sp₃.trans (sp₂.trans sp₁), mem₃.trans (mem₂.trans mem₁), fun q hq => ?_⟩
  · rw [feistel, runBlock_append', runBlock_append', runBlock_append', run₀, Option.bind_some,
      run₁, Option.bind_some, run₂, Option.bind_some, run₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [outs q hq]
    have hLq : bitOf (outWords s₂) (64 + q) = (l.setWidth 64).getLsbD q := by
      rw [bitOf_hi _ hq]
      simp only [outWords, show (1 : Nat) ≠ 0 by decide, ite_false, hL₂]
    by_cases hq32 : q < 32
    · simp only [outBits, hq32, ite_true, List.cons_append, List.nil_append, xorBits_cons,
        xorBits_nil, Bool.xor_false, hLq]
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, hq, decide_true, Bool.true_and]
      rw [VG.Proof.TripleDes.roundFunction_bit _ _ q hq32]
      simp only []
      obtain ⟨hb, hll, hlo⟩ := pSrc_shape q hq32
      have hsrc : pSrc q = 8 * ((32 - Spec.TripleDes.p.getD (31 - q) 1) / 4) +
          outLane ((32 - Spec.TripleDes.p.getD (31 - q) 1) / 4)
            ((32 - Spec.TripleDes.p.getD (31 - q) 1) % 4) := rfl
      generalize 32 - Spec.TripleDes.p.getD (31 - q) 1 = t at hb hll hlo hsrc ⊢
      generalize hb' : t / 4 = b at hb hll hlo hsrc ⊢
      generalize hl' : outLane b (t % 4) = ll at hll hlo hsrc
      have hs64 : pSrc q < 64 := by omega
      have hs64' : pSrc q + 4 < 64 := by omega
      rw [bitOf_lo _ hs64, bitOf_lo _ hs64']
      simp only [outWords, ite_true]
      rw [tabs _ hs64, tabs _ hs64', laneInput_eq masks _ hs64, laneInput_eq masks _ hs64', hsrc,
        show (8 * b + ll + 4) / 8 = b by omega, show (8 * b + ll) / 8 = b by omega,
        lane_pair b ll _ hll (BitVec.isLt _), hlo, hR₀, hK₀, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      rfl
    · simp only [outBits, hq32, ite_false, List.append_nil, xorBits_cons, xorBits_nil,
        Bool.xor_false, hLq, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor]
      rw [BitVec.getLsbD_of_ge l q (by omega),
        BitVec.getLsbD_of_ge (Spec.TripleDes.roundFunction _ _) q (by omega)]
      rfl
  · have hA : q ∈ .a1 :: feistelKept := List.mem_cons_of_mem _ hq
    have hne : q ≠ .t4 := by revert hq; cases q <;> decide
    rw [keep₃ q (feistelOut_keep hq), keep₂ q (feistelTree_keep hA), keep₁ q (feistelIn_keep hA),
      gpr_write_of_ne _ _ hne]

end VG.Proof.TripleDes.RISCV64
