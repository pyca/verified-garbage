module

-- separate module: changes to the Montgomery loop do not recheck the two-prime normalization proof.

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryNormalize
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CarryStore
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma VG.Proof.Bignum.Amm52
open VG.Proof.Poly1305.X86_64.Avx2 (qword256_cat cases4)

private theorem carry_provisional_lt (L : Nat → Nat) {j : Nat}
    (h : ∀ i < j, L i < 2 ^ 63) : provisional L j < 2 ^ 63 := by
  unfold provisional
  have hmod := Nat.mod_lt (L j) (by decide : 0 < 2 ^ 52)
  cases j with
  | zero => simp [priorHigh]; omega
  | succ j =>
    have hj := h j (by omega)
    simp only [priorHigh]
    omega

/-- Each collected bit is the corresponding arithmetic comparison, with no
bits outside the stride layout. -/
theorem collectedCarry_bit (s u : State) (p : Nat) (L : Nat → Nat)
    (hcol : CarryCollected s u p 8) (hL : ∀ i < 32, L i < 2 ^ 63)
    (hrow : ∀ j < 8, ∀ k < 4, collect3072Value s p j k = BitVec.ofNat 64 (provisional L (j + 8 * k)))
    (gt : Bool) (j : Nat) :
    (u.gpr (if gt then .rax else .rcx)).getLsbD j =
      if j < 32 then
        if gt then decide (2 ^ 52 ≤ provisional L j) else decide (provisional L j = 2 ^ 52 - 1)
      else false := by
  rcases hcol with ⟨_, _, _, hbits, _⟩
  by_cases hj : j < 32
  · rw [hbits, collectedBit, ite_eq_left (show j < 32 ∧ j % 8 < 8 by omega),
      hrow (j % 8) (by omega) (j / 8) (by omega),
      show j % 8 + 8 * (j / 8) = j by omega, ite_eq_left hj]
    have hh := carry_provisional_lt L (j := j) fun k hk => hL k (by omega)
    have hh' : provisional L j < 2 ^ 64 := by omega
    have hm : mask52.toNat = 2 ^ 52 - 1 := by decide
    cases gt
    · simp only [Bool.false_eq_true, ite_false, ← BitVec.toNat_inj, BitVec.toNat_ofNat, hm,
        Nat.mod_eq_of_lt hh']
    · simp only [ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh', hm]
      congr 1
  · simp [hbits, collectedBit, hj]

/-- Full masks and the mathematical carry recurrence agree up to the
carry beyond the 32nd limb. -/
theorem collectedExtraCarry (s u : State) (p : Nat) (L : Nat → Nat)
    (hcol : CarryCollected s u p 8) (hL : ∀ i < 32, L i < 2 ^ 63)
    (hrow : ∀ j < 8, ∀ k < 4, collect3072Value s p j k = BitVec.ofNat 64 (provisional L (j + 8 * k)))
    {i : Nat} (hi : i ≤ 32) :
    ((u.gpr .rcx + (u.gpr .rax <<< 1)) ^^^ u.gpr .rcx).getLsbD i = extraCarry L i := by
  apply carryMask_eq_extraCarry L _ _ (by omega)
  · intro j hj
    have e := collectedCarry_bit s u p L hcol hL hrow true j
    simpa only [ite_true, ite_eq_left (show j < 32 by omega)] using e
  · intro j hj
    have e := collectedCarry_bit s u p L hcol hL hrow false j
    simpa only [Bool.false_eq_true, ite_false, ite_eq_left (show j < 32 by omega)] using e

/-- The four carried limbs as a single stride row. -/
def carried3072Row (L : Nat → Nat) (j : Nat) : BitVec 256 :=
  BitVec.ofNat 64 (carried L (j + 24)) ++ BitVec.ofNat 64 (carried L (j + 16)) ++
  BitVec.ofNat 64 (carried L (j + 8)) ++ BitVec.ofNat 64 (carried L j)

theorem carried3072Row_qword (L : Nat → Nat) (j : Nat) {k : Nat} (hk : k < 4) :
    qword256 (carried3072Row L j) k = BitVec.ofNat 64 (carried L (j + 8 * k)) := by
  rw [carried3072Row, qword256_cat _ _ _ _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem aligned3072Row_value (s : State) (p j : Nat) (hj : j < 8) (L : Nat → Nat)
    (hL : ∀ i < 32, L i < 2 ^ 63)
    (hr : ∀ k < 4, qv s (carryAcc3072 p j) k = BitVec.ofNat 64 (provisional L (j + 8 * k)))
    (hm : ∀ k < 4, qv s (vreg 24) k = mask52) (ho : ∀ k < 4, qv s (vreg 25) k = 1)
    (hs : s.gpr .rsi = 0x01010101)
    (hc : ∀ i < 32, (s.gpr .rax).getLsbD i = extraCarry L i) :
    aligned3072Row s p j (s.gpr .rax >>> j) = carried3072Row L j := by
  let t := s.setReg .rax (s.gpr .rax >>> j)
  have hg : t.gpr .rax = s.gpr .rax >>> j := RegUpd.gpr_setReg_self _ _ _
  have hs' : t.gpr .rsi = 0x01010101 :=
    (RegUpd.gpr_setReg_of_ne s _ (show Reg.rsi ≠ .rax by decide)).trans hs
  have hv (r : VReg) (k : Nat) : qv t r k = qv s r k := by cases r <;> rfl
  apply carry_row_ext
  intro k hk
  rw [carried3072Row_qword L j hk]
  change qword256 (normalizedCarryRow t (carryAcc3072 p j)) k = _
  rw [normalizedCarryRow_qword t _ hk (by rw [hv, hm k hk]) (by rw [hv, ho k hk]) hs',
    hg, BitVec.getLsbD_ushiftRight, hc _ (by omega), hv, hr _ hk]
  rw [show ((BitVec.ofBool (extraCarry L (j + 8 * k))).setWidth 64) =
      BitVec.ofNat 64 (extraCarry L (j + 8 * k)).toNat by
      cases extraCarry L (j + 8 * k) <;> decide]
  rw [← BitVec.ofNat_add]
  have hsmall := carry_provisional_lt L (j := j + 8 * k) fun i hi => hL i (by omega)
  have hbit := Bool.toNat_le (extraCarry L (j + 8 * k))
  rw [AmmSym.and_mask (by omega), carried_eq_provisional L _ fun i hi => hL i (by omega)]

def canonicalCarryWrites (p : Nat) (L : Nat → Nat) : List (Nat × BitVec 256) :=
  (List.range 8).map fun j => (lay3072.D * p + 32 * j, carried3072Row L j)

def carryLaneKeeps (p : Nat) (v : VReg) : Prop :=
  (∀ j < 8, v ≠ carryHigh3072 j ∧ v ≠ carryAcc3072 p j) ∧ v ≠ vreg 27

structure CarryLaneResult (s t : State) (p : Nat) (L : Nat → Nat) : Prop where
  mem : t.mem = AmmSym.wrList s.mem (s.gpr .r11) (canonicalCarryWrites p L)
  carry : (if p = 0 then t.gpr .r10 else t.gpr .rsi) = BitVec.ofNat 64 (carryIn L 32)
  preserveRsi : p = 0 → t.gpr .rsi = s.gpr .rsi
  restoreRdx : p = 1 → t.gpr .rdx = s.gpr .r10
  gpr : ∀ q, q ≠ .rax → q ≠ .rcx → q ≠ .rdx → q ≠ .rsi → q ≠ .r10 → t.gpr q = s.gpr q
  vec : ∀ v k, carryLaneKeeps p v → qv t v k = qv s v k
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

private theorem lane_carry_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

private theorem normalize3072Lane_code (p : Nat) :
    normalize3072Lane p = split3072Rows p 8 ++
      ([.eop (.valignq (vreg 27) (carryHigh3072 7) (vreg 26) 3),
        .alu32 .xor .rax (.reg .rax), .alu32 .xor .rcx (.reg .rcx)] : List Instr) ++
      collect3072Rows p 8 ++
      ([.shift .shl .rax 1, .alu .add .rax (.reg .rcx), .alu .xor .rax (.reg .rcx)] : List Instr) ++
      write3072Rows p 8 ++ finish3072Code p := by
  simp only [normalize3072Lane, collect3072Rows, write3072Rows,
    finish3072Code, List.append_assoc]
  rfl

private theorem lane_const_kept (p : Fin 2) :
    carryLaneKeeps p.val (vreg 24) ∧ carryLaneKeeps p.val (vreg 25) ∧ carryLaneKeeps p.val (vreg 26) := by
  have hh : ∀ (p : Fin 2) (j : Fin 8),
      (vreg 24 ≠ carryHigh3072 j.val ∧ vreg 24 ≠ carryAcc3072 p.val j.val) ∧
      (vreg 25 ≠ carryHigh3072 j.val ∧ vreg 25 ≠ carryAcc3072 p.val j.val) ∧
      (vreg 26 ≠ carryHigh3072 j.val ∧ vreg 26 ≠ carryAcc3072 p.val j.val) := by decide
  exact ⟨⟨fun j hj => (hh p ⟨j, hj⟩).1, by decide⟩,
    ⟨fun j hj => (hh p ⟨j, hj⟩).2.1, by decide⟩,
    ⟨fun j hj => (hh p ⟨j, hj⟩).2.2, by decide⟩⟩

private theorem lane_high_ne_acc (p : Fin 2) (j : Fin 8) :
    carryHigh3072 7 ≠ carryAcc3072 p.val j.val :=
  (show ∀ (p : Fin 2) (j : Fin 8), carryHigh3072 7 ≠ carryAcc3072 p.val j.val from by decide) p j

private theorem lane_high_ne_align : carryHigh3072 7 ≠ vreg 27 := by decide

private theorem carry_next_final (c : BitVec 64) : (c >>> 7) >>> 25 = c >>> 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  rw [show 7 + (25 + i) = 32 + i by omega]

/-- Each carry pass implements the scalar carry recurrence for one prime. -/
theorem normalize3072Lane_run (s : State) (p : Nat) (hp : p < 2) (L : Nat → Nat)
    (hL : ∀ i < 32, L i < 2 ^ 63)
    (hraw : ∀ j < 8, ∀ k < 4, qv s (carryAcc3072 p j) k = BitVec.ofNat 64 (L (j + 8 * k)))
    (hm : ∀ k < 4, qv s (vreg 24) k = mask52) (ho : ∀ k < 4, qv s (vreg 25) k = 1)
    (hz : qv s (vreg 26) 3 = 0) (hs : s.gpr .rsi = 0x01010101)
    (hw : ∀ j < 8, InRegions s.wr (s.ea (at_ .r11 (lay3072.D * p + 32 * j))) 32) :
    ∃ t, runBlock isa (normalize3072Lane p) s = some t ∧ CarryLaneResult s t p L := by
  obtain ⟨u, hu, ulo, uhi, uk⟩ := split3072Rows_run s p 8 hp (by decide) hm
  obtain ⟨ug, um, urd, uwr, ux⟩ := split3072Rows_frame s u p 8 hu
  have hconst := lane_const_kept ⟨p, hp⟩
  let a := begin3072Collect u
  obtain ⟨az1, az2, ag, am, ard, awr, ax⟩ := begin3072Collect_frame u
  have amask : ∀ k < 4, qv a (vreg 24) k = mask52 := by
    intro k hk
    rw [begin3072Collect_qv _ _ _ hconst.1.2, uk _ _ hconst.1.1, hm k hk]
  have asi : a.gpr .rsi = 0x01010101 := by rw [ag .rsi (by decide) (by decide), ug, hs]
  have hprovisional : ∀ j < 8, ∀ k < 4,
      collect3072Value a p j k = BitVec.ofNat 64 (provisional L (j + 8 * k)) := by
    intro j hj k hk
    apply provisional3072_qword u p hp L
    · intro i hi v hv
      rw [ulo i hi v hv, hraw i hi v hv, AmmSym.and_mask (by have := hL (i + 8 * v) (by omega); omega)]
    · intro i hi v hv
      rw [uhi i hi v hv, hraw i hi v hv, carry_word_hi _ (by have := hL (i + 8 * v) (by omega); omega)]
    · rw [uk _ _ hconst.2.2.1, hz]
    · exact hj
    · exact hk
  obtain ⟨b, hb, hcol⟩ := collect3072Rows_run a p 8 hp (by decide) amask asi ⟨az1, az2⟩
  have hbit := collectedCarry_bit a b p L hcol hL hprovisional
  have hcarry := @collectedExtraCarry a b p L hcol hL hprovisional
  obtain ⟨br, bv, bg, _, bm, brd, bwr, bx⟩ := hcol
  obtain ⟨c, hc, cmask, cg, cv, cm, crd, cwr, cx⟩ := carryMask_run b
  have hcbit : ∀ i ≤ 32, (c.gpr .rax).getLsbD i = extraCarry L i := by
    intro i hi
    rw [cmask, hcarry hi]
  have c12 (q : Reg) (h1 : q ≠ .rax) (h2 : q ≠ .rcx) (h3 : q ≠ .rdx) :
      c.gpr q = s.gpr q := by rw [cg q h1, bg q h1 h2 h3, ag q h1 h2, ug]
  have cmaskVec : ∀ k < 4, qv c (vreg 24) k = mask52 := by
    intro k hk
    unfold qv
    rw [cv, bv _ (fun j hj => (hconst.1.1 j hj).2)]
    exact amask k hk
  have coneVec : ∀ k < 4, qv c (vreg 25) k = 1 := by
    intro k hk
    have he : qv c (vreg 25) k = qv a (vreg 25) k := by
      unfold qv
      rw [cv, bv _ (fun j hj => (hconst.2.1.1 j hj).2)]
    rw [he, begin3072Collect_qv _ _ _ hconst.2.1.2, uk _ _ hconst.2.1.1, ho k hk]
  have crow (j : Nat) (hj : j < 8) (k : Nat) (hk : k < 4) :
      qv c (carryAcc3072 p j) k = BitVec.ofNat 64 (provisional L (j + 8 * k)) := by
    have he : qv c (carryAcc3072 p j) k = qv b (carryAcc3072 p j) k := by
      unfold qv; rw [cv]
    rw [he, br j hj k hk, hprovisional j hj k hk]
  have cw : c.wr = s.wr := cwr.trans (bwr.trans (awr.trans uwr))
  have cB : c.gpr .r11 = s.gpr .r11 := c12 .r11 (by decide) (by decide) (by decide)
  have csi : c.gpr .rsi = 0x01010101 := (c12 .rsi (by decide) (by decide) (by decide)).trans hs
  obtain ⟨d, dh, da, dm, dv, dg, drd, dwr, dx⟩ :=
    write3072Rows_run c p 8 hp (by decide) (fun j hj => by
      rw [cw]
      change InRegions s.wr (c.gpr .r11 + _) 32
      rw [cB]
      exact hw j hj)
  obtain ⟨t, th, tc, td, ts, tg, tv, tm, trd, twr, tx⟩ := finish3072Code_run d p hp
  have tword : finish3072Value d = BitVec.ofNat 64 (carryIn L 32) := by
    have hhi : qv d (carryHigh3072 7) 3 = BitVec.ofNat 64 (L 31 / 2 ^ 52) := by
      change qword256 (d.vy (carryHigh3072 7)) 3 = _
      rw [dv _ (fun j hj => lane_high_ne_acc ⟨p, hp⟩ ⟨j, hj⟩), cv,
        bv _ (fun j hj => lane_high_ne_acc ⟨p, hp⟩ ⟨j, hj⟩)]
      change qv a (carryHigh3072 7) 3 = _
      rw [begin3072Collect_qv _ _ _ lane_high_ne_align, uhi 7 (by decide) 3 (by decide),
        hraw 7 (by decide) 3 (by decide), carry_word_hi _ (by have := hL (7 + 8 * 3) (by decide); omega)]
    have hfinal : (c.gpr .rax >>> 32) =
        (BitVec.ofBool (extraCarry L 32)).setWidth 64 := by
      rw [cmask, carryMask_high_word]
      · rw [hcarry (by decide : 32 ≤ 32)]
      · intro i hi
        have he := hbit true i
        simpa only [ite_true, ite_eq_right (show ¬ i < 32 by omega)] using he
      · intro i hi
        have he := hbit false i
        simpa only [Bool.false_eq_true, ite_false, ite_eq_right (show ¬ i < 32 by omega)] using he
      · intro i hi
        have he := hbit true i
        have hf := hbit false i
        simp only [Bool.false_eq_true, ite_false, ite_true, ite_eq_left hi] at he hf
        rw [he, hf]
        by_cases h : provisional L i = 2 ^ 52 - 1 <;> simp [h]
    rw [finish3072Value, hhi, da, show 8 - 1 = 7 by decide, carry_next_final, hfinal,
      carryIn_eq_high_add L 32 hL, priorHigh, BitVec.ofNat_add]
    cases extraCarry L 32 <;> rfl
  have htable : carryWrites c p 8 = canonicalCarryWrites p L := by
    unfold carryWrites canonicalCarryWrites
    apply List.map_congr_left
    intro j hj
    have hj8 := List.mem_range.1 hj
    rw [aligned3072Row_value c p j hj8 L hL (crow j hj8) cmaskVec coneVec csi
      (fun i hi => hcbit i (by omega))]
  have hrun : runBlock isa (normalize3072Lane p) s = some t := by
    simp only [normalize3072Lane_code, List.append_assoc]
    rw [lane_carry_append, hu, Option.bind_some,
      lane_carry_append, begin3072Collect_run, Option.bind_some]
    rw [lane_carry_append, hb, Option.bind_some, lane_carry_append, hc, Option.bind_some,
      lane_carry_append, dh, Option.bind_some, th]
  refine ⟨t, hrun, ?_, tc.trans tword, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm, dm, cm, bm, am, um, cB, htable]
  · intro hp0
    rw [ts hp0, dg .rsi (by decide) (by decide), c12 .rsi (by decide) (by decide) (by decide)]
  · intro hp1
    rw [td hp1, dg .r10 (by decide) (by decide), c12 .r10 (by decide) (by decide) (by decide)]
  · intro q h1 h2 h3 h4 h5
    rw [tg q h1 h3 h4 h5, dg q h1 h3, c12 q h1 h2 h3]
  · intro v k hv
    have e : qv t v k = qv a v k := by
      unfold qv
      rw [tv v (hv.1 0 (by decide)).2, dv v (fun j hj => (hv.1 j hj).2), cv v,
        bv v (fun j hj => (hv.1 j hj).2)]
    rw [e, begin3072Collect_qv _ _ _ hv.2, uk _ _ hv.1]
  · exact trd.trans (drd.trans (crd.trans (brd.trans (ard.trans urd))))
  · exact twr.trans (dwr.trans cw)
  · exact tx.trans (dx.trans (cx.trans (bx.trans (ax.trans ux))))

structure CarryPairResult (s t : State) (L : Nat → Nat → Nat) : Prop where
  mem : t.mem = AmmSym.wrList (AmmSym.wrList s.mem (s.gpr .r11) (canonicalCarryWrites 0 (L 0)))
    (s.gpr .r11) (canonicalCarryWrites 1 (L 1))
  carry0 : t.gpr .rdx = BitVec.ofNat 64 (carryIn (L 0) 32)
  carry1 : t.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) 32)
  gpr : ∀ q, q ≠ .rax → q ≠ .rcx → q ≠ .rdx → q ≠ .rsi → q ≠ .r10 → q ≠ .r12 → t.gpr q = s.gpr q
  mask : t.gpr .r12 = mask52
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

private theorem carrySetup_frame (s : State) :
    (carrySetup s).gpr .rsi = 0x01010101 ∧ (carrySetup s).gpr .r12 = mask52 ∧
    (∀ q, q ≠ .rax → q ≠ .rsi → q ≠ .r12 → (carrySetup s).gpr q = s.gpr q) ∧
    (carrySetup s).mem = s.mem ∧ (carrySetup s).rd = s.rd ∧
    (carrySetup s).wr = s.wr ∧ (carrySetup s).mxcsr = s.mxcsr := by
  simp [carrySetup, EOp.exec, vreg, State.setVy, State.setReg, State.setReg32, carryRowMask]
  intro q ha hs h12
  simp [ha, hs, h12]

private theorem carrySetup_acc (s : State) (p : Fin 2) (j : Fin 8) (k : Nat) :
    qv (carrySetup s) (carryAcc3072 p.val j.val) k = qv s (carryAcc3072 p.val j.val) k := by
  have h : ∀ (p : Fin 2) (j : Fin 8), (match carryAcc3072 p.val j.val with
      | .lo _ => true
      | .hi _ => false) = true := by decide
  have he := h p j
  cases hr : carryAcc3072 p.val j.val with
  | lo r => rfl
  | hi r => simp [hr] at he

private theorem lane0_keeps_lane1 (j : Fin 8) : carryLaneKeeps 0 (carryAcc3072 1 j.val) := by
  have h : ∀ (i j : Fin 8), (carryAcc3072 1 j.val ≠ carryHigh3072 i.val ∧
      carryAcc3072 1 j.val ≠ carryAcc3072 0 i.val) ∧ carryAcc3072 1 j.val ≠ vreg 27 := by decide
  exact ⟨fun i hi => (h ⟨i, hi⟩ j).1, (h 0 j).2⟩

/-- The replacement for the scalar store-and-carry pass of the 3072-bit
Montgomery multiplication. -/
theorem normalize3072_run (s : State) (L : Nat → Nat → Nat)
    (hL : ∀ p < 2, ∀ i < 32, L p i < 2 ^ 63)
    (hraw : ∀ p < 2, ∀ j < 8, ∀ k < 4,
      qv s (carryAcc3072 p j) k = BitVec.ofNat 64 (L p (j + 8 * k)))
    (hw : ∀ p < 2, ∀ j < 8, InRegions s.wr (s.ea (at_ .r11 (lay3072.D * p + 32 * j))) 32) :
    ∃ t, runBlock isa normalize3072 s = some t ∧ CarryPairResult s t L := by
  let a := carrySetup s
  obtain ⟨asi, a12, ag, am, ar, aw, ax⟩ := carrySetup_frame s
  have aB := ag .r11 (by decide) (by decide) (by decide)
  have amask (k : Nat) (hk : k < 4) : qv a (vreg 24) k = mask52 := by
    rw [qv, carrySetup_mask, qword256_bcast _ hk]
  have aone (k : Nat) (hk : k < 4) : qv a (vreg 25) k = 1 := by
    rw [qv, carrySetup_one, qword256_bcast _ hk]
    rfl
  have az : qv a (vreg 26) 3 = 0 := by rw [qv, carrySetup_zero]; rfl
  have aRaw (p : Nat) (hp : p < 2) (j : Nat) (hj : j < 8) (k : Nat) (hk : k < 4) :
      qv a (carryAcc3072 p j) k = BitVec.ofNat 64 (L p (j + 8 * k)) :=
    (carrySetup_acc s ⟨p, hp⟩ ⟨j, hj⟩ k).trans (hraw p hp j hj k hk)
  have aW (p : Nat) (hp : p < 2) (j : Nat) (hj : j < 8) :
      InRegions a.wr (a.ea (at_ .r11 (lay3072.D * p + 32 * j))) 32 := by
    rw [aw]
    change InRegions s.wr (a.gpr .r11 + _) 32
    rw [aB]
    exact hw p hp j hj
  obtain ⟨b, hb, hb'⟩ := normalize3072Lane_run a 0 (by decide) (L 0) (hL 0 (by decide))
    (aRaw 0 (by decide)) amask aone az asi (aW 0 (by decide))
  have bB := hb'.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bmask (k : Nat) (hk : k < 4) : qv b (vreg 24) k = mask52 :=
    (hb'.vec _ k (lane_const_kept 0).1).trans (amask k hk)
  have bone (k : Nat) (hk : k < 4) : qv b (vreg 25) k = 1 :=
    (hb'.vec _ k (lane_const_kept 0).2.1).trans (aone k hk)
  have bz : qv b (vreg 26) 3 = 0 := (hb'.vec _ 3 (lane_const_kept 0).2.2).trans az
  have bsi : b.gpr .rsi = 0x01010101 := (hb'.preserveRsi rfl).trans asi
  have braw (j : Nat) (hj : j < 8) (k : Nat) (hk : k < 4) :
      qv b (carryAcc3072 1 j) k = BitVec.ofNat 64 (L 1 (j + 8 * k)) :=
    (hb'.vec _ k (lane0_keeps_lane1 ⟨j, hj⟩)).trans (aRaw 1 (by decide) j hj k hk)
  have bw (j : Nat) (hj : j < 8) : InRegions b.wr (b.ea (at_ .r11 (lay3072.D * 1 + 32 * j))) 32 := by
    rw [hb'.wr]
    change InRegions a.wr (b.gpr .r11 + _) 32
    rw [bB]
    exact aW 1 (by decide) j hj
  obtain ⟨t, ht, ht'⟩ := normalize3072Lane_run b 1 (by decide) (L 1) (hL 1 (by decide)) braw bmask bone bz bsi bw
  have hrun : runBlock isa normalize3072 s = some t := by
    simp only [normalize3072, List.append_assoc]
    rw [lane_carry_append, initialize3072Carry_run, Option.bind_some]
    change runBlock isa (normalize3072Lane 0 ++ normalize3072Lane 1) a = _
    rw [lane_carry_append, hb, Option.bind_some, ht]
  refine ⟨t, hrun, ?_, ?_, ht'.carry, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht'.mem, hb'.mem, aB, bB, aB, am]
  · exact (ht'.restoreRdx rfl).trans hb'.carry
  · intro q ha hc hd hs h10 h12
    exact (ht'.gpr q ha hc hd hs h10).trans ((hb'.gpr q ha hc hd hs h10).trans (ag q ha hs h12))
  · rw [ht'.gpr .r12 (by decide) (by decide) (by decide) (by decide) (by decide),
      hb'.gpr .r12 (by decide) (by decide) (by decide) (by decide) (by decide), a12]
  · exact ht'.rd.trans (hb'.rd.trans ar)
  · exact ht'.wr.trans (hb'.wr.trans aw)
  · exact ht'.mxcsr.trans (hb'.mxcsr.trans ax)

def pairCarryWrites (L : Nat → Nat → Nat) : List (Nat × BitVec 256) :=
  canonicalCarryWrites 0 (L 0) ++ canonicalCarryWrites 1 (L 1)

theorem mem_pairCarryWrites (L : Nat → Nat → Nat) (w : Nat × BitVec 256)
    (hw : w ∈ pairCarryWrites L) :
    ∃ p < 2, ∃ j < 8, w = (lay3072.D * p + 32 * j, carried3072Row (L p) j) := by
  rcases List.mem_append.1 hw with h | h
  · obtain ⟨j, hj, e⟩ := List.mem_map.1 h
    exact ⟨0, by decide, j, List.mem_range.1 hj, e.symm⟩
  · obtain ⟨j, hj, e⟩ := List.mem_map.1 h
    exact ⟨1, by decide, j, List.mem_range.1 hj, e.symm⟩

private theorem canonicalCarryWrites_append (m : Mem) (b : Addr) (a c : List (Nat × BitVec 256)) :
    AmmSym.wrList m b (a ++ c) = AmmSym.wrList (AmmSym.wrList m b a) b c := by
  induction a generalizing m with
  | nil => rfl
  | cons w a ih => cases w; exact ih _

theorem CarryPairResult.mem_pair {s t : State} {L : Nat → Nat → Nat} (h : CarryPairResult s t L) :
    t.mem = AmmSym.wrList s.mem (s.gpr .r11) (pairCarryWrites L) := by
  rw [h.mem, pairCarryWrites, canonicalCarryWrites_append]

open VG.Proof.Bignum (word)

/-- Reading the stored stride layout gives the carried value of any limb. -/
theorem CarryPairResult.word {s t : State} {L : Nat → Nat → Nat} (h : CarryPairResult s t L)
    (p q : Nat) (hp : p < 2) (hq : q < 32) :
    word t.mem (s.gpr .r11) (lay3072.D * p + lay3072.off q) =
      BitVec.ofNat 64 (carried (L p) q) := by
  let j := q % 8
  let k := q / 8
  let e := lay3072.D * p + 32 * j
  let v := carried3072Row (L p) j
  have hj : j < 8 := by omega
  have hk : k < 4 := by omega
  have dEq : lay3072.D = 10336 := by decide
  have eh : lay3072.D * p + lay3072.off q = e + 8 * k := by
    change lay3072.D * p + (32 * (q % 8) + 8 * (q / 8)) = _
    simp only [e, j, k, Nat.add_assoc]
  have hE : e + 32 ≤ 2 ^ 63 := by rw [show e = lay3072.D * p + 32 * j from rfl, dEq]; omega
  have hmem : (e, v) ∈ pairCarryWrites L := by
    rcases (show p = 0 ∨ p = 1 by omega) with hp0 | hp1
    · unfold pairCarryWrites
      apply List.mem_append_left
      exact List.mem_map.2 ⟨j, List.mem_range.2 hj, by simp [e, v, hp0]⟩
    · unfold pairCarryWrites
      apply List.mem_append_right
      exact List.mem_map.2 ⟨j, List.mem_range.2 hj, by simp [e, v, hp1]⟩
  rw [h.mem_pair, eh, AmmSym.word_wrList_unique (v := v) (t := k) _ hk hE _ _ hmem]
  · change qword256 (carried3072Row (L p) j) k = _
    rw [carried3072Row_qword _ _ hk, show j + 8 * k = q by omega]
  · intro w hw
    obtain ⟨p', hp', j', hj', rfl⟩ := mem_pairCarryWrites L w hw
    change lay3072.D * p' + 32 * j' + 32 ≤ 2 ^ 63 ∧ _
    dsimp only [e]
    rw [dEq]
    omega
  · intro w hw he
    obtain ⟨p', hp', j', hj', rfl⟩ := mem_pairCarryWrites L w hw
    change lay3072.D * p' + 32 * j' = lay3072.D * p + 32 * j at he
    rw [dEq] at he
    have hp_eq : p' = p := by omega
    have hj_eq : j' = j := by omega
    subst p' j'
    rfl

end VG.Proof.Bignum.X86_64.Ifma
