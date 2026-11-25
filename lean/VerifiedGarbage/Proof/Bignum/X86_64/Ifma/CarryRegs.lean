module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma

/-- Vector and scalar constants that are live across both carry passes. -/
def carrySetup (s : State) : State :=
  let s := s.setReg .r12 mask52
  let s := (EOp.vmovq (vreg 24) .r12).exec s
  let s := (EOp.vpbroadcastq (vreg 24) (vreg 24)).exec s
  let s := s.setReg32 .rax 1
  let s := (EOp.vmovq (vreg 25) .rax).exec s
  let s := (EOp.vpbroadcastq (vreg 25) (vreg 25)).exec s
  let s := (EOp.bin .vpxorq (vreg 26) (vreg 26) (vreg 26)).exec s
  s.setReg32 .rsi carryRowMask

theorem initialize3072Carry_run (s : State) :
    runBlock isa initialize3072Carry s = some (carrySetup s) := by
  simp only [initialize3072Carry, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, Option.map_some]
  rfl

/-- The initialized constants occupy only high vector registers, so all
sixteen accumulator rows retain their values. -/
theorem carrySetup_lo (s : State) (r : XReg) :
    (carrySetup s).vy (.lo r) = s.vy (.lo r) := rfl

theorem carrySetup_mask (s : State) :
    (carrySetup s).vy (vreg 24) = mask52 ++ mask52 ++ mask52 ++ mask52 := by
  have h : ((0 : BitVec 192) ++ mask52).extractLsb' 0 64 = mask52 :=
    qword256_low mask52 (k := 0) (by decide)
  simp [carrySetup, EOp.exec, vreg, State.setReg32, State.setReg, State.vy, State.setVy, qword256]
  let q := ((0 : BitVec 192) ++ mask52).extractLsb' 0 64
  change q ++ q ++ q ++ q = mask52 ++ mask52 ++ mask52 ++ mask52
  rw [show q = mask52 from h]

theorem carrySetup_one (s : State) :
    (carrySetup s).vy (vreg 25) = (1#64) ++ (1#64) ++ (1#64) ++ (1#64) := by
  simp [carrySetup, EOp.exec, vreg, State.setReg32, State.setReg, State.vy, State.setVy, qword256]

theorem carrySetup_zero (s : State) :
    (carrySetup s).vy (vreg 26) = 0 := by
  simp [carrySetup, EOp.exec, EBinOp.sse, lanes256, XBinOp.eval, vreg, State.vy, State.setVy,
    lane256, State.setReg32, State.setReg]

open VG.Proof.Poly1305.X86_64.Avx2 (qword_and qword_psrlq)

/-- Actual instruction semantics for the split of one stride row. -/
theorem split3072Row_run (s : State) (r high : VReg) (hr : r ≠ high) (hm : vreg 24 ≠ high)
    (hmask : ∀ k < 4, qv s (vreg 24) k = mask52) :
    ∃ t, runBlock isa (split3072Row r high) s = some t ∧
      (∀ k < 4, qv t r k = qv s r k &&& mask52) ∧
      (∀ k < 4, qv t high k = qv s r k >>> 52) ∧
      (∀ v k, v ≠ high → v ≠ r → qv t v k = qv s v k) := by
  let mid := (EOp.shift .vpsrlq high r 52).exec s
  let t := (EOp.bin .vpandq r r (vreg 24)).exec mid
  refine ⟨t, rfl, ?_, ?_, ?_⟩
  · intro k hk
    change qv (mid.setVy r (lanes256 XBinOp.pand.eval (mid.vy r) (mid.vy (vreg 24)))) r k = _
    rw [qv_setVy, ite_eq_left rfl, qword256_lanes _ _ _ hk]
    simp only [XBinOp.eval]
    rw [qword_and, qword_lane256, qword_lane256]
    change qv mid r k &&& qv mid (vreg 24) k = _
    change qv (s.setVy high _) r k &&& qv (s.setVy high _) (vreg 24) k = _
    rw [qv_setVy, ite_eq_right hr, qv_setVy, ite_eq_right hm]
    rw [hmask k hk]
  · intro k hk
    change qv (mid.setVy r _) high k = _
    rw [qv_setVy, ite_eq_right (Ne.symm hr)]
    change qv (s.setVy high _) high k = _
    rw [qv_setVy, ite_eq_left rfl, qword256_lanes _ _ _ hk]
    simp only [ZShiftOp.sse]
    rw [qword_psrlq _ (by decide) (Nat.mod_lt _ (by decide)), qword_lane256]
    rfl
  · intro v k hh hr
    change qv (mid.setVy r _) v k = _
    rw [qv_setVy, ite_eq_right hr]
    change qv (s.setVy high _) v k = _
    rw [qv_setVy, ite_eq_right hh]

open VG.Proof.Poly1305.X86_64.Avx2 (qword256_cat cases4)

/-- The register mask controls each result quadword independently. -/
theorem qword256_maskAddQ (mask : BitVec 64) (d a b : BitVec 256) {j : Nat} (hj : j < 4) :
    qword256 (maskAddQ mask d a b) j =
      if mask.getLsbD j then qword256 a j + qword256 b j else qword256 d j := by
  rw [maskAddQ, qword256_cat _ _ _ _ hj]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-- Bit `j` of the compare result is the selected comparison in lane `j`. -/
theorem cmpUqMask_bit (gt : Bool) (a b : BitVec 256) {j : Nat} (hj : j < 4) :
    (cmpUqMask gt a b).getLsbD j =
      if gt then decide ((qword256 b j).toNat < (qword256 a j).toNat)
      else decide (qword256 a j = qword256 b j) := by
  let test := fun k => if gt then decide ((qword256 b k).toNat < (qword256 a k).toNat)
    else decide (qword256 a k = qword256 b k)
  have h : ∀ (a0 a1 a2 a3 : Bool) (k : Fin 4),
      (BitVec.ofNat 32 (a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat)).getLsbD k.val =
        (if k.val = 0 then a0 else if k.val = 1 then a1 else if k.val = 2 then a2 else a3) := by decide
  have he : cmpUqMask gt a b = BitVec.ofNat 32
      ((test 0).toNat + 2 * (test 1).toNat + 4 * (test 2).toNat + 8 * (test 3).toNat) := by
    have ha (c : Prop) [Decidable c] (u n : Nat) :
        (if c then u + n else u) = u + n * (decide c).toNat := by
      by_cases h : c <;> simp [h]
    cases gt <;> simp [cmpUqMask, test, qword256, List.range_succ, ha] <;> rfl
  rw [he, h _ _ _ _ ⟨j, hj⟩]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

private theorem carry_runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

private theorem carryAcc3072_index :
    ∀ (p : Fin 2) (j : Fin 8), vi (carryAcc3072 p.val j.val) = 8 * p.val + (j.val + 6) % 8 := by decide

private theorem carryHigh3072_index :
    ∀ (j : Fin 8), vi (carryHigh3072 j.val) = 16 + j.val := by decide

private theorem carryAcc3072_ne (p q i j : Nat) (hp : p < 2) (hq : q < 2) (hi : i < 8) (hj : j < 8)
    (h : p ≠ q ∨ i ≠ j) : carryAcc3072 p i ≠ carryAcc3072 q j := by
  intro he
  have e := congrArg vi he
  rw [carryAcc3072_index ⟨p, hp⟩ ⟨i, hi⟩, carryAcc3072_index ⟨q, hq⟩ ⟨j, hj⟩] at e
  change 8 * p + (i + 6) % 8 = 8 * q + (j + 6) % 8 at e
  have ep : p = q := by omega
  have ei : i = j := by omega
  exact h.elim (fun h => h ep) (fun h => h ei)

private theorem carryHigh3072_ne (i j : Nat) (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    carryHigh3072 i ≠ carryHigh3072 j := by
  intro he
  have e := congrArg vi he
  rw [carryHigh3072_index ⟨i, hi⟩, carryHigh3072_index ⟨j, hj⟩] at e
  exact h (Nat.add_left_cancel e)

private theorem carryAcc3072_ne_high (p i j : Nat) (hp : p < 2) (hi : i < 8) (hj : j < 8) :
    carryAcc3072 p i ≠ carryHigh3072 j := by
  intro he
  have e := congrArg vi he
  rw [carryAcc3072_index ⟨p, hp⟩ ⟨i, hi⟩, carryHigh3072_index ⟨j, hj⟩] at e
  omega

private theorem mask_ne_carry (p j : Nat) (hp : p < 2) (hj : j < 8) :
    vreg 24 ≠ carryAcc3072 p j ∧ vreg 24 ≠ carryHigh3072 j := by
  constructor
  · intro he
    have e := congrArg vi he
    rw [vi_vreg _ (by decide), carryAcc3072_index ⟨p, hp⟩ ⟨j, hj⟩] at e
    omega
  · intro he
    have e := congrArg vi he
    rw [vi_vreg _ (by decide), carryHigh3072_index ⟨j, hj⟩] at e
    omega

private theorem split3072Rows_join (s u t : State) (p n : Nat)
    (h₁ : runBlock isa (split3072Rows p n) s = some u)
    (h₂ : runBlock isa (split3072Row (carryAcc3072 p n) (carryHigh3072 n)) u = some t) :
    runBlock isa (split3072Rows p (n + 1)) s = some t := by
  have h : split3072Rows p (n + 1) = split3072Rows p n ++
      split3072Row (carryAcc3072 p n) (carryHigh3072 n) := by
    simp only [split3072Rows, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [h, carry_runBlock_append, h₁, Option.bind_some, h₂]

/-- The split phase converts each row to high and low parts without changing
the other prime's accumulator registers or the carry constants. -/
theorem split3072Rows_run (s : State) (p n : Nat) (hp : p < 2) (hn : n ≤ 8)
    (hm : ∀ k < 4, qv s (vreg 24) k = mask52) :
    ∃ t, runBlock isa (split3072Rows p n) s = some t ∧
      (∀ j < n, ∀ k < 4, qv t (carryAcc3072 p j) k = qv s (carryAcc3072 p j) k &&& mask52) ∧
      (∀ j < n, ∀ k < 4, qv t (carryHigh3072 j) k = qv s (carryAcc3072 p j) k >>> 52) ∧
      (∀ v k, (∀ j < n, v ≠ carryHigh3072 j ∧ v ≠ carryAcc3072 p j) → qv t v k = qv s v k) := by
  induction n with
  | zero =>
    refine ⟨s, runBlock_nil, ?_, ?_, fun _ _ _ => rfl⟩ <;> simp
  | succ n ih =>
    have h8 : n < 8 := by omega
    obtain ⟨u, hu, hlo, hhi, hkeep⟩ := ih (by omega)
    have hmu : ∀ k < 4, qv u (vreg 24) k = mask52 := by
      intro k hk
      rw [hkeep _ _ (fun j hj => ⟨(mask_ne_carry p j hp (by omega)).2, (mask_ne_carry p j hp (by omega)).1⟩), hm k hk]
    have hnew : ∀ k, qv u (carryAcc3072 p n) k = qv s (carryAcc3072 p n) k := by
      intro k
      apply hkeep
      intro j hj
      exact ⟨carryAcc3072_ne_high p n j hp h8 (by omega),
        carryAcc3072_ne p p n j hp hp h8 (by omega) (.inr (by omega))⟩
    obtain ⟨t, ht, tl, th, tk⟩ := split3072Row_run u _ _
      (carryAcc3072_ne_high p n n hp h8 h8) (mask_ne_carry p n hp h8).2 hmu
    refine ⟨t, split3072Rows_join s u t p n hu ht, ?_, ?_, ?_⟩
    · intro j hj k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · rw [tk _ _ (carryAcc3072_ne_high p j n hp (by omega) h8)
          (carryAcc3072_ne p p j n hp hp (by omega) h8 (.inr (by omega))), hlo j h k hk]
      · rw [tl k hk, hnew k]
    · intro j hj k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · rw [tk _ _ (carryHigh3072_ne j n (by omega) h8 (by omega))
          (Ne.symm (carryAcc3072_ne_high p n j hp h8 (by omega))), hhi j h k hk]
      · rw [th k hk, hnew k]
    · intro v k h
      rw [tk _ _ (h n (by omega)).1 (h n (by omega)).2, hkeep _ _ (fun j hj => h j (by omega))]

open VG.Proof.Poly1305.X86_64.Avx2 (qword_paddq)

/-- A vector addition computes the provisional limbs independently. -/
theorem qv_add_row (s : State) (d a b : VReg) {k : Nat} (hk : k < 4) :
    qv ((EOp.bin .vpaddq d a b).exec s) d k = qv s a k + qv s b k := by
  change qv (s.setVy d (lanes256 XBinOp.paddq.eval (s.vy a) (s.vy b))) d k = _
  rw [qv_setVy, ite_eq_left rfl, qword256_lanes _ _ _ hk,
    qword_paddq _ _ (Nat.mod_lt _ (by decide)), qword_lane256, qword_lane256]
  rfl

/-- The first stride row uses zero for limb zero, and the high word of the
preceding row group for each subsequent limb. -/
theorem qv_align_row (s : State) {k : Nat} (hk : k < 4) :
    qv ((EOp.valignq (vreg 27) (carryHigh3072 7) (vreg 26) 3).exec s) (vreg 27) k =
      if k = 0 then qv s (vreg 26) 3 else qv s (carryHigh3072 7) (k - 1) := by
  change qv (s.setVy (vreg 27) (alignQwords (s.vy (carryHigh3072 7)) (s.vy (vreg 26)) 3)) (vreg 27) k = _
  rw [qv_setVy, ite_eq_left rfl, qword256_align _ _ _ hk (by decide)]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Bignum.X86_64.Ifma
