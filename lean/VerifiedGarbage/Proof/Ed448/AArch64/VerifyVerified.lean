import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyErase
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Persist
import VerifiedGarbage.Proof.Ed448.AArch64.Window.SBase
import VerifiedGarbage.Proof.Ed448.AArch64.Window.KInit
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Spec
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Cross
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Result
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Front
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Windows

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.BaseBits`. -/
section

/-!
# Ed448 base-point multiplication on AArch64: the scalar's bits

`bits`: the 57 bytes of the scalar, each expanded into its eight bits at
`BITS` (byte `t` is bit `t`, X448's `bitHead` and `bitJ`), counting `x19`
up to 57; then the output pointer into `x1`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside ofs bitHead bitJ bitHead_ok byteBits_ok bitRegs
  moveOutput_ok)
open VG.Impl.X448.AArch64 (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.x19, .x11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 57) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hb, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(BitVec.ofNat_add _ _).symm, check i hi, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.gpr .x8 = 1 ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++
    ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (VG.Proof.Ed448.AArch64.bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The loop's invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.AArch64.BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => VG.Proof.Ed448.AArch64.BInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => VG.Proof.Ed448.AArch64.BInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.AArch64.BInv base k s₀ s i) ?_ (57 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.AArch64.bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.Ed448.AArch64.BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr,
      hb.scr.nowrap⟩, (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · have hofs : ofs base (off base (BITS + t)) = BITS + t :=
        Mem.sub_ofNat_toNat base (by simp only [BITS]; omega)
      rw [o' _ (by rw [hofs]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

/-- `bits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`; then
`x1` is the output pointer, from `x20`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      s'.gpr .x1 = s.gpr .x20 ∧ (∀ r, r ∉ .x1 :: bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem k 57) >>> t) &&& 1) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => VG.Proof.Ed448.AArch64.BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      VG.Proof.X448.AArch64.Outside.refl _ _ _ _, fun t ht => absurd ht (by omega)⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (moveOutput_ok s₂) fun s₃ ⟨x1₃, m₃, k₃⟩ => ?_
  refine ⟨x1₃.trans (h₂.gpr _ (by decide)), fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr,
    by rw [m₃]; exact h₂.mem, fun t ht => ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [k₃.1 r (by simp only [List.mem_singleton]; exact hr.1)]
    exact h₂.gpr r (by simp only [bitRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.2)
  · rw [m₃, h₂.bits t (by omega), scalar_bit s.mem k ht]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyLocal`. -/
section

/-!
# Ed448 verification's equation on AArch64: the contract its callers use

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.Ed448.verifyEquationContract` it uses,
stated for AArch64), that the function has no frames, and `EqOk`: that it
meets the contract in constant time. `VerifyVerified.lean` proves `EqOk` with
the group law and the field arithmetic; the proofs of the functions that call
`vg_ed448_verify_equation` take it as a hypothesis, which their registration
files pass in, so that they do not import that algebra.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

/-- `vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2, scratch = x3) -> w0`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3

theorem verifyEquation_noFrames : verifyEquation.noFrames = true := by
  rw [← Code.noFrames_eraseImm, verifyEquation_eraseImm]; decide +kernel

/-- `vg_ed448_verify_equation` meets `verifyEquationLocal` and the ABI, in constant time. -/
structure EqOk : Prop where
  ok : ∀ s, verifyEquationLocal.pre s →
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'
  ct : ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain`. -/
section

/-!
# Ed448 verification's equation on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_verify_equation` against `verifyEquationLocal` (`VerifyLocal.lean`):
`x20` ends as the OR of the checks of `S` and of decoding `A` and `R`, and
slots 12–15 hold the cross products of `[4]Q` and `[4]R`, for `Q` the comb's
`[S]B` plus the windows' `[k](-A)`, which decide the equation when `A` and
`R` decode (`verifyEquation_eq`); every write is in the working space, so the
inputs are read unchanged, and the callee-saved registers are restored from
it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off limbs Outside Outside2 ofs far)
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Spec.Ed448 (bytesAt decodeLE)
open VG.Proof.Ed448.AArch64.Window

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [Spec.Ed448.bytesAt]

theorem verifyEquation_correct (hR : RecoverOk) {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa verifyEquation s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ verifyEquationLocal.post s t := by
  obtain ⟨hr, hw, hdk, hds, hdc, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x3 = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x0, 57⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 57) h (by omega)⟩
  have rsg : ∀ i < 114, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x1, 114⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 114) h (by omega)⟩
  have rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x2, 57⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 114, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 i) := fun i hi => far hds hi (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  have hSlt : S < 256 ^ 57 := by
    have h := VG.Proof.Ed448.decodeLE_lt' (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57)
    rwa [bytesAt_len, hS] at h
  unfold verifyEquation
  -- The entry, the checks and the decodings.
  refine WP.seq (WP.mono (wfront_ok hR hbase hws hn rpk rsg rch fpk fsg fch) fun s1 F => ?_)
  have B1 : VG.Proof.X448.AArch64.Base.Bits 57 base S s1.mem := by
    rw [← hS]; exact F.bits
  have P1 : Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)) s1.mem :=
    ⟨F.saved, F.savedX, F.savedV, F.kb⟩
  -- The table.
  refine WP.seq (WP.seq (WP.mono (tabInit_ok F.scr F.bnd) fun s2 I =>
    WP.mono (tabLoop_ok 14 s2 (by decide) (by decide) I.inv) fun s3 T => ?_))
  have P3 := (P1.iframe I.mem).tframe T.mem
  have B3 := Window.Bits.tframe (Window.Bits.iframe B1 I.mem) T.mem
  -- `[S]B`.
  refine WP.seq (WP.mono (sBase_ok T.scr T.env T.zero hSlt B3)
    fun s4 ⟨hs4, b4, z4, rep4, o4, lr4, x4, rd4, wr4⟩ => ?_)
  -- `[k](-A)`, added.
  refine WP.seq (WP.seq (WP.mono (kInit_ok hs4 b4 z4 (T.tab.of_outside2 o4 (by decide)) rfl)
    fun s5 ⟨K5, o5, lr5, x5, rd5, wr5⟩ => WP.mono (kLoop_ok 57 s5 (by decide) (by decide) K5) fun s6 K6 => ?_))
  have P6 := ((P3.outside2 o4).outside2 o5).outside2 K6.ctx.mem
  have hrl : ∀ o, o = RX ∨ o = RY → ∀ i < 8, limbs s6.mem base o i = limbs s2.mem base o i := fun o ho i hi => by
    rw [rlimbs_outside2 K6.ctx.mem ho hi, rlimbs_outside2 o5 ho hi, rlimbs_outside2 o4 ho hi,
      rlimbs_tframe T.mem ho hi]
  have hrx : ∀ i < 8, limbs s6.mem base RX i = limbs s1.mem base (slot 8) i := fun i hi =>
    (hrl _ (.inl rfl) i hi).trans (I.rx i hi)
  have hry : ∀ i < 8, limbs s6.mem base RY i = limbs s1.mem base (slot 9) i := fun i hi =>
    (hrl _ (.inr rfl) i hi).trans (I.ry i hi)
  -- The comparison and the result.
  rw [WP.block_append_iff]
  refine WP.mono (wcross_ok K6.ctx.scr K6.ctx.env K6.ctx.zero K6.ctx.one
    (ib_of_limbs hrx (weak_ib (F.bnd 8))) (ib_of_limbs hry (weak_ib (F.bnd 9))))
    fun s7 ⟨hs7, k7, o7, c7, b7⟩ => ?_
  have P7 := P6.outside2 o7
  refine WP.mono (wfinish_ok hs7 (fun i h1 h2 j hj => Nat.lt_trans (b7 i h1 h2 j hj) (by decide))
    P7.saved P7.savedX P7.savedV) fun t ⟨t0, t19, t20, tx, tv, t30, _, _, _⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : t.gpr .x30 = s.gpr .x30 := by
      rw [t30, k7.1 _ (by decide), K6.ctx.lr, lr5, lr4, T.lr, I.lr, F.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · show t.gpr .x0 = _
    obtain ⟨c0, cA, cR, hx, hc0, hcA, hcR⟩ := F.chk
    have hx7 : s7.gpr .x20 = 0 ||| c0 ||| cA ||| cR := by
      rw [k7.1 _ (by decide), K6.ctx.chk, x5, x4, T.chk, I.chk, hx]
    rw [t0]
    refine if_congr ?_ rfl rfl
    rw [hx7, or_eq_zero64, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x0) 57) with
    | none =>
      rw [VG.Proof.Ed448.verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hRr : Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x1) 57) with
      | none =>
        rw [VG.Proof.Ed448.verifyEquation_none (Or.inr (by rw [bytesAt_take57]; exact hRr))]
        refine ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hRr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hRr]; rfl)
        obtain ⟨rX, rY, rZ⟩ := F.rr r hRr
        have hRpt : (⟨FV s6.mem base RX, FV s6.mem base RY, 1⟩ : Spec.Ed448.Point) = r := by
          rw [FV_of_limbs hrx, FV_of_limbs hry]
          cases r
          simp only at rX rY rZ
          rw [← rX, ← rY, ← rZ]
          rfl
        have hP : slotPt s1.mem base = VG.Proof.Ed448.negPoint a := F.na a ha
        have hSB := rep4
        rw [natCast_zsmul, ← hS, ← bytesAt_drop57] at hSB
        have P5 := (P3.outside2 o4).outside2 o5
        have hb : ∀ i (h : i < 57), s5.mem (off base (KB + i)) =
            (bytesAt s.mem (s.gpr .x2) 57)[i]'(by rw [bytesAt_len]; exact h) := fun i h => by
          rw [P5.kb i h]; simp [Spec.Ed448.bytesAt]
        rw [verifyEquation_eq (bytesAt_len _ _ _) (bytesAt_len _ _ _) (bytesAt_len _ _ _) ha
          (by rw [bytesAt_take57]; exact hRr) hSB _ hb, c7.c12, c7.c13, c7.c14, c7.c15, K6.sb, K6.q, hRpt, hP,
          bytesAt_drop57, hS, cA0, cR0]
        rw [hS] at hc0
        simp only [Nat.sub_zero, dbl2, Spec.Ed448.pointEqual, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          true_and, and_true, hc0]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified`. -/
section

/-!
# Ed448 verification's equation on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness including the ABI,
given decoding's agreement with the specification (`RecoverOk`, which the
registration files pass in); constant time (by taint tracking, phase by phase, `VerifyCT/`: the only
branches are on the counters, every address is an argument plus a constant
or a counter, and the digits' masks only select; checked on the code without
its immediates, `VerifyErase.lean`); and a concrete state satisfying the
signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

def verifyEquationSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct hR hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  obtain ⟨_, e₁⟩ := front_ct
  obtain ⟨_, e₂⟩ := table_ct
  obtain ⟨_, e₃⟩ := sBase_ct
  obtain ⟨_, e₄⟩ := kWindows_ct
  obtain ⟨_, e₅⟩ := tail_ct
  refine Taint.constantTime_eraseImm_of_eq (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ verifyEquation_eraseImm
    (seq_ok e₁ (seq_ok e₂ (seq_ok e₃ (seq_ok e₄ e₅))))
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem verifyEquation_eqOk (hR : Proof.Ed448.RecoverOk) : EqOk := ⟨verifyEquation_ok hR, verifyEquation_ct⟩

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, verifyEquationLocal]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs]
    have h' : t.gpr .x0 = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, -, pk, sig, ch, base⟩ := h
    exact ⟨sp, pk, sig, ch, base⟩
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs] [verifyEquationSat] using verifyEquationSat

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) :
    Verified AArch64.target verifyEquation (Spec.Ed448.verifyEquationContract AArch64.abi) :=
  Verified.of_correct (verifyEquation_ok hR) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.AArch64

end
