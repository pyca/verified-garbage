import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# Ed448 base-point multiplication on x86 (32-bit): the loop over the bits

The doubling and addition programs (`Impl/Ed448/Formulas.lean`) run as X448's
verified field operations on the slots (`ops_ok`), and evaluate to `double`
and the specification's `pointAdd` (`baseEnv_r`): `Proof/Ed448/Ref.lean`'s
`ladderStep`. One iteration (`baseStep_ok`) doubles `R` (slots 0–2), adds
`B` (slots 8–10) into `T` (slots 3–5) and swaps `T` into `R` with the mask
of the bit; the loop (`baseLoop_ok`) leaves `R` as the ladder over all 456
bits, `ladder k 456`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double ladderStep ladder ladder_bit pt addWith)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.Ed448.X86 (toOp field baseMask baseSwap baseStep baseLoop)
open VG.Impl.X448.X86 (BITS slot ACC cswap)

/-! ## The field programs -/

def doubleFields : List FieldOp := [
  .add 12 0 1, .mul 12 12 12, .mul 13 0 0, .mul 14 1 1, .add 15 13 14, .mul 16 2 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

def addFields : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

theorem doubleFields_impl : doubleOps.map toOp = doubleFields.map FieldOp.impl := by decide +kernel
theorem addFields_impl : addOps.map toOp = addFields.map FieldOp.impl := by decide +kernel

/-- The slots after an iteration, for the bit `sw`. -/
def baseEnv (sw : Bool) (e : Env) : Env :=
  opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw (applyOps addFields (applyOps doubleFields e))))

theorem baseEnv_pt (sw : Bool) (e : Env) :
    pt (baseEnv sw e) 0 1 2 =
      if sw then addWith (e 11) (double (pt e 0 1 2)) (pt e 8 9 10) else double (pt e 0 1 2) := by
  cases sw <;> rfl

theorem baseEnv_r (sw : Bool) (e : Env) (hq : pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    pt (baseEnv sw e) 0 1 2 = ladderStep sw (pt e 0 1 2) := by
  rw [baseEnv_pt, hq, hd]; rfl

theorem baseEnv_q (sw : Bool) (e : Env) : pt (baseEnv sw e) 8 9 10 = pt e 8 9 10 := by
  cases sw <;> rfl

theorem baseEnv_d (sw : Bool) (e : Env) : baseEnv sw e 11 = e 11 := by
  cases sw <;> rfl

/-! ## One iteration -/

theorem mask_byte : ∀ b < 2, (0 : BitVec 32) - (BitVec.ofNat 8 b).setWidth 32 = mask (decide (b = 1)) := by
  decide

theorem baseMask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .esi = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseMask) s fun u =>
      u.gpr .ebx = mask (decide (b = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  unfold baseMask
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  have ba : u2.ea (Impl.X448.X86.at_ .ebp BITS) = off base (BITS + t) := by
    change (u2.gpr .ebp + BitVec.ofNat 32 BITS).setWidth 64 = _
    rw [v2.gpr]; change (u1.gpr .ebp + u1.gpr .esi + BitVec.ofNat 32 BITS).setWidth 64 = _
    rw [v1.gpr, v1.other .esi (by decide), hb, Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by omega)
  refine wp_load8 ba (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega)) fun u3 v3 => ?_
  refine wp_mov rfl fun u4 v4 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u5 v5 _ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v5.gpr]; change u4.gpr .ebx - u4.gpr .eax = _
    rw [v4.gpr, v4.other .eax (by decide), v3.gpr, v2.mem, v1.mem, hbit]
    exact mask_byte b hb2
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

theorem baseSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base)
    {t : Nat} (ht : t < 456) (hb : s.gpr .esi = BitVec.ofNat 32 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b) :
    WP isa (.block baseSwap) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      u.zf = some (decide (t = 0)) ∧
      E u.mem base = opSwap 2 5 (decide (b = 1)) (opSwap 1 4 (decide (b = 1))
        (opSwap 0 3 (decide (b = 1)) (E s.mem base))) := by
  unfold baseSwap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (baseMask_ok hs ht hb hb2 hbit) fun u1 ⟨c1, k1, m1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have K1 : Keep base s u1 := ⟨k1, by rw [m1]; exact Outside2.refl _ _ _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs1 (m1 ▸ hbd) 0 3 (by decide) c1) fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k2.scr hs1) b2 1 4 (by decide) (c2.trans c1)) fun u3 ⟨k3, b3, c3, e3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k3.scr (k2.scr hs1)) b3 2 5 (by decide) (c3.trans (c2.trans c1)))
    fun u4 ⟨k4, b4, _, e4⟩ => ?_
  refine wp_cmp rfl fun u5 v5 hz => WP.block_nil ?_
  have K5 : Keep base u4 u5 := ⟨v5.rest _, by rw [v5.mem]; exact Outside2.refl _ _ _ _ _ _⟩
  refine ⟨K1.trans (k2.trans (k3.trans (k4.trans K5))), v5.mem ▸ b4, ?_, by rw [v5.mem, e4, e3, e2, m1]⟩
  have esi : u4.gpr .esi = BitVec.ofNat 32 t := by
    rw [k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide),
      k1.1 _ (by decide), hb]
  rw [hz, esi, show BitVec.ofNat 32 t - (0 : BitVec 32) = BitVec.ofNat 32 t from BitVec.sub_zero _,
    ofNat_beq_zero (by omega)]

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure BaseInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  r : pt (E s.mem base) 0 1 2 = ladder k (456 - n)
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E s.mem base 11 = Spec.Ed448.d

theorem bit_lt (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem baseStep_ok {s₀ s : State} {base : Addr} {k n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : BaseInv base k s₀ s (n + 1)) :
    WP isa baseStep s fun t => BaseInv base k s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold baseStep
  refine WP.seq (WP.mono (decCounter_ok (by omega) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  rw [field, doubleFields_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ (m₁ ▸ hi.bounded) doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [field, addFields_impl]
  refine WP.seq (WP.mono (ops_ok (k₂.scr hs₁) bb₂ addFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.mono (baseSwap_ok hs₃ bb₃ (by omega) b₃ (bit_lt k n) bit₃) fun t ⟨k₄, bb₄, z₄, e₄⟩ => ?_
  have core := k₂.trans (k₃.trans k₄)
  have ee : E t.mem base = baseEnv (decide ((k >>> n) &&& 1 = 1)) (E s.mem base) := by
    rw [e₄, e₃, e₂, m₁]; rfl
  refine ⟨⟨core.scr hs₁, bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₄⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p hp hq, m₁]
  · rw [ee, baseEnv_r _ _ hi.q hi.d, hi.r, ladder_bit k hn]; rfl
  · rw [ee, baseEnv_q]; exact hi.q
  · rw [ee, baseEnv_d]; exact hi.d

theorem baseLoop_ok {s₀ s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → BaseInv base k s₀ s' 456) :
    WP isa baseLoop s fun s' => BaseInv base k s₀ s' 0 := by
  unfold baseLoop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := baseStep) (c := .ne) (Q := fun s' => BaseInv base k s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ BaseInv base k s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (baseStep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.X86
