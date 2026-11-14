module

public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86.BaseSetup
public import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.X86.Counters
public import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.X448.X86.Iter
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
public import VerifiedGarbage.Proof.X448.X86.Runs
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.X25519.X86

/-! ### `Ed448.X86.BaseStep`, which only this module used -/

section

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

@[expose] public section

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
    exact hs.ea (by omega_arith)
  refine wp_load8 ba (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega_arith)) fun u3 v3 => ?_
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
  have K1 : Keep base s u1 := ⟨k1, by rw [m1]; exact WsOut2.refl _ _ _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs1 (m1 ▸ hbd) 0 3 (by decide) c1) fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k2.scr hs1) b2 1 4 (by decide) (c2.trans c1)) fun u3 ⟨k3, b3, c3, e3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k3.scr (k2.scr hs1)) b3 2 5 (by decide) (c3.trans (c2.trans c1)))
    fun u4 ⟨k4, b4, _, e4⟩ => ?_
  refine wp_cmp rfl fun u5 v5 hz => WP.block_nil ?_
  have K5 : Keep base u4 u5 := ⟨v5.rest _, by rw [v5.mem]; exact WsOut2.refl _ _ _ _ _ _⟩
  refine ⟨K1.trans (k2.trans (k3.trans (k4.trans K5))), v5.mem ▸ b4, ?_, by rw [v5.mem, e4, e3, e2, m1]⟩
  have esi : u4.gpr .esi = BitVec.ofNat 32 t := by
    rw [k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide),
      k1.1 _ (by decide), hb]
  rw [hz, esi, show BitVec.ofNat 32 t - (0 : BitVec 32) = BitVec.ofNat 32 t from BitVec.sub_zero _,
    ofNat_beq_zero (by omega_arith)]

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure BaseInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : WsOut2 base 64 2816 ACC 512 s₀.mem s.mem
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
    rw [hi.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact hbits n hn
  unfold baseStep
  refine WP.seq (WP.mono (decCounter_ok (by omega_arith) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  have hc₁ : CallCtx s₁ base := hi.ctx.keep (g₁ _ (by decide))
  rw [field, doubleFields_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ hc₁ (m₁ ▸ hi.bounded) doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [field, addFields_impl]
  refine WP.seq (WP.mono (ops_ok (k₂.scr hs₁) (k₂.ctx hc₁) bb₂ addFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (BITS + n)) = BitVec.ofNat 8 ((k >>> n) &&& 1) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith), m₁, bitval]
  refine WP.mono (baseSwap_ok hs₃ bb₃ (by omega_arith) b₃ (bit_lt k n) bit₃) fun t ⟨k₄, bb₄, z₄, e₄⟩ => ?_
  have core := k₂.trans (k₃.trans k₄)
  have ee : E t.mem base = baseEnv (decide ((k >>> n) &&& 1 = 1)) (E s.mem base) := by
    rw [e₄, e₃, e₂, m₁]; rfl
  refine ⟨⟨core.scr hs₁, core.ctx hc₁, bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₄⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    rw [core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
  · rw [core.regs.1 _ (by decide), b₁]
  · refine hi.mem.trans ?_
    intro p h8 hp hq
    rw [core.mem p h8 hp hq, m₁]
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
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (baseStep_ok (by omega_arith) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, hi'⟩

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 base-point multiplication on x86 (32-bit): the whole function

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarBaseLocal`, `BaseLocal.lean`: the arguments
only read): it
computes the encoding of the ladder over the scalar's bits
(`scalarBase_ladder`): the entry, the scalar's bits, the loop (`R` ends as
`ladder k 456`), the inversion of `Z` and the encoding. Every write is in the
working space but the result's, so the arguments and the scalar are read
unchanged; the callee-saved registers are restored from the working space,
and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (ladder pt)
open VG.Impl.Ed448.X86 (scalarBase initSlots baseBits baseEntry initVal)
open VG.Impl.X448.X86 (slot BITS ACC at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  scalar_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_out : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 2))

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- The stack the calls use, as `below`. -/
theorem stkR_below {s : State} (h : 20 ≤ (s.gpr .esp).toNat) : stkR s = below (s.gpr .esp) 20 := by
  simp only [below]; rw [VG.X86.Taint.sub_setWidth h]

theorem BasePre.stk_args {s : State} (h : BasePre s) : (stkR s).Disjoint ⟨argAddr s 0, 12⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem BasePre.stk_ret {s : State} (h : BasePre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem BasePre.args {s : State} (h : BasePre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_using [this], by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem initE (e : Env) (he : ∀ i : Index, e i = Proof.X448.toFe (initVal i.val)) :
    pt e 0 1 2 = Spec.Ed448.identity ∧ pt e 8 9 10 = Spec.Ed448.basePoint ∧ e 11 = Spec.Ed448.d := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pt, he]
    rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
      show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · simp only [pt, he]
    rw [show ((8 : Index) : Nat) = 8 from rfl, show ((9 : Index) : Nat) = 9 from rfl,
      show ((10 : Index) : Nat) = 10 from rfl, show initVal 8 = Spec.Ed448.basePoint.X.val from rfl,
      show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self,
      Proof.X448.toFe_self, Proof.X448.toFe_self]
  · rw [he]; exact Proof.X448.toFe_self _

section
variable (σ : State)
/-- The working space and the scalar, from the entry state `σ`. -/
abbrev bsB : Addr := (arg σ 2).setWidth 64
abbrev kB : Nat := decodeLE (bytesAt σ.mem ((arg σ 1).setWidth 64) 57)
end

/-- After the entry block, from the entry state `σ`. -/
structure BMid (σ s : State) : Prop where
  pre : BasePre σ
  fe : FE bsB σ s
  rd : s.rd = σ.rd
  saved : Saved (bsB σ) σ.gpr s.mem
  bits : ∀ t < 456, s.mem (off (bsB σ) (BITS + t)) = BitVec.ofNat 8 ((kB σ >>> t) &&& 1)
  start : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
    s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → BaseInv (bsB σ) (kB σ) s s' 456

theorem entry_stage {s₀ : State} (h : BasePre s₀) :
    WP isa baseEntry s₀ (BMid s₀) := by
  have hA := h.args
  have hin : Input s₀ (bsB s₀) (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) h.scalar_sc
  refine WP.seq (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside (bsB s₀) 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega_using []) (by omega_using [])).trans (o₂.mono (by omega_using []) (by omega_using []))
  unfold baseBits
  refine WP.seq (hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 o02 (by decide)
    fun s₃ u₃ => WP.block_nil ?_)
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem (bsB s₀) i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E l₂ i]
    simp only [E, F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []), u₃.mem]
  have b₄ : BoundedEnv s₄.mem (bsB s₀) := by
    intro i j hj
    rw [o₄.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []) hj, u₃.mem]
    exact initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := initE _ e₄
  have k04 : Keeps [.eax, .ebx, .ebp, .edi, .esi, .edx, .ecx] s₀ s₄ :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans (k₄.mono (by decide)))
  have sp₄ : s₄.gpr .esp = s₀.gpr .esp := k04.1 _ (by decide)
  have hc₄ : CallCtx s₄ (bsB s₀) := ⟨by rw [sp₄]; exact h.sp_room, by
    simp only [callStk, sp₄]; rw [← stkR_below h.sp_room]; exact h.stk_sc.symm⟩
  have o4w : Outside (bsB s₀) 0 8192 s₃.mem s₄.mem := o₄.mono (by omega_using []) (by simp only [BITS]; omega_using [])
  rw [u₃.mem] at o4w
  have ws : (⟨bsB s₀, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
    rw [h.wr]; simp
  refine ⟨h, ⟨⟨hs₄, hc₄, b₄⟩, sp₄, k04.2.2, (Outside.frame (o02.trans o4w)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ws⟩, k04.2.1,
    (sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide), bits₄, fun s' h1 h2 h3 h4 h5 => ?_⟩
  have k' : Keeps (.esi :: workRegs) s₄ s' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
  exact ⟨hs₄.of_keeps k' (by decide), hc₄.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
    h3 ▸ WsOut2.refl _ _ _ _ _ _, by rw [h3, er]; rfl, by rw [h3]; exact eq, by rw [h3]; exact ed⟩

/-- In the loop, `n` iterations from its end, which started in `s₄`. -/
def BL (σ s₄ s : State) (n : Nat) : Prop :=
  BMid σ s₄ ∧ BaseInv (bsB σ) (kB σ) s₄ s n ∧ FE bsB σ s

/-- `FE` from the loop's invariant, for code keeping it. -/
theorem BL.fin {σ s₄ s t : State} {n m : Nat} (h : BL σ s₄ s n) (ht : BaseInv (bsB σ) (kB σ) s₄ t m) :
    FInv (bsB σ) t ∧ t.gpr .esp = s.gpr .esp ∧ t.wr = s.wr :=
  ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, (ht.regs.1 _ (by decide)).trans (h.2.1.regs.1 _ (by decide)).symm,
    ht.regs.2.2.trans h.2.1.regs.2.2.symm⟩

theorem loop_stage {σ s : State} (h : BMid σ s) :
    WP isa Impl.Ed448.X86.baseLoop s fun t => BL σ s t 0 :=
  WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => BaseInv (bsB σ) (kB σ) s t 0) (WP.mono (baseLoop_ok h.bits h.start) fun t ht =>
      ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, ht.regs.1 _ (by decide), ht.regs.2.2, ht⟩))
    fun t ⟨fe, ht⟩ => ⟨h, ht, fe⟩

theorem step_stage {σ s₄ s : State} {n : Nat} (hn : n < 456) (h : BL σ s₄ s (n + 1)) :
    WP isa Impl.Ed448.X86.baseStep s fun t => BL σ s₄ t n ∧ t.zf = some (decide (n = 0)) :=
  WP.mono (h.2.2.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => BaseInv (bsB σ) (kB σ) s₄ t n ∧ t.zf = some (decide (n = 0)))
    (WP.mono (baseStep_ok hn h.1.bits h.2.1) fun t ⟨ht, z⟩ => ⟨(BL.fin h ht).1, (BL.fin h ht).2.1, (BL.fin h ht).2.2, ht, z⟩))
    fun t ⟨fe, ht, z⟩ => ⟨⟨h.1, ht, fe⟩, z⟩

theorem encode_stage {σ s₄ s : State} (h : BL σ s₄ s 0) :
    WP isa Impl.Ed448.X86.baseEncode s fun t => abiPreserved σ t ∧
      bytesAt t.mem ((arg σ 0).setWidth 64) 57 = Spec.Ed448.encodePoint (ladder (kB σ) 456) := by
  obtain ⟨m, hy, fe⟩ := h
  have hp := m.pre
  have hawr : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, 4 * 3⟩ : Region).Disjoint r := by
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.args_out
    · exact hp.args_sc
    · exact hp.stk_args.symm
  refine WP.mono (baseEncode_ok hp.args (by decide) fe.sp (hy.regs.2.1.trans m.rd) fe.wr fe.frame hawr
    fe.fin.scr fe.fin.ctx fe.fin.bounded (by rw [hp.wr]; simp) hp.out_fit hp.out_sc
    (m.saved.wsout2 hy.mem (by decide) (by decide))) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), fe.sp]
  · have ret : (retR σ).Contains ((σ.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((σ.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine (fe.frame.trans ft).readW ret ?_ (by decide)
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_out
    · exact hp.ret_sc
    · exact hp.stk_ret.symm
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r

theorem scalarBase_ladder {s₀ : State} (h : BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (ladder (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57)) 456) := by
  unfold scalarBase
  exact WP.seq (WP.mono (entry_stage h) fun _ m => WP.seq (WP.mono (loop_stage m) fun _ l => encode_stage l))

end VG.Proof.Ed448.X86
