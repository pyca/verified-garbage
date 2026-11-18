module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.Ed448.RISCV64.VJoint
import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarBit
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.X448.RISCV64.R64.Lit
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.X448.RISCV64.R64.Lit

/-! ### `Ed448.RISCV64.VCT`, which this module and modules that import it used -/

section

/-!
# Ed448's verification equation on RISCV64: the pieces the taint analysis checks

Every piece of `verifyEquation` but the joint loop's branches on its digits
is constant time from the registers it addresses through and its counters
(`taint_decide`). The branches are on digits of `S` and `k`, which two runs
with the same inputs share, and each branch is constant time from the digit
(`VTiming.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64

/-- Code the taint analysis checks from the registers `rs`. -/
theorem ctp {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨(hP a b hab).1, fun r hr => (hP a b hab).2 r (Taint.mem_ofRegs.mp hr)⟩) h

variable {P : State → State → Prop}

theorem prefix_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], a.gpr r = b.gpr r) :
    RelCT isa P vPrefix fun _ _ => True := ctp _ hP (by taint_decide)

theorem init_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ ([.li .t1 464] : List Instr)))
      fun _ _ => True := ctp _ hP (by taint_decide)

theorem dec_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block [.addi .t1 .t1 (-1)]) fun _ _ => True := ctp _ hP (by taint_decide)

theorem dbl_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P (opsProg dblOps) fun _ _ => True := ctp _ hP (by taint_decide)

theorem load2_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block (loadDigit 2)) fun _ _ => True := ctp _ hP (by taint_decide)

theorem load3_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block (loadDigit 3)) fun _ _ => True := ctp _ hP (by taint_decide)

theorem baseBody_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3, .a5], a.gpr r = b.gpr r) :
    RelCT isa P baseBody fun _ _ => True := ctp _ hP (by taint_decide)

theorem keyBody_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3, .a5], a.gpr r = b.gpr r) :
    RelCT isa P keyBody fun _ _ => True := ctp _ hP (by taint_decide)

theorem addNegR_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P addNegR fun _ _ => True := ctp _ hP (by taint_decide)

theorem vFinish_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3], a.gpr r = b.gpr r) :
    RelCT isa P (.block vFinish) fun _ _ => True := ctp _ hP (by taint_decide)

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecode`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VSel`, which this module and modules that import it used -/

section

/-!
# Ed448 on RISCV64: selections as updates of the slots

`sel o q r` as an update of the slots `qs` (`selG`): `o` (a slot of the field
area, separate from the others or one of them) gets `pick sw x y` for the
elements `x` and `y` at `q` and `r`, which may be anywhere in the working
space, `q` even `o` itself.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (Fe)

section
variable {b : Addr}

theorem fs_pick {m m' : Mem} {o q r : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 14, limb m' b o j = VG.Proof.X25519.sel sw (limb m b q j) (limb m b r j)) :
    FS m' b o = pick sw (FS m b q) (FS m b r) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [FS, V, val32_congr (g := limb m b q) fun j hj => h j hj]; rfl
  · rw [FS, V, val32_congr (g := limb m b r) fun j hj => h j hj]; rfl

theorem selG {o q r : Nat} {qs : List Nat} {v : Nat → Fe} {x y : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hqf : q + 56 ≤ 2048) (hrf : r + 56 ≤ 2048)
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o ∨ o = q) (hor : o + 56 ≤ r ∨ r + 56 ≤ o)
    (hq4 : q % 4 = 0) (hr4 : r % 4 = 0) {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) (hx : FS s.mem b q = x) (hy : FS s.mem b r = y) :
    WP isa (.block (sel o q r)) s fun s' => Rest [.a2, .a4] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (pick sw x y)) := by
  have hA := X448.RISCV64.ACC_eq
  refine WP.mono (sel_ok (b := b) (o := o) (q := q) (r := r) (by omega_using [ho, hA]) hqf hrf hoq hor (sep1_o hq) hq4 hr4 hc hsw h11)
    fun s' h => ⟨h.rest, ?_, fun q' hq' => ?_⟩
  · exact h.frame.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hx]; exact Offset.sub_base _ (by omega_using [ho])⟩
  · by_cases hqo : q' = o
    · subst hqo
      rw [upd_self, fs_pick hsw h.lo, hx, hy]
    · rw [upd_of_ne _ _ hqo]
      exact slots_after hq ho (frame_o (h.frame : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] _ _)) hS
        ((List.mem_cons.mp hq').resolve_left hqo) hqo

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecodeCheck`, which this module and modules that import it used -/

section

/-! ### `Ed448.RISCV64.VDecodeY`, which this module and modules that import it used -/

section

/-!
# Ed448's verification on RISCV64: the y-coordinate of a point

`decodeY p` copies the words of the 56 bytes at `p` into `DY` and `X2`,
checks that they are their full reduction (so `y < p`) and that bits 0–6
of byte 56 are 0, stores bit 7 at `SIGN`, and writes 1 to `DON`
(`decodeY_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC freeze)
open VG.Spec.X448 (P)

/-- The number of the 56 bytes at `p`, as fourteen words. -/
def yw (m : Mem) (b : Addr) (p : Nat) : Nat := val32 (fun k => wd m b (p + 4 * k)) 14

section
variable {b : Addr}

/-- After `k` words of the copy. -/
structure CpInv (b : Addr) (p : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 DY, 4 * k⟩, ⟨b + BitVec.ofNat 64 X2, 4 * k⟩] s0.mem s.mem
  vals : ∀ j < k, limb s.mem b DY j = wd s0.mem b (p + 4 * j) ∧ limb s.mem b X2 j = wd s0.mem b (p + 4 * j)

theorem copyIn_ok {s0 : State} (hc : Ctx b s0) {p : Nat} (hp : p + 56 ≤ 2048) (hp' : 1064 ≤ p) (hp4 : p % 4 = 0) :
    WP isa (.block ((List.range 14).flatMap fun k => [.load .w .a4 .a3 (p + 4 * k),
      .store .w .a4 .a3 (DY + 4 * k), .store .w .a4 .a3 (X2 + 4 * k)])) s0 (CpInv b p s0 14) := by
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  refine wp_range_flatMap (M := isa) (CpInv b p s0) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  obtain win : wd s.mem b (p + 4 * k) = wd s0.mem b (p + 4 * k) :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
      · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine lw0_ok hcs (d := p + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
  obtain hc1 : Ctx b t1 := hcs.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)
  refine sw0_ok hc1 (d := DY + 4 * k) (by omega_arith) (by omega_arith) fun t2 v2 => ?_
  refine sw0_ok (hc1.of_rest (v2.rest []) (by decide)) (d := X2 + 4 * k) (by omega_arith) (by omega_arith)
    fun t3 v3 => WP.block_nil ?_
  obtain ev : ((t1.gpr .a4).setWidth 32).toNat = wd s0.mem b (p + 4 * k) := by
    rw [v1.gpr, lo32_ext, ← win]; rfl
  obtain ev2 : t2.gpr .a4 = t1.gpr .a4 := by rw [v2.gpr]
  obtain hm3 : t3.mem = (s.mem.writeW (b + BitVec.ofNat 64 (DY + 4 * k)) ((t1.gpr .a4).setWidth 32)).writeW
      (b + BitVec.ofNat 64 (X2 + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [v3.mem, ev2, v2.mem, v1.mem]
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans ((v2.rest _).trans (v3.rest _))), ?_, fun j hj => ?_⟩
  · rw [hm3]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
  · rw [limb, limb, hm3]
    rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.vals j hj
    · exact ⟨by rw [wd_write_self, ev], by rw [wd_write_self, ev]⟩

/-- The frame of decoding's first part. -/
abbrev yW (b : Addr) : List Region :=
  [FA b, ⟨b + BitVec.ofNat 64 OUT, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 SIGN, 1⟩]

/-- A byte at an offset in `[1064, 1696)` or from `1705` up to `2048` is outside `yW`. -/
theorem yW_byte {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d)
    (hd' : d + 1 ≤ 1696 ∨ 1705 ≤ d ∧ d + 1 ≤ 2048) :
    m' (b + BitVec.ofNat 64 d) = m (b + BitVec.ofNat 64 d) := by
  obtain ⟨h1, h2, h3, h4⟩ := offs
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact fun h => Offset.disjoint_base b (d := d) (n := 1) (k := ACC + 112) (by omega_arith)
      (by omega_arith) _ (Region.contains_self _ _) h
  all_goals exact fun h => Offset.disjoint b (d := d) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h

theorem yW_wd {m m' : Mem} (hf : Frame (yW b) m m') {d : Nat} (hd : 1064 ≤ d) (hd' : d + 4 ≤ 1696) :
    wd m' b d = wd m b d := by
  obtain ⟨h1, h2, h3, h4⟩ := offs
  refine wd_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base b (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)

theorem toNat_and127 (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x &&& BitVec.ofNat 64 127).toNat = x % 128 := by
  rw [BitVec.toNat_and, toNat_imm hx, toNat_imm (by decide),
    show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem decodeY_ok {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p) (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) :
    WP isa (.block (decodeY p)) s fun t => VCtx b t ∧ Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0] s t ∧
      Frame (yW b) s.mem t.mem ∧ V t.mem b DY = yw s.mem b p ∧ V t.mem b DON = 1 ∧
      FS t.mem b DK = FS s.mem b DK ∧
      t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 ((s.mem (b + BitVec.ofNat 64 (p + 56))).toNat / 128) ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧ yw s.mem b p < P ∧
        (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 = 0) := by
  have hA := ACC_eq
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  have hY : Y = 896 := rfl
  unfold decodeY
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The copy.
  refine WP.append (copyIn_ok hc.ctx (by omega_arith) hp hp4) fun s1 h1 => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  obtain f1 : Frame (yW b) s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_cons_self .., by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  -- The full reduction.
  refine WP.append (freeze_ok hc1.ctx hc1.a0 (fun k hk => by
      rw [Offset.add_add]; exact hc1.inW (by unfold OUT; omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by decide) (by decide)).symm))
    fun s2 ⟨_, hr2, hf2, hw2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain f2 : Frame (yW b) s1.mem s2.mem := hf2.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  obtain hv1 : V s1.mem b X2 = yw s.mem b p := val32_congr fun j hj => (h1.vals j hj).2
  -- The comparison.
  refine WP.append (outSame_ok hc2 (p := p) (by omega_arith) hp4) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain f3 : Frame (yW b) s2.mem s3.mem := hf3.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  -- The last byte.
  refine wp_lbz (a := b + BitVec.ofNat 64 (p + 56)) (by omega_arith) (by rw [hc3.ctx.a3])
    (hc3.inR (by omega_arith)) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_and fun s6 u6 => ?_
  obtain hr6 : Rest [.a4, .a5] s3 s6 :=
    (u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide)))
  obtain hm6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  obtain hc6 : VCtx b s6 := hc3.of_rest hr6 (by decide) (by decide)
  obtain hB : (s3.mem (b + BitVec.ofNat 64 (p + 56))).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [yW_byte f3 (by omega_arith) (.inl (by omega_arith)), yW_byte f2 (by omega_arith) (.inl (by omega_arith)),
      yW_byte f1 (by omega_arith) (.inl (by omega_arith))]
  obtain e7 : (s6.gpr .a4).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, toNat_imm (by omega_arith), hB]
  obtain e8 : (s6.gpr .a5).toNat = (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat % 128 := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, hB, toNat_and127 _ (by omega_arith)]
  refine WP.append (orBad_ok hc6 (r := .a5) (by decide)) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  -- The sign.
  refine wp_srl (by decide) fun s8 u8 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 SIGN) (by decide)
    (by rw [u8.other _ (by decide), hc7.ctx.a3]) (by rw [u8.wr]; exact hc7.inW (by decide)) fun s9 u9 => ?_
  obtain hc9 : VCtx b s9 := hc7.of_rest ((u8.rest (ws := [.a4]) (by decide)).trans (u9.rest _)) (by decide)
    (by decide)
  obtain hm9 : s9.mem = s7.mem.writeW (b + BitVec.ofNat 64 SIGN) ((s8.gpr .a4).setWidth 8) := by
    rw [u9.mem, u8.mem]
  refine WP.mono (constField_ok hc9.ctx (o := DON) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨hrt, hft, hvt⟩ => ?_
  obtain f9 : Frame (yW b) s7.mem t.mem := by
    refine (Frame.trans (m₂ := s9.mem) ?_ (hft.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by unfold DON; omega_arith)⟩))
    rw [hm9]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ (8 / 8))
  obtain f7 : Frame (yW b) s3.mem s7.mem := by
    rw [← hm6]; exact hf7.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  obtain hrt' : Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0] s t :=
    (h1.rest.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans (((u8.rest (ws := [.a4]) (by decide)).trans
        (u9.rest _)).trans hrt |>.mono (by decide))))))
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDON : DON = 224 := rfl
  -- What changes after the copy.
  obtain fS : Frame [⟨b + BitVec.ofNat 64 SIGN, 1⟩] s7.mem s9.mem := by
    rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (8 / 8))
  let L1 : List Region := [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
    ⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 SIGN, 1⟩, ⟨b + BitVec.ofNat 64 DON, 56⟩]
  obtain g1 : Frame L1 s1.mem t.mem := by
    refine (hf2.mono fun r hr => ?_).trans ((hf3.mono fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp [L1]
    · rw [List.mem_singleton.mp hr]; simp [L1]
    rw [← hm6]
    refine (hf7.mono fun r hr => ?_).trans ((fS.mono fun r hr => ?_).trans (hft.mono fun r hr => ?_))
    all_goals (rw [List.mem_singleton.mp hr]; simp [L1])
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', f1.trans (f2.trans (f3.trans (f7.trans f9))), ?_, hvt, ?_, ?_, ?_⟩
  · -- `y` stays in `DY`.
    refine (val32_congr fun j hj => ?_).trans (val32_congr fun j hj => (h1.vals j hj).1)
    refine limb_frame g1 (fun r hr k hk => ?_) j hj
    simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · -- `d` stays in `DK`.
    obtain g0 : Frame (⟨b + BitVec.ofNat 64 DY, 56⟩ :: ⟨b + BitVec.ofNat 64 X2, 56⟩ :: L1) s.mem t.mem :=
      (h1.frame.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
        (g1.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    obtain e := limb_frame (o := DK) g0 fun r hr k hk => by
      simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- The sign.
    rw [hft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (e := DON) (k := 56) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h, hm9, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    refine stb_byte ?_
    rw [u8.gpr, BitVec.toNat_ushiftRight, hr7.gpr _ (by decide), e7, Nat.shiftRight_eq_div_pow]
  · -- The checks.
    obtain b2 : bad s2.mem b = bad s.mem b := by
      unfold bad
      rw [hf2.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        h1.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    obtain bt : bad t.mem b = bad s7.mem b := by
      unfold bad
      rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        fS.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    obtain b6 : bad s6.mem b = bad s3.mem b := by rw [bad, bad, hm6]
    rw [bt, hb7, b6, hb3, b2, e8, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, orw_eq_zero]
    obtain hin : ∀ k < 14, wd s2.mem b (p + 4 * k) = wd s.mem b (p + 4 * k) := fun k hk => by
      rw [yW_wd f2 (by omega_arith) (by omega_arith), yW_wd f1 (by omega_arith) (by omega_arith)]
    obtain hiff : (∀ k < 14, (wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * k) ^^^ wd s2.mem b (p + 4 * k)) = 0) ↔
        yw s.mem b p < P := by
      obtain hP0 : P ≠ 0 := by have := P_eq; omega_arith
      obtain e1 : yw s.mem b p % P = val32 (fun j => wd s2.mem (b + BitVec.ofNat 64 OUT) (4 * j)) 14 := by
        rw [← hv1, hw2]
      obtain e2 : yw s.mem b p = val32 (fun k => wd s2.mem b (p + 4 * k)) 14 :=
        val32_congr fun k hk => (hin k hk).symm
      rw [← Nat.mod_eq_iff_lt hP0, e1]
      conv => rhs; rhs; rw [e2]
      rw [val32_inj (fun k _ => wd_lt _ _ _) (fun k _ => wd_lt _ _ _)]
      refine forall_congr' fun k => imp_congr_right fun hk => ?_
      rw [xor_eq_zero]
    rw [hiff]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.RISCV64

end

end

/-!
# Ed448's verification on RISCV64: the checks of the candidate x-coordinate

`decodeCheck` checks `v x² = u` and that `x = 0` does not come with the sign
1 (at `SIGN`), and leaves `x` fully reduced at `OUT` (`decodeCheck_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC freeze)
open VG.Spec.X448 (P Fe)

/-- `z - 1 >> 63` is 1 exactly when `z` is 0, for `z < 2³²`. -/
theorem isZero_shift {z : Nat} (hz : z < 2 ^ 32) :
    ((BitVec.ofNat 64 z - BitVec.ofNat 64 1) >>> 63).toNat = if z = 0 then 1 else 0 := by
  by_cases h : z = 0
  · subst h; decide
  · rw [ofNat_sub_one (by omega_arith) (by omega_arith), BitVec.toNat_ushiftRight, toNat_imm (by omega_arith),
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega_arith), ite_eq_right h]

/-- An element is 0 exactly when the words of its full reduction are. -/
theorem fs_zero {m : Mem} {b : Addr} {o : Nat} {w : Nat → Nat} (hw : val32 w 14 = V m b o % P) :
    FS m b o = 0 ↔ val32 w 14 = 0 := by
  rw [hw, FS, ← VG.Proof.X448.toFe_zero, VG.Proof.X448.toFe_eq_iff, Nat.zero_mod]

/-- The slots `decodeCheck` keeps. -/
def CQ : List Nat := [DXX, DV, DU, DY, DK, DTMP]

section
variable {b : Addr}

theorem decodeCheck_eq : decodeCheck = R64.opsCode [.mul DTMP DXX DXX, .mul DTMP DV DTMP]
    (.block (Impl.X448.RISCV64.R64.sub X2 DTMP DU ++ freeze ++ outZero ++ copy X2 DXX ++ freeze ++ outOr ++
      ([.addi .a7 .a7 (-1), .shift .srl .d .a7 .a7 63, .load .b .a4 .a3 SIGN, .logic .and .a5 .a7 .a4] : List Instr) ++
        orBad .a5)) := rfl

theorem decodeCheck_ok {s : State} (hc : VCtx b s) {x v u : Fe} (hx : FS s.mem b DXX = x)
    (hv : FS s.mem b DV = v) (hu : FS s.mem b DU = u) {sg : Nat} (hsg : sg ≤ 1)
    (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCheck s fun t => VCtx b t ∧ Rest R64.work s t ∧
      Frame (yW b) s.mem t.mem ∧ (∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s.mem b q) ∧
      t.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) ∧
      VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ sg = 1)) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := ACC_eq
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  obtain h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) CQ (FS s.mem b) s := ⟨hc.ctx, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeCheck_eq]
  refine R64.ops_ok _ CQ _ s (by decide) h0 fun s1 h1 => ?_
  simp only [outZero, copy, List.append_assoc, List.cons_append, List.nil_append]
  obtain hc1 : VCtx b s1 := hc.of_rest h1.stp.rest (by decide) (by decide)
  -- `v x² - u` into `X2`.
  refine WP.append (R64.subS (o := X2) (x := DTMP) (y := DU) (by decide) (by decide) (by decide) (by decide)
    h1.ctx h1.slots) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain e2 : FS s2.mem b X2 = v * (x * x) - u := by
    rw [hS2 X2 (by decide)]
    have hx' : FS s.mem b 672 = x := hx
    have hv' : FS s.mem b 448 = v := hv
    have hu' : FS s.mem b 392 = u := hu
    simp only [upd, runOps, FOp.out, FOp.val, X2, DTMP, DXX, DV, DU, Nat.reduceEqDiff, ↓reduceIte, hx', hv', hu']
  -- Its full reduction, checked to be 0.
  refine WP.append (freeze_ok hc2.ctx hc2.a0 (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    ((Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm))
    fun s3 ⟨_, hr3, hf3, hw3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_arith) (by omega_arith)).symm
  obtain hS3 := slots_freeze hf3 hdo hS2 (by decide)
  refine WP.append (outOr_ok hc3) fun s4 ⟨hr4, hm4, hv4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine WP.append (orBad_ok hc4 (r := .a7) (by decide)) fun s5 ⟨hr5, hf5, hb5⟩ => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest hr5 (by decide) (by decide)
  obtain hS5 := SlotsOk.lo (m := s3.mem) (m' := s5.mem) (by rw [← hm4]; exact hf5) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_arith) (by omega_arith)) hS3 (by decide)
  -- `x` into `X2`, and its full reduction.
  refine wp_li (by decide) fun s6 u6 => ?_
  obtain hc6 : VCtx b s6 := hc5.of_rest (u6.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  refine WP.append (sel_ok (b := b) (o := X2) (q := DXX) (r := DXX) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc6.ctx (sw := 0) (by decide) (by rw [u6.gpr]; rfl)) fun s7 h7 => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest h7.rest (by decide) (by decide)
  obtain e7 : V s7.mem b X2 = V s6.mem b DXX := val32_congr fun j hj => h7.lo j hj
  refine WP.append (freeze_ok hc7.ctx hc7.a0 (fun k hk => by rw [Offset.add_add]; exact hc7.inW (by omega_arith))
    hdo) fun s8 ⟨hb8, hr8, hf8, hw8⟩ => ?_
  obtain hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (outOr_ok hc8) fun s9 ⟨hr9, hm9, hv9⟩ => ?_
  obtain hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- Zero with the sign 1.
  refine wp_subi (by decide) fun s10 u10 => wp_srl (by decide) fun s11 u11 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u11.other _ (by decide), u10.other _ (by decide), hc9.ctx.a3]) (by
      rw [u11.rd, u11.wr, u10.rd, u10.wr]; exact hc9.inR (by omega_arith)) fun s12 u12 => wp_and fun s13 u13 => ?_
  obtain hr13 : Rest [.a4, .a5, .a7] s9 s13 := (u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    ((u12.rest (by decide)).trans (u13.rest (by decide))))
  obtain hm13 : s13.mem = s9.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem]
  obtain hc13 : VCtx b s13 := hc9.of_rest hr13 (by decide) (by decide)
  refine WP.mono (orBad_ok hc13 (r := .a5) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  have hX' : DXX = 672 := rfl
  -- The registers.
  obtain hrw : Rest R64.work s t := by
    refine h1.stp.rest.trans ((hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans ?_))
    refine (hr4.mono (by decide)).trans ((hr5.mono (by decide)).trans ?_)
    refine ((u6.rest (ws := [.t0]) (by decide)).mono (by decide)).trans ((h7.rest.mono (by decide)).trans ?_)
    exact (hr8.mono (by decide)).trans ((hr9.mono (by decide)).trans ((hr13.mono (by decide)).trans
      (hrt.mono (by decide))))
  -- The memory.
  let L2 : List Region := [FA b, ⟨b + BitVec.ofNat 64 OUT, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩]
  obtain sFA : ∀ {m m' : Mem} {o n : Nat}, o + n ≤ 1064 → Frame [⟨b + BitVec.ofNat 64 o, n⟩] m m' → Frame L2 m m' :=
    fun ho hf => hf.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)⟩
  obtain sYO : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩] m m' →
      Frame L2 m m' := fun hf => hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (Nat.le_refl _)⟩
  obtain sB : ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] m m' → Frame L2 m m' :=
    fun hf => hf.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [L2]
  obtain fs3 : Frame L2 s.mem s3.mem :=
    (h1.stp.frame.mono (by simp [L2])).trans ((hf2.mono (by simp [L2])).trans (sYO hf3))
  obtain f58 : Frame L2 s5.mem s8.mem := by
    rw [← u6.mem]; exact (sFA (o := X2) (n := 4 * 14) (by omega_arith) h7.frame).trans (sYO hf8)
  obtain f8t : Frame L2 s8.mem t.mem := by rw [← hm9, ← hm13]; exact sB hft
  obtain fst : Frame L2 s.mem t.mem := fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans
    (f58.trans f8t))
  -- The slots kept, through `s5`.
  obtain k5 : ∀ q ∈ [DXX, DY, DK], FS s5.mem b q = FS s.mem b q := by
    intro q hq
    rw [hS5 q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      simp only [upd, runOps, FOp.out, X2, DTMP, DXX, DY, DK, Nat.reduceEqDiff, ↓reduceIte]
  obtain kt : ∀ q ∈ [DXX, DY, DK], FS t.mem b q = FS s5.mem b q := by
    intro q hq
    obtain hq' : (q = 672 ∨ q = 168 ∨ q = 336) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; exact hq
    obtain f : Frame [⟨b + BitVec.ofNat 64 X2, 56⟩, ⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨b + BitVec.ofNat 64 OUT, 56⟩,
        ⟨b + BitVec.ofNat 64 BAD, 8⟩] s5.mem t.mem := by
      rw [← u6.mem]
      refine (h7.frame.mono (by simp)).trans ((hf8.mono ?_).trans ?_)
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
      · rw [← hm9, ← hm13]; exact hft.mono (by simp)
    obtain e := limb_frame (o := q) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  obtain hxv : V s7.mem b X2 % P = x.val := by
    rw [e7, ← VG.Proof.X448.toFe_val, ← FS, show FS s6.mem b DXX = FS s5.mem b DXX by rw [u6.mem], k5 _ (by simp),
      hx]
  refine ⟨hc.of_rest hrw (by decide) (by decide), hrw, fst.mono (by simp [L2]), fun q hq => (kt q hq).trans (k5 q hq),
    ?_, ?_, ?_⟩
  · -- The sign.
    exact fst _ fun r hr => by
      simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith)
          (by omega_arith) _ (Region.contains_self _ _) h
      all_goals exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h
  · -- `x` at `OUT`.
    rw [← hxv, ← hb8]
    simp only [VG.Spec.X448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    rw [Offset.add_add, hft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint b (d := OUT + i) (n := 1) (e := BAD) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h, hm13, hm9]
  · -- The checks.
    obtain rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
      unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
    obtain b3 : bad s3.mem b = bad s.mem b := by
      rw [rB hf3 (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        rB hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)),
        rB h1.stp.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith))]
    obtain b13 : bad s13.mem b = bad s5.mem b := by
      obtain e1 : bad s13.mem b = bad s8.mem b := by rw [bad, bad, hm13, hm9]
      obtain e2 : bad s8.mem b = bad s7.mem b := rB hf8 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      obtain e3 : bad s7.mem b = bad s6.mem b :=
        rB h7.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      obtain e4 : bad s6.mem b = bad s5.mem b := by rw [bad, bad, u6.mem]
      rw [e1, e2, e3, e4]
    obtain fs8 : Frame L2 s.mem s8.mem :=
      fs3.trans ((by rw [← hm4]; exact sB hf5 : Frame L2 s3.mem s5.mem).trans f58)
    obtain hsg12 : (s12.gpr .a4).toNat = sg := by
      rw [u12.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), u11.mem, u10.mem, hm9]
      have : s8.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) := by
        refine fs8 _ fun r hr => ?_
        simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith)
            (by omega_arith) _ (Region.contains_self _ _) h
        all_goals exact fun h => Offset.disjoint b (d := SIGN) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) h
      rw [this, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    obtain hz := orw_lt (f := fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) (n := 14) fun k _ => wd_lt _ _ _
    obtain hz12 : (s12.gpr .a7).toNat =
        if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0 := by
      rw [u12.other _ (by decide), u11.gpr, u10.gpr, ← isZero_shift hz]
      congr 3
      exact BitVec.eq_of_toNat_eq (by rw [hv9, toNat_imm (by omega_arith)])
    obtain hx7 : FS s7.mem b X2 = x := by
      rw [FS, e7, ← FS, show FS s6.mem b DXX = FS s5.mem b DXX by rw [u6.mem], k5 _ (by simp), hx]
    rw [hbt, b13, hb5, hm4, b3, hv4, u13.gpr, BitVec.toNat_and, hz12, hsg12, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff,
      orw_eq_zero, ← val32_eq_zero, ← fs_zero hw3, e2, fin_sub_eq_zero]
    obtain hz0 : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ x = 0 := by
      rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw8, hx7]
    obtain hr8 : ((if orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 then 1 else 0) &&& sg = 0) ↔
        ¬ (x = 0 ∧ sg = 1) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl
      · rw [Nat.and_zero]; exact ⟨fun _ h => absurd h.2 (by decide), fun _ => rfl⟩
      · by_cases h : orw (fun k => wd s8.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0
        · rw [ite_eq_left h]; exact ⟨fun h1 => absurd h1 (by decide), fun h2 => absurd ⟨hz0.mp h, rfl⟩ h2⟩
        · rw [ite_eq_right h]; exact ⟨fun _ h2 => h (hz0.mpr h2.1), fun _ => rfl⟩
    rw [hr8]; exact and_assoc

end
end VG.Proof.Ed448.RISCV64
end

end

/-! ### `Ed448.RISCV64.VDecodeNeg`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`, at multiples of 4. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo) ∧
    xo % 4 = 0 ∧ yo % 4 = 0

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest R64.clob64 s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy, hx4, hy4⟩ := ho
  have hPK : PK = 1456 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (R64.subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (R64.subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc1.ctx hS1) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  obtain hf12 : Frame [FA b] s.mem s2.mem := hf1.trans hf2
  -- The mask: the low bit of `x` against the sign.
  obtain hb2 : s2.mem (b + BitVec.ofNat 64 OUT) = BitVec.ofNat 8 x.val := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := OUT) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact byte0 hout
  obtain hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact hs
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by rw [hc2.a0, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.a3])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  obtain hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  obtain hr9 : Rest [.a4, .a5, .a6, .t0] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  obtain hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  obtain hsg' : sg < 2 ^ 64 := by omega_arith
  obtain hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  obtain e5 : (s5.gpr .a5).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  obtain e6 : (s6.gpr .a4).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  obtain e7 : s7.gpr .a5 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  obtain e11 : s9.gpr .t0 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hx4 (by decide) (by decide) hc9.ctx hm e11) fun s10 h10 => ?_
  obtain hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hy4 (by decide) (by decide) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  obtain hrt : Rest R64.clob64 s t :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr9.mono (by decide)).trans
      ((h10.rest.mono (by decide)).trans (ht.rest.mono (by decide)))))
  -- The values.
  obtain v2 : ∀ q ∈ [DNEG, DXX, DY, DK], FS s2.mem b q = upd (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX))
      DNEG (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DTMP -
        upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DXX) q := fun q hq => hS2 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> decide)
  have hx' : FS s.mem b 672 = x := hx
  have hy' : FS s.mem b 168 = y := hy
  obtain eN : FS s2.mem b DNEG = (x - x) - x := by
    rw [v2 DNEG (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  obtain eX : FS s2.mem b DXX = x := by
    rw [v2 DXX (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  obtain eY : FS s2.mem b DY = y := by
    rw [v2 DY (by simp)]; simp only [upd, DNEG, DTMP, DY, Nat.reduceEqDiff, ↓reduceIte, hy']
  obtain hxo : FS s10.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x := by
    rw [fs_pick hm h10.lo, hm9, eN, eX]
  obtain eK : FS s2.mem b DK = FS s.mem b DK := by
    rw [v2 DK (by simp)]; simp only [upd, DNEG, DTMP, DK, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, ?_, ?_, ?_⟩
  · refine (hf12.mono (by simp)).trans ?_
    rw [← hm9]
    exact (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  · -- `xo` is kept by the write of `yo`.
    rw [← hxo]
    obtain e := limb_frame (o := xo) ht.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := xo + 4 * k) (n := 4) (e := yo) (k := 4 * 14) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- `y`, kept by the write of `xo`.
    rw [fs_pick hm ht.lo]
    obtain e := limb_frame (o := DY) h10.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold DY; omega_arith) (by omega_arith) (by omega_arith)
    rw [show FS s10.mem b DY = FS s9.mem b DY by rw [FS, V, val32_congr e]; rfl, hm9, eY]
    unfold pick VG.Proof.X25519.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    obtain f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    obtain e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecodeX`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VRoot`, which only this module used -/

section

/-!
# Ed448 on RISCV64: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2`
(`rootQ_ok`) by X448's addition chain for the inversion as far as
`z^(2²²³ - 1)` (`R64.chain223Call_ok`), then 223 squarings and the product with
`z^(2²²² - 1)`, since `(p-3)/4 = (2²²³ - 1) 2²²³ + (2²²² - 1)` (`root_exp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Impl.X448.RISCV64.R64 (T6)
open VG.Spec.X448 (P Fe)

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

/-- `(p - 3) / 4 = (2²²³ - 1) 2²²³ + (2²²² - 1)`. -/
theorem root_exp : (2 ^ 223 - 1) * 2 ^ 223 + (2 ^ 222 - 1) = RE := by decide +kernel

section
variable {b : Addr}

theorem rootQ_ok {qs : List Nat} (hq : R64.Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : R64.TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa root s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) RE)) := by
  obtain hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := R64.drop_R hq hT hc hS h0
  obtain hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  unfold root
  refine WP.seq (WP.mono (R64.chain223Call_ok hfR hZf hfT hC) fun s1 h1 => ?_)
  obtain ⟨f6, _⟩ := R64.temps_get hfT (t := T6) (by decide)
  refine WP.seq (WP.mono (R64.sqnP (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h1) fun s2 h2 => ?_)
  refine WP.mono (R64.opMulP (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 223) (eb := 2 ^ 222 - 1) (ee := RE)
    (by sep8) (by decide) (by simp) (by simp) (by look) (by look) root_exp h2) fun s3 ⟨c3, h3⟩ =>
    ⟨h3.stp, h3.ctx, fun q hq' => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h3.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq'' : q ∈ qs.filter (· ≠ R) := by simp [hq', eR]
    obtain e6 : q ≠ T6 := fun e => (R64.temps_get hT (t := T6) (by decide)).2 (e ▸ hq')
    rw [h3.slots q (by repeat (first | exact hq'' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [R64.chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: the candidate x-coordinate

`decodeX` computes, from `y` at `DY`, `1` at `DON` and `d` at `DK`,
`u = y² - 1` (at `DU`), `v = d y² - 1` (at `DV`), `t = u³v` (at `DT`) and
`x = t (t (uv)²)^((p-3)/4)` (at `DXX`) (`decodeX_ok`), as `recoverRef` has
them.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Spec.X448 (P Fe)

/-- The field operations of `decodeX` before the power. -/
def xOps : List FOp :=
  [.mul DYY DY DY, .sub DU DYY DON, .mul DV DK DYY, .sub DV DV DON, .mul DT DU DU, .mul DT DT DU,
    .mul DT DT DV, .mul DW DU DV, .mul DW DW DW, .mul Z2 DT DW]

theorem decodeX_eq : decodeX = R64.opsCode xOps (.seq root (Impl.X448.RISCV64.R64.mul DXX DT R)) := rfl

/-- The slots `decodeX` reads, and `R` and `Z2`. -/
def XQ : List Nat := [DY, DON, DK, R, Z2]

theorem xOps_ok : R64.opsOk xOps XQ = true := by decide

/-- The slots kept across `root`: not `DYY` and `DW`, which its chain uses. -/
def RootQ : List Nat := [R, Z2, DT, DV, DU, DY, DK]

theorem RootQ_sub : ∀ q ∈ RootQ, q ∈ outsQ xOps XQ := by decide

/-- `u`, `v`, `t` and the candidate `x` for `y`. -/
def uOf (y : Fe) : Fe := y * y - 1
def vOf (y : Fe) : Fe := Spec.Ed448.d * (y * y) - 1
def tOf (y : Fe) : Fe := uOf y * uOf y * uOf y * vOf y
def xOf (y : Fe) : Fe :=
  tOf y * VG.Proof.X448.pw (tOf y * ((uOf y * vOf y) * (uOf y * vOf y))) RE

section
variable {b : Addr}

theorem decodeX_ok {s : State} (hc : Ctx b s) {y : Fe} (hy : FS s.mem b DY = y) (hon : FS s.mem b DON = 1)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa decodeX s fun t => R64.Stp b s t ∧ Ctx b t ∧ FS t.mem b DXX = xOf y ∧ FS t.mem b DV = vOf y ∧
      FS t.mem b DU = uOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d := by
  have hy' : FS s.mem b 168 = y := hy
  have hon' : FS s.mem b 224 = 1 := hon
  have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
  obtain h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) XQ (FS s.mem b) s := ⟨hc, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeX_eq]
  refine R64.ops_ok xOps XQ _ s xOps_ok h0 fun s1 h1 => ?_
  refine WP.seq (WP.mono (rootQ_ok (qs := RootQ) (by decide) (by decide) (by decide) h1.ctx
    (fun q hq _ => h1.slots q (RootQ_sub q hq)) h1.t2) fun s2 ⟨hst2, hc2, hS2⟩ => ?_)
  refine WP.mono (R64.mulS (o := DXX) (x := DT) (y := R) (by decide) (by decide) (by decide) (by decide) hc2 hS2)
    fun t ⟨hrt, hft, hSt⟩ => ?_
  refine ⟨h1.stp.trans (hst2.trans ⟨hrt.mono (by decide), hft⟩), hc2.of_rest hrt (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | rw [hSt DXX (by decide)] | rw [hSt DV (by decide)] | rw [hSt DU (by decide)]
    | rw [hSt DY (by decide)] | rw [hSt DK (by decide)]
  all_goals
    simp only [upd, runOps, xOps, FOp.out, FOp.val, DXX, DT, DV, DU, DY, DK, DW, DYY, DON, R, Z2,
      Nat.reduceEqDiff, ↓reduceIte, hy', hon', hd', xOf, tOf, uOf, vOf]
end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

theorem fin_neg_neg {n : Nat} [NeZero n] (x : Fin n) : 0 - (0 - x) = x := by grind

theorem fin_neg_sub {n : Nat} [NeZero n] (x : Fin n) : (x - x) - x = 0 - x := by rw [Fin.sub_self]

/-- The negation of the decoded x-coordinate, as `decodeNeg` selects it. -/
theorem neg_pick (x : Fe) {sg : Nat} (hsg : sg ≤ 1) :
    pick (x.val % 2 ^^^ sg) ((x - x) - x) x =
      0 - (if (x.val % 2 == 1) == (sg == 1) then x else (x - x) - x) := by
  rw [fin_neg_sub]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl <;>
    simp only [h, pick, VG.Proof.X25519.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeCoreCall (.block (decodeNeg xo yo))) := rfl

/-- The 57 bytes at `p` in terms of the words and the last byte. -/
theorem bytes57 (m : Mem) (p : Nat) :
    Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).take 56) = yw m b p ∧
      ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).getD 56 0).toNat =
        (m (b + BitVec.ofNat 64 (p + 56))).toNat := by
  constructor
  · rw [show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
      List.take_left' (by simp [Spec.X25519.bytesAt]), Proof.Ed448.decodeLE_eq, show (56 : Nat) = 4 * 14 from rfl]
    rw [show Spec.X25519.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) =
      VG.Spec.X448.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) from rfl, leNum_bytesAt4]
    exact val32_congr fun k _ => wd_shift _ _ _ _
  · rw [getD_bytesAt _ _ (by decide), Offset.add_add]

/-- The writes of the shared core and its return-address slot. -/
abbrev coreW (b : Addr) : List Region := yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩]

/-- The decoded candidate, sign, canonical bytes and accumulated checks. -/
def CoreFacts (b : Addr) (y : Fe) (sg : Nat) (m : Mem) (t : State) : Prop :=
  FS t.mem b DXX = xOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d ∧
  t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg ∧
  VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 (xOf y).val ∧
  (bad t.mem b = 0 ↔ bad m b = 0 ∧ vOf y * (xOf y * xOf y) = uOf y ∧ ¬ (xOf y = 0 ∧ sg = 1))

theorem decodeCore_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCore s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (yW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCore
  refine WP.seq (WP.mono (decodeX_ok hc.ctx hy hon hd)
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  obtain hc2 : VCtx b s2 := hc.of_rest hst2.rest (by decide) (by decide)
  obtain hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [← hs]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_
  obtain hb2 : bad s2.mem b = bad s.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  exact ⟨hc3, hst2.rest.trans hr3, (hst2.frame.mono (by simp [yW])).trans hf3,
    by rw [hk3 DXX (by simp), hx2], by rw [hk3 DY (by simp), hy2],
    by rw [hk3 DK (by simp), hd2], hs3.trans hs2, hout3, by rwa [hb2] at hb3⟩

/-- The shared decode call preserves its caller's return address, including
across its nested exponentiation call. -/
theorem decodeCoreCall_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCoreCall s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (coreW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCoreCall
  refine WP.seq (R64.sd_ok hc.ctx (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain hc1 := hc.of_rest (u1.rest []) (by decide) (by decide)
  obtain fs : Frame [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩] s.mem s1.mem := by
    rw [u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepFS {q : Nat} (hq : q + 56 ≤ DECODE_RA) : FS s1.mem b q = FS s.mem b q := by
    obtain e := limb_frame fs (o := q) fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      have hRA : DECODE_RA = 1712 := rfl
      exact Offset.disjoint b (.inl (by omega_using [hq, hk])) (by omega_using [hq, hk, hRA]) (by decide)
    rw [FS, V, val32_congr e]; rfl
  obtain hsign : s1.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) :=
    fs _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact Offset.disjoint b (d := SIGN) (n := 1) (e := DECODE_RA) (k := 8)
        (by decide) (by decide) (by decide) _ (Region.contains_self _ _) hcon
  obtain hbad : bad s1.mem b = bad s.mem b := by
    unfold bad
    rw [fs.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)) (by decide)]
  obtain hcE : VCtx b s1.callEntry := ⟨⟨hc1.ctx.a3, hc1.ctx.al, hc1.ctx.wr⟩, hc1.ws, hc1.a0⟩
  obtain ⟨tr, s2, he, hc2, hr2, hf2, facts⟩ := decodeCore_ok hcE
    ((keepFS (q := DY) (by decide)).trans hy) ((keepFS (q := DON) (by decide)).trans hon)
    ((keepFS (q := DK) (by decide)).trans hd) hsg (hsign.trans hs)
  obtain hra := hr2.gpr .ra (by decide)
  obtain hret : isa.ret s1.callEntry s2 = some s2 := by simp only [isa, ret, hra, ↓reduceIte]
  refine WP.seq ⟨_, s2, Exec.call (call_callEntry s1) he hret, ?_⟩
  obtain saved : s2.mem.readW (b + BitVec.ofNat 64 DECODE_RA) 64 = s.gpr .ra := by
    rw [hf2.readW (Region.contains_self _ (64 / 8)) ?_ (by decide), State.callEntry_mem,
      u1.mem, Mem.readW_writeW_self64]
    intro r hr
    simp only [yW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base b (by decide) (by decide)
    all_goals exact Offset.disjoint b (by decide) (by decide) (by decide)
  refine R64.ld_ok hc2.ctx (by decide) (by decide) fun s3 u3 => WP.block_nil ?_
  obtain rest : Rest R64.work s s3 := by
    refine ⟨?_, u3.rd.trans (hr2.rd.trans u1.rd), u3.wr.trans (hr2.wr.trans u1.wr),
      u3.sp.trans (hr2.sp.trans u1.sp)⟩
    intro r hr
    by_cases er : r = .ra
    · subst r; exact u3.gpr.trans saved
    · rw [u3.other r er, hr2.gpr r hr,
        State.callEntry_gpr s1 (by
          obtain hn : ∀ (r : Reg), r ∉ R64.work → r ≠ Reg.ra → r ∉ linkRegs := by
            intro r; cases r <;> simp [R64.work, linkRegs]
          exact hn r hr er), u1.gpr]
  refine ⟨hc2.of_rest (u3.rest (ws := [.ra]) (by decide)) (by decide) (by decide), rest, ?_, ?_⟩
  · rw [u3.mem]
    exact (fs.mono (by simp [coreW])).trans (hf2.mono (by simp [coreW]))
  · unfold CoreFacts at facts ⊢
    rw [u3.mem]
    simpa only [State.callEntry_mem, hbad] using facts

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp' hp4) fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  obtain hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  obtain hsg : B / 128 ≤ 1 := by omega_using [hB]
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  obtain hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  obtain hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeCoreCall_ok hc1 hy hon (hk1.trans hd) hsg hs1)
    fun s3 ⟨hc3, hr3, hf3, hx3, hy3, hd3, hs3, hout3, hb3⟩ => ?_)
  refine WP.mono (decodeNeg_ok hc3 ho hx3 hy3 hout3 hsg hs3)
    fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5, -, -⟩ := ho
  have hPK : PK = 1456 := rfl
  obtain ⟨o1, o2, o3, o4⟩ := offs
  -- The code's view of `decodePoint`.
  obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem p
  rw [hB] at eB
  obtain hdp := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)
    (by simp [Spec.Ed448.bytesAt]) _ B e56 eB y (uOf y) (vOf y) (tOf y) (xOf y) hY rfl rfl rfl (by
      rw [xOf, Proof.Ed448.rootPow_eq, VG.Proof.X448.pow_pw]; rfl)
  obtain hbt : bad t.mem b = bad s3.mem b := by
    unfold bad
    rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      all_goals exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)) (by decide)]
  refine ⟨hct, hr1.mono (by decide) |>.trans (hr3.trans (hrt.mono (by decide))), ?_,
    by rw [hkt, hd3], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hf3.mono (by simp [coreW, decW])).trans (hft.mono ?_))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb1, hdp]
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC, Option.isSome_some]
      exact ⟨fun h => ⟨h.1.1, rfl⟩, fun h => ⟨⟨h.1, hC.1.2, hC.1.1⟩, hC.2⟩⟩
    · rw [ite_eq_right hC, Option.isSome_none]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => absurd ⟨⟨h3, h2⟩, h4⟩ hC, fun h => absurd h.2 (by decide)⟩
  · intro pt hpt
    rw [hdp] at hpt
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC] at hpt
      cases Option.some.inj hpt
      exact ⟨by rw [hxt, neg_pick _ hsg], hyt, rfl⟩
    · rw [ite_eq_right hC] at hpt
      exact absurd hpt (by simp)

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VMain`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VSetup`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the setup

`vSetup` rounds the working space up to a multiple of 8 (Ed25519's
`align_ok`, the same two instructions), copies the inputs into it
(`copyB_ok`), points `a0` at `OUT`, clears `BAD`, and writes `d`, `B` and 1
(`vSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Spec.X448 (P Fe)
open VG.Proof.Ed25519.RISCV64 (base)

section
variable {b : Addr}

/-- After `k` bytes of a copy from `src` to `o`. -/
structure CopyInv (b src : Addr) (o : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, k⟩] s0.mem s.mem
  bytes : ∀ i < k, s.mem (b + BitVec.ofNat 64 (o + i)) = s0.mem (src + BitVec.ofNat 64 i)

theorem copyB_ok {s0 : State} (hc : Ctx b s0) {rs : Reg} (hrs : rs ≠ .a4 ∧ rs ≠ .a3) {src : Addr} {so : Nat}
    (h : s0.gpr rs + BitVec.ofNat 64 so = src) {n o : Nat} (hin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (src + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, n⟩ ⟨b + BitVec.ofNat 64 o, n⟩) (ho : o + n ≤ 2048) (hso : so + n ≤ 2048) :
    WP isa (.block (copyBytes rs so o n)) s0 (CopyInv b src o s0 n) := by
  obtain ⟨h7, h6⟩ := hrs
  refine wp_range_flatMap (M := isa) (CopyInv b src o s0) (fun k s hk h' => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h'.rest (by decide)
  refine wp_lbz (a := src + BitVec.ofNat 64 k) (by omega_arith)
    (by rw [h'.rest.gpr _ (by simpa using h7), ← h, Offset.add_add])
    (by rw [h'.rest.rd, h'.rest.wr]; exact hin k hk) fun s1 u1 => ?_
  refine wp_sb (a := b + BitVec.ofNat 64 (o + k)) (by omega_arith)
    (by rw [u1.other _ (by decide), h'.rest.gpr _ (by decide), hc.a3])
    (by rw [u1.wr, h'.rest.wr]; exact hc.inW (by omega_arith)) fun s2 u2 => WP.block_nil ?_
  obtain hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + k)) ((s1.gpr .a4).setWidth 8) := by rw [u2.mem, u1.mem]
  obtain hsrc : s.mem (src + BitVec.ofNat 64 k) = s0.mem (src + BitVec.ofNat 64 k) :=
    h'.frame _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  refine ⟨h'.rest.trans ((u1.rest (by decide)).trans (u2.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm2]
    exact (h'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hm2, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [X448.RISCV64.iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))]; exact h'.bytes i hi
    · rw [X448.RISCV64.iteT rfl, u1.gpr, ← hsrc]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.mem (src + BitVec.ofNat 64 i)).isLt
      omega_arith

/-- The bytes of a region apart from a frame's regions stay. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n < 2 ^ 64) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc

theorem bytes_copy {m m0 : Mem} {src : Addr} {o n : Nat}
    (h : ∀ i < n, m (b + BitVec.ofNat 64 (o + i)) = m0 (src + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 o) n = Spec.Ed448.bytesAt m0 src n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]; exact h i (List.mem_range.mp hi)

/-- The precondition, by register: `pk` in `a0`, the signature in `a1`, the
challenge in `a2` and `scratch` in `a3`. -/
structure VPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a1, 114⟩, ⟨s.gpr .a2, 57⟩]
  wr : s.wr = [⟨s.gpr .a3, 8192⟩]
  pk_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  sig_ws : (⟨s.gpr .a1, 114⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  ch_ws : (⟨s.gpr .a2, 57⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩

/-- A range of the rounded working space below `8184`, in the working space. -/
theorem base_sub8 (q : Addr) {o n : Nat} (h : o + n ≤ 8184) :
    Region.Sub ⟨base q + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩ := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact Offset.sub_base _ (by omega_using [h, this])

/-- A range of the rounded working space below `8184`, in the regions of the working space. -/
theorem base_in {rs : List Region} {q : Addr} (hws : (⟨q, 8192⟩ : Region) ∈ rs) {d n : Nat} (h : d + n ≤ 8184) :
    InRegions rs (base q + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact in_base hws (by omega_using [h, this]) (by omega_using [h, this])

/-- The regions the copies write. -/
abbrev copyW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 PK, 57⟩, ⟨b + BitVec.ofNat 64 SG, 57⟩, ⟨b + BitVec.ofNat 64 SGS, 57⟩,
    ⟨b + BitVec.ofNat 64 CH, 57⟩]

/-- The copies of the public key, `R`, `S` and the challenge. -/
theorem copies_ok {s0 : State} (hc : Ctx b s0) {q : Addr}
    (sub8 : ∀ {o n : Nat}, o + n ≤ 8184 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩)
    (hrd : s0.rd = [⟨s0.gpr .a0, 57⟩, ⟨s0.gpr .a1, 114⟩, ⟨s0.gpr .a2, 57⟩])
    (pk_ws : (⟨s0.gpr .a0, 57⟩ : Region).Disjoint ⟨q, 8192⟩)
    (sig_ws : (⟨s0.gpr .a1, 114⟩ : Region).Disjoint ⟨q, 8192⟩)
    (ch_ws : (⟨s0.gpr .a2, 57⟩ : Region).Disjoint ⟨q, 8192⟩) :
    WP isa (.block (copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++
        copyBytes .a2 0 CH 57)) s0 fun s4 =>
      Rest [.a4] s0 s4 ∧ Frame (copyW b) s0.mem s4.mem ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a0) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 SG) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a1) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 SGS) 57 =
        Spec.Ed448.bytesAt s0.mem (s0.gpr .a1 + BitVec.ofNat 64 57) 57 ∧
      Spec.Ed448.bytesAt s4.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s0.mem (s0.gpr .a2) 57 := by
  have hPK : PK = 1456 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hCH : CH = 1636 := rfl
  obtain hin : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region) ∈ s0.rd → n ≤ 114 → ∀ i < n,
      InRegions (s0.rd ++ s0.wr) (p + BitVec.ofNat 64 i) 1 :=
    fun {p n} hr hn i hi => in_base (P := p) (len := n) (d := i) (n := 1) (List.mem_append_left s0.wr hr)
      (by omega_using [hi]) (by omega_using [hn, hi])
  obtain sigR : (⟨s0.gpr .a1, 114⟩ : Region) ∈ s0.rd := by rw [hrd]; simp only [List.mem_cons, true_or, or_true]
  obtain sR : (⟨s0.gpr .a1 + BitVec.ofNat 64 57, 57⟩ : Region).Disjoint ⟨q, 8192⟩ :=
    sig_ws.sub_left (Offset.sub_base (s0.gpr .a1) (d := 57) (n := 57) (k := 114) (by decide))
  obtain rR : (⟨s0.gpr .a1, 57⟩ : Region).Disjoint ⟨q, 8192⟩ := sig_ws.sub_left (Region.sub_prefix (by omega_arith))
  simp only [List.append_assoc]
  refine WP.append (copyB_ok hc (rs := .a0) (so := 0) (by decide) (BitVec.add_zero _)
    (n := 57) (o := PK) (hin (by rw [hrd]; simp only [List.mem_cons, true_or]) (by omega_arith))
    (pk_ws.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s1 h1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest h1.rest (by decide)
  refine WP.append (copyB_ok hc1 (rs := .a1) (so := 0) (by decide)
    (by rw [h1.rest.gpr _ (by decide), BitVec.add_zero]) (n := 57) (o := SG)
    (by rw [h1.rest.rd, h1.rest.wr]
        exact fun i hi => in_base (List.mem_append_left _ sigR) (by omega_arith) (by omega_arith))
    (rR.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s2 h2 => ?_
  obtain hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.append (copyB_ok hc2 (rs := .a1) (so := 57) (by decide)
    (by rw [h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide)]) (n := 57) (o := SGS)
    (by rw [h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr]
        exact fun i hi => by
          rw [Offset.add_add]
          exact in_base (List.mem_append_left _ sigR) (by omega_arith) (by omega_arith))
    (sR.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s3 h3 => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest h3.rest (by decide)
  refine WP.mono (copyB_ok hc3 (rs := .a2) (so := 0) (by decide)
    (by rw [h3.rest.gpr _ (by decide), h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide), BitVec.add_zero])
    (n := 57) (o := CH)
    (by rw [h3.rest.rd, h3.rest.wr, h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr]
        exact hin (by rw [hrd]; simp only [List.mem_cons, true_or, or_true]) (by omega_arith))
    (ch_ws.sub_right (sub8 (by omega_arith))) (by omega_arith) (by decide)) fun s4 h4 => ?_
  obtain dq : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨q, 8192⟩ → ∀ r ∈ copyW b, (⟨p, n⟩ : Region).Disjoint r :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hd.sub_right (sub8 (by omega_arith))
  obtain k1 : Frame (copyW b) s0.mem s1.mem := h1.frame.mono (by simp)
  obtain k2 : Frame (copyW b) s1.mem s2.mem := h2.frame.mono (by simp)
  obtain k3 : Frame (copyW b) s2.mem s3.mem := h3.frame.mono (by simp)
  obtain k4 : Frame (copyW b) s3.mem s4.mem := h4.frame.mono (by simp)
  obtain ds : ∀ {o o' : Nat}, o + 57 ≤ o' ∨ o' + 57 ≤ o → o + 57 ≤ 2048 → o' + 57 ≤ 2048 →
      ∀ r ∈ [(⟨b + BitVec.ofNat 64 o', 57⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 o, 57⟩ r :=
    fun h1 h2 h3 r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ h1 (by omega_arith) (by omega_arith)
  refine ⟨h1.rest.trans (h2.rest.trans (h3.rest.trans h4.rest)), k1.trans (k2.trans (k3.trans k4)), ?_, ?_, ?_, ?_⟩
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h3.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h2.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h1.bytes]
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep h3.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h2.bytes,
      bytes_keep k1 (dq rR) (by decide)]
  · rw [bytes_keep h4.frame (ds (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), bytes_copy h3.bytes,
      bytes_keep k2 (dq sR) (by decide), bytes_keep k1 (dq sR) (by decide)]
  · rw [bytes_copy h4.bytes, bytes_keep k3 (dq ch_ws) (by decide), bytes_keep k2 (dq ch_ws) (by decide),
      bytes_keep k1 (dq ch_ws) (by decide)]

/-- The regions the constants write. -/
abbrev constW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 BAD, 8⟩, ⟨b + BitVec.ofNat 64 DK, 56⟩, ⟨b + BitVec.ofNat 64 ONE, 56⟩]

/-- `a0 = OUT`, `BAD = 0`, and the constants. -/
theorem consts_ok {s4 : State} (hc : Ctx b s4) :
    WP isa (.block (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField ONE 1)) s4 fun t =>
      Rest [.a0, .a4] s4 t ∧ t.gpr .a0 = b + BitVec.ofNat 64 OUT ∧ Frame (constW b) s4.mem t.mem ∧
      bad t.mem b = 0 ∧ FS t.mem b DK = Spec.Ed448.d ∧ FS t.mem b ONE = 1 := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hDK : DK = 336 := rfl
  have hON : ONE = 1400 := rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s5 u5 => wp_addi (by decide) fun s6 u6 => wp_li (by decide) fun s7 u7 => ?_
  obtain hr7 : Rest [.a0, .a4] s4 s7 := (u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  obtain hc7 : Ctx b s7 := hc.of_rest hr7 (by decide)
  refine wp_sd (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc7.a3])
    (al8 hc7.al (by decide)) (hc7.inW (by decide)) fun s8 u8 => ?_
  obtain hc8 : Ctx b s8 := hc7.of_rest (u8.rest []) (by decide)
  obtain hm8 : s8.mem = s4.mem.writeW (b + BitVec.ofNat 64 BAD) (BitVec.ofNat 64 0) := by
    rw [u8.mem, u7.gpr, u7.mem, u6.mem, u5.mem]
  refine WP.append (constField_ok hc8 (o := DK) (by decide) (by decide) (fe_lt _)) fun s9 ⟨r9, f9, v9⟩ => ?_
  obtain hc9 := hc8.of_rest r9 (by decide)
  refine WP.mono (constField_ok hc9 (o := ONE) (by decide) (by decide) (v := 1) (by decide)) fun t ⟨rt, ft, vt⟩ => ?_
  obtain fB : Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s4.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  refine ⟨hr7.trans ((u8.rest _).trans ((r9.mono (by decide)).trans (rt.mono (by decide)))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [rt.gpr _ (by decide), r9.gpr _ (by decide), u8.gpr, u7.other _ (by decide), u6.gpr, u5.gpr, hc.a3,
      Offset.add_add]
    rfl
  · exact (fB.mono (by simp)).trans ((f9.mono (by simp)).trans (ft.mono (by simp)))
  · have f8t : Frame (constW b |>.drop 1) s8.mem t.mem := (f9.mono (by simp)).trans (ft.mono (by simp))
    unfold bad
    rw [f8t.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        simp only [List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide),
      hm8, Mem.readW_writeW_self64]
    rfl
  · rw [FS, slot_keep ft (by omega_arith) (by omega_arith) (by omega_arith), v9, VG.Proof.X448.toFe_self]
  · rw [FS, vt, VG.Proof.X448.toFe_one]

theorem vSetup_eq : vSetup = Impl.X25519.RISCV64.align ++
    ((copyBytes .a0 0 PK 57 ++ copyBytes .a1 0 SG 57 ++ copyBytes .a1 57 SGS 57 ++ copyBytes .a2 0 CH 57) ++
    (([.addi .a0 .a3 2047, .addi .a0 .a0 1, .li .a4 0, .store .d .a4 .a3 BAD] : List Instr) ++
        constField DK Spec.Ed448.d.val ++ constField ONE 1)) := by
  simp only [vSetup, List.append_assoc]; rfl

theorem vSetup_ok {s : State} (hp : VPre s) :
    WP isa (.block vSetup) s fun t => VCtx (base (s.gpr .a3)) t ∧ Rest [.a0, .a3, .a4] s t ∧
      Frame [⟨s.gpr .a3, 8192⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 SG) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 SGS) 57 =
        Spec.Ed448.bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 57) 57 ∧
      Spec.Ed448.bytesAt t.mem (base (s.gpr .a3) + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57 ∧
      bad t.mem (base (s.gpr .a3)) = 0 ∧ FS t.mem (base (s.gpr .a3)) DK = Spec.Ed448.d ∧
      FS t.mem (base (s.gpr .a3)) ONE = 1 := by
  obtain ⟨q, hq⟩ : ∃ q, q = s.gpr .a3 := ⟨_, rfl⟩
  rw [← hq]
  obtain hws : (⟨q, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hq]; simp
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hPK : PK = 1456 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hCH : CH = 1636 := rfl
  have hDK : DK = 336 := rfl
  have hON : ONE = 1400 := rfl
  rw [vSetup_eq]
  refine WP.append (Proof.Ed25519.RISCV64.align_ok (q := q) hq.symm hws) fun s0 ⟨hc, h0r, hm0⟩ => ?_
  obtain ⟨b, hb⟩ : ∃ b, b = base q := ⟨_, rfl⟩
  rw [← hb] at hc ⊢
  obtain sub8 : ∀ {o n : Nat}, o + n ≤ 8184 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩ :=
    fun h => by rw [hb]; exact base_sub8 q h
  obtain g0 : s0.gpr .a0 = s.gpr .a0 := h0r.gpr _ (by decide)
  obtain g1 : s0.gpr .a1 = s.gpr .a1 := h0r.gpr _ (by decide)
  obtain g2 : s0.gpr .a2 = s.gpr .a2 := h0r.gpr _ (by decide)
  refine WP.append (copies_ok hc sub8 (by rw [h0r.rd, hp.rd, g0, g1, g2])
    (by rw [g0, hq]; exact hp.pk_ws) (by rw [g1, hq]; exact hp.sig_ws) (by rw [g2, hq]; exact hp.ch_ws))
    fun s4 ⟨r4, f4, ePK, eSG, eSS, eCH⟩ => ?_
  obtain hc4 : Ctx b s4 := hc.of_rest r4 (by decide)
  refine WP.mono (consts_ok hc4) fun t ⟨rt, at0, ft, bt, dt, ot⟩ => ?_
  rw [hm0, g0] at ePK
  rw [hm0, g1] at eSG eSS
  rw [hm0, g2] at eCH
  obtain hwt : t.wr = s.wr := by rw [rt.wr, r4.wr, h0r.wr]
  obtain dc : ∀ {o : Nat}, 1456 ≤ o → o + 57 ≤ 1696 → ∀ r ∈ constW b, Region.Disjoint ⟨b + BitVec.ofNat 64 o, 57⟩ r :=
    fun h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨hc4.of_rest rt (by decide), fun d n hd => by rw [hwt, hb]; exact base_in hws hd, at0⟩,
    (h0r.mono (by decide)).trans ((r4.mono (by decide)).trans (rt.mono (by decide))), ?_,
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), ePK],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSG],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eSS],
    by rw [bytes_keep ft (dc (by decide) (by decide)) (by decide), eCH], bt, dt, ot⟩
  obtain sw : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨q, 8192⟩) → ∀ r ∈ rs, ∃ r' ∈ [(⟨q, 8192⟩ : Region)], Region.Sub r r' :=
    fun h r hr => ⟨_, List.mem_singleton_self _, h r hr⟩
  refine (f4.sub (sw fun r hr => ?_)).trans (ft.sub (sw fun r hr => ?_)) |> fun h => by rw [← hm0]; exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact sub8 (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub8 (by omega_arith)

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VCheckScalar`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: `S < L`

`checkS` checks that the 57 bytes of `S` (at `SGS`) are below `L`: its
low 448 bits plus `2⁴⁴⁸ - L` do not carry out (scalar reduction's
`subtract_ok`), and its byte 56 is 0 (`checkS_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 ACC)
open VG.Spec.X448 (P Fe)

theorem L_lt448 : Spec.Ed448.L < 256 ^ 56 := by decide +kernel

/-- 57 bytes are below `L` exactly when the last is 0 and the first 56 are. -/
theorem lt_L_iff (bs : List Byte) (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Spec.Ed448.L ↔
      (bs.getD 56 0).toNat = 0 ∧ Spec.Ed448.decodeLE (bs.take 56) < Spec.Ed448.L := by
  rw [Proof.Ed448.decodeLE_57 bs h]
  have := L_lt448
  constructor
  · intro hl
    obtain h0 : (bs.getD 56 0).toNat = 0 := by
      by_contra hne
      have : 256 ^ 56 ≤ 256 ^ 56 * (bs.getD 56 0).toNat := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
      omega_arith
    exact ⟨h0, by omega_using [hl]⟩
  · rintro ⟨h0, h1⟩
    rw [h0, Nat.mul_zero, Nat.add_zero]; exact h1

section
variable {b : Addr}

theorem checkS_ok {s : State} (hc : VCtx b s) :
    WP isa (.block checkS) s fun t => VCtx b t ∧ Rest [.a2, .a4, .a5, .a6] s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem ∧ FS t.mem b DK = FS s.mem b DK ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 (SGS)) 57) < Spec.Ed448.L) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hSS : SGS = 1576 := rfl
  have hSD : SD = 56 := rfl
  have hX : X2 = 56 := rfl
  have hD : DY = 168 := rfl
  unfold checkS
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (copyIn_ok hc.ctx (p := SGS) (by omega_using [hSS]) (by omega_using [hSS]) (by decide)) fun s1 h1 => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest h1.rest (by decide) (by decide)
  refine wp_li (by decide) fun s2 u2 => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest (u2.rest (ws := [.a5]) (by decide)) (by decide) (by decide)
  refine WP.append (subtract_ok (o := DY) ⟨by decide, by decide, by decide⟩ hc2.ctx (by rw [u2.gpr]; rfl))
    fun s3 ⟨hr3, hf3, _, h83, _⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  refine WP.append (orBad_ok hc3 (r := .a5) (by decide)) fun s4 ⟨hr4, hf4, hb4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_lbz (a := b + BitVec.ofNat 64 (SGS + 56)) (by omega_using [hSS]) (by rw [hc4.ctx.a3])
    (hc4.inR (by omega_using [hSS])) fun s5 u5 => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.a4]) (by decide)) (by decide) (by decide)
  refine WP.mono (orBad_ok hc5 (r := .a4) (by decide)) fun t ⟨hrt, hft, hbt⟩ => ?_
  -- The frames.
  obtain fC : Frame [FA b] s.mem s1.mem := h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  obtain fS : Frame [FA b] s2.mem s3.mem := hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hSD])⟩
  obtain f3 : Frame [FA b] s.mem s3.mem := fC.trans (by rw [u2.mem] at fS; exact fS)
  obtain hrt' : Rest [.a2, .a4, .a5, .a6] s t := (h1.rest.mono (by decide)).trans
    (((u2.rest (ws := [.a5]) (by decide)).mono (by decide)).trans ((hr3.mono (by decide)).trans
      ((hr4.mono (by decide)).trans (((u5.rest (ws := [.a4]) (by decide)).mono (by decide)).trans
        (hrt.mono (by decide))))))
  refine ⟨hc.of_rest hrt' (by decide) (by decide), hrt', ?_, ?_, ?_⟩
  · refine (f3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
    rw [← u5.mem]; exact hft.mono (by simp)
  · -- `d` stays.
    have hK : DK = 336 := rfl
    obtain f : Frame [⟨b + BitVec.ofNat 64 DY, 4 * 14⟩, ⟨b + BitVec.ofNat 64 X2, 4 * 14⟩,
        ⟨b + BitVec.ofNat 64 SD, 56⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩] s.mem t.mem := by
      refine (h1.frame.mono (by simp)).trans ?_
      rw [u2.mem] at hf3
      refine (hf3.mono (by simp)).trans ((hf4.mono (by simp)).trans ?_)
      rw [← u5.mem]; exact hft.mono (by simp)
    obtain e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [hK, hk]) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- The checks.
    obtain b3 : bad s3.mem b = bad s.mem b := by
      unfold bad
      rw [f3.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])) (by decide)]
    obtain hB : (s5.gpr .a4).toNat = (s.mem (b + BitVec.ofNat 64 (SGS + 56))).toNat := by
      rw [u5.gpr, toNat_imm (Nat.lt_trans (BitVec.isLt _) (by decide)), hf4 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint b (d := SGS + 56) (n := 1) (e := BAD) (k := 8) (by omega_using [o3, hSS])
            (by omega_using [hSS]) (by omega_using [o3]) _ (Region.contains_self _ _) h,
        f3 _ fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact fun h => Offset.disjoint_base b (d := SGS + 56) (n := 1) (k := ACC + 112) (by omega_using [o1, hSS])
            (by omega_using [hSS]) _ (Region.contains_self _ _) h]
    obtain hV : V s2.mem b DY = yw s.mem b (SGS) := by
      rw [u2.mem]; exact val32_congr fun j hj => (h1.vals j hj).1
    obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem (SGS)
    rw [hbt, u5.mem, hb4, b3, h83, hB, hV, lt_L_iff _ (by simp [Spec.Ed448.bytesAt]), e56, eB,
      Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
    have : (if Spec.Ed448.L ≤ yw s.mem b (SGS) then 1 else 0) = 0 ↔ yw s.mem b (SGS) < Spec.Ed448.L := by
      by_cases h : Spec.Ed448.L ≤ yw s.mem b (SGS)
      · rw [ite_eq_left h]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega_using [h'])⟩
      · rw [ite_eq_right h]; exact ⟨fun _ => by omega_using [h], fun _ => rfl⟩
    rw [this]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VFinish`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the result

`vFinish` checks that `Q` is the neutral point, `X = 0` and `Y - Z = 0`
fully reduced, and returns 1 exactly when no check failed (`vFinish_ok`):
1 less the top bit of `BAD | -BAD` (`top_nz`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y Z2 ACC freeze)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

/-- The top bit of `x | -x` is set exactly when `x` is not 0. -/
theorem top_nz (x : BitVec 64) : ((x ||| (0 - x)) >>> 63).toNat = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; decide
  · rw [ite_eq_right h, BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_or_distrib]
    obtain hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hlt := x.isLt
    obtain hn : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub]; simp; omega_using [hx]
    rw [hn, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    obtain h2 : (2 ^ 64 - x.toNat) / 2 ^ 63 ≤ 1 := by omega_using [hx]
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h3 | h3
    · rw [Nat.div_eq_of_lt h3, show (2 ^ 64 - x.toNat) / 2 ^ 63 = 1 by omega_using [hx, h3]]; rfl
    · rw [show x.toNat / 2 ^ 63 = 1 by omega_using [h3]]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with e | e <;> rw [e] <;> rfl

theorem bad_zero_iff {m : Mem} {b : Addr} : (m.readW (b + BitVec.ofNat 64 BAD) 64 = 0) ↔ bad m b = 0 := by
  unfold bad
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

section
variable {b : Addr}

theorem vFinish_ok {s : State} (hc : VCtx b s) {Q : Point} (hS : SlotsOk s.mem b RQ (ptV Q Q)) :
    WP isa (.block vFinish) s fun t =>
      t.gpr .a0 = BitVec.ofNat 64 (if bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z then 1 else 0) := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hA := X448.RISCV64.ACC_eq
  have hY : Y = 896 := rfl
  obtain hdo : Region.Disjoint ⟨b, 2048⟩ ⟨b + BitVec.ofNat 64 OUT, 56⟩ :=
    (Offset.disjoint_base b (d := OUT) (n := 56) (k := 2048) (by omega_using [o2]) (by omega_using [o2])).symm
  unfold vFinish
  simp only [outZero, copy, List.append_assoc, List.cons_append]
  -- `X`.
  refine WP.append (freeze_ok hc.ctx hc.a0 (fun k hk => by rw [Offset.add_add]; exact hc.inW (by omega_using [o2, hk])) hdo)
    fun s1 ⟨_, hr1, hf1, hw1⟩ => ?_
  obtain hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (outOr_ok hc1) fun s2 ⟨hr2, hm2, hv2⟩ => ?_
  obtain hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  refine WP.append (orBad_ok hc2 (r := .a7) (by decide)) fun s3 ⟨hr3, hf3, hb3⟩ => ?_
  obtain hc3 : VCtx b s3 := hc2.of_rest hr3 (by decide) (by decide)
  obtain hS3 := SlotsOk.lo (m := s1.mem) (m' := s3.mem) (by rw [← hm2]; exact hf3) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact disj_hi (by omega_using [o3]) (by omega_using [o3])) (slots_freeze hf1 hdo hS (by decide))
    (by decide)
  -- `Y - Z`.
  refine WP.append (R64.subS (o := TA) (x := RY) (y := RZ) (by decide) (by decide) (by decide) (by decide) hc3.ctx hS3)
    fun s4 ⟨hr4, hf4, hS4⟩ => ?_
  obtain hc4 : VCtx b s4 := hc3.of_rest hr4 (by decide) (by decide)
  refine wp_li (by decide) fun s5 u5 => ?_
  obtain hc5 : VCtx b s5 := hc4.of_rest (u5.rest (ws := [.t0]) (by decide)) (by decide) (by decide)
  have hS5 := hS4
  rw [← u5.mem] at hS5
  refine WP.append (selG (o := X2) (q := TA) (r := TA) (sw := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5.ctx (by decide) (by rw [u5.gpr]; rfl) hS5 (hS5 TA (by decide)) (hS5 TA (by decide)))
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_
  obtain hc6 : VCtx b s6 := hc5.of_rest hr6 (by decide) (by decide)
  refine WP.append (freeze_ok hc6.ctx hc6.a0 (fun k hk => by rw [Offset.add_add]; exact hc6.inW (by omega_using [o2, hk])) hdo)
    fun s7 ⟨_, hr7, hf7, hw7⟩ => ?_
  obtain hc7 : VCtx b s7 := hc6.of_rest hr7 (by decide) (by decide)
  refine WP.append (outOr_ok hc7) fun s8 ⟨hr8, hm8, hv8⟩ => ?_
  obtain hc8 : VCtx b s8 := hc7.of_rest hr8 (by decide) (by decide)
  refine WP.append (orBad_ok hc8 (r := .a7) (by decide)) fun s9 ⟨hr9, hf9, hb9⟩ => ?_
  obtain hc9 : VCtx b s9 := hc8.of_rest hr9 (by decide) (by decide)
  -- The result.
  refine wp_ld (a := b + BitVec.ofNat 64 BAD) (by decide) (by rw [hc9.ctx.a3]) (hc9.al8 (by decide))
    (hc9.inR (by omega_using [o3]))
    fun t1 v1 => wp_li (by decide) fun t2 v2 => wp_sub fun t3 v3 => ?_
  refine wp_or fun t4 v4 => wp_srl (by decide) fun t5 v5 => wp_li (by decide) fun t6 v6 => wp_sub fun t7 v7 => ?_
  refine WP.block_nil ?_
  -- `BAD` along the way.
  obtain rB : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) → bad m' b = bad m b := fun hf hd => by
    unfold bad; rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]
  obtain dYO : ∀ r ∈ [(⟨b + BitVec.ofNat 64 Y, 56⟩ : Region), ⟨b + BitVec.ofNat 64 OUT, 56⟩],
      Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)
  obtain dFA : ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_using [o1, o3]) (by omega_using [o3])
  obtain b1 : bad s1.mem b = bad s.mem b := rB hf1 dYO
  obtain b8 : bad s8.mem b = bad s3.mem b := by
    rw [bad, hm8, ← bad, rB hf7 dYO, rB hf6 dFA, bad, u5.mem, ← bad, rB hf4 dFA]
  obtain e9 : bad s9.mem b = bad s.mem b |||
      orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 |||
      orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 := by
    rw [hb9, b8, hb3, hv8, hv2, bad, hm2, ← bad, b1]
  -- The two elements.
  obtain hX : FS s.mem b X2 = Q.X := by
    rw [hS X2 (by decide)]; simp only [ptV, RX, X2, ↓reduceIte]
  obtain hYZ : FS s6.mem b X2 = Q.Y - Q.Z := by
    rw [hS6 X2 (by decide)]
    simp only [upd, ptV, pick, VG.Proof.X25519.sel, TA, RX, RY, RZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte]
  obtain i1 : orw (fun k => wd s1.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.X = 0 := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw1, hX]
  obtain i2 : orw (fun k => wd s7.mem (b + BitVec.ofNat 64 OUT) (4 * k)) 14 = 0 ↔ Q.Y = Q.Z := by
    rw [orw_eq_zero, ← val32_eq_zero, ← fs_zero hw7, hYZ, fin_sub_eq_zero]
  -- The result.
  obtain ev : t3.gpr .a6 = s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.gpr]
  obtain e8 : t3.gpr .a5 = 0 - s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 := by
    rw [v3.gpr, v2.gpr, v2.other _ (by decide), v1.gpr]; rfl
  obtain hz : (t5.gpr .a6).toNat = if s9.mem.readW (b + BitVec.ofNat 64 BAD) 64 = 0 then 0 else 1 := by
    rw [v5.gpr, v4.gpr, ev, e8, top_nz]
  rw [v7.gpr, v6.gpr, v6.other _ (by decide)]
  obtain hc' : (bad s9.mem b = 0) ↔ (bad s.mem b = 0 ∧ Q.X = 0 ∧ Q.Y = Q.Z) := by
    rw [e9, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, i1, i2, and_assoc]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : bad s9.mem b = 0
  · rw [ite_eq_left (hc'.mp h0), ite_eq_left (bad_zero_iff.mpr h0)] at *
    rw [BitVec.toNat_sub, hz]; rfl
  · rw [ite_eq_right (fun h => h0 (hc'.mpr h)), ite_eq_right (fun h => h0 (bad_zero_iff.mp h))] at *
    rw [BitVec.toNat_sub, hz]; rfl

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification equation on RISCV64: the whole function

`vg_ed448_verify_equation` returns 1 exactly when `verifyEquation` holds
(`verifyEquation_correct`), given that `recoverX` is `recoverRef`
(`RecoverOk`, proven in `Proof/Ed448/Facts.lean` and passed in by the
registration): with `-A` and `-R` decoded, `S` checked, the digits of `S`
and `k` recoded and the two tables built, the joint loop leaves `Q`
representing `[S]B + [k](-A)` (`joint_ok`); `[4](Q + (-R))` is the neutral
point exactly when `[4]Q = [4]R`, the equation (`neutral_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)
open VG.Proof.Ed25519.RISCV64 (base)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Impl.Ed448.WnafWide (digitAt residual)

/-! ## The equation -/

theorem pointEqual_identity (q : Point) :
    Spec.Ed448.pointEqual q Spec.Ed448.identity = (decide (q.X = 0) && decide (q.Y = q.Z)) := by
  simp only [Spec.Ed448.pointEqual, Spec.Ed448.identity, Fin.mul_one, Fin.zero_mul, Fin.one_mul]
  rfl

/-- `[4](Q + (-R))` is neutral exactly when the equation holds, for `Q = [S]B + [k](-A)`. -/
theorem neutral_eq {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114) (hc : ch.length = 57)
    {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a) (hr : Spec.Ed448.decodePoint (sig.take 57) = some r)
    {Q : Point} (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a))) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double
          (Spec.Ed448.pointAdd Q (Proof.Ed448.negPoint r)))) Spec.Ed448.identity) := by
  obtain hR := Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hr)
  rw [Proof.Ed448.verifyEquation_some hl hs hc ha hr hQ hR]
  refine congrArg (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) && ·) ?_
  generalize Spec.Ed448.decodeLE (sig.drop 57) • baseAff + Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a) = x at hQ
  obtain h1 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hQ)
  obtain h2 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hR)
  obtain h3 := Proof.Ed448.double_rep (Proof.Ed448.double_rep (Proof.Ed448.pointAdd_rep hQ hR.neg))
  rw [Bool.eq_iff_iff, Proof.Ed448.pointEqual_rep h1 h2, Proof.Ed448.pointEqual_rep h3 Proof.Ed448.identity_rep,
    Proof.Ed448.four_smul, Proof.Ed448.four_smul, Proof.Ed448.four_smul, smul_add, smul_neg, add_neg_eq_zero]

/-! ## The digits -/

theorem residual_tail {k : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) :
    ∀ n, 464 ≤ n → residual false k n = 0
  | n, h => by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 464 with h' | h'
      · have e : n = 463 := by omega_using [h, h']
        subst e
        exact residual_464 hk
      · show Impl.Ed448.WnafWide.next false (residual false k n) = 0
        rw [ih h']; rfl

theorem digit_tail {k n : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hn : 464 ≤ n) : digitAt false k n = 0 := by
  unfold digitAt; rw [residual_tail hk n hn]; rfl

theorem bit_tail {k i : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hi : 456 ≤ i) :
    Proof.Ed448.WnafWide.bit k i = 0 := by
  unfold Proof.Ed448.WnafWide.bit; rw [Proof.Ed448.WnafWide.tail_quotient hk hi]

/-- The bits written by `bitsOf`. -/
theorem tbSet_bit {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : tbSet 1 K (tbSet 0 S fun _ => 0) h =
      if h % 4 = 0 then Proof.Ed448.WnafWide.bit S (h / 4) else if h % 4 = 1 then Proof.Ed448.WnafWide.bit K (h / 4)
      else 0 := by
  unfold tbSet
  by_cases h0 : h % 4 = 0
  · rw [ite_eq_right (by omega_using [h0]), ite_eq_left h0]
    by_cases hi : h / 4 < 456
    · rw [ite_eq_left ⟨h0, hi⟩, Proof.Ed448.WnafWide.bit_shift]
    · rw [ite_eq_right (fun c => hi c.2), bit_tail hS (by omega_using [hi])]
  · rw [ite_eq_right h0]
    by_cases h1 : h % 4 = 1
    · rw [ite_eq_left h1]
      by_cases hi : h / 4 < 456
      · rw [ite_eq_left ⟨h1, hi⟩, Proof.Ed448.WnafWide.bit_shift]
      · rw [ite_eq_right (fun c => hi c.2), ite_eq_right (by omega_using [h0]), bit_tail hK (by omega_using [hi])]
    · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1]), ite_eq_right (by omega_using [h0])]

theorem dig_eq {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : recCur 1 K (recCur 0 S (tbSet 1 K (tbSet 0 S fun _ => 0)) 464) 464 h = digV S K h := by
  unfold recCur digV
  rw [tbSet_bit hS hK]
  rcases (by omega_using [] : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3) with e | e | e | e <;>
    simp only [e, Nat.reduceEqDiff, false_and, ite_false, ite_true, true_and, Nat.reduceAdd]
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hS (by omega_using [hn])]; rfl
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hK (by omega_using [hn])]; rfl

section
variable {b : Addr}

/-! ## Frames -/

/-- An element whose slot is apart from a frame's regions stays. -/
theorem fs_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) :
    FS m' b q = FS m b q := fsD hf hd

theorem disj_decW {d n xo yo : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 1696) (hxo : d + n ≤ xo ∨ xo + 56 ≤ d)
    (hyo : d + n ≤ yo ∨ yo + 56 ≤ d) (hx : xo + 56 ≤ 2048) (hy : yo + 56 ≤ 2048) :
    ∀ r ∈ decW b xo yo, Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hRA : DECODE_RA = 1712 := rfl
  intro r hr
  simp only [decW, yW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_FAB {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) (h3 : d + n ≤ 1696 ∨ 1704 ≤ d) :
    ∀ r ∈ [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_one {d n e k : Nat} (h1 : d + n ≤ e ∨ e + k ≤ d) (h2 : d + n ≤ 8192) (h3 : e + k ≤ 8192) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 e, k⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ h1 (by omega_using [h2]) (by omega_using [h3])

theorem disj_FA {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)

theorem disj_FAK {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3976) :
    ∀ r ∈ [FA b, KR b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by unfold KT; omega_using [h2]) (by omega_using [h2]) (by unfold KT; omega_using [])

theorem bytes_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.take_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem bytes_drop (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem keyOk_BT {a : VG.Proof.EdwardsLaw.EPoint dZ} {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 BT, 896⟩] m m') (h : KeyOk b a m) : KeyOk b a m' := fun i hi => by
  have hK : KT = 3976 := rfl
  have hB : BT = 5320 := rfl
  rw [kpt_keep hf fun o ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [List.mem_singleton.mp hr]
    rcases ho with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_using [hi, hK, hB]) (by omega_using [hi, hK]) (by omega_using [hB])]
  exact h i hi

theorem limit_of {bs : List Byte} (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Impl.Ed448.WnafWide.scalarLimit := by
  have := Proof.Ed448.decodeLE_below h
  unfold Impl.Ed448.WnafWide.scalarLimit Impl.Ed448.WnafWide.pow2
  exact this

theorem bad_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) : bad m' b = bad m b := by
  unfold bad
  rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]

/-- What the code before the joint loop leaves, for the inputs of `s`. -/
def PreOk (s u : State) : Prop :=
  VCtx (base (s.gpr .a3)) u ∧ u.sp = s.sp ∧
    JFix (base (s.gpr .a3)) (Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57))
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57)) u.mem ∧
    FS u.mem (base (s.gpr .a3)) DK = Spec.Ed448.d ∧
    (bad u.mem (base (s.gpr .a3)) = 0 ↔
      (Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57)).isSome ∧
      (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)).isSome ∧
      Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) < Spec.Ed448.L) ∧
    (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) = some a →
      KeyOk (base (s.gpr .a3)) (-Proof.Ed448.toAffine a) u.mem) ∧
    (∀ r, Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) = some r →
      FS u.mem (base (s.gpr .a3)) NRX = 0 - r.X ∧ FS u.mem (base (s.gpr .a3)) NRY = r.Y ∧ r.Z = 1)

theorem pre_run (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s fun u => PreOk s u ∧
    Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s u := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hTB : TB = 2104 := rfl
  have hKT : KT = 3976 := rfl
  have hBT : BT = 5320 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hPK : PK = 1456 := rfl
  have hCH : CH = 1636 := rfl
  have hNAX : NAX = 1176 := rfl
  have hNAY : NAY = 1232 := rfl
  have hNRX : NRX = 1288 := rfl
  have hNRY : NRY = 1344 := rfl
  have hONE : ONE = 1400 := rfl
  have hDK : DK = 336 := rfl
  unfold PreOk
  generalize hb : base (s.gpr .a3) = b
  unfold vPrefix
  refine WP.seq (WP.mono (vSetup_ok hp) fun s1 ⟨hc1, hr1, hf1, ePK, eSG, eSS, eCH, hb1, hd1, hone⟩ => ?_)
  rw [hb] at hc1 ePK eSG eSS eCH hb1 hd1 hone
  refine WP.seq (WP.mono (decode_ok hR hc1 (p := SG) (by decide) (by decide) (by decide) (xo := NRX) (yo := NRY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd1)
    fun s2 ⟨hc2, hr2, hf2, hd2, hb2, hv2⟩ => ?_)
  refine WP.seq (WP.mono (decode_ok hR hc2 (p := PK) (by decide) (by decide) (by decide) (xo := NAX) (yo := NAY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd2)
    fun s3 ⟨hc3, hr3, hf3, hd3, hb3, hv3⟩ => ?_)
  refine WP.seq (WP.mono (checkS_ok hc3) fun s4 ⟨hc4, hr4, hf4, hk4, hb4⟩ => ?_)
  refine WP.seq (WP.mono (bitsZero_ok hc4) fun s5 ⟨hc5, hr5, hf5, ht5⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc5 (src := SGS) (e := 0) (by decide) (by decide) (by decide) ht5)
    fun s6 ⟨hc6, hr6, hf6, ht6⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc6 (src := CH) (e := 1) (by decide) (by decide) (by decide) ht6)
    fun s7 ⟨hc7, hr7, hf7, ht7⟩ => ?_)
  -- What the digits' phases keep: everything below `TB`.
  obtain dTB : ∀ {d n : Nat}, d + n ≤ 2104 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 TB, 1872⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega_using [hTB, h])) (by omega_using [h]) (by omega_using [hTB])
  -- The inputs, as the phases read them.
  obtain kA : Spec.Ed448.bytesAt s2.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57 := by
    rw [bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
      (by decide), ePK]
  obtain kR : Spec.Ed448.bytesAt s1.mem (b + BitVec.ofNat 64 SG) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57 := by rw [eSG, bytes_take]
  obtain kS3 : Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eSS, bytes_drop]
  obtain kS5 : Spec.Ed448.bytesAt s5.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf5 (dTB (by omega_using [hSS])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), kS3]
  obtain kK : Spec.Ed448.bytesAt s6.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57 := by
    rw [bytes_keep hf6 (dTB (by omega_using [hCH])) (by decide), bytes_keep hf5 (dTB (by omega_using [hCH])) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eCH]
  rw [kS5] at ht6 ht7
  rw [kK] at ht7
  obtain hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  obtain hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  obtain hKl := limit_of hl5
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (recode_ok hc7 (e := 0) (k := S) (by decide) (fun i _ => by
      rw [tbSet_bit hSl hKl, ite_eq_left (by omega_using []), show (4 * i + 0) / 4 = i by omega_using []]) ht7)
    fun s8 ⟨hc8, hr8, hf8, ht8⟩ => ?_)
  refine WP.seq (WP.mono (recode_ok hc8 (e := 1) (k := K) (by decide) (fun i _ => by
      rw [recCur, ite_eq_right (by omega_using []), tbSet_bit hSl hKl, ite_eq_right (by omega_using []), ite_eq_left (by omega_using []),
        show (4 * i + 1) / 4 = i by omega_using []]) ht8)
    fun s9 ⟨hc9, hr9, hf9, ht9⟩ => ?_)
  obtain hdig : TbIs b s9.mem (digV S K) := fun h hh => by rw [ht9 h hh, dig_eq hSl hKl]
  -- The slots above the field area, from the checks to the digits.
  obtain k49 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s9.mem b q = FS s4.mem b q := fun h1 h2 => by
    rw [fs_disj hf9 (dTB (by omega_using [h2])), fs_disj hf8 (dTB (by omega_using [h2])), fs_disj hf7 (dTB (by omega_using [h2])),
      fs_disj hf6 (dTB (by omega_using [h2])), fs_disj hf5 (dTB (by omega_using [h2]))]
  obtain k34 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s4.mem b q = FS s3.mem b q := fun h1 h2 =>
    fs_disj hf4 (disj_FAB (by omega_using [h1]) (by omega_using [h2]) (by omega_using [h2]))
  obtain kFS1 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1176 ∨ 1400 ≤ q → q + 56 ≤ 1456 → FS s3.mem b q = FS s1.mem b q :=
    fun h1 h2 h3 => by
      rw [fs_disj hf3 (disj_decW (by omega_arith) (by omega_arith) (by unfold NAX; omega_arith)
          (by unfold NAY; omega_arith) (by decide) (by decide)),
        fs_disj hf2 (disj_decW (by omega_arith) (by omega_arith) (by unfold NRX; omega_arith)
          (by unfold NRY; omega_arith) (by decide) (by decide))]
  obtain kR3 : ∀ {q : Nat}, q = NRX ∨ q = NRY → FS s3.mem b q = FS s2.mem b q := fun h => by
    rcases h with rfl | rfl <;>
      exact fs_disj hf3 (disj_decW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `-A` and `d` before the tables.
  let A' : Point := ⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩
  obtain hpA : Pt s9.mem b NAX NAY ONE A' := ⟨rfl, rfl, rfl⟩
  obtain hd9 : FS s9.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf9 (dTB (by omega_using [hDK])), fs_disj hf8 (dTB (by omega_using [hDK])), fs_disj hf7 (dTB (by omega_using [hDK])),
      fs_disj hf6 (dTB (by omega_using [hDK])), fs_disj hf5 (dTB (by omega_using [hDK])), hk4, hd3]
  refine WP.seq (WP.mono (keyTable_ok hc9 hpA hd9) fun s10 hK10 => ?_)
  have hc10 : VCtx b s10 := hK10.1
  refine WP.mono (baseTable_ok hc10) fun s11 ⟨hc11, hr11, hf11, hB11⟩ => ?_
  obtain dBT : ∀ {d n : Nat}, d + n ≤ 5320 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 BT, 896⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega_using [hBT, h])) (by omega_using [h]) (by omega_using [hBT])
  obtain hfx : JFix b S K s11.mem := ⟨fun h hh => by
      obtain e1 := hf11 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact fun hc => (dBT (d := TB + h) (n := 1) (by omega_using [hTB, hh]) _ (List.mem_singleton_self _)) _
          (Region.contains_self _ _) hc
      obtain e2 := hK10.2.2.1 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        exact fun hc => (disj_FAK (d := TB + h) (n := 1) (by omega_using [hTB]) (by omega_using [hTB, hh]) r hr) _ (Region.contains_self _ _) hc
      rw [e1, e2]; exact hdig h hh, hB11⟩
  obtain hd11 : FS s11.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf11 (dBT (by omega_using [hDK]))]; exact hK10.2.2.2.2.2.2.2.1
  obtain dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega_using [o3]) (by omega_using [o3])
  obtain k911 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s11.mem b q = FS s9.mem b q := fun h1 h2 => by
    rw [fs_disj hf11 (dBT (by omega_using [h2])), fs_disj hK10.2.2.1 (disj_FAK (by omega_using [h1]) (by omega_using [h2]))]
  refine ⟨?_, (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans
    ((hr3.mono (by decide)).trans ((hr4.mono (by decide)).trans
    ((hr5.mono (by decide)).trans ((hr6.mono (by decide)).trans
    ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
    ((hr9.mono (by decide)).trans ((hK10.2.1.mono (by decide)).trans (hr11.mono (by decide)))))))))))⟩
  refine ⟨hc11, ?_, hfx, hd11, ?_, fun a hA => ?_, fun r hRr => ?_⟩
  · rw [hr11.sp, hK10.2.1.sp, hr9.sp, hr8.sp, hr7.sp, hr6.sp, hr5.sp, hr4.sp, hr3.sp, hr2.sp, hr1.sp]
  · rw [bad_keep hf11 (dBT (by omega_using [o3])), bad_keep hK10.2.2.1 (disj_FAK (by omega_using [o3]) (by omega_using [o3])),
      bad_keep hf9 (dTB (by omega_using [o3])), bad_keep hf8 (dTB (by omega_using [o3])), bad_keep hf7 (dTB (by omega_using [o3])),
      bad_keep hf6 (dTB (by omega_using [o3])), bad_keep hf5 (dTB (by omega_using [o3])), hb4, hb3, hb2, kA, kR, kS3, hS]
    simp only [hb1, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · obtain ⟨ax, ay, az⟩ := hv3 a (by rw [kA]; exact hA)
    obtain eA : A' = Proof.Ed448.negPoint a := by
      show (⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩ : Point) = ⟨0 - a.X, a.Y, a.Z⟩
      rw [k49 (by decide) (by decide), k49 (by decide) (by decide), k49 (by decide) (by decide),
        k34 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide), ax, ay,
        kFS1 (by decide) (by decide) (by decide), hone, az]
    obtain hArep : Rep A' (-Proof.Ed448.toAffine a) := by
      rw [eA]; exact (Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hA)).neg
    exact keyOk_BT hf11 (keyOk_of hArep hK10)
  · obtain ⟨rx, ry, rz⟩ := hv2 r (by rw [kR]; exact hRr)
    rw [k911 (by decide) (by decide), k911 (by decide) (by decide), k49 (by decide) (by decide),
      k49 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide),
      kR3 (.inl rfl), kR3 (.inr rfl), rx, ry, rz]
    exact ⟨rfl, rfl, rfl⟩

theorem pre_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s (PreOk s) :=
  WP.mono (pre_run hR hp) fun _ h => h.1

theorem verifyEquation_correct (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) :
    WP isa verifyEquation s fun t => ((t.gpr .a0).setWidth 32 =
      if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
        (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0) ∧
      Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s t := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  obtain hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  obtain hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  obtain hKl := limit_of hl5
  unfold verifyEquation
  refine WP.seq (WP.mono (pre_run hR hp) fun u ⟨⟨hcu, _, hfx, hdu, hbad, hkey, hnr⟩, hru⟩ => ?_)
  generalize hb : base (s.gpr .a3) = b at hcu hfx hdu hbad hkey hnr
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (joint_ok hSl hKl hcu hfx hdu) fun s12 ⟨sL, hvL, fL, rL, ⟨⟨t2', C12⟩, d12, rep12⟩⟩ => ?_)
  refine WP.seq (WP.mono (addNegR_ok hvL C12 d12) fun s13 ⟨hc13, st13, sl13⟩ => ?_)
  obtain ⟨tf, t, hef, ht, hk⟩ := WP.keep
    [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (vFinish_ok hc13 sl13) (by decide +kernel)
  obtain rf : Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s13 t :=
    ⟨hk.1, hk.2.1, hk.2.2, Exec.sp hef⟩
  refine ⟨tf, t, hef, ?_, hru.trans ((rL.mono (by decide)).trans
    ((st13.rest.mono (by decide)).trans rf))⟩
  rw [ht]
  obtain dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega_using [o3]) (by omega_using [o3])
  obtain hb13 : bad s13.mem b = bad u.mem b := by rw [bad_keep st13.frame dF, bad_keep fL dF]
  obtain kU : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s12.mem b q = FS u.mem b q := fun h1 h2 => by
    rw [fs_hi C12.stp.frame (by omega_using [o1, h1]) (by omega_using [h2]), fs_hi fL (by omega_using [o1, h1]) (by omega_using [h2])]
  rw [hb13] at *
  obtain res : ∀ (c : Prop) [Decidable c] (v : Bool), (c ↔ v = true) →
      (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if v then 1 else 0 := by
    intro c _ v h
    by_cases hc : c
    · rw [ite_eq_left hc, ite_eq_left (h.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun hv => hc (h.mpr hv))]; rfl
  refine res _ _ ?_
  cases hA : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) with
  | none =>
    rw [Proof.Ed448.verifyEquation_none (.inl hA)]
    exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).2.1; rw [hA] at this; exact absurd this (by decide),
      fun h => absurd h (by decide)⟩
  | some a =>
    cases hRr : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) with
    | none =>
      rw [Proof.Ed448.verifyEquation_none (.inr hRr)]
      exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).1; rw [hRr] at this; exact absurd this (by decide),
        fun h => absurd h (by decide)⟩
    | some r =>
      obtain hQ := rep12 _ (keyOk_FA fL (hkey a hA))
      simp only [Impl.Ed448.WnafWide.residual, natCast_zsmul] at hQ
      obtain ⟨rx, ry, rz⟩ := hnr r hRr
      obtain eR : (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = Proof.Ed448.negPoint r := by
        show (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = ⟨0 - r.X, r.Y, r.Z⟩
        rw [kU (by decide) (by decide), kU (by decide) (by decide), rx, ry, rz]
      rw [← hS, ← hK] at hQ
      rw [neutral_eq hl3 hl4 hl5 hA hRr hQ, hS, pointEqual_identity, hbad]
      simp only [hA, hRr, Option.isSome_some, true_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [eR]

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# `vg_ed448_verify_equation` on RISC-V, verified

The function meets `verifyRISCV64` (`VTiming.lean`), with no stack. Its
correctness proof preserves registers across the shared addition-chain call
and establishes the ABI obligations (`verifyEquation_ok`), and it is
constant time from its pointers and inputs (`verifyEquation_ct`).

Two runs from states with the same pointers and the same inputs leak the same
trace (`verifyEquation_rel`). Everything before the joint loop, its start,
`[4](R + (-R'))` and the end are constant time from the pointers
(`VCT.lean`). In the loop, both runs hold the same digits of the same `S`
and `k` (`pre_ok`, from the same inputs), so at each position both take the
same branches, and each branch is constant time from its digit
(`base_rel`, `key_rel`, `step_rel`, `loop_rel`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Ed448.RISCV64.Comb (ptOf DQ)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.RISCV64 (ACC)
open VG.Proof.Ed25519.RISCV64 (base)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Registers and stack pointers equal in two given states. -/
theorem eq2_regs {σ₁ σ₂ : State} {rs : List Reg} (hsp : σ₁.sp = σ₂.sp) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) :
    ∀ a b, Eq2 σ₁ σ₂ a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := fun a b ⟨ha, hb⟩ => by
  subst ha hb; exact ⟨hsp, hr⟩

section
variable {b : Addr}

/-! ## The digits' branches -/

theorem a5_digit {S K : Nat} {w z l : State} {t2v : BitVec 64} {m : Nat} (hm : m < 464)
    (hc : R64.Cur b w t2v (BitVec.ofNat 64 m) DQ (FS z.mem b) z) (hfx : JFix b S K w.mem) {e : Nat}
    (he : e = 2 ∨ e = 3)
    (h5 : l.gpr .a5 = BitVec.ofNat 64 (z.mem (b + BitVec.ofNat 64 (TB + (4 * m + e)))).toNat) :
    l.gpr .a5 = dByte (digitAt false (if e = 2 then S else K) m) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  rw [h5, byte_hi hc.stp.frame (by omega_using [hA, hT]) (by omega_using [hm, he, hT]), dig_byte hfx.1 (by omega_using [hm]) he]

theorem base_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addBase TT := by
  obtain y₁ := vctx_cur hv₁ c₁
  obtain y₂ := vctx_cur hv₂ c₂
  unfold addBase
  refine rel_seq (load2_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 2) (by omega_using [hm]) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 2) (by omega_using [hm]) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  obtain d₁ := a5_digit hm c₁ hf₁ (.inl rfl) e₁
  obtain d₂ := a5_digit hm c₂ hf₂ (.inl rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => baseBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

theorem key_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addKey TT := by
  obtain y₁ := vctx_cur hv₁ c₁
  obtain y₂ := vctx_cur hv₂ c₂
  unfold addKey
  refine rel_seq (load3_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 3) (by omega_using [hm]) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 3) (by omega_using [hm]) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  obtain d₁ := a5_digit hm c₁ hf₁ (.inr rfl) e₁
  obtain d₂ := a5_digit hm c₂ hf₂ (.inr rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => keyBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

/-! ## The loop -/

theorem step_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {x₁ x₂ : State} (hx₁ : WInv b S K w₁ (m + 1) x₁) (hx₂ : WInv b S K w₂ (m + 1) x₂) :
    RelCT isa (Eq2 x₁ x₂) jointStep TT := by
  have hx₁' := hx₁
  have hx₂' := hx₂
  obtain ⟨⟨_, cx₁⟩, -, -⟩ := hx₁'
  obtain ⟨⟨_, cx₂⟩, -, -⟩ := hx₂'
  unfold jointStep
  refine rel_seq (dec_ct (eq2_regs (by rw [cx₁.stp.rest.sp, cx₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cx₁.t1, cx₂.t1]))
    (decStep_ok hm hx₁) (decStep_ok hm hx₂) fun y₁ y₂ ⟨⟨_, cy₁⟩, dy₁, ry₁⟩ ⟨⟨_, cy₂⟩, dy₂, ry₂⟩ => ?_
  refine rel_seq (dbl_ct (eq2_regs (by rw [cy₁.stp.rest.sp, cy₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cy₁.ctx.a3, cy₂.ctx.a3]))
    (dblStep_ok cy₁ dy₁ ry₁) (dblStep_ok cy₂ dy₂ ry₂) fun z₁ z₂ ⟨⟨_, cz₁⟩, dz₁, rz₁⟩ ⟨⟨_, cz₂⟩, dz₂, rz₂⟩ => ?_
  refine rel_seq (base_rel hv₁ hv₂ hf₁ hf₂ hw hm cz₁ cz₂) (addBase_ok hv₁ hf₁ hm cz₁ dz₁ rz₁)
    (addBase_ok hv₂ hf₂ hm cz₂ dz₂ rz₂) fun q₁ q₂ ⟨⟨_, cq₁⟩, _, _⟩ ⟨⟨_, cq₂⟩, _, _⟩ => ?_
  exact key_rel hv₁ hv₂ hf₁ hf₂ hw hm cq₁ cq₂

theorem loop_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp)
    (h₁ : WInv b S K w₁ 464 w₁) (h₂ : WInv b S K w₂ 464 w₂) :
    RelCT isa (Eq2 w₁ w₂) (.loop jointStep (.nonzero .t1)) TT := by
  refine (RelCT.loop (Q := TT) (fun n a b' => 1 ≤ n ∧ n ≤ 464 ∧ WInv b S K w₁ n a ∧ WInv b S K w₂ n b') ?_
    464).mono (fun a b' ⟨ha, hb⟩ => by subst ha hb; exact ⟨by decide, le_refl _, h₁, h₂⟩) fun _ _ h => h
  intro n
  rcases n with _ | m
  · exact RelCT.of_false fun a b' h => absurd h.1 (by decide)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn1, hn2, hs₁, hs₂⟩ e₁ e₂
    obtain hm : m < 464 := by omega_using [hn2]
    obtain r := ((step_rel hv₁ hv₂ hf₁ hf₂ hw hm hs₁ hs₂).wp
      (F₁ := fun (t : State) => WInv b S K w₁ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0))
      (F₂ := fun (t : State) => WInv b S K w₂ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0)) fun a b' ⟨ha, hb⟩ => by
        subst ha hb; exact ⟨jointStep_ok hv₁ hf₁ hm hs₁, jointStep_ok hv₂ hf₂ hm hs₂⟩)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
    obtain ⟨ht, -, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := r
    refine ⟨ht, ⟨by rw [eval_nonzero, eval_nonzero, z₁, z₂], fun _ => trivial, fun hc => ⟨m, by omega_using [], ?_⟩⟩⟩
    rw [eval_nonzero, z₁] at hc
    have : m ≠ 0 := by simpa using hc
    exact ⟨by omega_using [this], by omega_using [hn2], g₁, g₂⟩

theorem jointLoop_rel {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit)
    (hK : K < Impl.Ed448.WnafWide.scalarLimit) {u₁ u₂ : State} (hv₁ : VCtx b u₁) (hv₂ : VCtx b u₂)
    (hf₁ : JFix b S K u₁.mem) (hf₂ : JFix b S K u₂.mem) (hd₁ : FS u₁.mem b DK = Spec.Ed448.d)
    (hd₂ : FS u₂.mem b DK = Spec.Ed448.d) (hu : u₁.sp = u₂.sp) :
    RelCT isa (Eq2 u₁ u₂) jointLoop TT := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  have hDK : DK = 336 := rfl
  unfold jointLoop
  refine rel_seq (init_ct (eq2_regs hu fun r hr => by rw [List.mem_singleton.mp hr, hv₁.ctx.a3, hv₂.ctx.a3]))
    (jointInit_ok hv₁) (jointInit_ok hv₂) fun w₁ w₂ ⟨vw₁, rw₁, fw₁, pw₁, tw₁⟩ ⟨vw₂, rw₂, fw₂, pw₂, tw₂⟩ => ?_
  obtain fa : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → Frame [FA b] u.mem w.mem := fun hf =>
    hf.sub fun r hr => ⟨FA b, by simp, by
      have hA : ACC = 952 := rfl
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)⟩
  obtain dk : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → FS w.mem b DK = FS u.mem b DK := fun hf =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_using [hDK]) (by omega_arith)
  obtain start : ∀ {w : State}, VCtx b w → ptOf (FS w.mem b) = Spec.Ed448.identity →
      w.gpr .t1 = BitVec.ofNat 64 464 → FS w.mem b DK = Spec.Ed448.d → WInv b S K w 464 w :=
    fun hv hp ht hd => ⟨⟨_, ⟨hv.ctx, R64.Stp.refl _ _, rfl, ht, fun _ _ => rfl⟩⟩, hd, fun a _ => by
      beta_reduce
      rw [hp, residual_464 hS, residual_464 hK]
      simpa only [Nat.cast_zero, zero_smul, add_zero] using Proof.Ed448.identity_rep⟩
  exact loop_rel vw₁ vw₂ (jfix_FA (fa fw₁) hf₁) (jfix_FA (fa fw₂) hf₂) (by rw [rw₁.sp, rw₂.sp, hu])
    (start vw₁ pw₁ tw₁ (by rw [dk fw₁, hd₁])) (start vw₂ pw₂ tw₂ (by rw [dk fw₂, hd₂]))

end

/-! ## The whole function -/

/-- `verifyEquationContract` by register. -/
def verifyRISCV64 : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 57⟩
    let sig : Region := ⟨s.gpr .a1, 114⟩
    let ch : Region := ⟨s.gpr .a2, 57⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a2) 57).map (·.toNat) =
    (Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a2) 57).map (·.toNat)


theorem bytes_parts {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  obtain hi : Function.Injective (fun x : Byte => x.toNat) := fun x y hxy => BitVec.eq_of_toNat_eq hxy
  obtain e := List.map_injective_iff.mpr hi h
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verifyEquation_rel (hR : Proof.Ed448.RecoverOk) {σ₁ σ₂ : State} (h₁ : VPre σ₁) (h₂ : VPre σ₂)
    (hpub : verifyRISCV64.pub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) verifyEquation TT := by
  obtain ⟨p0, p1, p2, p3, psp, pb⟩ := hpub
  obtain ⟨-, eS, eK⟩ := bytes_parts (by simp [Spec.Ed448.bytesAt]) (by simp [Spec.Ed448.bytesAt]) pb
  unfold verifyEquation
  refine rel_seq (prefix_ct (eq2_regs psp fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption))
    (pre_ok hR h₁) (pre_ok hR h₂) fun u₁ u₂ ⟨c₁, sp₁, f₁, d₁, _⟩ ⟨c₂, sp₂, f₂, d₂, _⟩ => ?_
  rw [← p3] at c₂ f₂ d₂
  rw [← eS, ← eK] at f₂
  obtain hl4 : (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  obtain hSl := limit_of (bs := (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  obtain hKl := limit_of (bs := Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a2) 57) (by simp [Spec.Ed448.bytesAt])
  generalize base (σ₁.gpr .a3) = b at c₁ c₂ f₁ f₂ d₁ d₂
  obtain hu : u₁.sp = u₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (jointLoop_rel hSl hKl c₁ c₂ f₁ f₂ d₁ d₂ hu) (joint_ok hSl hKl c₁ f₁ d₁) (joint_ok hSl hKl c₂ f₂ d₂)
    fun v₁ v₂ ⟨L₁, vL₁, _, rL₁, ⟨⟨_, cv₁⟩, dv₁, _⟩⟩ ⟨L₂, vL₂, _, rL₂, ⟨⟨_, cv₂⟩, dv₂, _⟩⟩ => ?_
  obtain hv : v₁.sp = v₂.sp := by rw [cv₁.stp.rest.sp, cv₂.stp.rest.sp, rL₁.sp, rL₂.sp, hu]
  refine rel_seq (addNegR_ct (eq2_regs hv fun r hr => by
      rw [List.mem_singleton.mp hr, cv₁.ctx.a3, cv₂.ctx.a3]))
    (addNegR_ok vL₁ cv₁ dv₁) (addNegR_ok vL₂ cv₂ dv₂) fun t₁ t₂ ⟨ct₁, st₁, _⟩ ⟨ct₂, st₂, _⟩ => ?_
  refine vFinish_ct (eq2_regs (by rw [st₁.rest.sp, st₂.rest.sp, rL₁.sp, rL₂.sp, hu]) fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ct₁.a0, ct₂.a0]
  · rw [ct₁.ctx.a3, ct₂.ctx.a3]

theorem verifyEquation_ct (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyRISCV64.pre verifyRISCV64.pub verifyEquation :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (verifyEquation_rel hR (σ₁ := s₁) (σ₂ := s₂) ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2⟩
      ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2⟩ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1


/-! ## Correctness with the ABI -/

open VG VG.RISCV64


open VG VG.RISCV64

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State)
    (hs : verifyRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, h, hr⟩ := verifyEquation_correct hR ⟨h1, h2, h3, h4, h5⟩
  exact ⟨t, s', he, ⟨fun r hm => hr.gpr r (by cases r <;> simp_all [preserved]),
    hr.sp, hr.gpr .ra (by decide)⟩, h⟩

end VG.Proof.Ed448.RISCV64
