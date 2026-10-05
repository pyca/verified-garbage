import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.BaseAccumulate`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PointAccumulateLoop`. -/
section
/-! The counter of the descending-bit loops. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem CounterKeep.refl (base : Addr) (s : State) : CounterKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

end VG.Proof.Ed25519.AArch64
end

/-!
# Adding cached points

The cached addition is the specification's `pointAdd` (`ring`); a table's
cached point is loaded straight into slots 4–7.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Fin.CommRing

def addCachedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : Env) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = addCachedResult e := rfl

theorem pointAddCached_eval (e : Env) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [pointAddCached_formula]
  simp only [addCachedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> ring

theorem pointAddCached_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  point_ops_high _ (by decide) e i hi

theorem pointAddCached_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : point (env s.mem base) 4 5 6 7 = cache q) :
    WP isa (.block pointAddCached) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointAddCachedOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAddCached_eval _ q hq, pointAddCached_high _⟩

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores_ok ht (by constructor <;> omega) .x4 .x5 .x6 .x7) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · change F (st4 _ _ _ _ _ _ _) base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, fe_st4 _ _ (by omega), hv]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega⟩ = env t.mem base ⟨4 + j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base o ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : TableKeep base 192 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableQ_other {base : Addr} {s t : State} (h : TableKeep base 192 128 s t)
    (i : Slot) (hi : i.val < 4 ∨ 8 ≤ i.val) : env t.mem base i = env s.mem base i := by
  change F t.mem base (offset i) = F s.mem base (offset i)
  rcases hi with hi | hi
  · exact Outside_F h.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  · exact Outside_F h.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyFrame`. -/
section
/-! Verification preserves input buffers and its saved pointers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64


theorem tableFrame_work {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o ≤ 64) (hn : 768 ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega) hp

theorem outside_bytes {base p : Addr} {o n len : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192)
    (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt m' p len = Spec.Ed25519.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  apply h
  change ofs base (off p i) < o ∨ o + n ≤ ofs base (off p i)
  have := hf i (List.mem_range.mp hi)
  omega

theorem PowersKeep.header {base : Addr} {o n d : Nat} {s t : State}
    (h : PowersKeep base o n s t) (hd : 7936 ≤ d) (hb : d + 8 ≤ 8192) (hn : o + n ≤ 7936) :
    t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (by omega) (Or.inr (by omega)) (by omega)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyInputs`. -/
section
/-! Reload verification pointers and check the complete unsigned scalar S. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) (d : Nat)
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [ld r d]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  rw [runBlock_cons, load_sc hs ha hd, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.addImm .x r r 32]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (32 : Nat) < 4096 from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  refine WP.mono (loadWords_ok s .x2 (by decide) (by rw [hp]; exact hr)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, kt⟩
  rw [scalarValue, tv, hp, decodeLE_inputWords]

theorem setZeroX10_ok (s : State) :
    WP isa (.block [.movz .w .x10 0 0]) s fun t => t.gpr .x10 = 0 ∧ Keeps [.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hk)

theorem carryMask_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block [.sbcs .x .x8 .x10 .x10]) s fun t =>
      (t.gpr .x8 != 0) = !s.c ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun k hk => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_addWithCarry, ite_true, BitVec.setWidth_eq, hz]
    cases s.c <;> decide
  · simp only [RegUpd.gpr_addWithCarry,
      show k ≠ .x8 by simpa only [List.mem_singleton] using hk, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      (t.gpr .x8 != 0) = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L) := by
  change WP isa (.block (([ld .x2 7944] : List Instr) ++
    ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr) ++
    loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) s _
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .x2) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (setZeroX10_ok b) fun z ⟨zz, kz⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok z (off sig 32) ((kz.gpr _ (by decide)).trans bp) (by
    intro d hd; rw [kz.rd, kz.wr, kb.rd, kb.wr, ka.rd, ka.wr]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok c ((kc.gpr _ (by decide)).trans zz)) fun d ⟨dc, _, _, kd⟩ => ?_
  refine WP.mono (carryMask_ok d ((kd.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans zz)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨(((((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kz (by decide))).trans (Keep.of_keeps kc (by decide))).trans
    (Keep.of_keeps kd (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.mem.trans (kd.mem.trans (kc.mem.trans (kz.mem.trans (kb.mem.trans ka.mem)))), ?_⟩
  rw [tz, dc, cv, kz.mem, kb.mem, ka.mem]
  simp only [← decide_not, Nat.not_le]

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's windows: doublings, digits and table additions

The accumulator in slots 0–3 always represents a point of the group: four
doublings multiply it by 16 (`dbl-2008-hwcd`, which reads only `X : Y : Z`,
`RepP`), and a nonzero digit `v` adds entry `v - 1` of a table, which
represents `[v]X`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a window may change: the field workspace, and the registers it
computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp,
    by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : WinKeep base s t :=
  ⟨fun r hr _ hs => h.gpr r hs hr, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.of_counter {base : Addr} {s t : State} (h : CounterKeep base s t) : WinKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Small blocks -/

theorem movzW_ok (s : State) (r : Reg) (imm : BitVec 16) :
    WP isa (.block [.movz .w r imm 0]) s fun t => t.gpr r = imm.setWidth 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_setWidth (by decide)]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-! ## Four doublings -/

theorem dblOps_eval (e : Env) :
    point (evalOps (dblOps true) e) 0 1 2 3 = dblPoint (point e 0 1 2 3) ∧
    evalOps (dblOps false) e 0 = (dblPoint (point e 0 1 2 3)).X ∧
    evalOps (dblOps false) e 1 = (dblPoint (point e 0 1 2 3)).Y ∧
    evalOps (dblOps false) e 2 = (dblPoint (point e 0 1 2 3)).Z :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dbl_ok {s : State} {base : Addr} (hs : Scr s base) (t : Bool) {a : EPoint dZ}
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (fieldCode (dblOps t))) s fun u => Keep base s u ∧
      RepP (point (env u.mem base) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (env u.mem base) 0 1 2 3) (a + a)) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok _ hs) fun u ⟨ku, vu⟩ => ?_
  have hr := dblPoint_rep ha
  refine ⟨ku, ?_, fun ht => ?_, fun i hi => by
    rw [vu]; exact point_ops_high _ (by cases t <;> decide) _ i hi⟩
  · rw [vu]
    cases t
    · obtain ⟨_, ex, ey, ez⟩ := dblOps_eval (env s.mem base)
      refine ⟨?_, ?_, ?_⟩
      · show toZ (evalOps _ _ 2) ≠ 0
        rw [ez]; exact hr.z
      · show toZ (evalOps _ _ 0) = _ * toZ (evalOps _ _ 2)
        rw [ex, ez]; exact hr.x
      · show toZ (evalOps _ _ 1) = _ * toZ (evalOps _ _ 2)
        rw [ey, ez]; exact hr.y
    · rw [(dblOps_eval _).1]; exact hr.proj
  · subst ht
    rw [vu, (dblOps_eval _).1]; exact hr

theorem doubleWindow_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scr s base)
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa doubleWindow s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [doubleWindow]
  refine WP.seq (WP.mono (movzW_ok s .x1 3) fun s₁ ⟨c1, k1⟩ => ?_)
  have hs₁ : Scr s₁ base := hs.of_keeps k1 (by decide)
  have k1d : DoubleKeep base s s₁ := ⟨fun r hr _ => k1.gpr r (by simpa using hr), k1.rd, k1.wr, k1.sp,
    by rw [k1.mem]; exact Outside.refl _ _ _ _⟩
  have keepD {x y : State} (k : Keep base x y) : DoubleKeep base x y :=
    ⟨fun r _ hc => k.gpr r hc, k.rd, k.wr, k.sp, k.mem⟩
  refine WP.seq ?_
  apply WP.loop (fun (n : Nat) (t : State) => 0 < n ∧ n ≤ 3 ∧ Scr t base ∧
    t.gpr .x1 = BitVec.ofNat 64 n ∧ RepP (point (env t.mem base) 0 1 2 3) ((2 ^ (3 - n) : Nat) • a) ∧
    (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t) (n := 3)
  · intro n t ⟨hn0, hn3, ht, tc, tv, th, tk⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [WP.block_append_iff]
    refine WP.mono (dbl_ok ht false tv) fun u ⟨ku, uv, _, uh⟩ => ?_
    refine WP.mono (doubleDec_ok u k ((ku.gpr _ (by decide)).trans tc)) fun w ⟨wc, kw⟩ => ?_
    have wrep : RepP (point (env w.mem base) 0 1 2 3) ((2 ^ (3 - k) : Nat) • a) := by
      rw [kw.mem, show 3 - k = (3 - (k + 1)) + 1 by omega, pow_succ, mul_nsmul, two_nsmul]
      exact uv
    have wh : ∀ i : Slot, 16 ≤ i.val → env w.mem base i = env s.mem base i :=
      fun i h => by rw [kw.mem, uh i h, th i h]
    have wk : DoubleKeep base s w := tk.trans ((keepD ku).trans
      ⟨fun r hr _ => kw.gpr r (by simpa using hr), kw.rd, kw.wr, kw.sp,
        by rw [kw.mem]; exact Outside.refl _ _ _ _⟩)
    have hk : k < 16 := by omega
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, wc, point_counter_nonzero 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_⟩
      refine WP.mono (dbl_ok (wk.scratch hs) true wrep) fun v ⟨kv, _, vr, vh⟩ => ?_
      refine ⟨?_, fun i h => (vh i h).trans (wh i h), wk.trans (keepD kv)⟩
      rw [show (16 : Nat) = 2 ^ (3 - 0) * 2 by rfl, mul_nsmul, two_nsmul]
      exact vr rfl
    · exact Or.inr ⟨by simp only [eval, read_x, wc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, by omega, by omega, wk.scratch hs, wc, wrep, wh, wk⟩
  · refine ⟨by decide, by decide, hs₁, c1, ?_, fun i _ => by rw [k1.mem], k1d⟩
    rw [show (2 ^ (3 - 3) : Nat) = 1 from rfl, one_nsmul, k1.mem]; exact ha

/-! ## Digits -/

private theorem byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

private theorem high_nibble : ∀ b : BitVec 8,
    BitVec.ofNat 64 b.toNat >>> 4 = BitVec.ofNat 64 (b.toNat / 16) := by decide

private theorem low_nibble : ∀ b : BitVec 8,
    BitVec.ofNat 64 b.toNat <<< 60 >>> 60 = BitVec.ofNat 64 (b.toNat % 16) := by decide

theorem digitByte_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off (off P add) i)).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [digitByte, show ([ld .x2 ptr, ld .x8 56, .add .x .x8 .x2 .x8, .ldrb .x19 .x8 add] : List Instr) =
      [ld .x2 ptr] ++ ([ld .x8 56] ++ [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add]) from rfl,
    WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 ptr hpa hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok (hs.of_keeps ka (by decide)) .x8 56 (by decide) (by decide))
    fun b ⟨bp, kb⟩ => ?_
  have hm : b.mem = s.mem := kb.mem.trans ka.mem
  have hrd : b.rd ++ b.wr = s.rd ++ s.wr := by rw [kb.rd, kb.wr, ka.rd, ka.wr]
  have b2 : b.gpr .x2 = P := by rw [kb.gpr _ (by decide), ap, hp]
  have b8 : b.gpr .x8 = BitVec.ofNat 64 i := by rw [bp, ka.mem, hc]
  have hea : P + BitVec.ofNat 64 i + BitVec.ofNat 64 add = off (off P add) i := by
    simp only [off]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
  have hok : add % 1 = 0 ∧ add < 4096 * 1 := ⟨Nat.mod_one _, by omega⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    b2, b8, hea, hok, hrd, hm, hr, read_byte, byte_ext, and_self,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kb.wr, ka.wr], by simp only [RegUpd.sp_write, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2, ite_false]
  rw [kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.1])]

theorem shiftR4_ok (s : State) (v : Nat) (hc : s.gpr .x19 = BitVec.ofNat 64 v) :
    WP isa (.block [.lsr .x .x19 .x19 4]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 v >>> 4 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (4 : Nat) < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc], ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem shiftLR60_ok (s : State) (v : Nat) (hc : s.gpr .x19 = BitVec.ofNat 64 v) :
    WP isa (.block [.lsl .x .x19 .x19 60, .lsr .x .x19 .x19 60]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 v <<< 60 >>> 60 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (60 : Nat) < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, hc]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
  rw [RegUpd.gpr_write_of_ne _ _ _ h, RegUpd.gpr_write_of_ne _ _ _ h]

theorem digitHigh_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitHigh ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat / 16) ∧
      Keeps [.x2, .x8, .x19] s t := by
  rw [digitHigh, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hpa hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (shiftR4_ok a _ av) fun t ⟨tv, kt⟩ => ?_
  exact ⟨tv.trans (high_nibble _), ka.trans (kt.mono (by decide))⟩

theorem digitLow_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitLow ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat % 16) ∧
      Keeps [.x2, .x8, .x19] s t := by
  rw [digitLow, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hpa hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (shiftLR60_ok a _ av) fun t ⟨tv, kt⟩ => ?_
  exact ⟨tv.trans (low_nibble _), ka.trans (kt.mono (by decide))⟩

/-! ## Adding a table entry -/

/-- `p` agrees with `r`: entirely if `full`, and otherwise on `X : Y : Z`. -/
def Agrees : Bool → Spec.Ed25519.Point → Spec.Ed25519.Point → Prop
  | true, p, r => p = r
  | false, p, r => p.X = r.X ∧ p.Y = r.Y ∧ p.Z = r.Z

/-- `p` represents `a` (`Rep`) if `full`, and otherwise its `X : Y : Z` do (`RepP`). -/
def RepIf : Bool → Spec.Ed25519.Point → EPoint dZ → Prop
  | true, p, a => Rep p a
  | false, p, a => RepP p a

theorem RepIf.of_rep {full : Bool} {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    RepIf full p a := by
  cases full
  · exact h.proj
  · exact h

theorem RepIf.proj {full : Bool} {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : RepIf full p a) :
    RepP p a := by
  cases full
  · exact h
  · exact Rep.proj h

theorem RepIf.of_agrees {full : Bool} {p r : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep r a)
    (hp : Agrees full p r) : RepIf full p a := by
  cases full
  · obtain ⟨hx, hy, hz⟩ := hp
    exact ⟨by rw [hz]; exact h.z, by rw [hx, hz]; exact h.x, by rw [hy, hz]; exact h.y⟩
  · have e : p = r := hp
    subst e
    exact h

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`: all of the
sum if `full`, and otherwise its `X : Y : Z`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (full : Bool) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scr s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => Keep base s t ∧
      Agrees full (point (env t.mem base) 0 1 2 3)
        (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i

theorem pointAddCached_spec : AddSpec pointAddCached cache true := fun _ _ q hs _ hq =>
  pointAddCached_ok hs q hq

theorem cachedP_eval (e : Env) :
    evalOps pointAddCachedOps.dropLast e 0 = evalOps pointAddCachedOps e 0 ∧
    evalOps pointAddCachedOps.dropLast e 1 = evalOps pointAddCachedOps e 1 ∧
    evalOps pointAddCachedOps.dropLast e 2 = evalOps pointAddCachedOps e 2 := ⟨rfl, rfl, rfl⟩

theorem pointAddCachedP_spec : AddSpec pointAddCachedP cache false := fun s base q hs _ hq => by
  refine WP.mono (fieldCode_ok _ hs) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => by
    rw [vt]; exact point_ops_high _ (by decide) _ i hi⟩
  have e := pointAddCached_eval (env s.mem base) q hq
  obtain ⟨e0, e1, e2⟩ := cachedP_eval (env s.mem base)
  refine ⟨?_, ?_, ?_⟩
  · show env t.mem base 0 = _
    rw [vt, e0]; exact congrArg Spec.Ed25519.Point.X e
  · show env t.mem base 1 = _
    rw [vt, e1]; exact congrArg Spec.Ed25519.Point.Y e
  · show env t.mem base 2 = _
    rw [vt, e2]; exact congrArg Spec.Ed25519.Point.Z e

theorem tableEntryAdd_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    {full : Bool} (hadd : AddSpec add f full) {s : State} {base : Addr} (hs : Scr s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (tableAddr o ++ pointFromTableQ ++ add)) s fun t => Keep base s t ∧
      Agrees full (point (env t.mem base) 0 1 2 3)
        (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.x0 o j hj hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kae.scr hs) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have o := tableQ_other kb
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), ka.mem]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.mem, hq]
  have bd : env b.mem base 16 = env s.mem base 16 := by rw [o 16 (by decide), ka.mem]
  refine WP.mono (hadd b base q ((kae.trans kbe).scr hs) (bd.trans hd) bq) fun t ⟨kt, tp, th⟩ => ?_
  rw [bp] at tp
  exact ⟨(kae.trans kbe).trans kt, tp, by rw [th 16 (by decide), bd]⟩

/-- Entries `j < 15` of the table at byte `o` are `f` of representatives of `[j + 1]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ j < 15, ∃ q, tablePoint m base (o + 128 * j) = f q ∧ Rep q ((j + 1) • X)

theorem addDigit_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {full : Bool}
    (hadd : AddSpec add f full) {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 v)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t => RepIf full (point (env t.mem base) 0 1 2 3) (a + v • X) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (decide (v ≠ 0)) (by simp only [eval, read_x, hc, point_counter_nonzero v hv])
    (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := of_decide_eq_true h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
    refine WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    rw [← List.append_assoc]
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega) (by omega) bc q
      (by rw [kb.mem]; exact hq) (by rw [kb.mem]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨?_, by rw [td, kb.mem], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
    rw [kb.mem] at tp
    exact RepIf.of_agrees (pointAdd_rep ha hr) tp
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    exact WP.block_nil ⟨by rw [zero_smul, add_zero]; exact RepIf.of_rep ha, rfl, WinKeep.refl _ _⟩

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scr s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  aTab : TableOf cache s.mem base 5376 A
  bTab : TableOf cache s.mem base 2048 (-baseAff)

theorem win_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 56 712 m m') {d : Nat}
    (hd : 768 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

theorem TableOf.of_win {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 56 712 m m')
    (ho : 768 ≤ o) (hb : o + 1920 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [win_tablePoint k (by omega) (by omega)]; exact hq, hr⟩

theorem Outside.widen {base : Addr} {m m' : Mem} (h : Outside base 64 704 m m') :
    Outside base 56 712 m m' := h.mono (by decide) (by decide)

theorem WinKeep.header {base : Addr} {s t : State} (h : WinKeep base s t) {d : Nat} (hd : 768 ≤ d)
    (hb : d + 8 ≤ 8192) : t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (Or.inr (by omega)) (by omega)

theorem WinCtx.of_keep {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.header (by decide) (by decide)).trans h.kHeader,
    (k.header (by decide) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide),
    h.bTab.of_win (Outside.widen k.mem) (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem WinCtx.byteK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 64) : t.mem (off kp i) = s.mem (off kp i) :=
  k.mem _ (by have := h.kFar i hi; omega)

theorem WinCtx.byteS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 32) :
    t.mem (off (off sp 32) i) = s.mem (off (off sp 32) i) :=
  k.mem _ (by have := h.sFar i hi; omega)

theorem off_zero (p : Addr) : off p 0 = p := by
  simp only [off, BitVec.add_zero]

/-- A digit's code, with its value `v`, from any state the window has reached. -/
def DigitSpec (base : Addr) (s : State) (digit : List Instr) (v : Nat) : Prop :=
  ∀ t, WinKeep base s t → WP isa (.block digit) t fun u =>
    u.gpr .x19 = BitVec.ofNat 64 v ∧ Keeps [.x2, .x8, .x19] t u

theorem DigitSpec.of_keep {base : Addr} {s t : State} {digit : List Instr} {v : Nat}
    (h : DigitSpec base s digit v) (k : WinKeep base s t) : DigitSpec base t digit v :=
  fun u ku => h u (k.trans ku)

theorem windowWith_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digit add : List Instr} {full : Bool} (hadd : AddSpec add cache full) {v : Nat} (hv : v < 16)
    (hdig : DigitSpec base s digit v) :
    WP isa (windowWith digit add) s fun t =>
      RepIf full (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowWith]
  refine WP.seq (WP.mono (doubleWindow_ok h.scratch ha) fun b ⟨br, bh, bk⟩ => ?_)
  have kb := WinKeep.of_double bk
  refine WP.seq (WP.mono (hdig b kb) fun c ⟨cv, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a) hadd (kbc.scratch h.scratch) (by decide)
    (by decide) (h.aTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) v hv cv
    (by rw [kc.mem, bh 16 (by decide)]; exact hd) (by rw [kc.mem]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.mem, bh 16 (by decide)]; exact hd, kbc.trans kt⟩

theorem windowA_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digit : List Instr} {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (windowA digit) s fun t => RepP (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t :=
  windowWith_ok h hd ha pointAddCachedP_spec hv hdig

theorem windowAB_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digitA digitB : List Instr} {vA vB : Nat} (hvA : vA < 16) (hvB : vB < 16)
    (hdA : DigitSpec base s digitA vA) (hdB : DigitSpec base s digitB vB) :
    WP isa (windowAB digitA digitB) s fun t =>
      RepP (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + vA • A + vB • (-baseAff)) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowAB]
  refine WP.seq (WP.mono (windowWith_ok h hd ha pointAddCached_spec hvA hdA) fun b ⟨br, bd, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdB b kb) fun c ⟨cv, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a + vA • A) pointAddCachedP_spec
    (kbc.scratch h.scratch) (by decide) (by decide)
    (h.bTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) vB hvB cv
    (by rw [kc.mem]; exact bd) (by rw [kc.mem]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.mem]; exact bd, kbc.trans kt⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.WindowByte`. -/
section
/-!
# Verification's bytes: two windows per byte of the scalars

Byte `i` of `k` (and of `S`) gives two digits, high nibble first; after it,
the accumulator represents `[k / 256^i]A - [S / 256^i]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a byte of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 56 712 s.mem t.mem

theorem ByteKeep.refl (base : Addr) (s : State) : ByteKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.of_counter {base : Addr} {s t : State}
    (ag : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r) (ar : t.rd = s.rd) (aw : t.wr = s.wr) (asp : t.sp = s.sp)
    (am : Outside base 56 8 s.mem t.mem) : ByteKeep base s t :=
  ⟨fun r _ hb _ => ag r hb, ar, aw, asp, am.mono (by decide) (by decide)⟩

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.mem.word (Or.inr (by decide)) (by decide)).trans h.kHeader,
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win k.mem (by decide) (by decide), h.bTab.of_win k.mem (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem ByteKeep.bytesK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

/-! ## Digits from the inputs -/

theorem digitKHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7952 0) ((s.mem (off kp i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7952 0 (by decide) (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitKLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7952 0) ((s.mem (off kp i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7952 0 (by decide) (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitSHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7944 32) ((s.mem (off (off sp 32) i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7944 32 (by decide) (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [h.byteS kt hi] at uv
  exact ⟨uv, ku⟩

theorem digitSLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7944 32) ((s.mem (off (off sp 32) i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7944 32 (by decide) (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, ku⟩ => ?_
  rw [h.byteS kt hi] at uv
  exact ⟨uv, ku⟩

/-! ## A byte -/

private theorem above_cmp : ∀ i < 65,
    (BitVec.ofNat 64 i - BitVec.ofNat 64 32 != 0) = decide (i ≠ 32) := by decide

theorem aboveLow_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i ≤ 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block aboveLow) s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 32)) ∧
      Keeps [.x19] s t := by
  rw [aboveLow, show ([ld .x19 56, .subImm .x .x19 .x19 32] : List Instr) =
    [ld .x19 56] ++ [.subImm .x .x19 .x19 32] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (32 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write, ka.mem],
    by simp only [RegUpd.rd_write, ka.rd], by simp only [RegUpd.wr_write, ka.wr],
    by simp only [RegUpd.sp_write, ka.sp]⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, av, hc, above_cmp i (by omega)]
  · have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
    rw [RegUpd.gpr_write_of_ne _ _ _ h, ka.gpr r hr]

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

theorem byteStepA_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa byteStepA s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) hi, ka.bytesK h]
  refine WP.seq (WP.mono (windowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha)
    (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (digitKHigh ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowA_ok hb' bd br (Nat.mod_lt _ (by decide))
    (digitKLow hb' hi (kb.counter.trans av))) fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (aboveLow_ok hc'.scratch i (by omega) (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb hi] at cr
    rw [kt.mem]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem byteStepAB_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa byteStepAB s fun t => t.gpr .x19 = BitVec.ofNat 64 i ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  set S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) with hSdef
  have hbK : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) (by omega), ka.bytesK h]
  have hbS : (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256 := by
    rw [scalar_byte (n := 32) hi, ka.bytesS h]
  have lt16 (b : Byte) : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by have := b.isLt; omega)
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (lt16 _) (lt16 _)
    (digitKHigh ha' (by omega) av) (digitSHigh ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowAB_ok hb' bd br (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (digitKLow hb' (by omega) (kb.counter.trans av)) (digitSLow hb' hi (kb.counter.trans av)))
    fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (batchTest_ok hc'.scratch i (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb (by omega), ha'.byteS kb hi] at cr
    rw [kt.mem, ← window_step A (-baseAff) K S i _ _ hbK hbS]
    exact cr

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's loops over the bytes of the scalars

The leading zero bytes of `k` above its low 32 are skipped, as the sum before
them is zero; bytes 63 down to 32 hold digits of `k` alone, bytes 31 down to 0
of both scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- The loops' invariant, with `c` bytes left. -/
structure WinLoop (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : RepP (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

theorem WinLoop.of_keeps {s₀ s t : State} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    {rs : List Reg} (h : WinLoop s₀ base kp sp A K S c s) (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinLoop s₀ base kp sp A K S c t := by
  have kb : ByteKeep base s t := ByteKeep.of_keeps k hrs
  exact ⟨h.ctx.of_byte kb, by rw [k.mem]; exact h.d, by rw [k.mem]; exact h.counter,
    by rw [k.mem]; exact h.kVal, by rw [k.mem]; exact h.sVal, by rw [k.mem]; exact h.value,
    h.keep.trans kb⟩

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem stepA_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (32 + (j + 1)) t) :
    WP isa byteStepA t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base kp sp A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (byteStepA_ok (i := 32 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal] at uv; exact uv, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem stepB_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (j + 1) t) :
    WP isa byteStepAB t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base kp sp A K S j u := by
  refine WP.mono (byteStepAB_ok (i := j) ht.ctx ht.d hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by simp only [eval, read_x, uz, counter_nonzero (by omega : j < 2 ^ 64)], ht.ctx.of_byte uk, ud, uc,
    by rw [uk.bytesK ht.ctx, ht.kVal], by rw [uk.bytesS ht.ctx, ht.sVal],
    by rw [ht.kVal, ht.sVal] at uv; exact uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) (h : WinLoop s₀ base kp sp A K S (32 + n) s) :
    WP isa (.loop byteStepA (.nonzero .x .x19)) s (WinLoop s₀ base kp sp A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, hn0, hn⟩

theorem windowsA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) (h : WinLoop s₀ base kp sp A K S c s) :
    WP isa windowsA s (WinLoop s₀ base kp sp A K S 32) := by
  rw [windowsA]
  refine WP.seq (WP.mono (aboveLow_ok h.ctx.scratch c (by omega) h.counter) fun a ⟨az, ka⟩ => ?_)
  have ha := h.of_keeps ka (by decide)
  refine WP.ite (decide (c ≠ 32)) az (fun hy => ?_) (fun hn => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    exact loopA_ok n (by have := of_decide_eq_true hy; omega) (by omega) ha
  · have : c = 32 := by simpa using hn
    subst this
    exact WP.block_nil ha

theorem loopB_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 32 s) :
    WP isa (.loop byteStepAB (.nonzero .x .x19)) s (WinLoop s₀ base kp sp A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem subOne_ok (s : State) (r : Reg) (n : Nat) (hc : s.gpr r = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x r r 1]) s fun t => t.gpr r = BitVec.ofNat 64 n ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem window_loop_byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

theorem skipLoad_ok {s : State} {base kp : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = kp) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1))
    (hr : InRegions (s.rd ++ s.wr) (off kp j) 1) :
    WP isa (.block skipLoad) s fun t => t.gpr .x8 = BitVec.ofNat 64 j ∧
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off kp j)).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [skipLoad, show ([ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952, .add .x .x2 .x2 .x8,
      .ldrb .x19 .x2 0] : List Instr) = [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++
      ([ld .x2 7952] ++ [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .x2 7952
    (by decide) (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hm : c.mem = s.mem := kc.mem.trans (kb.mem.trans ka.mem)
  have hrd : c.rd ++ c.wr = s.rd ++ s.wr := by rw [kc.rd, kc.wr, kb.rd, kb.wr, ka.rd, ka.wr]
  have c2 : c.gpr .x2 = kp := by rw [cp, kb.mem, ka.mem, hp]
  have c8 : c.gpr .x8 = BitVec.ofNat 64 j := by rw [kc.gpr _ (by decide), bv]
  have hea : kp + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off kp j := BitVec.add_zero _
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    c2, c8, hea, hrd, hm, hr, read_byte, window_loop_byte_ext,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kc.rd, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kc.wr, kb.wr, ka.wr],
    by simp only [RegUpd.sp_write, kc.sp, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
  rw [kc.gpr r (by simp [hr.1]), kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.2.1])]

theorem skipStore_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (32 + n)) :
    WP isa (.block [st .x8 56, .subImm .x .x19 .x8 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (32 + n) ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have he : BitVec.ofNat 64 (32 + n) - BitVec.ofNat 64 32 = BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc hs (by decide) (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (32 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, h8, he]
  refine ⟨trivial, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, ?_⟩
  · rw [RegUpd.mem_write, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write]; exact writeW_outside _ _ _ (by decide)

private theorem byte_nonzero : ∀ b : BitVec 8,
    (BitVec.ofNat 64 b.toNat != 0) = decide (b.toNat ≠ 0) := by decide

theorem movzZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => eval (.nonzero .x .x19) t = some false ∧
      Keeps [.x19] s t :=
  WP.mono (movzW_ok s .x19 0) fun t ⟨tv, kt⟩ => ⟨by simp only [eval, read_x, tv]; rfl, kt⟩

/-- Skipping: `c = 32 + n` bytes are left, and the bytes of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  WinLoop s₀ base kp sp A K S (32 + n) s ∧ K / 256 ^ (32 + n) = 0 ∧ 0 < n ∧ n ≤ 32

/-- Whether the skipping goes on below `32 + j + 1` bytes left: byte `32 + j` of `k` is zero,
and more than 32 bytes are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 256 ^ (32 + j) % 256 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `32 + j + 1` bytes left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 256 ^ (32 + j) % 256 = 0 then 32 else 32 + (j + 1)

theorem skipBody_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base kp sp A K S (j + 1) t) :
    WP isa skipBody t fun u => eval (.nonzero .x .x19) u = some (skipOn K j) ∧
      (skipOn K j = false → WinLoop s₀ base kp sp A K S (skipEnd K j) u) ∧
      (skipOn K j = true → SkipInv s₀ base kp sp A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  have hS : S < 256 ^ 32 := hl.sVal ▸ decodeLE_lt32 _ _
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx.scratch hl.ctx.kHeader (32 + j)
    (by rw [hl.counter]; rfl) (hl.ctx.kRead _ (by omega))) fun a ⟨a8, av, ka⟩ => ?_)
  have ha := hl.of_keeps ka (by decide)
  have hb : (t.mem (off kp (32 + j))).toNat = K / 256 ^ (32 + j) % 256 := by
    rw [scalar_byte (n := 64) (by omega), hl.kVal]
  refine WP.ite (decide ((t.mem (off kp (32 + j))).toNat ≠ 0))
    (by simp only [eval, read_x, av, byte_nonzero]) (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 256 ^ (32 + j) % 256 ≠ 0 := by rw [← hb]; simpa using hy
    have hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (movzZero_ok a) fun u ⟨uz, ku⟩ => ⟨by rw [uz, hoff], fun _ => ?_,
      fun ht => absurd ht (by rw [hoff]; decide)⟩
    have e : skipEnd K j = 32 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ha.of_keeps ku (by decide)
  · have h0 : K / 256 ^ (32 + j) % 256 = 0 := by rw [← hb]; simpa using hy
    refine WP.mono (skipStore_ok ha.ctx.scratch j a8) fun u ⟨uv, uc, ug, ur, uw, usp, um⟩ => ?_
    have ku : ByteKeep base a u := ByteKeep.of_counter ug ur uw usp um
    have hK : K / 256 ^ (32 + j) = 0 := by
      have := div_split K (32 + j)
      rw [show 32 + j + 1 = 32 + (j + 1) by omega, hz] at this
      omega
    have hw : WinLoop s₀ base kp sp A K S (32 + j) u := by
      refine ⟨ha.ctx.of_byte ku, by rw [header_env um]; exact ha.d, uc,
        by rw [ku.bytesK ha.ctx, ha.kVal], by rw [ku.bytesS ha.ctx, ha.sVal], ?_, ha.keep.trans ku⟩
      have v := ha.value
      rw [hz, high_zero hS (by omega)] at v
      rw [header_env um, hK, high_zero hS (by omega)]
      exact v
    have he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    have hj32 : j < 32 := by omega
    refine ⟨by simp only [eval, read_x, uv]; rw [counter_nonzero (by omega : j < 2 ^ 64), he], fun hf => ?_,
      fun ht => ⟨hw, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega, by omega⟩⟩
    have hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    have e : skipEnd K 0 = 32 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact hw

theorem skipEnd_range (K j : Nat) (hj : j < 32) : 32 ≤ skipEnd K j ∧ skipEnd K j ≤ 64 := by
  unfold skipEnd; split <;> omega

theorem skipZero_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 64 s) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ WinLoop s₀ base kp sp A K S c t := by
  have hK : K / 256 ^ 64 = 0 := Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base kp sp A K S) (n := 32)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega : n ≠ 0)
    have hj : j < 32 := by have := ht.2.2.2; omega
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨uz.trans (by rw [hs]), skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2,
        uf hs⟩
    · exact Or.inr ⟨uz.trans (by rw [hs]), j, by omega, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.WindowTables`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyTables`. -/
section
/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => t.gpr .x19 = 0 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, kt.sp, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · rw [table_env kt.mem hlo, kb.mem, ka.mem]

theorem pointTableRead_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [pointTableRead, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbr : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok ((kar.trans kbr).scr hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  refine ⟨(kar.trans kbr).trans (CounterKeep.of_keep (Keep.of_table kt)), ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · intro i hi
    rw [tableLoad_high kt i hi, kb.mem, ka.mem]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.BaseBatchTable`. -/
section
/-!
# Writing a batch's cached powers into the local table

Each constant field is four immediate words stored at a constant offset of
`x0`; the batch is chosen by subtracting each index from the public counter
`x19` and testing the difference for zero.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : Scr s base) (v : Spec.X25519.Fe)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base dst = v ∧ TableKeep base dst 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) ⟨ha, ho⟩) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · rw [F, fe_st4 _ _ (by omega), hv, toFe_self]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : Scr s base) (q : Spec.Ed25519.Point)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      tablePoint t.mem base dst = q ∧ TableKeep base dst 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok hs q.X ha (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (ka.scratch hs) q.Y (dst := dst + 32) (by omega) (by omega))
    fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (kb.scratch (ka.scratch hs)) q.Z (dst := dst + 64)
    (by omega) (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs))) q.T
    (dst := dst + 96) (by omega) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base dst = q.X := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)),
      Outside_F kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (dst + 32) = q.Y := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (dst + 64) = q.Z := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)), cz]
  simp only [tablePoint, ex, ey, ez, tt]

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

The table of multiples of `A` is built by repeated addition of `A`, which
stays in slots 4–7, each entry representing its multiple (`Rep`); the table of
negated multiples of `B` is stored from constants.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open VG.Impl.Ed25519 (negBaseCached)
open Fin.CommRing

/-! ## Cached `-[i]B` -/

theorem bTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat) (hn : n ≤ 15) :
    WP isa (.block ((List.range n).flatMap fun i => cachedPointStore (negBaseCached i) (2048 + 128 * i))) s
      fun t => (∀ i < n, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
        TableKeep base 2048 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) (negBaseCached n) (dst := 2048 + 128 * n)
      (by omega) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

theorem bTable_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block bTable) s fun t => (∀ i < 15, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
      TableKeep base 2048 1920 s t :=
  bTablePrefix_ok hs 15 (by decide)

/-! ## `[i]A` -/

private theorem aNext_cmp : ∀ n < 15,
    (BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 15 != 0) = decide (n + 1 ≠ 15) := by decide

theorem aNext_ok (s : State) (n : Nat) (hn : n < 15) (hc : s.gpr .x19 = BitVec.ofNat 64 n) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (n + 1) ∧ eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      Keeps [.x19, .x8] s t := by
  have ha : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) := by
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (1 : Nat) < 4096 from by decide, show (15 : Nat) < 4096 from by decide, ite_true,
    RegUpd.gpr_write, hc, ha, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, ite_false, reduceCtorEq,
      aNext_cmp n hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 = cache (point e 0 1 2 3) := by
  have h : point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 =
      ⟨e 1 - e 0, e 1 + e 0, (e 3 + e 3) * e 16, e 2 + e 2⟩ := rfl
  rw [h, hd]
  simp only [cache, point]
  congr 1 <;> ring

theorem saveCache_eval (e : Env) :
    point (evalOps (savePointOps ++ cacheOps) e) 4 5 6 7 = point e 4 5 6 7 ∧
    point (evalOps (savePointOps ++ cacheOps) e) 17 18 19 20 = point e 0 1 2 3 ∧
    evalOps (savePointOps ++ cacheOps) e 16 = e 16 := ⟨rfl, rfl, rfl⟩

theorem restore_eval (e : Env) :
    point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 ∧
    evalOps restorePointOps e 16 = e 16 := ⟨rfl, rfl⟩

theorem pointAddCached_q (e : Env) :
    point (evalOps pointAddCachedOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem PowersKeep.of_tableKeep {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t) :
    PowersKeep base o n s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp, TableFrame.table h.mem⟩

theorem storeCached_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 15)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block storeCached) s fun t =>
      tablePoint t.mem base (5376 + 128 * j) = cache (point (env s.mem base) 0 1 2 3) ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 ∧
      env t.mem base 16 = env s.mem base 16 ∧ t.gpr .x19 = s.gpr .x19 ∧
      PowersKeep base (5376 + 128 * j) 128 s t := by
  rw [storeCached, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (savePointOps ++ cacheOps) hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.scr hs).x0 5376 j (by omega) ((ka.gpr _ (by decide)).trans hc))
    fun b ⟨bp, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok ((ka.trans kbe).scr hs) bp (by omega) (by omega)) fun c ⟨cp, kc⟩ => ?_
  have ce : env c.mem base = env a.mem base := by rw [table_env kc.mem (by omega), kb.mem]
  refine WP.mono (fieldCode_ok restorePointOps (kc.scratch ((ka.trans kbe).scr hs)))
    fun t ⟨kt, vt⟩ => ?_
  obtain ⟨s4, s17, s16⟩ := saveCache_eval (env s.mem base)
  obtain ⟨r4, r16⟩ := restore_eval (env c.mem base)
  refine ⟨?_, ?_, ?_, ?_, by rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kbe.gpr _ (by decide),
    ka.gpr _ (by decide)], ((PowersKeep.of_keep (ka.trans kbe)).trans
    (PowersKeep.of_tableKeep kc)).trans (PowersKeep.of_keep kt)⟩
  · rw [workspace_tablePoint kt.mem (by omega) (by omega), cp, kb.mem, va, cacheOps_eval _ hd]
  · rw [vt, restorePoint_eval, ce, va, s17]
  · rw [vt, r4, ce, va, s4]
  · rw [vt, r16, ce, va, s16]

/-- The table of `A`'s multiples, cached, with `n` entries, `[n]A` in slots 0–3 and `A`
cached in slots 4–7. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) (n • A)
  q : ∃ qa, point (env s.mem base) 4 5 6 7 = cache qa ∧ Rep qa A
  table : ∀ j < n, ∃ q, tablePoint s.mem base (5376 + 128 * j) = cache q ∧ Rep q ((j + 1) • A)
  keep : PowersKeep base 5376 1920 s₀ s

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 15)
    (h : ATableInv s₀ base A n s) :
    WP isa (.block aTableBody) s fun t => eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      ATableInv s₀ base A (n + 1) t := by
  obtain ⟨qa, hq, hA⟩ := h.q
  rw [aTableBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointAddCachedOps h.scratch) fun c ⟨kc, vc⟩ => ?_
  have crep : Rep (point (env c.mem base) 0 1 2 3) ((n + 1) • A) := by
    rw [vc, pointAddCached_eval _ qa hq, succ_nsmul]
    exact pointAdd_rep h.value hA
  have cq : point (env c.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 := by
    rw [vc, pointAddCached_q]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by
    rw [vc, pointAddCached_high _ 16 (by decide)]; exact h.d
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kc.scr h.scratch) n hn ((kc.gpr _ (by decide)).trans h.counter) cd)
    fun d ⟨dt, d0, d4, d16, d19, kd⟩ => ?_
  refine WP.mono (aNext_ok d n hn (d19.trans
    ((kc.gpr _ (by decide)).trans h.counter))) fun t ⟨tc, tz, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((PowersKeep.of_keep kc).trans (kd.mono (by omega) (by omega))).trans
      (PowersKeep.of_keeps kt (by decide))
  refine ⟨tz, by omega, by omega, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [kt.mem, d16]; exact cd
  · rw [kt.mem, d0]; exact crep
  · exact ⟨qa, by rw [kt.mem, d4, cq]; exact hq, hA⟩
  · intro j hj
    rw [kt.mem]
    by_cases hjn : j < n
    · rw [kd.mem.point (by omega) (Or.inl (by omega)) (by omega),
        workspace_tablePoint kc.mem (by omega) (by omega)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      exact ⟨_, dt, crep⟩

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (.block aTableInit) s (ATableInv s base A 1) := by
  rw [aTableInit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hs 7424 (by decide) (by decide)) fun a ⟨ka, ap, ah⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok a) fun b ⟨bz, kb⟩ => ?_
  have kab := (PowersKeep.of_counter ka : PowersKeep base 5376 1920 s a).trans
    (PowersKeep.of_keeps kb (by decide))
  have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [kb.mem, ah 16 (by decide)]; exact hd
  have bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [kb.mem, ap]; exact hA
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kab.scratch hs) 0 (by decide) bz bd) fun c ⟨ct, c0, _, c16, c19, kc⟩ => ?_
  have kac := kab.trans (kc.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kac.scratch hs).x0 5376 0 (by decide)
    (c19.trans bz)) fun d ⟨dp, kd⟩ => ?_
  have kde : Keep base c d := Keep.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kde.scr (kac.scratch hs)) dp (by decide) (by decide))
    fun e ⟨ep, ke⟩ => ?_
  have kee := Keep.of_tableQ ke
  have o := tableQ_other ke
  refine WP.mono (movzW_ok e .x19 1) fun t ⟨tc, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((kac.trans (PowersKeep.of_keep (kde.trans kee))).trans (PowersKeep.of_keeps kt (by decide)))
  have e0 : point (env e.mem base) 0 1 2 3 = point (env c.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kd.mem]
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, kall⟩
  · rw [kt.mem, o 16 (by decide), kd.mem, c16]; exact bd
  · rw [kt.mem, e0, c0, one_nsmul]; exact bA
  · refine ⟨point (env b.mem base) 0 1 2 3, ?_, bA⟩
    rw [kt.mem, ep, kd.mem]
    simpa using ct
  · intro j hj
    obtain rfl : j = 0 := by omega
    refine ⟨point (env b.mem base) 0 1 2 3, ?_, by rw [zero_add, one_nsmul]; exact bA⟩
    rw [kt.mem, workspace_tablePoint kee.mem (by decide) (by decide), workspace_tablePoint kde.mem
      (by decide) (by decide)]
    simpa using ct

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa aTable s (ATableInv s base A 15) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (15 - n) t ∧ 0 < n) (n := 14)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 15 - n) (by omega) h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨uz.trans (by rw [he]; rfl), by rw [← he]; exact hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true he]), n - 1, by omega,
        by rw [show 15 - (n - 1) = 15 - n + 1 by omega]; exact hu, by have := hu.bound; omega⟩
  · exact ⟨ha, by decide⟩

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.PointMul`. -/
section
/-! Checkpoint generation before the batch descent. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scr s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  rw [mulCounterInit, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 (BitVec.ofNat 64 count)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc (hs.of_keeps ka (by decide)) (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ka.gpr r (by simpa only [List.mem_singleton] using hr), ka.rd, ka.wr, ka.sp, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact av
  · rw [ka.mem]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's equation, from the windows

The windows leave a representative of `[k]A - [S]B`, compared with `-R`: they
are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent
points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block negR) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 7552 0 (by decide) az) fun b ⟨pb, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at pb
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kbe.scr (kar.scr hs)) pb (by decide) (by decide))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_tableQ kc
  have o := tableQ_other kc
  have c0 : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kb.mem,
      ka.mem]
  refine WP.mono (fieldCode_ok _ (kce.scr (kbe.scr (kar.scr hs)))) fun t ⟨kt, vt⟩ => ?_
  refine ⟨kar.trans (CounterKeep.of_keep ((kbe.trans kce).trans kt)), ?_, ?_⟩
  · rw [vt, (negR_eval _).1, c0]
  · rw [vt, (negR_eval _).2, pc, kb.mem, ka.mem]

/-- Verification's code before the windows, regrouped. -/
def windowPrep : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) aTable) (.block bTable)) (.block windowInit)

theorem PowersKeep.of_table {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t)
    (ho : 56 ≤ o) (hn : o + n ≤ 7808) : PowersKeep base 56 7752 s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by omega) (by omega))⟩

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa windowPrep s fun e => WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constField_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  have aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  have ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  have bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch) fun c ⟨ct, kc⟩ => ?_
  have ksc := ksb.trans (PowersKeep.of_table kc (by decide) (by decide))
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table kc.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env kc.mem (by decide)]; exact hb.d
  have cA : TableOf cache c.mem base 5376 Aa := fun j hj => by
    obtain ⟨q, hq, hr⟩ := hb.table j hj
    exact ⟨q, by rw [(TableFrame.table kc.mem).point (by omega) (Or.inr (by omega)) (by omega)]; exact hq,
      hr⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [ct j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (ksc.scratch hs))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64)
    fun e ⟨ec, eg, er, ew, esp, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, esp, em.mono (by decide) (by decide)⟩
  have kce : ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksc.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), cR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact cd
  have ctx : WinCtx base challenge sig Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide)⟩
  have hK := decodeLE_lt64 e.mem challenge
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ByteKeep.refl _ _⟩, kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep.proj

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa verifyEquationPoints s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf'⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok hc32 hc64 hf') fun g hg => ?_)
  refine WP.seq (WP.mono (loopB_ok hg) fun h hh => ?_)
  have ksh := kse.trans (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksh.trans (PowersKeep.of_counter ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hv := hh.value
  simp only [pow_zero, Nat.div_one] at hv
  rw [tv, u0, u4, win_tablePoint hh.keep.mem (by decide) (by decide), eR,
    window_equation hA hR hv hR.neg.proj]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointDecode`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.CanonicalY`. -/
section
/-! Canonical decoding checks y before reduction modulo p. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = n) :
    WP isa (.block canonicalY) s fun t => (t.gpr .x8 == 0) = decide (n < Spec.X25519.P) ∧
      Keeps [.x10, .x11, .x21, .x22, .x23, .x24, .x8] s t := by
  have H := (add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (by rw [hv]; omega)).1
  have hz (w : Word) (hw : 0 - w = mask (decide (Spec.X25519.P ≤ n))) :
      (w == 0) = decide (n < Spec.X25519.P) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    have he : w = 0 ↔ mask (decide (Spec.X25519.P ≤ n)) = 0 := by
      rw [← hw]
      change w = 0#64 ↔ 0#64 - w = 0#64
      rw [BitVec.zero_sub, BitVec.neg_eq_zero_iff]
    rw [he]
    by_cases h : Spec.X25519.P ≤ n
    · simp only [decide_eq_true h, mask, ite_true]
      exact iff_of_false (by decide) (by omega)
    · simp only [decide_eq_false h, mask, Bool.false_eq_true, ite_false]
      exact iff_of_true True.intro (by omega)
  rw [hv] at H
  have H' := hz _ H
  apply WP.of_runBlock
  simp only [canonicalY, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, show 63 < Size.x.bits from by decide,
    show 16 * 0 < Size.w.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H' ⊢
    exact H'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : VG.Proof.Ed25519.AArch64.DecodeKeep base s t) (k : VG.Proof.Ed25519.AArch64.DecodeKeep base t u) : VG.Proof.Ed25519.AArch64.DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : VG.Proof.Ed25519.AArch64.DecodeKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_counter {base : Addr} {s t : State} (h : CounterKeep base s t) : VG.Proof.Ed25519.AArch64.DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.sp, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .x19 ∨ r = .x1) : VG.Proof.Ed25519.AArch64.DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => VG.Proof.Ed25519.AArch64.DecodeKeep base s t ∧
      t.gpr .x1 = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      VG.Proof.Ed25519.AArch64.env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      (t.gpr .x8 == 0) = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P) := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : VG.Proof.Ed25519.AArch64.DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.gpr _ (by decide)).trans hp)
    (by intro d hd; rw [ka.rd, ka.wr]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.mem] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok (kab.scratch hs) (slot_range 1)) fun c hc => ?_
  subst c
  have cmem := st4_outside b.mem base (show offset 1 + 32 < 2 ^ 64 by decide)
    (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)
  have kc : VG.Proof.Ed25519.AArch64.DecodeKeep base b { b with
                                       mem := (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) } :=
    ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, cmem.mono (by decide) (by decide)⟩
  have cy : VG.Proof.Ed25519.AArch64.env (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) base 1 =
      Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change Proof.X25519.toFe (fe _ base (offset 1)) = _
    rw [fe_st4 _ _ (by decide), byval]
  refine WP.mono (VG.Proof.Ed25519.AArch64.canonicalY_ok _ _ (Nat.mod_lt _ (by decide)) byval) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz⟩
  · rw [kt.gpr .x1 (by decide), kb.gpr .x1 (by decide)]; exact asign
  · rw [kt.mem]; exact cy

end VG.Proof.Ed25519.AArch64
end

/-! Canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa pointDecode s fun t => VG.Proof.Ed25519.AArch64.DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [eval, read_x, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter (CounterKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.WindowCT`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PointEqualCT`. -/
section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def EqualCTPre (base : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Scr s base ∧ point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = p ∧ point (VG.Proof.Ed25519.AArch64.env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      Keep base s t ∧
      eval (.zero .x .x8) t = some (decide (VG.Proof.Ed25519.AArch64.env s.mem base 0 * VG.Proof.Ed25519.AArch64.env s.mem base 6 = VG.Proof.Ed25519.AArch64.env s.mem base 4 * VG.Proof.Ed25519.AArch64.env s.mem base 2)) ∧
      VG.Proof.Ed25519.AArch64.env t.mem base 10 = VG.Proof.Ed25519.AArch64.env s.mem base 1 * VG.Proof.Ed25519.AArch64.env s.mem base 6 ∧
      VG.Proof.Ed25519.AArch64.env t.mem base 11 = VG.Proof.Ed25519.AArch64.env s.mem base 5 * VG.Proof.Ed25519.AArch64.env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · change some (t.gpr .x8 == 0) = _
    rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    CT (fun _ _ => True) (.block [.movz .w .x8 (if b then 1 else 0) 0]) (fun _ _ => True) := by
  cases b
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)

theorem equalSecond_ct (base : Addr) (u v : Spec.X25519.Fe) :
    CT (fun s t => (Scr s base ∧ VG.Proof.Ed25519.AArch64.env s.mem base 10 = u ∧ VG.Proof.Ed25519.AArch64.env s.mem base 11 = v) ∧
      (Scr t base ∧ VG.Proof.Ed25519.AArch64.env t.mem base 10 = u ∧ VG.Proof.Ed25519.AArch64.env t.mem base 11 = v))
      (.seq (.block (fieldEqual 10 11)) (.ite (.zero .x .x8) (.block [.movz .w .x8 1 0]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : CT (fun s t => (Scr s base ∧ VG.Proof.Ed25519.AArch64.env s.mem base 10 = u ∧ VG.Proof.Ed25519.AArch64.env s.mem base 11 = v) ∧
      (Scr t base ∧ VG.Proof.Ed25519.AArch64.env t.mem base 10 = u ∧ VG.Proof.Ed25519.AArch64.env t.mem base 11 = v))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : Scr s base ∧ VG.Proof.Ed25519.AArch64.env s.mem base 10 = u ∧ VG.Proof.Ed25519.AArch64.env s.mem base 11 = v) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun t k => ?_
    change some (t.gpr .x8 == 0) = _
    rw [k.1, h.2.1, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : Addr) (p q : Spec.Ed25519.Point) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.EqualCTPre base p q s ∧ VG.Proof.Ed25519.AArch64.EqualCTPre base p q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.EqualCTPre base p q s ∧ VG.Proof.Ed25519.AArch64.EqualCTPre base p q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.EqualCTPre base p q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          VG.Proof.Ed25519.AArch64.env t.mem base 10 = p.Y * q.Z ∧ VG.Proof.Ed25519.AArch64.env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (VG.Proof.Ed25519.AArch64.equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (VG.Proof.Ed25519.AArch64.equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The digits are
read through pointers and a counter in the scratch, the same in both runs by
correctness; everything else is public by the taint analysis. The skipped
bytes of `k` are its leading zeros, the same in both runs. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : CT (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  CT.seq ((CT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_x0 {x y : State} (h : x.gpr .x0 = y.gpr .x0) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [.x0], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-- Code the taint analysis proves constant time with `x0` alone public. -/
theorem x0_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .x0 = base)
    (h : CT (fun x y => x.gpr .x0 = y.gpr .x0) c (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree2 {x y : State} {a b : Reg} (h : x.gpr a = y.gpr a ∧ x.gpr b = y.gpr b) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [a, b], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

/-! ## Digits -/

/-- The digit's pointer and counter. -/
def digitPrefix (ptr : Nat) : List Instr := [ld .x2 ptr, ld .x8 56]

theorem digitPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ptr : Nat}
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) {P C : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P) (hc : s.mem.readW (off base 56) 64 = C) :
    WP isa (.block (VG.Proof.Ed25519.AArch64.digitPrefix ptr)) s fun t => t.gpr .x2 = P ∧ t.gpr .x8 = C := by
  rw [VG.Proof.Ed25519.AArch64.digitPrefix, show ([ld .x2 ptr, ld .x8 56] : List Instr) = [ld .x2 ptr] ++ [ld .x8 56] from rfl,
    WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 ptr hpa hptr) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (loadPointer_ok (hs.of_keeps ka (by decide)) .x8 56 (by decide) (by decide))
    fun t ⟨tp, kt⟩ => ?_
  exact ⟨by rw [kt.gpr _ (by decide), ap, hp], by rw [tp, ka.mem, hc]⟩

/-- A digit's code: its address by correctness, the rest by the taint analysis. -/
theorem digit_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {ptr : Nat} {P : Addr}
    {rest : List Instr} (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192)
    (hP : ∀ x, WinCtx base kp sp A x → x.mem.readW (off base ptr) 64 = P)
    (hpre : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block (VG.Proof.Ed25519.AArch64.digitPrefix ptr)) (fun _ _ => True))
    (hrest : CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block rest) (fun _ _ => True)) :
    CT (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (VG.Proof.Ed25519.AArch64.digitPrefix ptr ++ rest)) (fun _ _ => True) := by
  have w (x : State) (h : WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) :=
    VG.Proof.Ed25519.AArch64.digitPrefix_ok h.1.scratch hpa hptr (hP x h.1) h.2
  refine blockAppend_ct ((CT.wp (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => h.1.scratch.x0) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

theorem prefix_ct (ptr : Nat) (hptr : ptr = 7952 ∨ ptr = 7944) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block (VG.Proof.Ed25519.AArch64.digitPrefix ptr)) (fun _ _ => True) := by
  rcases hptr with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem high_ct (add : Nat) (hadd : add = 0 ∨ add = 32) :
    CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add, .lsr .x .x19 .x19 4]) (fun _ _ => True) := by
  rcases hadd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)

theorem low_ct (add : Nat) (hadd : add = 0 ∨ add = 32) :
    CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add, .lsl .x .x19 .x19 60, .lsr .x .x19 .x19 60])
      (fun _ _ => True) := by
  rcases hadd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  CT (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitKHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C (digitHigh 7952 0) :=
  VG.Proof.Ed25519.AArch64.digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) (VG.Proof.Ed25519.AArch64.prefix_ct _ (.inl rfl))
    (VG.Proof.Ed25519.AArch64.high_ct 0 (.inl rfl))

theorem digitKLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C (digitLow 7952 0) :=
  VG.Proof.Ed25519.AArch64.digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) (VG.Proof.Ed25519.AArch64.prefix_ct _ (.inl rfl))
    (VG.Proof.Ed25519.AArch64.low_ct 0 (.inl rfl))

theorem digitSHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C (digitHigh 7944 32) :=
  VG.Proof.Ed25519.AArch64.digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) (VG.Proof.Ed25519.AArch64.prefix_ct _ (.inr rfl))
    (VG.Proof.Ed25519.AArch64.high_ct 32 (.inr rfl))

theorem digitSLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C (digitLow 7944 32) :=
  VG.Proof.Ed25519.AArch64.digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) (VG.Proof.Ed25519.AArch64.prefix_ct _ (.inr rfl))
    (VG.Proof.Ed25519.AArch64.low_ct 32 (.inr rfl))

/-! ## Windows -/

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : VG.Proof.Ed25519.AArch64.env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, RepP (point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigit_ct (o : Nat) (add : List Instr) (h : o = 5376 ∧ add = pointAddCachedP ∨
    o = 5376 ∧ add = pointAddCached ∨ o = 2048 ∧ add = pointAddCachedP) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr} {v o : Nat}
    (hdig : VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x ∧ VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .x0 = base ∧ u.gpr .x19 = BitVec.ofNat 64 v :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, ku⟩ =>
      ⟨(ku.gpr _ (by decide)).trans h.ctx.scratch.x0, uv⟩
  refine CT.seq ((CT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  rw [addDigit]
  refine CT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ h => ⟨h.1, trivial⟩)
  · simp only [eval, read_x, h.1.2, h.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.trans h.1.2.2.symm⟩)
      (fun _ _ h => h)

theorem doubleWindow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) doubleWindow (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem windowWith_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v : Nat} (hdig : VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x ∧ VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v y)
      (windowWith digit add) (fun _ _ => True) := by
  have hw (x : State) (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x) :
      WP isa doubleWindow x (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (doubleWindow_ok h.ctx.scratch ha) fun b ⟨br, bh, bk⟩ => ?_
    have kb := WinKeep.of_double bk
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br.proj⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowWith]
  exact VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => h.ctx.scratch.x0) VG.Proof.Ed25519.AArch64.doubleWindow_ct) hw (VG.Proof.Ed25519.AArch64.digitAdd_ct hdig hadd)

theorem windowA_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C digit) :
    CT (fun x y => VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x ∧ VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v y)
      (windowA digit) (fun _ _ => True) :=
  VG.Proof.Ed25519.AArch64.windowWith_ct hdig (VG.Proof.Ed25519.AArch64.addDigit_ct _ _ (.inl ⟨rfl, rfl⟩))

/-- After a window of `k`, the next digit's start. -/
theorem windowWith_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next add : List Instr}
    {full : Bool} (hadd : AddSpec add cache full) {v w : Nat} {x : State}
    (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowWith digit add) x (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowWith_ok h.1.ctx h.1.d ha hadd h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br.proj⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowA_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next : List Instr}
    {v w : Nat} {x : State}
    (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowA digit) x (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C next w) :=
  VG.Proof.Ed25519.AArch64.windowWith_next pointAddCachedP_spec h

theorem windowAB_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C digitA) (hB : VG.Proof.Ed25519.AArch64.DigitCT base kp sp A C digitB) :
    CT (fun x y => (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact VG.Proof.Ed25519.AArch64.seq_same ((VG.Proof.Ed25519.AArch64.windowWith_ct hA (VG.Proof.Ed25519.AArch64.addDigit_ct _ _ (.inr (.inl ⟨rfl, rfl⟩)))).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => VG.Proof.Ed25519.AArch64.windowWith_next pointAddCached_spec h)
    (VG.Proof.Ed25519.AArch64.digitAdd_ct hB (VG.Proof.Ed25519.AArch64.addDigit_ct _ _ (.inr (.inr ⟨rfl, rfl⟩))))

/-- After a window of both scalars, the next digits' start. -/
theorem windowAB_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr}
    {digitA digitB nextA nextB : List Instr} {vA vB wA wB : Nat} {x : State}
    (h : (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (DigitSpec base x nextA wA ∧ wA < 16) ∧ (DigitSpec base x nextB wB ∧ wB < 16)) :
    WP isa (windowAB digitA digitB) x fun u =>
      VG.Proof.Ed25519.AArch64.WinPre base kp sp A C nextA wA u ∧ DigitSpec base u nextB wB ∧ wB < 16 := by
  obtain ⟨a, ha⟩ := h.1.1.value
  refine WP.mono (windowAB_ok h.1.1.ctx h.1.1.d ha h.1.1.bound h.1.2.2 h.1.1.digit h.1.2.1)
    fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨⟨h.1.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.1.counter, h.2.1.1.of_keep kb,
    h.2.1.2⟩, h.2.2.1.of_keep kb, h.2.2.2⟩

/-! ## Bytes -/

theorem batchBegin_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchBegin) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem batchTest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchTest) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem aboveLow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block aboveLow) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem nibble_lt (b : Nat) : b % 256 / 16 < 16 :=
  Nat.div_lt_of_lt_mul (by have := Nat.mod_lt b (show 256 > 0 by decide); omega)

/-- After `batchBegin`: the counter is `i`, and the scalars' bytes are those of `K` and `S`. -/
theorem byteBegin_ok {s₀ x : State} {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64)
    (h : WinLoop s₀ base kp sp A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base kp sp A a ∧ VG.Proof.Ed25519.AArch64.env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, RepP (point (VG.Proof.Ed25519.AArch64.env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      (a.mem (off kp i)).toNat = K / 256 ^ i % 256 ∧
      (i < 32 → (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256) := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_
  have ka : ByteKeep base x a := ByteKeep.of_counter ag ar aw asp am
  refine ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩,
    av, ?_, fun hi32 => ?_⟩
  · rw [scalar_byte (n := 64) hi, ka.bytesK h.ctx, h.kVal]
  · rw [scalar_byte (n := 32) hi32, ka.bytesS h.ctx, h.sVal]

theorem byteStepA_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) byteStepA (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let vH := K / 256 ^ i % 256 / 16
  let vL := K / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a => VG.Proof.Ed25519.AArch64.WinPre base kp sp A C (digitHigh 7952 0) vH a ∧
        DigitSpec base a (digitLow 7952 0) vL ∧ vL < 16 := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (VG.Proof.Ed25519.AArch64.byteBegin_ok hi h) fun a ⟨actx, ad, av, ac, ak, _⟩ => ?_
    refine ⟨⟨actx, ad, av, ac, ?_, VG.Proof.Ed25519.AArch64.nibble_lt _⟩, ?_, Nat.mod_lt _ (by decide)⟩
    · rw [show vH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact digitKHigh actx hi ac
    · rw [show vL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact digitKLow actx hi ac
  have w3 (x : State) (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C (digitLow 7952 0) vL x) :
      WP isa (windowA (digitLow 7952 0)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).x0
  rw [byteStepA]
  refine VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) VG.Proof.Ed25519.AArch64.batchBegin_ct)
    w1 ?_
  refine VG.Proof.Ed25519.AArch64.seq_same ((VG.Proof.Ed25519.AArch64.windowA_ct VG.Proof.Ed25519.AArch64.digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => VG.Proof.Ed25519.AArch64.windowA_next h) ?_
  exact VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.windowA_ct VG.Proof.Ed25519.AArch64.digitKLow_ct) w3 (VG.Proof.Ed25519.AArch64.x0_ct (fun _ h => h) VG.Proof.Ed25519.AArch64.aboveLow_ct)

theorem byteStepAB_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 32) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) byteStepAB (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kH := K / 256 ^ i % 256 / 16
  let kL := K / 256 ^ i % 256 % 16
  let sH := S / 256 ^ i % 256 / 16
  let sL := S / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        (VG.Proof.Ed25519.AArch64.WinPre base kp sp A C (digitHigh 7952 0) kH a ∧ DigitSpec base a (digitHigh 7944 32) sH ∧
          sH < 16) ∧ (DigitSpec base a (digitLow 7952 0) kL ∧ kL < 16) ∧
          (DigitSpec base a (digitLow 7944 32) sL ∧ sL < 16) := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (VG.Proof.Ed25519.AArch64.byteBegin_ok (by omega) h) fun a ⟨actx, ad, av, ac, ak, as⟩ => ?_
    have as := as hi
    refine ⟨⟨⟨actx, ad, av, ac, ?_, VG.Proof.Ed25519.AArch64.nibble_lt _⟩, ?_, VG.Proof.Ed25519.AArch64.nibble_lt _⟩, ⟨?_, Nat.mod_lt _ (by decide)⟩,
      ⟨?_, Nat.mod_lt _ (by decide)⟩⟩
    · rw [show kH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact digitKHigh actx (by omega) ac
    · rw [show sH = (a.mem (off (off sp 32) i)).toNat / 16 by rw [as]]; exact digitSHigh actx hi ac
    · rw [show kL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact digitKLow actx (by omega) ac
    · rw [show sL = (a.mem (off (off sp 32) i)).toNat % 16 by rw [as]]; exact digitSLow actx hi ac
  have w3 (x : State) (h : VG.Proof.Ed25519.AArch64.WinPre base kp sp A C (digitLow 7952 0) kL x ∧
      DigitSpec base x (digitLow 7944 32) sL ∧ sL < 16) :
      WP isa (windowAB (digitLow 7952 0) (digitLow 7944 32)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).x0
  rw [byteStepAB]
  refine VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) VG.Proof.Ed25519.AArch64.batchBegin_ct)
    w1 ?_
  refine VG.Proof.Ed25519.AArch64.seq_same ((VG.Proof.Ed25519.AArch64.windowAB_ct VG.Proof.Ed25519.AArch64.digitKHigh_ct VG.Proof.Ed25519.AArch64.digitSHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)) (fun x h => VG.Proof.Ed25519.AArch64.windowAB_next h) ?_
  exact VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.windowAB_ct VG.Proof.Ed25519.AArch64.digitKLow_ct VG.Proof.Ed25519.AArch64.digitSLow_ct) w3 (VG.Proof.Ed25519.AArch64.x0_ct (fun _ h => h) VG.Proof.Ed25519.AArch64.batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` bytes left. -/
def LoopRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base kp sp A K S c x

theorem loopA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) :
    CT (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + n) x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + n) y)
      (.loop byteStepA (.nonzero .x .x19))
      (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 y) := by
  refine (CT.loop (fun n x y => (VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + n) x ∧
    VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + n) y) ∧ 0 < n ∧ n ≤ 32) ?_ n).mono
      (fun _ _ h => ⟨h, hn0, hn⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + (j + 1)) x) :
        WP isa byteStepA x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (32 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((VG.Proof.Ed25519.AArch64.byteStepA_ct (i := 32 + j) (by omega)).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

theorem windowsA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) :
    CT (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c y) windowsA
      (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 y) := by
  have hw (x : State) (h : VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c x) : WP isa (.block aboveLow) x fun u =>
      eval (.nonzero .x .x19) u = some (decide (c ≠ 32)) ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c u := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact WP.mono (aboveLow_ok h.ctx.scratch c hc64 h.counter) fun u ⟨uz, ku⟩ =>
      ⟨uz, s₀, r₀, h.of_keeps ku (by decide)⟩
  rw [windowsA]
  refine CT.seq ((CT.wp (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0)
    VG.Proof.Ed25519.AArch64.aboveLow_ct) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => h.1.1.trans h.2.1.symm) ?_ ?_
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    by_cases hn : n = 0
    · subst hn
      exact CT.of_false fun x y h => by
        have := h.2; rw [h.1.1.1] at this; cases this
    · exact (VG.Proof.Ed25519.AArch64.loopA_ct n (by omega) (by omega)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩)
        (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y h => ⟨h.1, ?_⟩
    have hc : c = 32 := by
      by_contra hne
      have := h.2.2; rw [h.2.1.1.1, decide_eq_true hne] at this; cases this
    subst hc
    exact ⟨h.2.1.1.2, h.2.1.2.2⟩

theorem loopB_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 32 y)
      (.loop byteStepAB (.nonzero .x .x19))
      (fun x y => VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 0 x ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S 0 y) := by
  refine (CT.loop (fun n x y => (VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S n x ∧
    VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S n y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (j + 1) x) :
        WP isa byteStepAB x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((VG.Proof.Ed25519.AArch64.byteStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

/-! ## Skipping the leading zero bytes of `k` -/

/-- A run of the skipping: from a state satisfying `R₀`, with `32 + n` bytes left. -/
def SkipRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S n : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipInv s₀ base kp sp A K S n x

/-- The byte's pointer and the counter, less one. -/
def skipPrefix : List Instr := [ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952]

theorem skipPrefix_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block VG.Proof.Ed25519.AArch64.skipPrefix) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem skipRest_ct : CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
    (.block [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree2 h) (by taint_decide)

theorem skipPrefix_ok {s : State} {base kp : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = kp) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block VG.Proof.Ed25519.AArch64.skipPrefix) s fun t => t.gpr .x2 = kp ∧ t.gpr .x8 = BitVec.ofNat 64 j := by
  rw [VG.Proof.Ed25519.AArch64.skipPrefix, show ([ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952] : List Instr) =
    [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++ [ld .x2 7952]) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .x2 7952
    (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
  exact ⟨by rw [tp, kb.mem, ka.mem, hp], by rw [kt.gpr _ (by decide), bv]⟩

theorem movzZero_ct : CT (fun _ _ => True) (.block [.movz .w .x19 0 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs []) (fun _ _ _ => agree_ofRegs (by simp)) (by taint_decide)

theorem skipStore_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0)
    (.block [st .x8 56, .subImm .x .x19 .x8 32]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)

theorem skipBody_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} :
    CT (fun x y => VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S (j + 1) x ∧ VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S (j + 1) y)
      skipBody (fun _ _ => True) := by
  let P := VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S (j + 1)
  have hx0 (x : State) (h : P x) : x.gpr .x0 = base := by
    obtain ⟨_, _, h, _⟩ := h; exact h.ctx.scratch.x0
  have hpre (x : State) (h : P x) : WP isa (.block VG.Proof.Ed25519.AArch64.skipPrefix) x fun t =>
      t.gpr .x2 = kp ∧ t.gpr .x8 = BitVec.ofNat 64 (32 + j) := by
    obtain ⟨_, _, h, _⟩ := h
    exact VG.Proof.Ed25519.AArch64.skipPrefix_ok h.ctx.scratch h.ctx.kHeader (32 + j) (by rw [h.counter]; rfl)
  have hload : CT (fun x y => P x ∧ P y) (.block skipLoad) (fun _ _ => True) := by
    rw [show skipLoad = VG.Proof.Ed25519.AArch64.skipPrefix ++ [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0] from rfl]
    refine blockAppend_ct ((CT.wp (VG.Proof.Ed25519.AArch64.x0_ct hx0 VG.Proof.Ed25519.AArch64.skipPrefix_ct) fun x y h => ⟨hpre x h.1, hpre y h.2⟩).mono
      (fun _ _ h => h) ?_) VG.Proof.Ed25519.AArch64.skipRest_ct
    intro x y ⟨_, hx, hy⟩
    exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
  have hw (x : State) (h : P x) : WP isa (.block skipLoad) x fun u => u.gpr .x0 = base ∧
      u.gpr .x19 = BitVec.ofNat 64 (K / 256 ^ (32 + j) % 256) := by
    obtain ⟨_, _, hl, _, _, hn⟩ := h
    refine WP.mono (skipLoad_ok hl.ctx.scratch hl.ctx.kHeader (32 + j) (by rw [hl.counter]; rfl)
      (hl.ctx.kRead _ (by omega))) fun u ⟨_, uv, ku⟩ => ⟨(ku.gpr _ (by decide)).trans
        hl.ctx.scratch.x0, by rw [uv, scalar_byte (n := 64) (by omega), hl.kVal]⟩
  rw [skipBody]
  refine CT.seq ((CT.wp hload fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => by simp only [eval, read_x, h.1.2, h.2.2]) ?_ ?_
  · exact movzZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact skipStore_ct.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem skipZero_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S 32 x ∧ VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S 32 y) skipZero
      (fun x y => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c x ∧
        VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S c y) := by
  rw [skipZero]
  refine CT.loop (fun n x y => VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S n x ∧ VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S n y)
    ?_ 32
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, h, _⟩ := h.1; exact Nat.lt_irrefl 0 h
  by_cases hj : j < 32
  · have hw (x : State) (h : VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S (j + 1) x) : WP isa skipBody x fun u =>
        eval (.nonzero .x .x19) u = some (skipOn K j) ∧
        (skipOn K j = false → VG.Proof.Ed25519.AArch64.LoopRun R₀ base kp sp A K S (skipEnd K j) u) ∧
        (skipOn K j = true → VG.Proof.Ed25519.AArch64.SkipRun R₀ base kp sp A K S j u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (skipBody_ok h) fun u ⟨uz, uf, ut⟩ =>
        ⟨uz, fun hf => ⟨s₀, r₀, uf hf⟩, fun ht => ⟨s₀, r₀, ut ht⟩⟩
    refine (CT.wp VG.Proof.Ed25519.AArch64.skipBody_ct fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipOn K j = false := Option.some.inj (xz.symm.trans he)
      exact ⟨skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2, xf hs, yf hs⟩
    · have hs : skipOn K j = true := Option.some.inj (xz.symm.trans he)
      exact ⟨j, by omega, xt hs, yt hs⟩
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, _, h⟩ := h.1; exact hj (by omega)

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scr s base ∧ RepP (point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3) P ∧ RepP (point (VG.Proof.Ed25519.AArch64.env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.EqRepPre base P Q s ∧ VG.Proof.Ed25519.AArch64.EqRepPre base P Q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.EqRepPre base P Q s ∧ VG.Proof.Ed25519.AArch64.EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (P.x = Q.x)) ∧
          (VG.Proof.Ed25519.AArch64.env t.mem base 10 = VG.Proof.Ed25519.AArch64.env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (VG.Proof.Ed25519.AArch64.equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact repP_cross_y h.2.1 h.2.2
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : CT (fun s t => (Scr s base ∧ (VG.Proof.Ed25519.AArch64.env s.mem base 10 = VG.Proof.Ed25519.AArch64.env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scr t base ∧ (VG.Proof.Ed25519.AArch64.env t.mem base 10 = VG.Proof.Ed25519.AArch64.env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw2 (s : State) (h : Scr s base ∧ (VG.Proof.Ed25519.AArch64.env s.mem base 10 = VG.Proof.Ed25519.AArch64.env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      change some (t.gpr .x8 == 0) = _
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := CT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine CT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (CT.ite ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (VG.Proof.Ed25519.AArch64.returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext`. -/
section

/-! The verification inputs remain readable and outside the workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : VG.Proof.Ed25519.AArch64.DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, h.sp, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scr s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarBytes : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1
  challengeRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VG.Proof.Ed25519.AArch64.VerifyContext s base pk sig challenge) (k : VG.Proof.Ed25519.AArch64.VerifyKeep base s t) :
    VG.Proof.Ed25519.AArch64.VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarBytes _ ‹_›
  · exact h.challengeRead _ ‹_›

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

theorem decodedThen_ok {s : State} {base : Addr} {p : Option Spec.Ed25519.Point}
    {next : Prog isa} {P : State → Prop} (hr : DecodeResult base p s)
    (hn : ∀ t, Keeps [] s t → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, Keeps [] s t → p = some a → point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  rw [decodedThen]
  cases hp : p with
  | none =>
    rw [hp] at hr
    change s.gpr .x8 = 0 at hr
    apply WP.ite false (by simp only [eval, read_x, hr]; rfl)
    · intro h; contradiction
    · intro _; exact hn s ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ hp
  | some a =>
    rw [hp] at hr
    apply WP.ite true (by simp only [eval, read_x, hr.1]; rfl)
    · intro _; exact hy s a ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ hp hr.2
    · intro h; contradiction

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTPublic`. -/
section
/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (s : State) : Prop where
  context : VG.Proof.Ed25519.AArch64.VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {s t : State}
    (h : VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) (kt : VG.Proof.Ed25519.AArch64.VerifyKeep base s t) :
    VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs t :=
  ⟨h.context.of_keep kt, (VG.Proof.Ed25519.AArch64.verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (VG.Proof.Ed25519.AArch64.verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (VG.Proof.Ed25519.AArch64.verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (VG.Proof.Ed25519.AArch64.verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem pointTableWrite_ct (base : Addr) (o : Nat) (ho : o ∈ [7424, 7552]) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (pointTableWrite o)) (fun _ _ => True) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  all_goals
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1 h.2

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r s ∧
      VG.Proof.Ed25519.AArch64.PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r t) verifyEquationPoints (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : VG.Proof.Ed25519.AArch64.PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r x) :
      WP isa windowPrep x (VG.Proof.Ed25519.AArch64.SkipRun R₀ base challenge sig Aa K S 32) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarBytes
      c.scalarFar c.challengeRead c.challengeFar (by rw [h.2.1]; exact hA)) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we, Nat.div_eq_of_lt (show Spec.Ed25519.decodeLE kbs < 256 ^ (32 + 32) from we.kVal ▸ decodeLE_lt64 _ _), by decide,
      by decide⟩
  have wn (x : State) (h : VG.Proof.Ed25519.AArch64.LoopRun R₀ base challenge sig Aa K S 0 x) :
      WP isa (.block negR) x (VG.Proof.Ed25519.AArch64.EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [pow_zero, Nat.div_one] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨ku.scr hx.ctx.scratch, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg.proj
  have prepCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) windowPrep (fun _ _ => True) := by
    rw [windowPrep]
    exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)
  have negRCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block negR) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => VG.Proof.Ed25519.AArch64.agree_x0 h) (by taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  refine CT.seq ((CT.wp (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => h.1.context.scratch.x0) prepCT)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.seq VG.Proof.Ed25519.AArch64.skipZero_ct ?_
  refine CT.seq (fun x y tx ty x' y' ⟨hsp, c, hc32, hc64, hx, hy⟩ ex ey =>
    VG.Proof.Ed25519.AArch64.windowsA_ct hc32 hc64 x y tx ty x' y' ⟨hsp, hx, hy⟩ ex ey) ?_
  refine CT.seq VG.Proof.Ed25519.AArch64.loopB_ct ?_
  exact VG.Proof.Ed25519.AArch64.seq_same (VG.Proof.Ed25519.AArch64.x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0) negRCT) wn
    (VG.Proof.Ed25519.AArch64.pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTAdjust`. -/
section
/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ VG.Proof.Ed25519.AArch64.env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ eval (.zero .x .x8) t = some (((VG.Proof.Ed25519.AArch64.env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  change some (t.gpr .x8 == 0) = _
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    CT (fun x y => Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y)
      (.seq (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine CT.seq (R := fun x y => x.gpr .x0 = base ∧ y.gpr .x0 = base)
    (CT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : CT (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => agree_ofRegs (by simp)
    have hw := CT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some true) =>
        And.intro (WP.block_nil h.1.1.x0) (WP.block_nil h.1.2.1.x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct base).mono
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        ⟨h.1.1.x0, h.1.2.1.x0⟩) (fun _ _ h => h)
    have hw := CT.wp ht
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        And.intro (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) fun _ k => (k.1.scr h.1.1).x0)
          (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) fun _ k => (k.1.scr h.1.2.1).x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.SignCTPre base b x s ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.SignCTPre base b x s) :
      WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (VG.Proof.Ed25519.AArch64.parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.scr h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : VG.Proof.Ed25519.AArch64.SignCTPre base b x _ ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (VG.Proof.Ed25519.AArch64.adjustTail_ct base)

end VG.Proof.Ed25519.AArch64
end

/-! The negative-zero check leaks only the public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem testThenSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.SignCTPre base b x s ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x t)
      (.ite (.nonzero .x .x1) recoverInvalid recoverAdjustSign) (fun _ _ => True) := by
  refine CT.ite ?_ ?_ ?_
  · intro s t h
    simp only [eval, read_x, h.1.2.1, h.2.2.1]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.AArch64.recoverAdjustSign_ct base b x).mono (fun _ _ h => h.1) (fun _ _ h => h)

theorem recoverSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.SignCTPre base b x s ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x t)
      recoverSign (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : VG.Proof.Ed25519.AArch64.SignCTPre base b x _ ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        VG.Proof.Ed25519.AArch64.SignCTPre base b x t ∧ eval (.zero .x .x8) t = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨tz, kt, tm⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩, ?_⟩
    · rw [tm]; exact h.2.2
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · intro s t h
    exact h.2.1.2.trans h.2.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.AArch64.recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def RootCTState (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  VG.Proof.Ed25519.AArch64.SignCTPre base b (rootX y) s ∧
    VG.Proof.Ed25519.AArch64.env s.mem base 11 = rootV y * rootX y * rootX y ∧
    VG.Proof.Ed25519.AArch64.env s.mem base 6 = rootU y ∧ VG.Proof.Ed25519.AArch64.env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.RootCTState base b y s ∧ VG.Proof.Ed25519.AArch64.RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6)))
      (fun s t => (VG.Proof.Ed25519.AArch64.RootCTState base b y s ∧ eval (.zero .x .x8) s = some (VG.Proof.Ed25519.AArch64.rootCheckValue y minus)) ∧
        (VG.Proof.Ed25519.AArch64.RootCTState base b y t ∧ eval (.zero .x .x8) t = some (VG.Proof.Ed25519.AArch64.rootCheckValue y minus))) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.RootCTState base b y s ∧ VG.Proof.Ed25519.AArch64.RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.RootCTState base b y s) :
      WP isa (.block (fieldEqual 11 (if minus then 12 else 6))) s fun t =>
        VG.Proof.Ed25519.AArch64.RootCTState base b y t ∧ eval (.zero .x .x8) t = some (VG.Proof.Ed25519.AArch64.rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨tz, kt, te⟩ => ?_
    refine ⟨⟨⟨kt.scr h.1.1, (kt.gpr _ (by decide)).trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    change some (t.gpr .x8 == 0) = _
    rw [tz, VG.Proof.Ed25519.AArch64.rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.SignCTPre base b x s ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x t)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      (fun _ _ => True) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.SignCTPre base b x s ∧ VG.Proof.Ed25519.AArch64.SignCTPre base b x t)
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.SignCTPre base b x s) :
      WP isa (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        VG.Proof.Ed25519.AArch64.SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1) fun t ⟨kt, te⟩ => ?_
    refine ⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩
    rw [te]
    change VG.Proof.Ed25519.AArch64.env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.Proof.Ed25519.AArch64.recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.RootCTState base b y s ∧ VG.Proof.Ed25519.AArch64.RootCTState base b y t)
      (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
        (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))
      (fun _ _ => True) := by
  refine CT.seq (VG.Proof.Ed25519.AArch64.rootCheck_ct base b y true) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.RootCTState base b y s ∧ VG.Proof.Ed25519.AArch64.RootCTState base b y t)
      (.seq (.block (fieldEqual 11 6)) (.ite (.zero .x .x8) recoverSign
        (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
          (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))))
      (fun _ _ => True) := by
  refine CT.seq (VG.Proof.Ed25519.AArch64.rootCheck_ct base b y false) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (VG.Proof.Ed25519.AArch64.recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ VG.Proof.Ed25519.AArch64.env s.mem base 1 = y

theorem recoverPoint_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.RecoverCTPre base b y s ∧ VG.Proof.Ed25519.AArch64.RecoverCTPre base b y t)
      recoverPoint (fun _ _ => True) := by
  have ht := (recoverCandidate_ct base).mono
    (fun _ _ (h : VG.Proof.Ed25519.AArch64.RecoverCTPre base b y _ ∧ VG.Proof.Ed25519.AArch64.RecoverCTPre base b y _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.RecoverCTPre base b y s) :
      WP isa recoverCandidate s (VG.Proof.Ed25519.AArch64.RootCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverPoint]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (VG.Proof.Ed25519.AArch64.recoverChecks_ct base b y)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PointDecodeCT`. -/
section
/-! Canonical point decoding leaks only its public bytes. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


def DecodeCTPre (base p : Addr) (bs : List Byte) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x2 = p ∧
    (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) ∧ Spec.Ed25519.bytesAt s.mem p 32 = bs

theorem pointDecode_ct (base p : Addr) (bs : List Byte) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.DecodeCTPre base p bs s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base p bs t)
      pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.DecodeCTPre base p bs s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base p bs t)
      (.block pointDecodeLoad) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.DecodeCTPre base p bs s) :
      WP isa (.block pointDecodeLoad) s fun t => VG.Proof.Ed25519.AArch64.RecoverCTPre base b y t ∧
        eval (.zero .x .x8) t = some (decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P)) := by
    refine WP.mono (VG.Proof.Ed25519.AArch64.pointDecodeLoad_ok h.1 h.2.1 h.2.2.1) fun t ⟨kt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.scratch h.1, ?_, ?_⟩, ?_⟩
    · rw [tb, h.2.2.2]
    · rw [ty, h.2.2.2]
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : Addr} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .x8 = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.AArch64
end

/-! A decoder's public success flag selects the continuation. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem DecodeResult.of_keeps {base : Addr} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (kt : Keeps [] s t) : DecodeResult base p t := by
  cases p with
  | none => exact (kt.gpr _ (by simp)).trans h
  | some p => exact ⟨(kt.gpr _ (by simp)).trans h.1, by rw [kt.mem]; exact h.2⟩

theorem decodedThen_ct (base : Addr) (p : Option Spec.Ed25519.Point) (P : State → Prop) (next : Prog isa)
    (_hP : ∀ s t, Keeps [] s t → P s → P t)
    (hn : ∀ a, p = some a → CT
      (fun s t => (P s ∧ point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = a) ∧
        (P t ∧ point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    CT (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  rw [decodedThen]
  refine CT.ite ?_ ?_ ?_
  · intro s t h
    simp only [eval, read_x, VG.Proof.Ed25519.AArch64.decodeResult_flag h.1.2, VG.Proof.Ed25519.AArch64.decodeResult_flag h.2.2]
  · cases p with
    | none =>
      apply CT.of_false
      intro s t h
      have hz : s.gpr .x8 = 0 := h.1.1.2
      have he := h.2
      change some (s.gpr .x8 != 0) = some true at he
      rw [hz] at he
      contradiction
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.2⟩, ⟨h.1.2.1, h.1.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-! Decoding R and selecting the public equation continuation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

def DecodeRCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧ tablePoint s.mem base 7424 = a

theorem verifyStoreR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    CT (fun s t => (VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = r) ∧ (VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = r))
      (.seq (.block (pointTableWrite 7552)) verifyEquationPoints) (fun _ _ => True) := by
  have ht := (VG.Proof.Ed25519.AArch64.pointTableWrite_ct base 7552 (by decide)).mono
    (fun s t (h : (VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = r) ∧ (VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t ∧
      point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = r)) => ⟨h.1.1.1.context.scratch.x0, h.2.1.1.context.scratch.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = r) :
      WP isa (.block (pointTableWrite 7552)) s (VG.Proof.Ed25519.AArch64.PointsCTPre base pk sig challenge pkbs rbs sbs kbs a r) := by
    refine WP.mono (pointTableWrite_ok h.1.1.context.scratch 7552 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    refine ⟨h.1.1.of_keep (kt.mono (by decide) (by decide)), ?_, tv.trans h.2⟩
    exact (kt.mem.point (by decide) (Or.inl (by decide)) (by decide)).trans h.1.2
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.Proof.Ed25519.AArch64.verifyEquationPoints_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR)

theorem verifyDecodeR_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a s ∧
      VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a t) verifyDecodeR (fun _ _ => True) := by
  let P := VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a
  have loadCT : CT (fun s t => P s ∧ P t)
      (.block [ld .x2 7944]) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.context.scratch.x0 h.2.1.context.scratch.x0
  have loadWP (s : State) (h : P s) :
      WP isa (.block [ld .x2 7944]) s fun t =>
        P t ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base sig rbs t := by
    refine WP.mono (loadPointer_ok h.1.context.scratch .x2 7944 (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VG.Proof.Ed25519.AArch64.VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.1.of_keep kp
    exact ⟨⟨hp, by rw [kt.mem]; exact h.2⟩,
      hp.context.scratch, tp.trans h.1.context.sigHeader, hp.context.rRead, hp.rBytes⟩
  have hl := CT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (VG.Proof.Ed25519.AArch64.pointDecode_ct base sig rbs).mono
    (fun s t (h : (P s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base sig rbs s) ∧ (P t ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base sig rbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base sig rbs s) :
      WP isa pointDecode s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint rbs) t := by
    have hd := VG.Proof.Ed25519.AArch64.pointDecode_ok (base := base) (p := sig) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    have kt := ht.1
    exact ⟨⟨h.1.1.of_keep (PowersKeep.of_decode kt),
      (workspace_tablePoint kt.mem (by decide) (by decide)).trans h.1.2⟩, ht.2⟩
  have hd := CT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeR]
  refine CT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (CT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply VG.Proof.Ed25519.AArch64.decodedThen_ct base (Spec.Ed25519.decodePoint rbs) P _
  · intro s t kt h
    exact ⟨h.1.of_keep (PowersKeep.of_keeps kt (by simp)), by rw [kt.mem]; exact h.2⟩
  · intro r hr
    obtain ⟨Ra, hR⟩ := decodePoint_rep hr
    exact VG.Proof.Ed25519.AArch64.verifyStoreR_ct base pk sig challenge pkbs rbs sbs kbs a r hA hR

end VG.Proof.Ed25519.AArch64
end

/-! Decoding the public key selects the public verification continuation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem verifyStoreA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte)
    (a : Spec.Ed25519.Point) {Aa : EPoint dZ} (hA : Rep a Aa) :
    CT (fun s t => (VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = a) ∧ (VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = a))
      (.seq (.block (pointTableWrite 7424)) verifyDecodeR) (fun _ _ => True) := by
  have ht := (VG.Proof.Ed25519.AArch64.pointTableWrite_ct base 7424 (by decide)).mono
    (fun s t (h : (VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = a) ∧ (VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs t ∧
      point (VG.Proof.Ed25519.AArch64.env t.mem base) 0 1 2 3 = a)) => ⟨h.1.1.context.scratch.x0, h.2.1.context.scratch.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      point (VG.Proof.Ed25519.AArch64.env s.mem base) 0 1 2 3 = a) :
      WP isa (.block (pointTableWrite 7424)) s (VG.Proof.Ed25519.AArch64.DecodeRCTPre base pk sig challenge pkbs rbs sbs kbs a) := by
    refine WP.mono (pointTableWrite_ok h.1.context.scratch 7424 (by decide) (by decide)) fun t ⟨kt, tv, _⟩ => ?_
    exact ⟨h.1.of_keep (kt.mono (by decide) (by decide)), tv.trans h.2⟩
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.Proof.Ed25519.AArch64.verifyDecodeR_ct base pk sig challenge pkbs rbs sbs kbs a hA)

theorem verifyDecodeA_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs t) verifyDecodeA (fun _ _ => True) := by
  let P := VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have loadCT : CT (fun s t => P s ∧ P t)
      (.block [ld .x2 7936]) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.context.scratch.x0 h.2.context.scratch.x0
  have loadWP (s : State) (h : P s) :
      WP isa (.block [ld .x2 7936]) s fun t =>
        P t ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base pk pkbs t := by
    refine WP.mono (loadPointer_ok h.context.scratch .x2 7936 (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
    have kp : VG.Proof.Ed25519.AArch64.VerifyKeep base s t := PowersKeep.of_keeps kt (by decide)
    have hp := h.of_keep kp
    exact ⟨hp, hp.context.scratch, tp.trans h.context.pkHeader, hp.context.pkRead, hp.pkBytes⟩
  have hl := CT.wp loadCT (fun s t h => ⟨loadWP s h.1, loadWP t h.2⟩)
  have decodeCT := (VG.Proof.Ed25519.AArch64.pointDecode_ct base pk pkbs).mono
    (fun s t (h : (P s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base pk pkbs s) ∧ (P t ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base pk pkbs t)) =>
      ⟨h.1.2, h.2.2⟩) (fun _ _ h => h)
  have decodeWP (s : State) (h : P s ∧ VG.Proof.Ed25519.AArch64.DecodeCTPre base pk pkbs s) :
      WP isa pointDecode s fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint pkbs) t := by
    have hd := VG.Proof.Ed25519.AArch64.pointDecode_ok (base := base) (p := pk) h.2.1 h.2.2.1 h.2.2.2.1
    rw [h.2.2.2.2] at hd
    with_reducible apply WP.mono hd
    intro t ht
    exact ⟨h.1.of_keep (PowersKeep.of_decode ht.1), ht.2⟩
  have hd := CT.wp decodeCT (fun s t h => ⟨decodeWP s h.1, decodeWP t h.2⟩)
  rw [verifyDecodeA]
  refine CT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (CT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_)
  apply VG.Proof.Ed25519.AArch64.decodedThen_ct base (Spec.Ed25519.decodePoint pkbs) P _
  · intro s t kt h
    exact h.of_keep (PowersKeep.of_keeps kt (by simp))
  · intro a ha
    obtain ⟨Aa, hA⟩ := decodePoint_rep ha
    exact VG.Proof.Ed25519.AArch64.verifyStoreA_ct base pk sig challenge pkbs rbs sbs kbs a hA

end VG.Proof.Ed25519.AArch64
end

/-! The canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem verifyScalar_ct (base pk sig challenge : Addr) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.VerifyContext s base pk sig challenge ∧ VG.Proof.Ed25519.AArch64.VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : CT (fun s t => VG.Proof.Ed25519.AArch64.VerifyContext s base pk sig challenge ∧ VG.Proof.Ed25519.AArch64.VerifyContext t base pk sig challenge)
      (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0])
      (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VG.Proof.Ed25519.AArch64.VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0]) s
        (fun t => t.gpr .x2 = off sig 32) := by
    change WP isa (.block (([ld .x2 7944] : List Instr) ++
      ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr))) s _
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, _⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add32_ok a .x2) fun b ⟨bp, _⟩ => ?_
    refine WP.mono (setZeroX10_ok b) fun t ⟨_, kt⟩ => ?_
    have tp := (kt.gpr .x2 (by decide)).trans bp
    rw [tp, ap, h.sigHeader]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : CT (fun s t => s.gpr .x2 = off sig 32 ∧ t.gpr .x2 = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  change CT _ (.block (([ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] : List Instr) ++
    (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr)))) _
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) (fun _ _ => True) := by
  let P := VG.Proof.Ed25519.AArch64.VerifyPublic base pk sig challenge pkbs rbs sbs kbs
  have ht := (VG.Proof.Ed25519.AArch64.verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ eval (.nonzero .x .x8) t = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead) fun t ⟨kt, _, tc⟩ => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt), by change some (t.gpr .x8 != 0) = _; rw [tc, h.sBytes]⟩
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (VG.Proof.Ed25519.AArch64.verifyDecodeA_ct base pk sig challenge pkbs rbs sbs kbs).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.VerifyLit`. -/
section
/-! A checked literal for the complete verification program. -/

namespace VG

materialize_code Impl.Ed25519.AArch64.verifyEquation

end VG
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifySetup`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyDecodeR`. -/
section
/-! Reject an invalid R encoding or evaluate the complete equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

theorem verifyDecodeR_ok {s : State} {base pk sig challenge : Addr}
    {Aa : EPoint dZ} (h : VerifyContext s base pk sig challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa verifyDecodeR s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeR]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := sig) ha.scratch (ap.trans h.sigHeader) ha.rRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem sig 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c r kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, equationWithR, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7552 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    have hd := h.of_keep kabcd
    have da : tablePoint d.mem base 7424 = tablePoint s.mem base 7424 := by
      rw [kd.mem.point (by decide) (Or.inl (by decide)) (by decide), kc.mem,
        workspace_tablePoint kb.mem (by decide) (by decide), ka.mem]
    obtain ⟨Ra, hRa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyEquationPoints_ok hd.scratch hd.sigHeader hd.challengeHeader
      hd.scalarBytes hd.scalarFar hd.challengeRead hd.challengeFar (by rw [da]; exact hA)
      (by rw [dp, cp]; exact hRa)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, da, verifyKeep_bytes kabcd h.scalarFar, verifyKeep_bytes kabcd h.challengeFar,
      hp, hy, equationWithR]

end VG.Proof.Ed25519.AArch64
end

/-! Reject an invalid public key encoding before computing the equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

theorem verifyDecodeA_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa verifyDecodeA s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeA]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7936 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := pk) ha.scratch (ap.trans h.pkHeader) ha.pkRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem pk 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c p kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, decodedEquation, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7424 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    obtain ⟨Aa, hAa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyDecodeR_ok (h.of_keep kabcd) (by rw [dp, cp]; exact hAa))
      fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, verifyKeep_bytes kabcd h.rFar, verifyKeep_bytes kabcd h.scalarFar,
      verifyKeep_bytes kabcd h.challengeFar, hp, hy, decodedEquation]

end VG.Proof.Ed25519.AArch64
end

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .x8 = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono (verifyScalar_ok h.scratch h.sigHeader h.scalarRead) fun a ⟨ka, am, ac⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ (congrArg some ac)
  · intro ht
    refine WP.mono (verifyDecodeA_ok (h.of_keep kap)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.AArch64
end

/-! Save the ABI registers and retain the three public input pointers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [mov .x8 .x2, mov .x2 .x3]) s fun t =>
      t.gpr .x8 = s.gpr .x2 ∧ t.gpr .x2 = s.gpr .x3 ∧ Keeps [.x8, .x2] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .x0 = base ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .x0 ∧
      t.mem.readW (off base 7944) 64 = s.gpr .x1 ∧
      t.mem.readW (off base 7952) 64 = s.gpr .x8 := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write]
    exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_write, write64_eq_writeW, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [mov .x2 .x0, mov .x0 .x8]) s fun t =>
      t.gpr .x2 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x8 ∧ Keeps [.x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 64⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 64) (bytesAt s.mem (s.gpr .x2) 64))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    bytesAt s.mem (s.gpr .x0) 32 = bytesAt t.mem (t.gpr .x0) 32 ∧
    bytesAt s.mem (s.gpr .x1) 64 = bytesAt t.mem (t.gpr .x1) 64 ∧
    bytesAt s.mem (s.gpr .x2) 64 = bytesAt t.mem (t.gpr .x2) 64

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  saved : Saved (s.gpr .x3) s.gpr t.mem
  frame : Frame [⟨s.gpr .x3, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], t.gpr r = s.gpr r

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hn⟩ := hs
  have hws : (⟨s.gpr .x3, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok asc (ka.wr ▸ hws)) fun b ⟨gb, rb, wb, spb, mb, svb⟩ => ?_
  have bs : b.gpr .x2 = s.gpr .x3 := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.wr]; exact hws))
    fun c ⟨cs, gc, rc, wc, spc, mc, cp, cr, cc⟩ => ?_
  have fm : Frame [⟨s.gpr .x3, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.mem] at f
    exact f
  have sv : Saved (s.gpr .x3) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.gpr
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.rd)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.wr)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.gpr .x0 (by decide)]
    · rw [cr, gb, ka.gpr .x1 (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .x1) 32) d = off (s.gpr .x1) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi; exact farScr hpk hi (by decide)
    · intro i hi; exact farScr hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact farScr hsig (by omega) (by decide)
    · intro i hi; exact farScr hchallenge hi (by decide)
  refine ⟨hc, sv, fm, spc.trans (spb.trans ka.sp), fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rw [gc _ (by decide), gb, ka.gpr _ (by decide)]

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ev, ke⟩ => ?_
  have er : e.gpr .x2 = s.gpr .x3 := es.trans (kd.scratch hc.scratch).x0
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.wr, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.mem]; exact svd)) fun t ⟨tr, kt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.x19, 0) (by decide)
    · exact tr (.x20, 8) (by decide)
    · exact tr (.x21, 16) (by decide)
    · exact tr (.x22, 24) (by decide)
    · exact tr (.x23, 32) (by decide)
    · exact tr (.x24, 40) (by decide)
    all_goals
      rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide) (by decide) (by decide)]
      exact hc0.regs _ (by decide)
  · exact kt.sp.trans (ke.sp.trans (kd.sp.trans hc0.sp))
  · change t.gpr .x0 = _
    rw [kt.gpr _ (by decide), ev, dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCT`. -/
section
/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide)⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem verifyBody_base_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid))
      (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) :
      WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) s
        (fun t => t.gpr .x0 = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).x0
  exact (CT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have setupCT : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x3]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  have whole : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      verifyEquation (fun _ _ => True) := by
    rw [verifyEquation]
    refine CT.seq hp ?_
    intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
    have pa := ha.public hab.1
    have pb := hb.public_right hab.2.1 hab.2.2
    exact CT.seq
      (verifyBody_base_ct (a.gpr .x3) (a.gpr .x0) (a.gpr .x1) (a.gpr .x2)
        (bytesAt a.mem (a.gpr .x0) 32) (bytesAt a.mem (a.gpr .x1) 32)
        (bytesAt a.mem (off (a.gpr .x1) 32) 32) (bytesAt a.mem (a.gpr .x2) 64))
      (verifyFinish_ct (a.gpr .x3)) _ _ _ _ _ _ ⟨hsp, pa, pb⟩ es et
  intro s t ts tt s' t' hs ht hp es et
  exact (whole _ _ _ _ _ _ ⟨hp.1, hs, ht, hp⟩ es et).1

end VG.Proof.Ed25519.AArch64
end

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := verify_correct hs

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, verifyLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] [verifySatState] using verifySatState

theorem verify_verified : Verified AArch64.target verifyEquation (Spec.Ed25519.verifyEquationContract AArch64.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.AArch64

end
