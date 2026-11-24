module

public import VerifiedGarbage.Impl.Ed25519.X86.Scalar
public import VerifiedGarbage.Proof.Ed25519.X86.Workspace
public import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.X25519.X86.Ops
import VerifiedGarbage.Proof.X25519.X86.Freeze

/-! ### `Ed25519.X86.ScalarStep`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

theorem scalarK_num : num (fun k => (scalarK k).toNat) 8 = 2 ^ 256 - L := by decide

theorem scalarSubtract_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarSubtract) s fun t => Keep s t ∧ Frame [sub x T 32] s.mem t.mem ∧
      fe t.mem x T + 2 ^ 256 * acc t = fe s.mem x scalarR + (2 ^ 256 - L) := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  have hs : num (fun k => colv u.mem x [.addM (scalarR + 4 * k), .addI (scalarK k)]) 8 =
      fe s.mem x scalarR + (2 ^ 256 - L) := by
    rw [← scalarK_num, fe, ← num_add, mu]
    exact num_congr fun k _ => by
      simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  refine WP.mono (cols_ok (ku.ctx hc) _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [treads, List.mem_singleton] at hd; subst hd
      exact ⟨by simp only [scalarR]; omega_using [hk], Or.inl (by simp only [scalarR, T]; omega_using [hk])⟩
    · simp only [treads, List.not_mem_nil] at hd
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := wv_lt u.mem x (scalarR + 4 * k)
    have hk := (scalarK k).isLt
    omega_using [hw, hk]
  · rw [au, Nat.zero_add, hs] at et
    rw [mu] at ft
    exact ⟨ku.trans kt, ft, et⟩

/-- The carry is the comparison with L; the low limbs are the subtraction. -/
theorem scalar_subtract_value {r t c : Nat} (hr : r < 2 ^ 256) (ht : t < 2 ^ 256)
    (h : t + 2 ^ 256 * c = r + (2 ^ 256 - L)) :
    c ≤ 1 ∧ (if c = 1 then t else r) = if L ≤ r then r - L else r := by
  have hl := order_bound
  have hp := order_pos
  refine ⟨by omega_using [hr, ht, h, hl], ?_⟩
  split <;> split <;> omega_arith

theorem scalarMask_ok {s : State} (ha : acc s ≤ 1) :
    WP isa (.block scalarMask) s fun t => Keep s t ∧ t.mem = s.mem ∧
      t.gpr .ecx = mask (acc s) := by
  refine Wp.wp_movi fun u hu => Wp.wp_sub fun t ht _ => WP.block_nil ?_
  refine ⟨(updKeep hu).trans (updKeep ht), ht.mem.trans hu.mem, ?_⟩
  rw [ht.gpr, hu.gpr, hu.other .ebx (by decide)]
  have hb : (s.gpr .ebx).toNat = acc s := by
    have he := (s.gpr .ebx).isLt
    change _ ≤ 1 at ha
    simp only [acc, v] at ha ⊢
    omega_using [ha, he]
  have hw : s.gpr .ebx = BitVec.ofNat 32 (acc s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hb, Nat.mod_eq_of_lt (by omega_using [ha])]
  rw [hw]; rfl

/-- `L` subtracted from the number at `scalarR` if it is not below it. -/
theorem scalarCondSub_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarCondSub) s fun t => Keep s t ∧
      Frame [sub x scalarR 32, sub x T 32] s.mem t.mem ∧
      fe t.mem x scalarR =
        if L ≤ fe s.mem x scalarR then fe s.mem x scalarR - L else fe s.mem x scalarR := by
  simp only [scalarCondSub, List.append_assoc]
  refine WP.block_append (WP.mono (scalarSubtract_ok hc) fun v ⟨kv, fv, ev⟩ => ?_)
  have hv := scalar_subtract_value (fe_lt s.mem x scalarR) (fe_lt v.mem x T) ev
  refine WP.block_append (WP.mono (scalarMask_ok hv.1) fun w ⟨kw, mw, ew⟩ => ?_)
  have ewR : fe w.mem x scalarR = fe s.mem x scalarR := by
    rw [mw]; exact fe_frame1 fv hc.fit (by decide) (by decide) (Or.inl (by decide))
  refine WP.mono (selects_ok (kw.ctx (kv.ctx hc)) (o := scalarR)
    (g := acc v) (by decide) hv.1 ew 8 (by decide) w
    ⟨Keep.refl _, rfl, Frame.refl _ _, fun _ h => by omega_using [h]⟩)
    fun t ht => ⟨kv.trans (kw.trans ht.keep), ?_, ?_⟩
  · have fm : Frame [sub x scalarR 32, sub x T 32] s.mem w.mem := by
      rw [mw]; exact fv.mono fun r h => List.mem_cons_of_mem _ h
    exact fm.trans (ht.frame.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or])
  · have es : fe t.mem x scalarR = if acc v = 1 then fe w.mem x T else fe w.mem x scalarR := by
      split
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_left ‹_›))
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_right ‹_›))
    rw [es, ewR, mw, hv.2]

end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.ScalarByte`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

def scalarFrame (x : BitVec 32) : List Region := [sub x scalarR 32, sub x T 32]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

structure ScalarKeep (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem ScalarKeep.refl (s : State) : ScalarKeep s s := ⟨rfl, rfl, rfl, rfl⟩
theorem ScalarKeep.trans {s t u : State} (h : ScalarKeep s t) (k : ScalarKeep t u) : ScalarKeep s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr⟩
theorem ScalarKeep.ctx {x : BitVec 32} {s t : State} (h : ScalarKeep s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr h.esp

theorem Keep.scalar {s t : State} (h : Keep s t) : ScalarKeep s t := ⟨h.edi, h.esp, h.rd, h.wr⟩
theorem scalarUpd {s t : State} {r : Reg} {v : BitVec 32} (h : Wp.Upd s t r v)
    (hr : r ≠ .edi ∧ r ≠ .esp := by decide) : ScalarKeep s t :=
  ⟨h.other _ hr.1.symm, h.other _ hr.2.symm, h.rd, h.wr⟩

theorem scalar_ld8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Wp.Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  change Option.map _ (if InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 1 then
    some (s.mem (addr (s.gpr b) o)) else none) = _
  simp only [ha, hin, ite_true, Option.map_some]

/-- The 64 bytes the scalar engine reduces, at byte 128 of the working space. -/
def scalarInput (m : Mem) (x : BitVec 32) : List Byte :=
  (List.range 64).map fun i => m (addr x (128 + i))

/-- What the scalar engine changes: the products' words, the difference and its temporary. -/
def scalarBodyFrame (x : BitVec 32) : List Region := sub x scalarQ 72 :: sub x scalarP 32 :: scalarFrame x

end VG.Proof.Ed25519.X86
