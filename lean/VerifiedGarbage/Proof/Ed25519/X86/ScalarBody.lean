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

theorem scalarDouble_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : acc s < 2) :
    WP isa (.block scalarDouble) s fun t => Keep s t ∧ Frame [sub x scalarR 32] s.mem t.mem ∧
      fe t.mem x scalarR = 2 * fe s.mem x scalarR + acc s := by
  have hs : num (fun k => colv s.mem x [.mulI (scalarR + 4 * k) 2]) 8 =
      2 * fe s.mem x scalarR := by
    rw [fe, ← num_mul]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    change wv s.mem x (scalarR + 4 * k) * 2 = 2 * wv s.mem x (scalarR + 4 * k)
    exact Nat.mul_comm _ _
  refine WP.mono (cols_ok hc _ 8 (by decide) (fun k hk t ht d hd => ?_)
    (fun k _ => ?_) (by omega_using [hb])) fun t ⟨keep, frame, eq, _⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact ⟨by simp only [scalarR]; omega_using [hk], Or.inr (Nat.le_refl _)⟩
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hw := wv_lt s.mem x (scalarR + 4 * k)
    change wv s.mem x (scalarR + 4 * k) * 2 < 2 ^ 68
    omega_using [hw]
  · rw [hs] at eq
    change fe t.mem x scalarR + 2 ^ 256 * acc t = _ at eq
    have hL := order_bound
    have hz : acc t = 0 := by omega_using [eq, hr, hb, hL]
    exact ⟨keep, frame, by rw [hz, Nat.mul_zero, Nat.add_zero] at eq; omega_using [eq]⟩

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
theorem scalar_subtract_value {r t c : Nat} (hr : r < 2 * L) (ht : t < 2 ^ 256)
    (h : t + 2 ^ 256 * c = r + (2 ^ 256 - L)) :
    c ≤ 1 ∧ (if c = 1 then t else r) = r % L := by
  have hl := order_bound
  have hp := order_pos
  constructor
  · omega_using [hr, ht, h, hl]
  · by_cases hc : c = 1
    · rw [ite_eq_left hc, Nat.mod_eq_sub_mod (by omega_using [h, hc, hp, hl]),
        Nat.mod_eq_of_lt (by omega_using [hr, h, hc, hl])]
      omega_using [h, hc, hl]
    · have hz : c = 0 := by omega_using [hr, h, hc, hl]
      rw [ite_eq_right hc, Nat.mod_eq_of_lt (by omega_using [ht, h, hz, hl])]

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

theorem scalarRound_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : acc s < 2) :
    WP isa (.block scalarRound) s fun t => Keep s t ∧
      Frame [sub x scalarR 32, sub x T 32] s.mem t.mem ∧
      fe t.mem x scalarR = (2 * fe s.mem x scalarR + acc s) % L := by
  simp only [scalarRound, List.append_assoc]
  refine WP.block_append (WP.mono (scalarDouble_ok hc hr hb) fun u ⟨ku, fu, eu⟩ => ?_)
  refine WP.block_append (WP.mono (scalarSubtract_ok (ku.ctx hc)) fun v ⟨kv, fv, ev⟩ => ?_)
  have hv := scalar_subtract_value (by rw [eu]; omega_using [hr, hb]) (fe_lt v.mem x T) ev
  refine WP.block_append (WP.mono (scalarMask_ok hv.1) fun w ⟨kw, mw, ew⟩ => ?_)
  have ewR : fe w.mem x scalarR = fe u.mem x scalarR := by
    rw [mw]; exact fe_frame1 fv hc.fit (by decide) (by decide) (Or.inl (by decide))
  refine WP.mono (selects_ok (kw.ctx (kv.ctx (ku.ctx hc))) (o := scalarR)
    (g := acc v) (by decide) hv.1 ew 8 (by decide) w
    ⟨Keep.refl _, rfl, Frame.refl _ _, fun _ h => by omega_using [h]⟩)
    fun t ht => ⟨ku.trans (kv.trans (kw.trans ht.keep)), ?_, ?_⟩
  · have fm : Frame [sub x scalarR 32, sub x T 32] u.mem w.mem := by
      rw [mw]; exact fv.mono fun r h => List.mem_cons_of_mem _ h
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]).trans
      (fm.trans (ht.frame.mono fun r h => by simp only [List.mem_singleton] at h; simp only [h, List.mem_cons, true_or]))
  · have es : fe t.mem x scalarR = if acc v = 1 then fe w.mem x T else fe w.mem x scalarR := by
      split
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_left ‹_›))
      · exact num_congr fun j hj => congrArg BitVec.toNat ((ht.done j hj).trans (ite_eq_right ‹_›))
    rw [es, ewR, mw, hv.2, eu]

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

theorem scalarFrame_word {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hf : Frame (scalarFrame x) m m') : wd m' x 32 = wd m x 32 := by
  apply wd_frame hf
  intro r hr
  simp only [scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hx]) (by simp only [scalarR]; omega_using [hx]) (Or.inl (by decide))
  · exact sub_disj (by omega_using [hx]) (by simp only [T]; omega_using [hx]) (Or.inl (by decide))

theorem scalarBitLoad_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat} (hj : j < 8) :
    WP isa (.block (scalarBitLoad j)) s fun t => Keep s t ∧ t.mem = s.mem ∧
      acc t = (wv s.mem x 32 / 2 ^ (j + 1)) % 2 := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u₁ h₁ => ?_
  refine Wp.wp_shr (by omega_using [hj]) fun u₂ h₂ _ => ?_
  refine Wp.wp_andi fun u₃ h₃ => Wp.wp_movi fun u₄ h₄ => Wp.wp_movi fun t h₅ => WP.block_nil ?_
  refine ⟨(updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans ((updKeep h₄).trans (updKeep h₅)))),
    by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  simp only [acc, v, h₅.gpr, h₅.other .ebx (by decide), h₅.other .ecx (by decide),
    h₄.gpr, h₄.other .ebx (by decide), toNat_zero32, Nat.mul_zero, Nat.add_zero]
  rw [h₃.gpr, h₂.gpr, h₁.gpr, BitVec.toNat_and]
  change (wd s.mem x 32 >>> (j + 1)).toNat &&& (2 ^ 1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem scalarBit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {j : Nat} (hj : j < 8)
    (hr : fe s.mem x scalarR < L) :
    WP isa (.block (scalarBit j)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (2 * fe s.mem x scalarR + (wv s.mem x 32 / 2 ^ (j + 1)) % 2) % L := by
  refine WP.block_append (WP.mono (scalarBitLoad_ok hc hj) fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (scalarRound_ok (ku.ctx hc) (by rw [mu]; exact hr)
    (by rw [au]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, ft, et⟩ => ?_
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, by rw [et, mu, au]⟩

/-- Pure bit recurrence, kept independent from machine states. -/
def scalarConsume (b : Nat) : Nat → Nat → Nat
  | 0, r => r
  | n + 1, r => scalarConsume b n ((2 * r + b / 2 ^ n % 2) % L)

theorem scalarConsume_eq (b n r : Nat) (hr : r < L) :
    scalarConsume b n r = (2 ^ n * r + b % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [scalarConsume, Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero,
      Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [scalarConsume, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a y z : Nat) : (a * (y % L) + z) % L = (a * y + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul, Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega_using []

theorem scalarBits_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n ≤ 8)
    (hr : fe s.mem x scalarR < L) :
    WP isa (.block (scalarBits n)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = scalarConsume (wv s.mem x 32 / 2) n (fe s.mem x scalarR) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨Keep.refl _, Frame.refl _ _, rfl⟩
  | succ n ih =>
    have ec : scalarBits (n + 1) = scalarBit n ++ scalarBits n := by
      simp only [scalarBits, List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.flatMap_append, List.flatMap_singleton]
    rw [ec]
    refine WP.block_append (WP.mono (scalarBit_ok hc (by omega_using [hn]) hr)
      fun u ⟨ku, fu, eu⟩ => ?_)
    refine WP.mono (ih (ku.ctx hc) (by omega_using [hn])
      (by rw [eu]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, ft, et⟩ => ?_
    refine ⟨ku.trans kt, fu.trans ft, ?_⟩
    rw [et, wv, scalarFrame_word hc.fit fu, scalarConsume, eu]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ n)]

theorem scalarEight_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (hr : fe s.mem x scalarR < L) (hb : wv s.mem x 32 / 2 < 256) :
    WP isa (.block (scalarBits 8)) s fun t => Keep s t ∧ Frame (scalarFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (256 * fe s.mem x scalarR + wv s.mem x 32 / 2) % L := by
  refine WP.mono (scalarBits_ok hc (by decide) hr) fun t ⟨kt, ft, et⟩ => ⟨kt, ft, ?_⟩
  rw [et, scalarConsume_eq _ _ _ hr, show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hb]
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

theorem scalarRead_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block scalarRead) s fun t => ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      Frame [sub x 32 4] s.mem t.mem ∧ wv t.mem x 32 = 2 * (s.mem (addr x (128 + n))).toNat := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_mov fun s₂ h₂ => Wp.wp_add fun s₃ h₃ _ => ?_
  have e₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [h₁.gpr, hs]
    exact (Wp.ofNat_pred (by omega_using [])).trans (congrArg (BitVec.ofNat 32) (by omega_using []))
  have k₃ := (scalarUpd h₁).trans ((scalarUpd h₂).trans (scalarUpd h₃))
  have c₃ := k₃.ctx hc
  have a₃ : addr (s₃.gpr .eax) 128 = addr x (128 + n) := by
    rw [h₃.gpr, h₂.gpr, h₂.other .esi (by decide), e₁, h₁.other .edi (by decide), hc.edi]
    simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n 128]
  refine scalar_ld8 a₃ (c₃.inRW (by omega_using [hn]) (by decide)) fun s₄ h₄ => ?_
  refine Wp.wp_add fun s₅ h₅ _ => ?_
  have c₅ := ((scalarUpd h₄).trans (scalarUpd h₅)).ctx c₃
  refine Wp.wp_stm c₅.edi (c₅.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₃.trans ((scalarUpd h₄).trans ((scalarUpd h₅).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)), ?_, ?_, ?_⟩
  · rw [ht.gpr, h₅.other .esi (by decide), h₄.other .esi (by decide), h₃.other .esi (by decide),
      h₂.other .esi (by decide), e₁]
  · rw [ht.mem, m₅]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, wv, wd_write_self, h₅.gpr, h₄.gpr, h₃.mem, h₂.mem, h₁.mem,
      BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
    have hb := (s.mem (addr x (128 + n))).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [hb])]
    omega_using []

def scalarBodyFrame (x : BitVec 32) : List Region := sub x 32 4 :: scalarFrame x

theorem scalarTest_ok (s : State) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (s.gpr .esi == 0) := by
  refine Wp.wp_test fun t ht hz => WP.block_nil ?_
  exact ⟨ht.gpr, ht.mem, ht.rd, ht.wr, by rw [hz, BitVec.and_self]⟩

theorem scalarByte_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) (hr : fe s.mem x scalarR < L) :
    WP isa (.block scalarByte) s fun t => ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.zf = some (decide (n = 0)) ∧ Frame (scalarBodyFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (256 * fe s.mem x scalarR + (s.mem (addr x (128 + n))).toNat) % L := by
  simp only [scalarByte, List.append_assoc]
  refine WP.block_append (WP.mono (scalarRead_ok hc hn hs) fun u ⟨ku, su, fu, eu⟩ => ?_)
  have vu : fe u.mem x scalarR = fe s.mem x scalarR :=
    fe_frame1 fu hc.fit (by decide) (by decide) (Or.inr (by decide))
  have bu : wv u.mem x 32 / 2 = (s.mem (addr x (128 + n))).toNat := by rw [eu]; omega_using []
  refine WP.block_append (WP.mono (scalarEight_ok (ku.ctx hc) (by rw [vu]; exact hr)
    (by rw [bu]; exact BitVec.isLt _)) fun v ⟨kv, fv, ev⟩ => ?_)
  refine WP.mono (scalarTest_ok v) fun t ⟨gt, mt, rt, wt, zt⟩ => ?_
  have st : t.gpr .esi = BitVec.ofNat 32 n := by rw [gt, kv.esi, su]
  refine ⟨ku.trans ((Keep.scalar kv).trans ⟨by rw [gt], by rw [gt], rt, wt⟩), st, ?_, ?_, ?_⟩
  · rw [zt, kv.esi, su, Wp.ofNat_beq_zero (by omega_using [hn])]
  · rw [mt]
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self).trans
      (fv.mono fun r h => List.mem_cons_of_mem _ h)
  · rw [mt, ev, vu, bu]
end VG.Proof.Ed25519.X86
