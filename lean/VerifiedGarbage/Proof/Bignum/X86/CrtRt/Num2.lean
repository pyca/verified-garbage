module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Loops
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Reduce
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.Front

/-! # Sums, differences, comparisons and imports in private CRT at a run-time width -/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (reduceLoop_ok compareLoop_ok byteAddr_ptr)
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The pointers and count of `chain`, its carry cleared. -/
theorem chainSetup_ok (h : In base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    {Q : State → Prop}
    (k : ∀ w, Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s w → w.mem = s.mem → PtrAt w base .ebp (lo len a) →
      PtrAt w base .ebx (lo len b) → PtrAt w base .edi (lo len o) → (w.gpr .edx).toNat = 4 * cw len n →
      w.gpr .ecx = cmask false → Q w) :
    WP isa (.block (ptrTo a .ebp .edx ++ ptrTo b .ebx .edx ++ ptrTo o .eax .edx ++ cntTo n .edx ++
      ([.mov .edi (.reg .eax), .mov .ecx (.imm 0)] : List Instr))) s Q := by
  have bl := h.bytes_lt
  simp only [List.append_assoc]
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega)
    fun u K m p => ?_
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega)
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) hv.edi hv.width h.upper' (by omega)
    fun w Kw mw pw => ?_
  have hw := hv.regs Kw mw
  refine cntTo_ok (r := .edx) hw.width h.upper' N.extra fun y Ky my cy => ?_
  refine wp_movS rfl fun y₁ u₁ _ => wp_movS rfl fun y₂ u₂ _ => WP.block_nil ?_
  refine k y₂ ((((((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans
    (Ky.mono (by decide))).trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide)))
    (by rw [u₂.mem, u₁.mem, my, mw, mv, m]) ?_ ?_ ?_ ?_ u₂.gpr
  · rw [PtrAt, u₂.other _ (by decide), u₁.other _ (by decide), Ky.1 _ (by decide), Kw.1 _ (by decide),
      Kv.1 _ (by decide)]; exact p
  · rw [PtrAt, u₂.other _ (by decide), u₁.other _ (by decide), Ky.1 _ (by decide), Kw.1 _ (by decide)]; exact pv
  · rw [PtrAt, u₂.other _ (by decide), u₁.gpr, Ky.1 _ (by decide)]; exact pw
  · rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact cnt_toNat h.upper' N cy

theorem chainSub_ok (h : In base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    (hoa : Apart (lo len o) (cb len n) (lo len a) (cb len n)) (hob : Apart (lo len o) (cb len n) (lo len b) (cb len n)) :
    WP isa (chain .sbb o a b n) s fun u => Outside base (lo len o) (cb len n) s.mem u.mem ∧
      PtrAt u base .ebp (lo len a + cb len n) ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧ val32 u.mem base (lo len o) (cw len n) + val32 s.mem base (lo len b) (cw len n) =
        val32 s.mem base (lo len a) (cw len n) + 2 ^ (32 * cw len n) * c.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have ce := cb_eq (len := len) N
  unfold VG.Impl.Bignum.X86.CrtRt.chain
  refine WP.seq (chainSetup_ok h N ho ha hb fun w K m pa pb po c e => ?_)
  refine WP.seq (WP.mono (reduceLoop_ok (h.ws.of_keeps K) (a := lo len a) (m := lo len b) (d := lo len o)
    (N := cw len n) (cw_pos h.lower') (by omega) (by omega) (by omega) (by omega) (by omega) pa pb po c e)
    fun t ⟨O, P, V, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K.trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.crt.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  obtain ⟨c', ec', V'⟩ := V
  refine ⟨by rw [u₁.mem, ← m, ce]; exact O, by rw [PtrAt, u₁.other _ (by decide), ce]; exact P,
    ⟨c', by rw [u₁.other _ (by decide)]; exact ec', by rw [u₁.mem, ← m]; exact V'⟩,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) ed⟩

theorem chainAdd_ok (h : In base bytes len args s) {o a b : Loc} {n : Cnt} (N : CntOk n)
    (ho : lo len o + cb len n ≤ bytes) (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes)
    (hoa : Apart (lo len o) (cb len n) (lo len a) (cb len n)) (hob : Apart (lo len o) (cb len n) (lo len b) (cb len n)) :
    WP isa (chain .adc o a b n) s fun u => Outside base (lo len o) (cb len n) s.mem u.mem ∧
      PtrAt u base .ebp (lo len a + cb len n) ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧ val32 u.mem base (lo len o) (cw len n) + 2 ^ (32 * cw len n) * c.toNat =
        val32 s.mem base (lo len a) (cw len n) + val32 s.mem base (lo len b) (cw len n)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have ce := cb_eq (len := len) N
  unfold VG.Impl.Bignum.X86.CrtRt.chain
  refine WP.seq (chainSetup_ok h N ho ha hb fun w K m pa pb po c e => ?_)
  refine WP.seq (WP.mono (addLoop_ok (h.ws.of_keeps K) (a := lo len a) (m := lo len b) (d := lo len o)
    (N := cw len n) (cw_pos h.lower') (by omega) (by omega) (by omega) (by omega) (by omega) pa pb po c e)
    fun t ⟨O, P, _, V, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K.trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.crt.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have ed : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  obtain ⟨c', ec', V'⟩ := V
  refine ⟨by rw [u₁.mem, ← m, ce]; exact O, by rw [PtrAt, u₁.other _ (by decide), ce]; exact P,
    ⟨c', by rw [u₁.other _ (by decide)]; exact ec', by rw [u₁.mem, ← m]; exact V'⟩,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) ed⟩

theorem lessThan_ok (h : In base bytes len args s) {a b : Loc} {n : Cnt} (N : CntOk n)
    (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes) :
    WP isa (lessThan a b n) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (val32 s.mem base (lo len a) (cw len n) < val32 s.mem base (lo len b) (cw len n))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  unfold lessThan
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .esi) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega)
    fun u K m p => ?_)
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega)
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  refine cntTo_ok (r := .edx) hv.width h.upper' N.extra fun w Kw mw cv => wp_movS rfl fun y uy _ => WP.block_nil ?_
  have Ky : Keeps [.ecx, .edx, .ebp, .esi] s y :=
    (((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans (uy.keeps.mono (by decide))
  have my : y.mem = s.mem := by rw [uy.mem, mw, mv, m]
  refine WP.mono (compareLoop_ok (h.ws.of_keeps Ky) (x := lo len a) (y := lo len b) (N := cw len n)
    (cw_pos h.lower') (by omega) (by omega)
    (by rw [PtrAt, uy.other _ (by decide), Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, uy.other _ (by decide), Kw.1 _ (by decide)]; exact pv)
    (by rw [uy.other _ (by decide)]; exact cnt_toNat h.upper' N cv) uy.gpr)
    fun t ⟨mt, et, Kt⟩ => ⟨by rw [mt, my], by rw [et, my], (Ky.mono (by decide)).trans Kt⟩

theorem cmask_or_not (x y : Bool) : (cmask x ||| cmask y) ^^^ BitVec.allOnes 32 = cmask (!(x || y)) := by
  cases x <;> cases y <;> rfl

theorem equal_ok (h : In base bytes len args s) {a b : Loc} {n : Cnt} (N : CntOk n)
    (ha : lo len a + cb len n ≤ bytes) (hb : lo len b + cb len n ≤ bytes) :
    WP isa (equal a b n) s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (val32 s.mem base (lo len a) (cw len n) = val32 s.mem base (lo len b) (cw len n))) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  unfold equal
  refine WP.seq (WP.mono (lessThan_ok h N ha hb) fun u ⟨mu, eu, Ku⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u₁ uu _ => WP.block_nil ?_)
  have hu := h.regs ((Ku.mono (by decide)).trans (uu.keeps.mono (by decide)) :
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₁) (by rw [uu.mem, mu])
  refine WP.seq (WP.mono (lessThan_ok hu N hb ha) fun v ⟨mv, ev, Kv⟩ => ?_)
  refine wp_orS rfl fun v₁ w₁ => wp_logicS (.inr rfl) rfl fun v₂ w₂ => WP.block_nil ?_
  have mem₁ : u₁.mem = s.mem := by rw [uu.mem, mu]
  refine ⟨by rw [w₂.mem, w₁.mem, mv, mem₁], ?_,
    ((((Ku.mono (by decide)).trans (uu.keeps.mono (by decide))).trans (Kv.mono (by decide))).trans
      (w₁.keeps.mono (by decide))).trans (w₂.keeps.mono (by decide))⟩
  have ebx : v.gpr .ebx = cmask (decide (val32 s.mem base (lo len a) (cw len n) < val32 s.mem base (lo len b) (cw len n))) := by
    rw [Kv.1 _ (by decide), uu.gpr, eu]
  rw [w₂.gpr]
  show v₁.gpr .ecx ^^^ BitVec.allOnes 32 = _
  rw [w₁.gpr, ev, ebx, mem₁, cmask_or_not]
  congr 1
  rw [show ∀ x y : Nat, (decide (x = y)) = !(decide (y < x) || decide (x < y)) from fun x y => by
    by_cases h₁ : x = y <;> by_cases h₂ : y < x <;> by_cases h₃ : x < y <;> simp_all <;> omega]

end

end VG.Proof.Bignum.X86.CrtRt
