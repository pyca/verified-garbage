module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
import VerifiedGarbage.Proof.Framework.Omega

/-! # The subtraction and the selection of public RSA at a run-time width -/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem reduce_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbase : (args 8).toNat = base.toNat) :
    WP isa reduce s fun u => Outside base (numAt len 4) (wb len) s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base (numAt len 4) (nw len) + val32 s.mem base (numAt len 0) (nw len) =
          val32 s.mem base (numAt len 5) (nw len) + 2 ^ (32 * nw len) * c.toNat ∧
        u.gpr .ecx = cmask (decide (w32 s.mem base (numAt len 5 + wb len) < c.toNat))) ∧
      u.gpr .edi = s.gpr .edi ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have f4 := (h.fits (j := 4) (by decide)).1
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have nw' := h.scratch.nowrap
  have s45 := numAt_apart len (x := 5) (d := 4) (by decide)
  have s40 := numAt_apart len (x := 0) (d := 4) (by decide)
  have e45 : numAt len 5 = numAt len 4 + wb len := numAt_succ len 4
  unfold reduce
  refine WP.seq (slotPtr_ok (r := .eax) (t := .edx) (j := 4) (by decide) (by decide) h.edi h.width h.upper
    (by decide) fun u K m p _ => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebp) (t := .edx) (j := 5) (by decide) (by decide) hu.edi hu.width h.upper (by decide)
    fun v Kv mv pv _ => ?_
  have hv := hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebx) (t := .edx) (j := 0) (by decide) (by decide) hv.edi hv.width h.upper (by decide)
    fun w Kw' mw' pw cw => wp_movS rfl fun w₁ e₁ _ => wp_movS rfl fun w₂ e₂ _ => WP.block_nil ?_
  have Kw : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s w₂ :=
    ((((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw'.mono (by decide))).trans
      (e₁.keeps.mono (by decide))).trans (e₂.keeps.mono (by decide))
  have mw : w₂.mem = s.mem := by rw [e₂.mem, e₁.mem, mw', mv, m]
  have hw := h.ws.of_keeps Kw
  refine WP.seq (WP.mono (reduceLoop_ok hw (a := numAt len 5) (m := numAt len 0) (d := numAt len 4)
    (N := nw len) (by simp only [nw]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [PtrAt, e₂.other _ (by decide), e₁.other _ (by decide), Kw'.1 _ (by decide)]; exact pv)
    (by rw [PtrAt, e₂.other _ (by decide), e₁.other _ (by decide)]; exact pw)
    (by rw [PtrAt, e₂.other _ (by decide), e₁.gpr, Kw'.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [e₂.other _ (by decide), e₁.other _ (by decide), cw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact wbe)
    e₂.gpr) fun t ⟨O, ebp, ⟨c, ec, V⟩, Kt⟩ => ?_)
  have ht := hw.of_keeps Kt
  have top : w32 t.mem base (numAt len 5 + wb len) = w32 s.mem base (numAt len 5 + wb len) := by
    rw [O.w32 (d := numAt len 5 + wb len) (by omega_using [e45, wbe]) (by omega_using [f5, nw', e45, wbe]), mw]
  -- The mask: the top word less the borrow.
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega)) fun t₁ u₁ _ => ?_
  refine wp_carry (by rw [u₁.other _ (by decide), ec]) fun t₂ u₂ c₂ => ?_
  refine wp_sbbS rfl c₂ fun t₃ u₃ c₃ => ?_
  refine wp_sbb_self c₃ fun t₄ u₄ => wp_movS rfl fun t₅ u₅ _ => ?_
  have K₅ : Keeps [.eax, .ecx] t t₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
  have ht₅ := ht.of_keeps K₅
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t₅ := Kw.trans (Kt.trans (K₅.mono (by decide)))
  have m₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have Oall : Outside base 0 bytes s.mem t₅.mem := by
    rw [m₅, ← mw]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 8 (by decide)).keep Kall (by decide) Oall).readSrc fun t₆ u₆ _ => WP.block_nil ?_
  refine ⟨by rw [u₆.mem, m₅, ← mw, wbe]; exact O, ⟨c, by rw [u₆.mem, m₅, ← mw]; exact V, ?_⟩, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, ← top]
    have eax₂ : (t₂.gpr .eax).toNat = w32 t.mem base (numAt len 5 + 4 * nw len) := by
      rw [u₂.other _ (by decide), u₁.gpr, Nat.add_zero]
    rw [wbe, ← eax₂, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add] at *
  · rw [u₆.gpr]; exact h.edi_eq hbase
  · exact Kall.trans (u₆.keeps.mono (by decide))

theorem select_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbase : (args 8).toNat = base.toNat) {x d : Nat} (hx : x ≤ 7)
    (hd : d ≤ 7) (hxd : x ≠ d) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (select x d) s fun u => Outside base (numAt len d) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len d) (nw len) =
        (if k then val32 s.mem base (numAt len x) (nw len) else val32 s.mem base (numAt len d) (nw len)) ∧
      u.gpr .edi = s.gpr .edi ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] s u := by
  have fx := (h.fits hx).1
  have fd := (h.fits hd).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have sep := numAt_apart len hxd
  unfold select
  simp only [List.append_assoc]
  refine WP.seq (slotPtr_ok (r := .ebp) (t := .edx) (j := x) (by decide) (by decide) h.edi h.width h.upper
    (by omega) fun u K m p _ => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebx) (t := .edx) (j := d) (by decide) (by decide) hu.edi hu.width h.upper (by omega)
    fun v Kv mv pv cv => wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.ebx, .edx, .ebp, .edi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  have hw := h.ws.of_keeps Kw
  refine WP.seq (WP.mono (selectLoop_ok hw (x := numAt len x) (d := numAt len d) (N := nw len) k
    (by simp only [nw]; omega) (by omega) (by omega) (by omega)
    (by rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, uw.other _ (by decide)]; exact pv)
    (by rw [uw.gpr, cv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact wbe)
    (by rw [uw.other _ (by decide), Kv.1 _ (by decide), K.1 _ (by decide)]; exact hk))
    fun t ⟨O, V, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (Kw.mono (by decide)).trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 8 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  refine ⟨by rw [u₁.mem, ← mw, wbe]; exact O, by rw [u₁.mem, V, mw], by rw [u₁.gpr]; exact h.edi_eq hbase,
    Kall.trans (u₁.keeps.mono (by decide))⟩

end VG.Proof.Bignum.X86.PublicRt
