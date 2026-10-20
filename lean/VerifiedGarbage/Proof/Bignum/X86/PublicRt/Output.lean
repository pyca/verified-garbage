module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
public import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Framework.Omega

/-! # The comparison and the result of public RSA at a run-time width

`compare`: `ecx` all ones exactly if the input is below the modulus
(`compare_ok`); `maskOut`: the result cleared unless the mask at 144 is set
(`maskOut_ok`); `write`: the result's bytes to `out`, and the acceptance in
`eax` (`write_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem compare_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) :
    WP isa compare s fun u => u.mem = s.mem ∧
      u.gpr .ecx = cmask (decide (val32 s.mem base (numAt len 1) (nw len) < val32 s.mem base (numAt len 0) (nw len))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have f1 := (h.fits (j := 1) (by decide)).1
  have f0 := (h.fits (j := 0) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  unfold PublicRt.compare
  refine WP.seq (slotPtr_ok (r := .esi) (t := .edx) (j := 1) (by decide) (by decide) h.edi h.width h.upper (by decide)
    fun u K m p _ => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebp) (t := .edx) (j := 0) (by decide) (by decide) hu.edi hu.width h.upper (by decide)
    fun v Kv mv pv cv => wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.ecx, .edx, .ebp, .esi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  have esi : PtrAt w base .esi (numAt len 1) := by
    rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p
  have ebp : PtrAt w base .ebp (numAt len 0) := by rw [PtrAt, uw.other _ (by decide)]; exact pv
  have edx : (w.gpr .edx).toNat = 4 * nw len := by
    rw [uw.other _ (by decide), cv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wb_le h.upper; omega)]
    exact wbe
  refine WP.mono (compareLoop_ok (h.ws.of_keeps Kw) (N := nw len) (by simp only [nw]; omega)
    (by omega) (by omega) esi ebp edx uw.gpr) fun t ⟨mt, et, Kt⟩ => ⟨by rw [mt, mw], by rw [et, mw],
      (Kw.mono (by decide)).trans Kt⟩

theorem maskOut_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) {c : Bool}
    (hm : s.mem.readW (off base PublicFn.acceptanceOffset) 32 = cmask c) :
    WP isa maskOut s fun u => Outside base (numAt len 2) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len 2) (nw len) = (if c then val32 s.mem base (numAt len 2) (nw len) else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have f2 := (h.fits (j := 2) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  unfold maskOut
  refine WP.seq (slotPtr_ok (r := .ebp) (t := .edx) (j := 2) (by decide) (by decide) h.edi h.width h.upper (by decide)
    fun u K m p c' => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc hu.scratch (d := PublicFn.acceptanceOffset)
    (by simp only [PublicFn.acceptanceOffset, numAt, numOff] at f2 ⊢; omega)) fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.ecx, .edx, .ebp] s w := (K.mono (by decide)).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, m]
  refine WP.mono (maskLoop_ok (h.ws.of_keeps Kw) (x := numAt len 2) (N := nw len) (c := c) (by simp only [nw]; omega) (by omega)
    (by rw [PtrAt, uw.other _ (by decide)]; exact p)
    (by rw [uw.other _ (by decide), c', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wb_le h.upper; omega)]
        exact wbe)
    (by rw [uw.gpr, m, hm])) fun t ⟨O, V, Kt⟩ => ⟨by rw [← mw, wbe]; exact O, by rw [V, mw],
      (Kw.mono (by decide)).trans (Kt.mono (by decide))⟩

theorem write_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (fitv : val32 s.mem base (numAt len 2) (nw len) < 2 ^ (8 * len)) :
    WP isa write s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (val32 s.mem base (numAt len 2) (nw len)) len ∧
      t.gpr .eax = s.mem.readW (off base PublicFn.acceptanceOffset) 32 &&& 1 ∧
      Frame [⟨byteAddr (args 0), len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have f2 := (h.fits (j := 2) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have wbg := len_le_wb len
  have nw' := h.scratch.nowrap
  have hlow := h.lower
  have hup := h.upper
  unfold write
  simp only [PublicFn.outputArgs, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movS (h.stack 0 (by decide)).readSrc fun u₁ e₁ _ => ?_)
  have h₁ := h.keep e₁.keeps (by decide) (by decide) (by rw [e₁.mem]; exact Outside.refl _ _ _ _)
  refine wp_movS (h₁.stack 1 (by decide)).readSrc fun u₂ e₂ _ => ?_
  have h₂ := h₁.keep e₂.keeps (by decide) (by decide) (by rw [e₂.mem]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .esi) (t := .edx) (j := 2) (by decide) (by decide) h₂.edi h₂.width h.upper (by decide)
    fun v Kv mv pv _ => wp_addS rfl fun v₁ w₁ _ => wp_subS rfl fun v₂ w₂ _ => WP.block_nil ?_
  have K₂ : Keeps [.ebx, .ecx, .edx, .esi] s v₂ :=
    (((e₁.keeps.mono (by decide)).trans (e₂.keeps.mono (by decide))).trans (Kv.mono (by decide))).trans
      ((w₁.keeps.mono (by decide)).trans (w₂.keeps.mono (by decide)))
  have m₂ : v₂.mem = s.mem := by rw [w₂.mem, w₁.mem, mv, e₂.mem, e₁.mem]
  have src := v.gpr .esi
  have srcAddr : byteAddr (v.gpr .esi) = off base (numAt len 2) := byteAddr_ptr pv (by omega)
  have srcNat : (v.gpr .esi).toNat = base.toNat + numAt len 2 := by rw [pv, Nat.mod_eq_of_lt (by omega)]
  have ecx₂ : v₂.gpr .ecx = BitVec.ofNat 32 len := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.gpr, h.outLen]
  have ebx₂ : v₂.gpr .ebx = args 0 := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.other _ (by decide), e₁.gpr]
  have esi₂ : v₂.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [w₂.gpr, w₁.gpr, Kv.1 .ecx (by decide), e₂.gpr, h.outLen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have hsub : Region.Sub ⟨off base (numAt len 2), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := numAt len 2) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.seq (WP.mono (reverseBuffer_ok v₂ (src := v.gpr .esi) (dst := args 0) (n := len) (by omega)
    (by omega) h.outFit (by omega) (by rw [K₂.2.1, K₂.2.2, srcAddr]; exact h.scratch.read (by omega))
    (by rw [K₂.2.2]; exact h.outWrite) (by rw [srcAddr]; exact h.outApart.sub_left hsub) ebx₂ esi₂ ecx₂)
    fun t ⟨V, F, _, T⟩ => ?_)
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (K₂.mono (by decide)).trans (T.mono (by decide))
  have Ft : Frame [⟨byteAddr (args 0), len⟩] s.mem t.mem := by rw [← m₂]; exact F
  have ht := h.ws.of_keeps Kt
  have edit : (t.gpr .edi).toNat = base.toNat := by rw [Kt.1 _ (by decide)]; exact h.edi
  have st : Scr t base bytes := ⟨by rw [← h.scratch.edi, Kt.1 _ (by decide)], ht.wr, ht.nowrap,
    by rw [Kt.1 _ (by decide)]; exact h.scratch.stk⟩
  refine wp_movS (readSrc_sc st (d := PublicFn.acceptanceOffset)
    (by simp only [PublicFn.acceptanceOffset, numAt, numOff] at f2 ⊢; omega)) fun t₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t₂ u₂ => WP.block_nil ?_
  have acc : t.mem.readW (off base PublicFn.acceptanceOffset) 32 = s.mem.readW (off base PublicFn.acceptanceOffset) 32 :=
    Ft.readW (r := ⟨base, bytes⟩) (Scr.contains nw' (by simp only [PublicFn.acceptanceOffset, numAt, numOff] at f2 ⊢; omega))
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.outApart) (by decide)
  refine ⟨?_, ?_, by rw [u₂.mem, u₁.mem]; exact Ft, (Kt.trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide))⟩
  · rw [u₂.mem, u₁.mem, V, srcAddr, m₂]
    have eq : (s.mem.read (off base (numAt len 2)) (4 * nw len)).toNat = val32 s.mem base (numAt len 2) (nw len) :=
      read_eq_val32 _ _ _ _
    rw [VG.Proof.Bignum.read_prefix_value s.mem _ (by omega : len ≤ 4 * nw len) (by rw [eq]; exact fitv), eq]
  · rw [u₂.gpr, u₁.gpr, acc]; rfl

end VG.Proof.Bignum.X86.PublicRt
