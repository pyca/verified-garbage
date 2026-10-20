module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Recombine
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The result written out

`maskResult_ok`: the result (wide slot 19, `B` bytes) cleared unless the mask
at `accOff` is set. `writeResult_ok`: its `n_len` bytes to `out`,
big-endian, and the acceptance in `eax`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem maskResult_ok (h : In base bytes len args s) {c : Bool}
    (hm : s.mem.readW (off base accOff) 32 = cmask c) {P : Prog isa} {Q : State → Prop}
    (k : ∀ u, Outside base (lo len (.slot .wide 19)) (bc len .wide) s.mem u.mem →
      val32 u.mem base (lo len (.slot .wide 19)) (cwc len .wide) =
        (if c then val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) else 0) →
      Keeps [.eax, .ecx, .edx, .ebp] s u → WP isa P u Q) :
    WP isa (.seq (.block (ptrTo (.slot .wide 19) .ebp .edx ++ cntTo (one .wide) .edx ++
      ([.mov .ecx (.mem (sc accOff))] : List Instr))) (.seq maskLoop P)) s Q := by
  have f19 := h.slot_fit .wide (j := 19) (by decide)
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have bl := h.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (x := .slot .wide 19) (by decide) (by decide) h.edi h.width
    h.upper' (by omega) fun u K m p => ?_)
  have hu := h.regs K m
  refine cntTo_ok (r := .edx) (n := one .wide) hu.width h.upper' (one_ok .wide).extra fun v Kv mv cv => ?_
  have hv := hu.regs Kv mv
  refine wp_movS (readSrc_sc hv.crt.scratch (d := accOff) (by simp only [accOff]; omega)) fun w uw _ =>
    WP.block_nil ?_
  have Kw : Keeps [.ecx, .edx, .ebp] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.maskLoop_ok (h.ws.of_keeps Kw) (x := lo len (.slot .wide 19))
    (N := cwc len .wide) (c := c) (by omega) (by omega)
    (by rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [uw.other _ (by decide), cnt_toNat h.upper' (one_ok .wide) cv, cw1])
    (by rw [uw.gpr, mv, m, hm])) fun t ⟨O, V, Kt⟩ => k t (by rw [← mw, bw]; exact O) (by rw [V, mw])
      ((Kw.mono (by decide)).trans (Kt.mono (by decide))))

/-- The result's `n_len` bytes to `out`; they are its value's when it fits them. -/
theorem writeResult_ok (h : In base bytes len args s) :
    WP isa (.seq (.block (PublicFn.outputArgs ++ ptrTo (.slot .wide 19) .esi .edx ++
      ([.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)] : List Instr)))
      (.seq reverseBytes (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]))) s fun t =>
      (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) < 2 ^ (8 * len) →
        Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
          Spec.Rsa.i2osp (val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide)) len) ∧
      t.gpr .eax = s.mem.readW (off base accOff) 32 &&& 1 ∧
      Frame [⟨byteAddr (args 0), len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have f19 := h.slot_fit .wide (j := 19) (by decide)
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have lb := len_le_bc len
  have nw' := h.crt.scratch.nowrap
  have hlow := h.lower'
  have hup := h.upper'
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  simp only [PublicFn.outputArgs, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movS (h.crt.stack 0 (by decide)).readSrc fun u₁ e₁ _ => ?_)
  have h₁ := h.regs e₁.keeps e₁.mem
  refine wp_movS (h₁.crt.stack 1 (by decide)).readSrc fun u₂ e₂ _ => ?_
  have h₂ := h₁.regs e₂.keeps e₂.mem
  refine ptrTo_ok (r := .esi) (t := .edx) (x := .slot .wide 19) (by decide) (by decide) h₂.edi h₂.width
    h.upper' (by omega) fun v Kv mv pv => wp_addS rfl fun v₁ w₁ _ => wp_subS rfl fun v₂ w₂ _ => WP.block_nil ?_
  have K₂ : Keeps [.ebx, .ecx, .edx, .esi] s v₂ :=
    (((e₁.keeps.mono (by decide)).trans (e₂.keeps.mono (by decide))).trans (Kv.mono (by decide))).trans
      ((w₁.keeps.mono (by decide)).trans (w₂.keeps.mono (by decide)))
  have m₂ : v₂.mem = s.mem := by rw [w₂.mem, w₁.mem, mv, e₂.mem, e₁.mem]
  have srcAddr : byteAddr (v.gpr .esi) = off base (lo len (.slot .wide 19)) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have srcNat : (v.gpr .esi).toNat = base.toNat + lo len (.slot .wide 19) := by
    rw [pv, Nat.mod_eq_of_lt (by omega)]
  have ecx₂ : v₂.gpr .ecx = BitVec.ofNat 32 len := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.gpr, h.crt.outLen]
  have ebx₂ : v₂.gpr .ebx = args 0 := by
    rw [w₂.other _ (by decide), w₁.other _ (by decide), Kv.1 _ (by decide), e₂.other _ (by decide), e₁.gpr]
  have esi₂ : v₂.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [w₂.gpr, w₁.gpr, Kv.1 .ecx (by decide), e₂.gpr, h.crt.outLen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have hsub : Region.Sub ⟨off base (lo len (.slot .wide 19)), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len (.slot .wide 19)) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.seq (WP.mono (reverseBuffer_ok v₂ (src := v.gpr .esi) (dst := args 0) (n := len) (by omega)
    (by omega) h.crt.outFit (by omega) (by rw [K₂.2.1, K₂.2.2, srcAddr]; exact h.crt.scratch.read (by omega))
    (by rw [K₂.2.2]; exact h.crt.outWrite) (by rw [srcAddr]; exact h.crt.outApart.sub_left hsub) ebx₂ esi₂ ecx₂)
    fun t ⟨V, F, _, T⟩ => ?_)
  have Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := (K₂.mono (by decide)).trans (T.mono (by decide))
  have Ft : Frame [⟨byteAddr (args 0), len⟩] s.mem t.mem := by rw [← m₂]; exact F
  have ht := h.ws.of_keeps Kt
  have st' : Scr t base bytes := ⟨by rw [← h.crt.scratch.edi, Kt.1 _ (by decide)], ht.wr, ht.nowrap,
    by rw [Kt.1 _ (by decide)]; exact h.crt.scratch.stk⟩
  refine wp_movS (readSrc_sc st' (d := accOff) (by simp only [accOff]; omega)) fun t₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t₂ u₂ => WP.block_nil ?_
  have acc : t.mem.readW (off base accOff) 32 = s.mem.readW (off base accOff) 32 :=
    Ft.readW (r := ⟨base, bytes⟩) (Scr.contains nw' (by simp only [accOff]; omega))
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.crt.outApart) (by decide)
  refine ⟨?_, ?_, by rw [u₂.mem, u₁.mem]; exact Ft, (Kt.trans (u₁.keeps.mono (by decide))).trans (u₂.keeps.mono (by decide))⟩
  · intro fitv
    rw [u₂.mem, u₁.mem, V, srcAddr, m₂]
    have eq : (s.mem.read (off base (lo len (.slot .wide 19))) (4 * cwc len .wide)).toNat =
        val32 s.mem base (lo len (.slot .wide 19)) (cwc len .wide) := read_eq_val32 _ _ _ _
    rw [VG.Proof.Bignum.read_prefix_value s.mem _ (by omega : len ≤ 4 * cwc len .wide) (by rw [eq]; exact fitv), eq]
  · rw [u₂.gpr, u₁.gpr, acc]; rfl

end

end VG.Proof.Bignum.X86.CrtRt
