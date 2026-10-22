module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProductArgs
public import VerifiedGarbage.Proof.MillerRabin.X86.Inverse
import VerifiedGarbage.Proof.Framework.Offset

/-! # The i686 round reuses the existing runtime Montgomery callable -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Bignum.X86.RtCall (Offs)

theorem product_offsets {w bytes o a b : Nat}
    (hw : 4 ≤ w) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28) :
    Offs bytes w 256 56 (scratch w) (arrAt w o) (arrAt w a) (arrAt w b) := by
  have fm := array_fits_bytes hf (show 0 < 28 by decide)
  have fo := array_fits_bytes hf ho.2
  have fa := array_fits_bytes hf ha.2
  have fb := array_fits_bytes hf hb.2
  have sc := scratch_end w
  have sc5 := array_monotone w (show 5 ≤ 28 by decide)
  refine ⟨by omega, ?_, ?_, by omega, by omega, by omega, by omega,
    ?_, inverse_apart_scratch w,
    operand_apart_scratch w ho.1, operand_apart_scratch w ha.1, operand_apart_scratch w hb.1,
    ?_, operand_apart_inverse w ho.1⟩
  · simpa only [arrAt, VG.Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] using
      (show arrAt w 0 + 8 * w ≤ bytes by omega)
  · simp only [arrAt, VG.Spec.Rsa.Mont.hdrBytes] at fm
    omega
  · simpa only [arrAt, VG.Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] using
      modulus_apart_scratch w
  · simpa only [arrAt, VG.Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] using
      operand_apart_modulus w ho.1

theorem product_body_noSp (o a b : Nat) :
    NoSp (.seq (.block (productArgs o a b))
      (.call Spec.Rsa.MontMul.mulApi.name VG.Impl.Mont.X86.Rt.body) : Prog isa) := by
  apply NoSp.of_all
  have hc : (instrs VG.Impl.Mont.X86.Rt.body).all (fun i => !Taint.clobbers i .esp) = true := by
    simpa only [← Code.allInstrs_eq] using
      (by decide : VG.Impl.Mont.X86.Rt.body.allInstrs (fun i => !Taint.clobbers i .esp) = true)
  rw [Code.allInstrs_eq]
  simp only [instrs, productArgs, scratchOffset, width, arrayOffset, List.all_append,
    List.all_cons, List.all_nil, List.all_replicate, hc]
  simp [Taint.clobbers, Taint.dst]

/-- Allocation adds permissions but preserves already readable source words. -/
theorem read_alloc {s : State} {m m' : MemOp} {v : BitVec 32} {bytes : Nat}
    (ea : (allocFrame bytes s).ea m' = s.ea m) (hr : readSrc s (.mem m) = some v) :
    readSrc (allocFrame bytes s) (.mem m') = some v := by
  simp only [readSrc, State.load32] at hr ⊢
  rw [ea, allocFrame_mem]
  split at hr
  · rename_i rd
    rw [ite_eq_left ?_]
    · exact hr
    obtain ⟨r, hr, hc⟩ := rd
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, hc⟩
    · exact ⟨r, List.mem_append_right _ (by rw [allocFrame_wr]; exact List.mem_cons_of_mem _ hr), hc⟩
  · cases hr

theorem product_setup_ok {s : State} {base : Addr} {bytes w o a b : Nat} {wsLen : BitVec 32}
    (scr : Scr s base bytes) (R : CallRoom (s.gpr .esp) base bytes)
    (frameFit : (s.gpr .esp).toNat + VG.Impl.MillerRabin.X86.frameBytes ≤ 2 ^ 32)
    (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (width : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (length : readSrc s (.mem (sp savedLength)) = some wsLen) :
    let f := allocFrame 36 s
    WP isa (.block (productArgs o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        VG.Proof.Bignum.X86.RtCall.callArg (f.gpr .edi) wsLen w 256 56 (scratch w)
          (arrAt w o) (arrAt w a) (arrAt w b) i := by
  have low := R.low
  have h52 : 52 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  have hsp : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [allocFrame_esp, sub_toNat (by omega)]
  apply productArgs_ok hu
  · apply read_alloc (m := sc 48)
      (by simp only [State.ea, sc, at_, allocFrame_gpr (q := .edi) _ _ (by decide)])
    rw [readSrc_sc scr h52, width]
  · apply read_alloc (m := sp savedLength) ?_ length
    simp only [State.ea, sp, at_, allocFrame_esp]
    congr 1
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    congr 1
  · have ea : (allocFrame 36 s).ea (sc 48) = off base 48 := by
      simpa only [State.ea, sc, at_, allocFrame_gpr (q := .edi) _ _ (by decide)] using scr.ea (d := 48) (by omega)
    rw [ea, allocFrame_esp]
    exact (R.apart.symm.sub_left (Offset.sub_base _ (by omega : 48 + 4 ≤ bytes))).sub_right
      (below_sub (by decide) low)
  · have ea : (allocFrame 36 s).ea (sp (36 + savedLength)) =
        ((allocFrame 36 s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (36 + savedLength) := by
      exact addr_eq (by
        change ((allocFrame 36 s).gpr .esp).toNat + (36 + savedLength) < 2 ^ 32
        rw [hsp]
        simp only [VG.Impl.MillerRabin.X86.frameBytes, savedLength] at frameFit ⊢
        omega)
    rw [ea]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [hsp]
    have := (s.gpr .esp).isLt
    omega
  · rw [allocFrame_wr]
    exact List.mem_cons_self ..

theorem product_ok {s : State} {base : Addr} {bytes w o a b : Nat} {wsLen : BitVec 32}
    (scr : Scr s base bytes) (size : bytes = wsLen.toNat * 8)
    (R : CallRoom (s.gpr .esp) base bytes)
    (frameFit : (s.gpr .esp).toNat + VG.Impl.MillerRabin.X86.frameBytes ≤ 2 ^ 32)
    (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (width : s.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (length : readSrc s (.mem (sp savedLength)) = some wsLen)
    (inverse : (val32 s.mem base 256 (2 * w) * w32 s.mem base 56 + 1) % 2 ^ 32 = 0)
    (bLt : val32 s.mem base (arrAt w b) (2 * w) < val32 s.mem base 256 (2 * w)) :
    WP isa (product o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (arrAt w o), 8 * w⟩, ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
        below (s.gpr .esp) 40] s.mem t.mem ∧
      val32 t.mem base (arrAt w o) (2 * w) < val32 s.mem base 256 (2 * w) ∧
      val32 t.mem base (arrAt w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem base 256 (2 * w) =
        val32 s.mem base (arrAt w a) (2 * w) * val32 s.mem base (arrAt w b) (2 * w) %
          val32 s.mem base 256 (2 * w) := by
  apply VG.Proof.Bignum.X86.RtCall.call_ok scr size R (product_offsets hw hf ho ha hb) inverse bLt
    (product_body_noSp o a b)
  exact product_setup_ok scr R frameFit hu hf width length

end VG.Proof.MillerRabin.X86
