module

public import VerifiedGarbage.Proof.MillerRabin.X86.ArgsTaintInput
public import VerifiedGarbage.Proof.MillerRabin.X86.Product
public import VerifiedGarbage.Proof.Bignum.X86.RtCallTiming

/-! # Reuse the runtime Montgomery contract at the round's public offsets -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Bignum.X86.RtCall (callArg callee_abi callee_arg)
open VG.Proof.Bignum.X86.PublicRt (calleeOf)

abbrev ProductCall (base : Addr) (bytes w : Nat) (sp len : BitVec 32) (o a b : Nat) :=
  VG.Proof.Bignum.X86.RtCall.CallState base bytes sp
    (callArg (BitVec.ofNat 32 base.toNat) len w 256 56
      (scratch w) (arrAt w o) (arrAt w a) (arrAt w b))

theorem product_call_setup {s : State} {base : Addr} {bytes w o a b : Nat} {sp len : BitVec 32}
    (h : PieceInput base bytes w sp len s) (size : bytes = len.toNat * 8)
    (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (inverse : (val32 s.mem base 256 (2 * w) * w32 s.mem base 56 + 1) % 2 ^ 32 = 0)
    (reduced : val32 s.mem base (arrAt w b) (2 * w) < val32 s.mem base 256 (2 * w)) :
    WP isa (.block (productArgs o a b)) (allocFrame 36 s) (ProductCall base bytes w sp len o a b) := by
  have length : readSrc s (.mem (VG.Impl.MillerRabin.X86.sp savedLength)) = some len := by
    rw [h.context.read_sp (by decide), h.stack, h.length]
  refine WP.mono (product_setup_ok h.context.ws h.room h.context.stackFit hu hf h.width length) ?_
  rintro g ⟨K, frame, read⟩
  have gsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [K.1 _ (by decide), allocFrame_esp]
  have F : Frame [below (s.gpr .esp) 36] s.mem g.mem := frame
  have reads : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) len w 256 56 (scratch w) (arrAt w o) (arrAt w a) (arrAt w b) i := by
    intro i hi
    rw [K.1 .esp (by decide), read i hi, allocFrame_gpr _ _ (by decide)]
  have abi := callee_abi h.context.ws size h.room (product_offsets hw hf ho ha hb) gsp F reads inverse reduced
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [h.context.ws.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := h.context.ws.nowrap; have := h.capacity; omega)]
  refine ⟨abi, by rw [gsp, h.stack], ?_, ?_, ?_⟩
  · intro i hi
    rw [callee_arg h.room.low gsp reads hi, edi]
  · rw [K.2.2, allocFrame_wr, gsp]
    exact List.mem_cons_self
  · rw [K.2.2, allocFrame_wr]
    exact List.mem_cons_of_mem _ h.context.ws.wr

end VG.Proof.MillerRabin.X86
