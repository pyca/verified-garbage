module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
public import VerifiedGarbage.Proof.Bignum.ReadPrefix
public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Loops
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Reduce
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Rt.Blocks
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
public import VerifiedGarbage.Proof.Mont.X86.Rt.Front
public import VerifiedGarbage.Proof.Mont.X86.Rt.Row
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Rt.Rows
public import VerifiedGarbage.Proof.Mont.X86.Rt.Save
public import VerifiedGarbage.Proof.Mont.X86.Rt.Stages
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Rt.Zero

/-! # The import of big-endian bytes in private CRT at a run-time width

`load x n p l` zeroes the number at `x`, then reverses the bytes of argument
`p`, as many as argument `l`, into it (`load_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (byteAddr_ptr)
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem load_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In base bytes len args s) {x : Loc} {n : Cnt} (N : CntOk n) (hx : lo len x + cb len n ≤ bytes)
    {p l L : Nat} (hp : p < 18) (hl : l < 18)
    (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLc : L ≤ cb len n) (fit : (args p).toNat + L ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (load x n p l) s fun t =>
      val32 t.mem base (lo len x) (cw len n) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
      Outside base (lo len x) (cb len n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.crt.scratch.nowrap
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  have srcLen : L < 2 ^ 32 := by omega
  unfold load
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, Z, K⟩ => ?_)
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
  have hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega)
    fun v Kv mv pv => ?_)
  have hv := hu.regs Kv mv
  refine wp_movS (hv.arg hp) fun v₁ u₁ _ => ?_
  have hv₁ := hv.regs u₁.keeps u₁.mem
  refine wp_movS (hv₁.arg hl) fun v₂ u₂ _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off base (lo len x) := byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = base.toNat + lo len x := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hlen]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (L - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, hlen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) L := by rw [keep.2.1, keep.2.2]; exact rd
  have vw : InRegions v₄.wr (byteAddr dst) L := by
    rw [keep.2.2, dstAddr]; exact h.crt.scratch.write (by omega)
  have hsub : Region.Sub ⟨off base (lo len x), L⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len x) (n := L) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hd : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨off base (lo len x), L⟩ := apart.sub_right hsub
  have ctx := reverseCtx_of_regions v₄ (args p) dst srcLen fit (by omega) vr vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside base (lo len x) (cb len n) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = lo len x + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have Ov : Outside base (lo len x) (cb len n) s.mem v₄.mem := by rw [m₄]; exact O
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) L = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega) apart
  have padding : ∀ k, L ≤ k → k < cb len n → t.mem (off base (lo len x) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 Z (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off base (lo len x)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  refine ⟨?_, Ov.trans Ot, keep.trans (I.rest.mono (by decide))⟩
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base (lo len x)) (n := cw len n) (by omega : L ≤ 4 * cw len n)
    (by intro k hk hkn; exact padding k hk (by omega))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Bignum.X86.CrtRt
