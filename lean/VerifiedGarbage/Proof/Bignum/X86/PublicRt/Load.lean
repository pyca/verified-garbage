module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Reading a number of public RSA at a run-time width

`load j p l`: number `j` is the big-endian bytes at argument `p`, as many as
argument `l` says (`load_ok`), as `loadBE_ok` at a fixed offset.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- A register holding `W + x`, below `2³²`, as an address. -/
theorem byteAddr_ptr {s : State} {W : Addr} {r : Reg} {x : Nat} (hp : PtrAt s W r x)
    (hx : W.toNat + x < 2 ^ 32) : byteAddr (s.gpr r) = off W x := by
  apply BitVec.eq_of_toNat_eq
  have hW : W.toNat < 2 ^ 64 := W.isLt
  simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp,
    Nat.mod_eq_of_lt (a := W.toNat + x) hx, Nat.mod_eq_of_lt (a := x) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem load_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {j p l : Nat} (hj : j ≤ 7) (hp : p < 10) (hl : l < 10)
    (hlen : args l = BitVec.ofNat 32 len) (fit : (args p).toNat + len ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) len)
    (apart : Region.Disjoint ⟨byteAddr (args p), len⟩ ⟨base, bytes⟩) :
    WP isa (load j p l) s fun t =>
      val32 t.mem base (numAt len j) (nw len) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) len) ∧
      Outside base (numAt len j) (wb len) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .ebp, .esi] s t := by
  have fit' := (h.fits hj).1
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbl := wb_le h.upper
  have wbg := len_le_wb len
  have wbe := wb_eq len
  have hlow := h.lower
  have srcLen : len < 2 ^ 32 := by omega
  unfold load
  refine WP.seq (WP.mono (zero_ok h hj) fun u ⟨O, Z, K⟩ => ?_)
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
  have hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (slotPtr_ok (r := .ebx) (t := .ecx) (by decide) (by decide) hu.edi hu.width h.upper (by omega)
    fun v Kv mv pv _ => ?_)
  have hv := hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv.stack p hp).readSrc fun v₁ u₁ _ => ?_
  have hv₁ := hv.keep u₁.keeps (by decide) (by decide) (by rw [u₁.mem]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv₁.stack l hl).readSrc fun v₂ u₂ _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off base (numAt len j) := byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = base.toNat + numAt len j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 len := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hlen]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (len - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, hlen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) len := by rw [keep.2.1, keep.2.2]; exact rd
  have vw : InRegions v₄.wr (byteAddr dst) len := by
    rw [keep.2.2, dstAddr]; exact h.scratch.write (by omega)
  have hsub : Region.Sub ⟨off base (numAt len j), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := numAt len j) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hd : Region.Disjoint ⟨byteAddr (args p), len⟩ ⟨off base (numAt len j), len⟩ := apart.sub_right hsub
  have ctx := reverseCtx_of_regions v₄ (args p) dst srcLen fit (by omega) vr vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside base (numAt len j) (wb len) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = numAt len j + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have Ov : Outside base (numAt len j) (wb len) s.mem v₄.mem := by rw [m₄]; exact O
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) len :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega) apart
  have padding : ∀ k, len ≤ k → k < wb len → t.mem (off base (numAt len j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 Z (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off base (numAt len j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  refine ⟨?_, Ov.trans Ot, keep.trans (I.rest.mono (by decide))⟩
  have value := I.os2ip fit (by omega : dst.toNat + len ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base (numAt len j)) (n := nw len) (by omega : len ≤ 4 * nw len)
    (by intro k hk hkn; exact padding k hk (by omega))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Bignum.X86.PublicRt
