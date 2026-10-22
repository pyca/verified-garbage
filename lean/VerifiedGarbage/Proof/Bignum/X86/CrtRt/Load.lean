module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding

/-! # The import of big-endian bytes in private CRT at a run-time width

`load x n p l` zeroes the number at `x`, then reverses the bytes of argument
`p`, as many as argument `l`, into it (`load_ok`); `loadTop` into its top
bytes, the bytes' value times `256^(cb − l)` (`loadTop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (byteAddr_ptr)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The `L` bytes at `P` reversed into the zeroed number at `x`, from its address in `ebx`, `L` in
`ecx` and the address of the last byte in `esi`. -/
theorem reverseInto_ok {v : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args v) {x : Loc} {n : Cnt} (N : CntOk n) (hx : lo len x + cb len n ≤ bytes)
    (Z : val32 v.mem base (lo len x) (cw len n) = 0) {P : BitVec 32} {L : Nat} (hL : 0 < L)
    (hLc : L ≤ cb len n) (fit : P.toNat + L ≤ 2 ^ 32) (rd : InRegions (v.rd ++ v.wr) (byteAddr P) L)
    (apart : Region.Disjoint ⟨byteAddr P, L⟩ ⟨base, bytes⟩) (pv : PtrAt v base .ebx (lo len x))
    (ecx : v.gpr .ecx = BitVec.ofNat 32 L) (esi : v.gpr .esi = P + BitVec.ofNat 32 (L - 1)) :
    WP isa reverseBytes v fun t =>
      val32 t.mem base (lo len x) (cw len n) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (byteAddr P) L) ∧
      Outside base (lo len x) (cb len n) v.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] v t := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  have srcLen : L < 2 ^ 32 := by omega
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off base (lo len x) := byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = base.toNat + lo len x := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have vw : InRegions v.wr (byteAddr dst) L := by
    rw [dstAddr]; exact h.scratch.write (by omega)
  have hsub : Region.Sub ⟨off base (lo len x), L⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len x) (n := L) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hd : Region.Disjoint ⟨byteAddr P, L⟩ ⟨off base (lo len x), L⟩ := apart.sub_right hsub
  have ctx := reverseCtx_of_regions v P dst srcLen fit (by omega) rd vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v ctx (by omega) esi rfl ecx) fun t I => ?_
  have Ot : Outside base (lo len x) (cb len n) v.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = lo len x + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have padding : ∀ k, L ≤ k → k < cb len n → t.mem (off base (lo len x) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_]
    · exact byte_zero_of_val32 Z (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off base (lo len x)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  refine ⟨?_, Ot, I.rest.mono (by decide)⟩
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr] at value
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base (lo len x)) (n := cw len n) (by omega : L ≤ 4 * cw len n)
    (by intro k hk hkn; exact padding k hk (by omega))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

theorem load_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) {x : Loc} {n : Cnt} (N : CntOk n) (hx : lo len x + cb len n ≤ bytes)
    {p l L : Nat} (hp : p < 18) (hl : l < 18)
    (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLc : L ≤ cb len n) (fit : (args p).toNat + L ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (load x n p l) s fun t =>
      val32 t.mem base (lo len x) (cw len n) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
      Outside base (lo len x) (cb len n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
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
  have K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hlen]
  have ebx₄ : v₄.gpr .ebx = v.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (L - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, hlen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have hv₄ : In Ex base bytes len args v₄ := hv.regs K₄ (by rw [m₄, mv])
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) L := by rw [keep.2.1, keep.2.2]; exact rd
  have Ov : Outside base (lo len x) (cb len n) s.mem v₄.mem := by rw [m₄]; exact O
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) L = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega) apart
  refine WP.mono (reverseInto_ok hv₄ N hx (by rw [m₄]; exact Z) hL hLc fit vr apart
    (by rw [PtrAt, ebx₄]; exact pv) ecx₄ esi₄) fun t ⟨V, Ot, Kt⟩ => ⟨by rw [V, input], Ov.trans Ot, keep.trans Kt⟩

/-- The `L` bytes at `P` reversed into the top `L` bytes of the zeroed number at `x`, from the address
of its byte `d = cb − L` in `ebx`: the bytes' value times `2^(8 d)`. -/
theorem reverseIntoTop_ok {v : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args v) {x : Loc} {n : Cnt} (N : CntOk n) (hx : lo len x + cb len n ≤ bytes)
    (Z : val32 v.mem base (lo len x) (cw len n) = 0) {P : BitVec 32} {L d : Nat} (hL : 0 < L)
    (hd : d + L = cb len n) (fit : P.toNat + L ≤ 2 ^ 32) (rd : InRegions (v.rd ++ v.wr) (byteAddr P) L)
    (apart : Region.Disjoint ⟨byteAddr P, L⟩ ⟨base, bytes⟩) (pv : PtrAt v base .ebx (lo len x + d))
    (ecx : v.gpr .ecx = BitVec.ofNat 32 L) (esi : v.gpr .esi = P + BitVec.ofNat 32 (L - 1)) :
    WP isa reverseBytes v fun t =>
      val32 t.mem base (lo len x) (cw len n) =
        2 ^ (8 * d) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (byteAddr P) L) ∧
      Outside base (lo len x) (cb len n) v.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] v t := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  have srcLen : L < 2 ^ 32 := by omega
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off base (lo len x + d) := byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = base.toNat + (lo len x + d) := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have vw : InRegions v.wr (byteAddr dst) L := by
    rw [dstAddr]; exact h.scratch.write (by omega)
  have hsub : Region.Sub ⟨off base (lo len x + d), L⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len x + d) (n := L) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hdj : Region.Disjoint ⟨byteAddr P, L⟩ ⟨off base (lo len x + d), L⟩ := apart.sub_right hsub
  have ctx := reverseCtx_of_regions v P dst srcLen fit (by omega) rd vw (by rw [dstAddr]; exact hdj)
  refine WP.mono (reverseBytes_ok v ctx (by omega) esi rfl ecx) fun t I => ?_
  have Ot : Outside base (lo len x) (cb len n) v.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = lo len x + d + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have low : ∀ k < d, t.mem (off base (lo len x) + BitVec.ofNat 64 k) = 0 := by
    intro k hk
    rw [I.outside _ ?_]
    · exact byte_zero_of_val32 Z (by omega)
    · intro i hi he
      have e2 : off base (lo len x + d) = off base (lo len x) + BitVec.ofNat 64 d := by
        simp only [off]; rw [Offset.add_add]
      rw [byteAddr_add (by omega), dstAddr, e2, Offset.add_add (off base (lo len x)) d i] at he
      have e := congrArg (fun a => (a - off base (lo len x)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : d + i < 2 ^ 64)] at e
      omega
  refine ⟨?_, Ot, I.rest.mono (by decide)⟩
  have value := I.os2ip fit (by omega : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr] at value
  rw [← read_eq_val32, ← ce, ← hd, Nat.add_comm d L, read_toNat_add,
    read_zero_bytes _ _ _ low, Nat.zero_add, Offset.add_add, value]

theorem loadTop_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) {x : Loc} {n : Cnt} (N : CntOk n) (hx : lo len x + cb len n ≤ bytes)
    {p l L : Nat} (hp : p < 18) (hl : l < 18)
    (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLc : L ≤ cb len n) (fit : (args p).toNat + L ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (loadTop x n p l) s fun t =>
      val32 t.mem base (lo len x) (cw len n) =
        2 ^ (8 * (cb len n - L)) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
      Outside base (lo len x) (cb len n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have ce := cb_eq (len := len) N
  unfold loadTop
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, Z, K⟩ => ?_)
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
  have hu := h.keep K (by decide) (by decide) Ou
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega)
    fun v Kv mv pv => ?_)
  have hv := hu.regs Kv mv
  refine cntTo_ok (r := .edx) hv.width h.upper' N.extra fun w Kw mw ew => ?_
  have hw := hv.regs Kw mw
  refine wp_addS rfl fun w₁ a₁ _ => ?_
  have hw₁ := hw.regs a₁.keeps a₁.mem
  refine wp_movS (hw₁.arg hl) fun w₂ a₂ _ => wp_subS rfl fun w₃ a₃ _ => ?_
  have hw₃ := (hw₁.regs a₂.keeps a₂.mem).regs a₃.keeps a₃.mem
  refine wp_movS (hw₃.arg hp) fun v₁ u₁ _ => wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  have K₄ : Keeps [.ebx, .ecx, .esi, .edx] v v₄ :=
    ((((((Kw.mono (by decide)).trans (a₁.keeps.mono (by decide))).trans (a₂.keeps.mono (by decide))).trans
      (a₃.keeps.mono (by decide))).trans (u₁.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₁.mem, a₃.mem, a₂.mem, a₁.mem, mw, mv]
  have ecx₃ : w₃.gpr .ecx = BitVec.ofNat 32 L := by rw [a₃.other _ (by decide), a₂.gpr, hlen]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide), ecx₃]
  have ebx₄ : v₄.gpr .ebx = v.gpr .ebx + BitVec.ofNat 32 (cb len n) - BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide), a₃.gpr, a₂.other _ (by decide),
      a₂.gpr, a₁.gpr, ew, Kw.1 _ (by decide), hlen]
  have esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (L - 1) := by
    rw [u₄.gpr, u₃.gpr, u₁.gpr, u₁.other _ (by decide), ecx₃]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have pv₄ : PtrAt v₄ base .ebx (lo len x + (cb len n - L)) := by
    rw [PtrAt, ebx₄]
    rw [PtrAt] at pv
    rw [BitVec.toNat_sub, BitVec.toNat_add, pv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : cb len n < 2 ^ 32 := by omega
    have : L < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt (a := cb len n) (by omega), Nat.mod_eq_of_lt (a := L) (by omega)]
    omega
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have hv₄ : In Ex base bytes len args v₄ := hv.regs K₄ (by rw [m₄, mv])
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) L := by rw [keep.2.1, keep.2.2]; exact rd
  have Ov : Outside base (lo len x) (cb len n) s.mem v₄.mem := by rw [m₄]; exact O
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) L = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega) apart
  refine WP.mono (reverseIntoTop_ok hv₄ N hx (by rw [m₄]; exact Z) hL (d := cb len n - L) (by omega) fit vr apart
    pv₄ ecx₄ esi₄) fun t ⟨V, Ot, Kt⟩ => ⟨by rw [V, input], Ov.trans Ot, keep.trans Kt⟩

end VG.Proof.Bignum.X86.CrtRt
