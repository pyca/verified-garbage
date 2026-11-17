module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding

/-! ### `Bignum.X86.CrtRt.Load`, which this module and modules that import it used -/

section

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
  obtain ce := cb_eq (len := len) N
  obtain srcLen : L < 2 ^ 32 := by omega_arith
  let dst := v.gpr .ebx
  obtain dstAddr : byteAddr dst = off base (lo len x) := byteAddr_ptr pv (by omega_arith)
  obtain dstNat : dst.toNat = base.toNat + lo len x := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega_arith)]
  obtain vw : InRegions v.wr (byteAddr dst) L := by
    rw [dstAddr]; exact h.scratch.write (by omega_arith)
  obtain hsub : Region.Sub ⟨off base (lo len x), L⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len x) (n := L) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_arith)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain hd : Region.Disjoint ⟨byteAddr P, L⟩ ⟨off base (lo len x), L⟩ := apart.sub_right hsub
  obtain ctx := reverseCtx_of_regions v P dst srcLen fit (by omega_arith) rd vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v ctx (by omega_arith) esi rfl ecx) fun t I => ?_
  obtain Ot : Outside base (lo len x) (cb len n) v.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    obtain ek : ofs base a = lo len x + k := by
      rw [he, byteAddr_add (by omega_arith), dstAddr]
      exact ofs_off base (by omega_arith)
    omega_arith
  obtain padding : ∀ k, L ≤ k → k < cb len n → t.mem (off base (lo len x) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_]
    · exact byte_zero_of_val32 Z (by omega_arith)
    · intro i hi he
      rw [byteAddr_add (by omega_arith), dstAddr] at he
      obtain e := congrArg (fun a => (a - off base (lo len x)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega_arith : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega_arith : i < 2 ^ 64)] at e
      omega_arith
  refine ⟨?_, Ot, I.rest.mono (by decide)⟩
  obtain value := I.os2ip fit (by omega_arith : dst.toNat + L ≤ 2 ^ 32)
  rw [dstAddr] at value
  rw [← read_eq_val32]
  obtain ext := val32_zero_extension t.mem (off base (lo len x)) (n := cw len n) (by omega_arith : L ≤ 4 * cw len n)
    (by intro k hk hkn; exact padding k hk (by omega_arith))
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
  obtain ce := cb_eq (len := len) N
  unfold load
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, Z, K⟩ => ?_)
  obtain Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega_arith)
  obtain hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_)
  obtain hv := hu.regs Kv mv
  refine wp_movS (hv.arg hp) fun v₁ u₁ _ => ?_
  obtain hv₁ := hv.regs u₁.keeps u₁.mem
  refine wp_movS (hv₁.arg hl) fun v₂ u₂ _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  obtain K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  obtain m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  obtain ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hlen]
  obtain ebx₄ : v₄.gpr .ebx = v.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (L - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, hlen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  obtain keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  obtain hv₄ : In Ex base bytes len args v₄ := hv.regs K₄ (by rw [m₄, mv])
  obtain vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) L := by rw [keep.2.1, keep.2.2]; exact rd
  obtain Ov : Outside base (lo len x) (cb len n) s.mem v₄.mem := by rw [m₄]; exact O
  obtain input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) L = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega_arith) apart
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
  obtain ce := cb_eq (len := len) N
  obtain srcLen : L < 2 ^ 32 := by omega_arith
  let dst := v.gpr .ebx
  obtain dstAddr : byteAddr dst = off base (lo len x + d) := byteAddr_ptr pv (by omega_arith)
  obtain dstNat : dst.toNat = base.toNat + (lo len x + d) := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega_arith)]
  obtain vw : InRegions v.wr (byteAddr dst) L := by
    rw [dstAddr]; exact h.scratch.write (by omega_arith)
  obtain hsub : Region.Sub ⟨off base (lo len x + d), L⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := lo len x + d) (n := L) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_arith)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain hdj : Region.Disjoint ⟨byteAddr P, L⟩ ⟨off base (lo len x + d), L⟩ := apart.sub_right hsub
  obtain ctx := reverseCtx_of_regions v P dst srcLen fit (by omega_arith) rd vw (by rw [dstAddr]; exact hdj)
  refine WP.mono (reverseBytes_ok v ctx (by omega_arith) esi rfl ecx) fun t I => ?_
  obtain Ot : Outside base (lo len x) (cb len n) v.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    obtain ek : ofs base a = lo len x + d + k := by
      rw [he, byteAddr_add (by omega_arith), dstAddr]
      exact ofs_off base (by omega_arith)
    omega_arith
  obtain low : ∀ k < d, t.mem (off base (lo len x) + BitVec.ofNat 64 k) = 0 := by
    intro k hk
    rw [I.outside _ ?_]
    · exact byte_zero_of_val32 Z (by omega_arith)
    · intro i hi he
      obtain e2 : off base (lo len x + d) = off base (lo len x) + BitVec.ofNat 64 d := by
        simp only [off]; rw [Offset.add_add]
      rw [byteAddr_add (by omega_arith), dstAddr, e2, Offset.add_add (off base (lo len x)) d i] at he
      obtain e := congrArg (fun a => (a - off base (lo len x)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega_arith : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega_arith : d + i < 2 ^ 64)] at e
      omega_arith
  refine ⟨?_, Ot, I.rest.mono (by decide)⟩
  obtain value := I.os2ip fit (by omega_arith : dst.toNat + L ≤ 2 ^ 32)
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
  obtain ce := cb_eq (len := len) N
  unfold loadTop
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, Z, K⟩ => ?_)
  obtain Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega_arith)
  obtain hu := h.keep K (by decide) (by decide) Ou
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_arith)
    fun v Kv mv pv => ?_)
  obtain hv := hu.regs Kv mv
  refine cntTo_ok (r := .edx) hv.width h.upper' N.extra fun w Kw mw ew => ?_
  obtain hw := hv.regs Kw mw
  refine wp_addS rfl fun w₁ a₁ _ => ?_
  obtain hw₁ := hw.regs a₁.keeps a₁.mem
  refine wp_movS (hw₁.arg hl) fun w₂ a₂ _ => wp_subS rfl fun w₃ a₃ _ => ?_
  obtain hw₃ := (hw₁.regs a₂.keeps a₂.mem).regs a₃.keeps a₃.mem
  refine wp_movS (hw₃.arg hp) fun v₁ u₁ _ => wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  obtain K₄ : Keeps [.ebx, .ecx, .esi, .edx] v v₄ :=
    ((((((Kw.mono (by decide)).trans (a₁.keeps.mono (by decide))).trans (a₂.keeps.mono (by decide))).trans
      (a₃.keeps.mono (by decide))).trans (u₁.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  obtain m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₁.mem, a₃.mem, a₂.mem, a₁.mem, mw, mv]
  obtain ecx₃ : w₃.gpr .ecx = BitVec.ofNat 32 L := by rw [a₃.other _ (by decide), a₂.gpr, hlen]
  obtain ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide), ecx₃]
  obtain ebx₄ : v₄.gpr .ebx = v.gpr .ebx + BitVec.ofNat 32 (cb len n) - BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide), a₃.gpr, a₂.other _ (by decide),
      a₂.gpr, a₁.gpr, ew, Kw.1 _ (by decide), hlen]
  obtain esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (L - 1) := by
    rw [u₄.gpr, u₃.gpr, u₁.gpr, u₁.other _ (by decide), ecx₃]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  obtain pv₄ : PtrAt v₄ base .ebx (lo len x + (cb len n - L)) := by
    rw [PtrAt, ebx₄]
    rw [PtrAt] at pv
    rw [BitVec.toNat_sub, BitVec.toNat_add, pv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : cb len n < 2 ^ 32 := by omega_arith
    have : L < 2 ^ 32 := by omega_arith
    rw [Nat.mod_eq_of_lt (a := cb len n) (by omega_arith), Nat.mod_eq_of_lt (a := L) (by omega_arith)]
    omega_arith
  obtain keep : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  obtain hv₄ : In Ex base bytes len args v₄ := hv.regs K₄ (by rw [m₄, mv])
  obtain vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) L := by rw [keep.2.1, keep.2.2]; exact rd
  obtain Ov : Outside base (lo len x) (cb len n) s.mem v₄.mem := by rw [m₄]; exact O
  obtain input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) L = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega_arith) apart
  refine WP.mono (reverseIntoTop_ok hv₄ N hx (by rw [m₄]; exact Z) hL (d := cb len n - L) (by omega_arith) fit vr apart
    pv₄ ecx₄ esi₄) fun t ⟨V, Ot, Kt⟩ => ⟨by rw [V, input], Ov.trans Ot, keep.trans Kt⟩

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # The key's components read

`importComponents_ok`: `n` (wide slot 9, `2 B` bytes), the input (15), `p`
(10), `q` (11), `dP` (12), `dQ` (13) and `qInv` (14), each the number of its
argument's bytes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A wide slot's change keeps the other wide slots. -/
theorem wide_keep (h : In Ex base bytes len args s) {a b n k : Nat} (hb : b ≤ 19) (hab : a ≠ b)
    (hn : n ≤ st len .wide) (hk : 4 * k ≤ st len .wide) {m m' : Mem}
    (O : VG.Proof.Mont.Outside base (lo len (.slot .wide a)) n m m') :
    val32 m' base (lo len (.slot .wide b)) k = val32 m base (lo len (.slot .wide b)) k := by
  obtain f := h.slot_fit .wide (j := 19) (by decide)
  have bl := h.bytes_lt
  obtain hb' := Nat.mul_le_mul_right (st len .wide) hb
  have ea : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have eb : lo len (.slot .wide b) = numBase + b * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  refine O.val32 ?_ (by omega_using [hk, f, bl, hb', eb, e19])
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ b by omega_using [hlt])
    rw [Nat.succ_mul] at this; exact .inr (by omega_using [hn, ea, eb, this])
  · have := Nat.mul_le_mul_right (st len .wide) (show b + 1 ≤ a by omega_using [hlt])
    rw [Nat.succ_mul] at this; exact .inl (by omega_using [hk, ea, eb, this])

/-- A component's bytes into the wide slot `j`. -/
theorem loadComp_ok (h : RIn base bytes len args s) {j : Nat} (hj : j ≤ 19) {n : Cnt} (N : CntOk n)
    (hn : cb len n ≤ st len .wide) (hlen : len ≤ cb len n) {i : Nat} (hi : i ∈ componentArguments) :
    WP isa (load (.slot .wide j) n i (i + 1)) s fun t =>
      val32 t.mem base (lo len (.slot .wide j)) (cw len n) = componentValue s.mem args i ∧
      VG.Proof.Mont.Outside base (lo len (.slot .wide j)) (cb len n) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain f := h.slot_fit .wide (j := j) (by omega_using [hj])
  obtain hi18 : i + 1 < 18 := by
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  obtain pos := h.crt.positive i hi
  obtain bnd := h.crt.bounded i hi
  exact load_ok h N (by omega_using [hn, f]) (p := i) (l := i + 1) (L := (args (i + 1)).toNat) (by omega_using [hi18]) hi18
    (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (args (i + 1)).isLt]))
    pos (by omega_using [hlen, bnd]) (h.crt.fits i hi) (h.crt.readable i hi) (h.crt.apart i hi)

/-- The key's components read into the wide slots 9 to 15. -/
theorem importComponents_ok (h : RIn base bytes len args s) :
    WP isa importComponents s fun u =>
      VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = componentValue s.mem args 2 ∧
      val32 u.mem base (lo len (.slot .wide 15)) (2 * cwc len .wide) = componentValue s.mem args 4 ∧
      val32 u.mem base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue s.mem args 6 ∧
      val32 u.mem base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue s.mem args 8 ∧
      val32 u.mem base (lo len (.slot .wide 12)) (cwc len .wide) = componentValue s.mem args 10 ∧
      val32 u.mem base (lo len (.slot .wide 13)) (cwc len .wide) = componentValue s.mem args 12 ∧
      val32 u.mem base (lo len (.slot .wide 14)) (2 * cwc len .wide) = componentValue s.mem args 14 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  obtain f := h.slot_fit .wide (j := 19) (by decide)
  have bl := h.bytes_lt
  obtain bw := bc_eq_cwc len .wide
  obtain lb := len_le_bc len
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  obtain cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  obtain cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  obtain cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  obtain cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_using [bw]
  obtain n1 : cb len (one .wide) ≤ st len .wide := by rw [cb1]; omega_using [est]
  obtain n2 : cb len (two .wide) ≤ st len .wide := by rw [cb2]; omega_using [est]
  obtain l1 : len ≤ cb len (one .wide) := by rw [cb1]; omega_using [lb]
  obtain l2 : len ≤ cb len (two .wide) := by rw [cb2]; omega_using [lb]
  obtain k1 : 4 * cwc len .wide ≤ st len .wide := by omega_using [bw, est]
  obtain k2 : 4 * (2 * cwc len .wide) ≤ st len .wide := by omega_using [f, bl, bw, lb, est, e19, cb1, cb2, n1, n2, l1, l2, k1]
  -- An import's slot within the wide slots 9 to 15.
  obtain within : ∀ {j : Nat} {m m' : Mem}, 9 ≤ j → j ≤ 15 → ∀ {n : Nat}, n ≤ st len .wide →
      VG.Proof.Mont.Outside base (lo len (.slot .wide j)) n m m' → VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) m m' :=
    fun {j} {_ _} hj9 hj {_} hn O => O.mono
      (by have := Nat.mul_le_mul_right (st len .wide) hj9; show _ ≤ numBase + j * st len .wide; omega_using [e9, this])
      (by have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 16 by omega_using [hj]); rw [Nat.succ_mul] at this
          show numBase + j * st len .wide + _ ≤ _; omega_using [e9, hn, this])
  -- The components' bytes, outside the working space.
  obtain cv : ∀ {m : Mem}, VG.Proof.Mont.Outside base 0 bytes s.mem m → ∀ {i}, i ∈ componentArguments →
      componentValue m args i = componentValue s.mem args i := fun O i hi => by
    unfold componentValue
    rw [VG.Proof.Bignum.scratch_bytes O (by have := (args (i + 1)).isLt; omega_using []) (h.crt.apart i hi)]
  obtain wide : ∀ {t : State} {m m' : Mem}, VG.Proof.Mont.Outside base (lo len (.slot .wide 9)) (7 * st len .wide) m m' →
      VG.Proof.Mont.Outside base 0 bytes m m' := fun O => O.mono (Nat.zero_le _) (by omega_using [f, bl, bw, lb, est, e9, e19, cb1, cb2, n1, n2, l1, l2, k1, k2])
  unfold importComponents
  refine WP.seq (WP.mono (loadComp_ok h (j := 9) (by decide) (two_ok .wide) n2 l2 (i := 2) (by decide))
    fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  obtain O₁' := within (by decide) (by decide) n2 O₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (wide (t := s) O₁')
  refine WP.seq (WP.mono (loadComp_ok h₁ (j := 15) (by decide) (two_ok .wide) n2 l2 (i := 4) (by decide))
    fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  obtain O₂' := O₁'.trans (within (by decide) (by decide) n2 O₂)
  obtain h₂ := h.keep (K₁.trans K₂) (by decide) (by decide) (wide (t := s) O₂')
  refine WP.seq (WP.mono (loadComp_ok h₂ (j := 10) (by decide) (one_ok .wide) n1 l1 (i := 6) (by decide))
    fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  obtain O₃' := O₂'.trans (within (by decide) (by decide) n1 O₃)
  obtain h₃ := h.keep ((K₁.trans K₂).trans K₃) (by decide) (by decide) (wide (t := s) O₃')
  refine WP.seq (WP.mono (loadComp_ok h₃ (j := 11) (by decide) (one_ok .wide) n1 l1 (i := 8) (by decide))
    fun u₄ ⟨V₄, O₄, K₄⟩ => ?_)
  obtain O₄' := O₃'.trans (within (by decide) (by decide) n1 O₄)
  obtain h₄ := h.keep (((K₁.trans K₂).trans K₃).trans K₄) (by decide) (by decide) (wide (t := s) O₄')
  refine WP.seq (WP.mono (loadComp_ok h₄ (j := 12) (by decide) (one_ok .wide) n1 l1 (i := 10) (by decide))
    fun u₅ ⟨V₅, O₅, K₅⟩ => ?_)
  obtain O₅' := O₄'.trans (within (by decide) (by decide) n1 O₅)
  obtain h₅ := h.keep ((((K₁.trans K₂).trans K₃).trans K₄).trans K₅) (by decide) (by decide) (wide (t := s) O₅')
  refine WP.seq (WP.mono (loadComp_ok h₅ (j := 13) (by decide) (one_ok .wide) n1 l1 (i := 12) (by decide))
    fun u₆ ⟨V₆, O₆, K₆⟩ => ?_)
  obtain O₆' := O₅'.trans (within (by decide) (by decide) n1 O₆)
  obtain h₆ := h.keep (((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆) (by decide) (by decide)
    (wide (t := s) O₆')
  refine WP.mono (loadComp_ok h₆ (j := 14) (by decide) (two_ok .wide) n2 l2 (i := 14) (by decide))
    fun u ⟨V₇, O₇, K₇⟩ => ?_
  obtain O₇' := O₆'.trans (within (by decide) (by decide) n2 O₇)
  rw [cw2] at V₁ V₂ V₇
  rw [cw1] at V₃ V₄ V₅ V₆
  rw [cv (wide (t := s) O₁') (by decide)] at V₂
  rw [cv (wide (t := s) O₂') (by decide)] at V₃
  rw [cv (wide (t := s) O₃') (by decide)] at V₄
  rw [cv (wide (t := s) O₄') (by decide)] at V₅
  rw [cv (wide (t := s) O₅') (by decide)] at V₆
  rw [cv (wide (t := s) O₆') (by decide)] at V₇
  obtain kw : ∀ {a b k : Nat} {m m' : Mem}, a ≤ 19 → b ≤ 19 → a ≠ b → 4 * k ≤ st len .wide →
      VG.Proof.Mont.Outside base (lo len (.slot .wide a)) (cb len (one .wide)) m m' →
      val32 m' base (lo len (.slot .wide b)) k = val32 m base (lo len (.slot .wide b)) k :=
    fun _ hb hab hk O => wide_keep h hb hab n1 hk O
  obtain kw2 : ∀ {a b k : Nat} {m m' : Mem}, a ≤ 19 → b ≤ 19 → a ≠ b → 4 * k ≤ st len .wide →
      VG.Proof.Mont.Outside base (lo len (.slot .wide a)) (cb len (two .wide)) m m' →
      val32 m' base (lo len (.slot .wide b)) k = val32 m base (lo len (.slot .wide b)) k :=
    fun _ hb hab hk O => wide_keep h hb hab n2 hk O
  refine ⟨O₇', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ((((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆).trans K₇)⟩
  · rw [kw2 (by decide) (by decide) (by decide) k2 O₇, kw (by decide) (by decide) (by decide) k2 O₆,
      kw (by decide) (by decide) (by decide) k2 O₅, kw (by decide) (by decide) (by decide) k2 O₄,
      kw (by decide) (by decide) (by decide) k2 O₃, kw2 (by decide) (by decide) (by decide) k2 O₂, V₁]
  · rw [kw2 (by decide) (by decide) (by decide) k2 O₇, kw (by decide) (by decide) (by decide) k2 O₆,
      kw (by decide) (by decide) (by decide) k2 O₅, kw (by decide) (by decide) (by decide) k2 O₄,
      kw (by decide) (by decide) (by decide) k2 O₃, V₂]
  · rw [kw2 (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆,
      kw (by decide) (by decide) (by decide) k1 O₅, kw (by decide) (by decide) (by decide) k1 O₄, V₃]
  · rw [kw2 (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆,
      kw (by decide) (by decide) (by decide) k1 O₅, V₄]
  · rw [kw2 (by decide) (by decide) (by decide) k1 O₇, kw (by decide) (by decide) (by decide) k1 O₆, V₅]
  · rw [kw2 (by decide) (by decide) (by decide) k1 O₇, V₆]
  · exact V₇

end

end VG.Proof.Bignum.X86.CrtRt
