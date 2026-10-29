module
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
public import VerifiedGarbage.Spec.Ed448.Contract

import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): the bits of `S` and `k`

`vbits_ok`: byte `t` at `BITS` is bit `t` of `S` (the signature's last 57
bytes), and byte `t` at `KBITS` bit `t` of `k` (the challenge), for `t < 456`
(`VBits`), by X448's `bitsLoop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Impl.X448.X86 (BITS at_)
open VG.Impl.Ed448.X86 (KBITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The bits of `S` at `BITS` and those of `K` at `KBITS`, one per byte. -/
def VBits (base : Addr) (S K : Nat) (m : Mem) : Prop :=
  ∀ t < 456, m (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) ∧
    m (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)

/-- `vbits`: the bits of `k` (the challenge, the argument at `[esp + 12]`) at `KBITS`, then those of
`S` (the signature's last 57 bytes, from the argument at `[esp + 8]`) at `BITS`, with `esi` back at
the signature. -/
theorem vbits_ok {s : State} {base : Addr} (hs : Scr s base) {a8 a12 : Addr}
    (ha8 : s.ea (at_ .esp 8) = a8) (hr8 : InRegions (s.rd ++ s.wr) a8 4)
    (ha12 : s.ea (at_ .esp 12) = a12) (hr12 : InRegions (s.rd ++ s.wr) a12 4)
    {sg ch : BitVec 32} (hsg : s.mem.readW a8 32 = sg) (hch : s.mem.readW a12 32 = ch)
    (hfs : sg.toNat + 114 ≤ 2 ^ 32) (hfk : ch.toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ i < 57, InRegions (s.rd ++ s.wr) (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) 1)
    (hkr : ∀ i < 57, InRegions (s.rd ++ s.wr) (ch.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hsd : ∀ i < 57, 8192 ≤ ofs base (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i))
    (hkd : ∀ i < 57, 8192 ≤ ofs base (ch.setWidth 64 + BitVec.ofNat 64 i)) :
    WP isa vbits s fun t =>
      t.gpr .esi = sg ∧ Keeps [.esi, .ebp, .eax, .ecx, .edx, .ebx] s t ∧
      (∃ m, Outside base KBITS 456 s.mem m ∧ Outside base BITS 456 m t.mem) ∧
      VBits base (decodeLE (bytesAt s.mem (sg.setWidth 64 + BitVec.ofNat 64 57) 57))
        (decodeLE (bytesAt s.mem (ch.setWidth 64) 57)) t.mem := by
  have hB : BITS = 3072 := rfl
  have hK : KBITS = 4608 := rfl
  unfold vbits
  refine WP.seq (wp_load ha12 hr12 fun u hu => ?_)
  refine wp_load (a := a8) (by change addr (u.gpr .esp) 8 = _; rw [hu.other _ (by decide)]; exact ha8)
    (by rw [hu.rd, hu.wr]; exact hr8) fun v hv => WP.block_nil ?_
  rw [hu.mem, hsg] at hv
  rw [hch] at hu
  have vs := (hs.of_upd hu (by decide)).of_upd hv (by decide)
  have rv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hv.rd, hv.wr, hu.rd, hu.wr]
  have ve : v.gpr .esi = ch := by rw [hv.other _ (by decide), hu.gpr]
  -- The bits of `k`.
  refine WP.seq (WP.mono (bitsLoop_ok vs (o := KBITS) (n := 57) (by decide) (by decide) (by decide)
    (k := ch.setWidth 64) (by rw [ve]) (by rw [ve]; omega) (by rw [rv]; exact hkr) hkd)
    fun w ⟨wk, wo, wb, _⟩ => ?_)
  have ws := vs.of_keeps wk (by decide)
  have wx : w.gpr .ebx = sg := by rw [wk.1 _ (by decide), hv.gpr]
  -- The bits of `S`.
  refine WP.seq (wp_mov rfl fun x hx => wp_alu (Or.inl rfl) rfl fun y hy _ => WP.block_nil ?_)
  have ys := (ws.of_upd hx (by decide)).of_upd hy (by decide)
  have ye : y.gpr .esi = sg + BitVec.ofNat 32 57 := by
    rw [hy.gpr]; change x.gpr .esi + BitVec.ofNat 32 57 = _; rw [hx.gpr]; change w.gpr .ebx + _ = _; rw [wx]
  have ry : y.rd ++ y.wr = s.rd ++ s.wr := by rw [hy.rd, hy.wr, hx.rd, hx.wr, wk.2.1, wk.2.2, rv]
  have ym : y.mem = w.mem := by rw [hy.mem, hx.mem]
  refine WP.seq (WP.mono (bitsLoop_ok ys (o := BITS) (n := 57) (by decide) (by decide) (by decide)
    (k := sg.setWidth 64 + BitVec.ofNat 64 57)
    (by rw [ye]; exact (addr_eq (x := sg) (k := 57) (by omega) : _))
    (by rw [ye, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rw [ry]; exact hsr) hsd)
    fun z ⟨zk, zo, zb, ze⟩ => ?_)
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun t ht _ =>
    WP.block_nil ⟨?_, ?_, ⟨w.mem, ?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
  · rw [ht.gpr]; change z.gpr .esi - BitVec.ofNat 32 114 = _
    rw [ze, ye, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · refine (hu.rest (by decide)).trans ((hv.rest (by decide)).trans ((wk.mono (by simp [bitRegs])).trans
      ((hx.rest (by decide)).trans ((hy.rest (by decide)).trans ((zk.mono (by simp [bitRegs])).trans
        (ht.rest (by decide)))))))
  · rw [hv.mem, hu.mem] at wo; exact wo
  · rw [ht.mem, ← ym]; exact zo
  · have src : y.mem (off (sg.setWidth 64 + BitVec.ofNat 64 57) (j / 8)) =
        s.mem (off (sg.setWidth 64 + BitVec.ofNat 64 57) (j / 8)) := by
      rw [ym, wo _ (Or.inr (Nat.le_trans (by decide) (hsd (j / 8) (by omega)))), hv.mem, hu.mem]
    rw [ht.mem, zb j (by omega), src, Proof.Ed448.scalar_bit _ _ hj]
  · have src : v.mem (off (ch.setWidth 64) (j / 8)) = s.mem (off (ch.setWidth 64) (j / 8)) := by
      rw [hv.mem, hu.mem]
    rw [ht.mem, zo _ (Or.inr (by rw [ofs_off' base (by omega)]; omega)), ym, wb j (by omega), src,
      Proof.Ed448.scalar_bit _ _ hj]

end VG.Proof.Ed448.X86
