module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: the pointers the header gives

Each block of loads from the P space's header (`ptrP`, `ptrQ`, …) leaves a
pointer in `r12` and a length in `r6`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify

/-- A header word is readable. -/
theorem hdr_rd {s : State} {L : Lay} (hL : L.Ok) (hs : ScrL s L) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (L.S + BitVec.ofNat 64 d) 8 :=
  hs.ld (show d + 8 ≤ L.Z by have := hL.room; rcases hL.pl with e | e | e <;> omega)

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `ptrP`: the key, `p_len`. -/
theorem ptrP_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrP) s fun t =>
      (t.gpr .r12 = key ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  have r0 := hdr_rd hL hs (d := 0) (by decide)
  have r8 := hdr_rd hL hs (d := 8) (by decide)
  have v0 : s.mem.readW (L.S + BitVec.ofNat 64 0) 64 = key := hh.key
  have v8 : s.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := hh.pl
  unfold ptrP
  prun [h21, r0, r8, v0, v8, hKey, hP]

/-- `ptrQ`: the key plus `p_len`, `q_len`. -/
theorem ptrQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrQ) s fun t =>
      (t.gpr .r12 = off key L.pl ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  have r0 := hdr_rd hL hs (d := 0) (by decide)
  have r8 := hdr_rd hL hs (d := 8) (by decide)
  have r16 := hdr_rd hL hs (d := 16) (by decide)
  have v0 : s.mem.readW (L.S + BitVec.ofNat 64 0) 64 = key := hh.key
  have v8 : s.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := hh.pl
  have v16 : s.mem.readW (L.S + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 L.ql := hh.ql
  unfold ptrQ
  prun [h21, r0, r8, r16, v0, v8, v16, hKey, hP, hQ]

/-- `ptrG`: the key plus `p_len + q_len`, `p_len`. -/
theorem ptrG_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrG) s fun t =>
      (t.gpr .r12 = off key (L.pl + L.ql) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  have r0 := hdr_rd hL hs (d := 0) (by decide)
  have r8 := hdr_rd hL hs (d := 8) (by decide)
  have r16 := hdr_rd hL hs (d := 16) (by decide)
  have v0 : s.mem.readW (L.S + BitVec.ofNat 64 0) 64 = key := hh.key
  have v8 : s.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := hh.pl
  have v16 : s.mem.readW (L.S + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 L.ql := hh.ql
  unfold ptrG
  prun [h21, r0, r8, r16, v0, v8, v16, hKey, hP, hQ]

/-- `ptrY`: the key plus `2 p_len + q_len`, `p_len`. -/
theorem ptrY_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrY) s fun t =>
      (t.gpr .r12 = off key (2 * L.pl + L.ql) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  unfold ptrY
  rw [WP.block_append_iff]
  refine WP.mono (ptrG_ok hL hs hh h21) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off key (2 * L.pl + L.ql) ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6]
  rw [show L.pl + L.ql + L.pl = 2 * L.pl + L.ql by omega]

/-- `ptrR`: the signature, `q_len`. -/
theorem ptrR_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrR) s fun t =>
      (t.gpr .r12 = sig ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  have r40 := hdr_rd hL hs (d := 40) (by decide)
  have r16 := hdr_rd hL hs (d := 16) (by decide)
  have v40 : s.mem.readW (L.S + BitVec.ofNat 64 40) 64 = sig := hh.sig
  have v16 : s.mem.readW (L.S + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 L.ql := hh.ql
  unfold ptrR
  prun [h21, r40, r16, v40, v16, hSig, hQ]

/-- `ptrS`: the signature plus `q_len`, `q_len`. -/
theorem ptrS_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrS) s fun t =>
      (t.gpr .r12 = off sig L.ql ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r6, .r12] s t := by
  unfold ptrS
  rw [WP.block_append_iff]
  refine WP.mono (ptrR_ok hL hs hh h21) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off sig L.ql ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6]

/-- `ptrBuf`: the buffer, `q_len`. -/
theorem ptrBuf_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrBuf) s fun t =>
      (t.gpr .r12 = L.Buf ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.r6, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  have r32 := hdr_rd hL hs (d := 32) (by decide)
  have r16 := hdr_rd hL hs (d := 16) (by decide)
  have v32 : s.mem.readW (L.S + BitVec.ofNat 64 32) 64 = L.Buf := hh.buf
  have v16 : s.mem.readW (L.S + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 L.ql := hh.ql
  unfold ptrBuf
  prun [h21, r32, r16, v32, v16, hBuf, hQ]

/-- `ptrBuf2`: the buffer plus `q_len`, `q_len`. -/
theorem ptrBuf2_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block ptrBuf2) s fun t =>
      (t.gpr .r12 = off L.Buf L.ql ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r6, .r12] s t := by
  unfold ptrBuf2
  rw [WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hL hs hh h21) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off L.Buf L.ql ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ =>
    ⟨⟨b12, (ku.gpr .r6 (by decide)).trans a6, mu.trans m⟩, (k.trans ku).mono (by decide)⟩
  prun [a12, a6]

end VG.Proof.Dsa.PPC64LE
