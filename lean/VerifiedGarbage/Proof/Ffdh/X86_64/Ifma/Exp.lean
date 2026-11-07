module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Vec
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Glue
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.FrameTrim
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Vec
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Glue
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.FrameTrim
meta import VerifiedGarbage.Proof.Bignum.Octets

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64: one layout

`exp_ok`: for a one-lane layout (`PubOk`) of the prime's `W` words and an
exponent of at most `8 W` bytes, `Ifma.exp` does what `CrtExpL.ok` asks of
an exponentiation: the area in the room after the prime's arrays, its base
and the first digit (`head_ok`), the region (`region_ok`), the vector code
(`vec_ok`), the result (`result_ok`), and `sCtr`, which `k1` counts in,
back (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Ffdh.X86_64.Ifma
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk PubOk.amm PubOk.nl)
open VG.Proof.MlKem.X86_64

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- What the one-lane layouts' sizes give. -/
theorem PubOk.sizes (hl : PubOk l) : oArea l = slot l.W 8 ∧ l.nl = 1 ∧ l.w = 4 ∧ l.E = 8 * l.W ∧ l.P = l.E ∧
    l.ND = 2 * l.P ∧ oSv l + 8 ≤ wsTab l.W ∧ oSt l = l.D + 8 ∧ oSv l = l.D + 16 ∧ 32 ≤ l.W ∧ l.W ≤ 64 ∧
    2 * l.P < 2 ^ 31 ∧ l.D + 24 < 2 ^ 31 := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- `head`: `sCtr` into `r8`, `2 (P - len)` into `rdx`, the area's base
`rdi + oArea` into `rax` and `sIfma`, and `rdx` and `r8` at `oSt` and `oSv`. -/
theorem head_ok (hl : PubOk l) {s : State} {B : Addr} {Z o w : Nat} {minv : BitVec 64} {sl L : Nat}
    (hc : SubCtx s B Z o w l.W minv) (hT : o + slot l.W 8 + wsTab l.W ≤ Z) (hsl : sl < 32)
    (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 L) (hL : L ≤ l.P) :
    WP isa (.block (head l sl)) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * sIfma)) (off B (o + oArea l))).writeW
        (off B (o + oArea l + oSt l)) (BitVec.ofNat 64 (2 * (l.P - L)))).writeW
          (off B (o + oArea l + oSv l)) (word s.mem (off B o) (8 * sCtr)) ∧
      Keep [.rax, .rcx, .rdx, .r8] s t := by
  obtain ⟨hA, -, -, -, -, -, hv, hSt, hSv, hW1, hW2, hP, -⟩ := PubOk.sizes hl
  have hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have hs := hc.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT' : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  have hlo := hc.lo
  have hw8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hT, hT', this])
  have hldB : InRegions (s.rd ++ s.wr) (off B (8 * sl)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 hsl; omega_using [hT, hT', this, hlo])
  have hst : ∀ d, d + 8 ≤ slot l.W 8 + wsTab l.W → InRegions s.wr (off (off B o) d) 8 := fun d hd => by
    rw [off_off]; exact hs.st (by omega_using [hT, hd])
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r8] (Q := fun t =>
    t.mem = ((s.mem.writeW (off (off B o) (8 * sIfma)) (off B (o + oArea l))).writeW
        (off B (o + oArea l + oSt l)) (BitVec.ofNat 64 (2 * (l.P - L)))).writeW
          (off B (o + oArea l + oSv l)) (word s.mem (off B o) (8 * sCtr))) (by
    have sA := AmmSym.se_ofNat (show oArea l < 2 ^ 31 by omega_using [hA, hS8, hW2])
    have eSt : off B o + BitVec.ofNat 64 (oArea l) + BitVec.ofNat 64 (oSt l) = off (off B o) (oArea l + oSt l) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have eSv : off B o + BitVec.ofNat 64 (oArea l) + BitVec.ofNat 64 (oSv l) = off (off B o) (oArea l + oSv l) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have w32 : BitVec.setWidth 64 (BitVec.ofNat 32 (2 * l.P)) = BitVec.ofNat 64 (2 * l.P) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hP]), Nat.mod_eq_of_lt (by omega_using [hP]), Nat.mod_eq_of_lt (by omega_using [hP])]
    rw [Impl.Ffdh.X86_64.Ifma.head]
    xrun [State.ea, hdr, ws, at_, eaG', BitVec.ofInt_natCast, hc.rdi, hdrOff, hld sCtr (by decide), hld sLink (by decide), hc.link, hldB,
      hel, sA, w32, eSt, eSv, hst (8 * sIfma) (by unfold sIfma sFn; omega_using [h8]),
      hst (oArea l + oSt l) (by omega_using [hA, hv, hSt, hSv]), hst (oArea l + oSv l) (by omega_using [hA, hv, hSv])]
    have esub : BitVec.ofNat 64 (2 * l.P) - (BitVec.ofNat 64 L + BitVec.ofNat 64 L) =
        BitVec.ofNat 64 (2 * (l.P - L)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using [hL, hP]
    have e1 : off B o + BitVec.ofNat 64 (oArea l) = off B (o + oArea l) := off_off B o (oArea l)
    rw [e1, esub, off_off B o (oArea l + oSt l), off_off B o (oArea l + oSv l), ← Nat.add_assoc, ← Nat.add_assoc,
      show word s.mem (off B o) (8 * sCtr) = s.mem.readW (off (off B o) (8 * sCtr)) 64 from rfl]) rfl) fun t ⟨me, k⟩ => ⟨me, k⟩

/-- `tail`: `sCtr` back from `oSv` of the area at `sIfma`. -/
theorem tail_ok (hl : PubOk l) {s : State} {B : Addr} {Z o a : Nat} {v : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hia : word s.mem (off B o) (8 * sIfma) = off B a)
    (hv : word s.mem B (a + oSv l) = v) (hoa : o + slot l.W 8 ≤ a) (haZ : a + oSv l + 8 ≤ Z) :
    WP isa (.block (tail l)) s fun t =>
      t.mem = s.mem.writeW (off (off B o) (8 * sCtr)) v ∧ Keep [.rax, .rcx] s t := by
  obtain ⟨-, -, -, -, -, -, -, -, hSv, -, -, -, hD⟩ := PubOk.sizes hl
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot l.W 8 hi; omega_using [hoa, haZ, this])
  have hstC : InRegions s.wr (off (off B o) (8 * sCtr)) 8 := by
    rw [off_off]; exact hs.st (by unfold sCtr sFn; omega_using [hoa, haZ, h8])
  have eV : off B a + BitVec.ofNat 64 (oSv l) = off B (a + oSv l) := off_off B a (oSv l)
  have hldV : InRegions (s.rd ++ s.wr) (off B a + BitVec.ofNat 64 (oSv l)) 8 := by
    rw [eV]; exact hs.ld haZ
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem.writeW (off (off B o) (8 * sCtr)) v) (by
    rw [Impl.Ffdh.X86_64.Ifma.tail]
    have sv := AmmSym.se_ofNat (show oSv l < 2 ^ 31 by omega_using [hSv, hD])
    xrun [State.ea, hdr, at_, eaG', BitVec.ofInt_natCast, hdi, hdrOff, hld sIfma (by decide), hia, hldV, hstC]
    rw [eV, show s.mem.readW (off B (a + oSv l)) 64 = word s.mem B (a + oSv l) from rfl, hv]) rfl)
    fun t ⟨me, k⟩ => ⟨me, k⟩

/-- A frame of `B` at offsets shifted by `o` is one of `B + o`. -/
theorem Frm.unshift {B : Addr} {o : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B (shiftRanges o rs) m m')
    (ho : o < 2 ^ 64) : Frm (off B o) rs m m' := fun x hx => h x fun r' hr' => by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  rcases VG.Proof.Bignum.X86_64.AmmSym.ofs_rebase' B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx r hr with h3 | h3
    · exact .inl (by simp only; omega_using [h1, h2, h3])
    · exact .inr (by simp only; omega_using [h1, h2, h3])
  · exact .inl (by simp only; omega_using [h1])

/-- What changes within the prime's arrays and the room after them keeps
the prime's workspace. -/
theorem SubCtx.of_frmW {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + wsTab wx)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  have hL : o + (slot wx 8 + wsTab wx) ≤ 2 ^ 64 := by omega_arith
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + wsTab wx := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
          omega_arith)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega_arith) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega_arith)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), h.lo, h.hi⟩

/-- After `head`: the area's base in `sIfma`, the first digit and `sCtr` in
the area, and the rest of the prime's workspace as it was. -/
structure HeadOut (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s t : State) (B : Addr) (o L : Nat) : Prop where
  ia : word t.mem (off B o) (8 * sIfma) = off B (o + oArea l)
  st : word t.mem B (o + oArea l + oSt l) = BitVec.ofNat 64 (2 * (l.P - L))
  sv : word t.mem B (o + oArea l + oSv l) = word s.mem (off B o) (8 * sCtr)
  f : Frm (off B o) [(8 * sIfma, 8), (oArea l + oSt l, 8), (oArea l + oSv l, 8)] s.mem t.mem

theorem headOut_of (hl : PubOk l) {s t : State} {B : Addr} {Z o w L : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w l.W minv) (hT : o + slot l.W 8 + wsTab l.W ≤ Z)
    (hm : t.mem = ((s.mem.writeW (off (off B o) (8 * sIfma)) (off B (o + oArea l))).writeW
        (off B (o + oArea l + oSt l)) (BitVec.ofNat 64 (2 * (l.P - L)))).writeW
          (off B (o + oArea l + oSv l)) (word s.mem (off B o) (8 * sCtr))) : HeadOut l s t B o L := by
  obtain ⟨hA, -, -, -, -, -, hv, hSt, hSv, -, -, -, -⟩ := PubOk.sizes hl
  have hn := hc.scr.nowrap
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT' : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  have hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have e2 : off B (o + oArea l + oSt l) = off (off B o) (oArea l + oSt l) := by rw [off_off, Nat.add_assoc]
  have e3 : off B (o + oArea l + oSv l) = off (off B o) (oArea l + oSv l) := by rw [off_off, Nat.add_assoc]
  rw [e2, e3] at hm
  have hW := hc.hi
  have hb1 : 8 * sIfma + 8 ≤ 2 ^ 64 := by unfold sIfma sFn; omega_using []
  have hb2 : oArea l + oSt l + 8 ≤ 2 ^ 64 := by omega_using [hn, hT, hA, hv, hSt, hSv]
  have hb3 : oArea l + oSv l + 8 ≤ 2 ^ 64 := by omega_using [hn, hT, hA, hv, hSv]
  generalize hv1 : off B (o + oArea l) = v1 at hm ⊢
  generalize hv3 : word s.mem (off B o) (8 * sCtr) = v3 at hm ⊢
  have O1 := writeW_outside s.mem (off B o) (d := 8 * sIfma) v1 hb1
  have O2 := writeW_outside (s.mem.writeW (off (off B o) (8 * sIfma)) v1) (off B o) (d := oArea l + oSt l)
    (BitVec.ofNat 64 (2 * (l.P - L))) hb2
  have O3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * sIfma)) v1).writeW (off (off B o) (oArea l + oSt l))
    (BitVec.ofNat 64 (2 * (l.P - L)))) (off B o) (d := oArea l + oSv l) v3 hb3
  rw [← hm] at O3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [O3.word (.inl (by unfold sIfma sFn; omega_using [hA, hS8])) hb1,
      O2.word (.inl (by unfold sIfma sFn; omega_using [hA, hS8])) hb1, word_writeW_self]
    exact hv1.symm
  · rw [Nat.add_assoc, ← word_off, O3.word (.inl (by omega_using [hSt, hSv])) hb2, word_writeW_self]
  · rw [Nat.add_assoc, ← word_off, hm, word_writeW_self]
    exact hv3.symm
  · exact ((Frm.of_outside O1 (by simp)).trans (Frm.of_outside O2 (by simp))).trans (Frm.of_outside O3 (by simp))

end VG.Proof.Ffdh.X86_64.Ifma
