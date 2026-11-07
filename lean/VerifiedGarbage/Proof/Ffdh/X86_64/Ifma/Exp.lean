module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Vec
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Glue
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTIfma
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Region
import VerifiedGarbage.Proof.Bignum.FrameTrim
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Vec
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Glue
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTIfma
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Region
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

/-- The ranges of the prime's workspace that the exponentiation writes:
`crtExpRanges5`'s, and `sCtr`, which it puts back. -/
def expRanges (wx : Nat) : List (Nat × Nat) := (8 * sCtr, 8) :: crtExpRanges5 wx

theorem expRanges_ok (wx : Nat) : ∀ r ∈ expRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + wsTab wx := by
  intro r hr
  simp only [expRanges, List.mem_cons] at hr
  rcases hr with rfl | hr
  · have := hdr_lt_slot wx 8 (show sCtr < 32 by decide); unfold sCtr sFn at *; simp only; omega_using [this]
  · exact crtExpRanges5_ok wx r hr

/-- After `head`, from `s`. -/
structure Mid (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s t : State) (B : Addr) (Z o w : Nat) (minv : BitVec 64)
    (sp sl : Nat) (ep : Addr) (eb : List Byte) : Prop where
  sub : SubCtx t B Z o w l.W minv
  ho : HeadOut l s t B o eb.length
  arr : ∀ j < 8, wv t.mem (off B o) (slot l.W j) l.W = wv s.mem (off B o) (slot l.W j) l.W
  nw : word t.mem (off B o) (slot l.W Public.aN) = word s.mem (off B o) (slot l.W Public.aN)
  pv : word t.mem B (8 * sp) = word s.mem B (8 * sp)
  lv : word t.mem B (8 * sl) = word s.mem B (8 * sl)
  src : Src t B Z ep eb
  fw : Frm (off B o) (expRanges l.W) s.mem t.mem

theorem head_mid (hl : PubOk l) {s : State} {B : Addr} {Z o w : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w l.W minv) (hT : o + slot l.W 8 + wsTab l.W ≤ Z)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) (hLW : eb.length ≤ 8 * l.W) (he : Src s B Z ep eb) :
    WP isa (.block (head l sl)) s fun t => Mid l s t B Z o w minv sp sl ep eb ∧ Keep [.rax, .rcx, .rdx, .r8] s t := by
  obtain ⟨hA, -, -, hE, hP, -, hv, hSt, hSv, -, -, -, -⟩ := PubOk.sizes hl
  have hnw := hc.scr.nowrap
  have hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have hT' : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  have hlo := hc.lo
  have hw8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hoZ : o < 2 ^ 64 := by omega_using [hnw, hT, hS8]
  refine WP.mono (head_ok hl hc hT hsl hel (by omega_using [hLW, hE, hP])) fun t ⟨m, k⟩ => ?_
  have ho := headOut_of hl hc hT m
  have hr : ∀ r ∈ [(8 * sIfma, 8), (oArea l + oSt l, 8), (oArea l + oSv l, 8)],
      (r.1 + r.2 ≤ slot l.W 0) ∨ (slot l.W 8 ≤ r.1 ∧ r.1 + r.2 ≤ slot l.W 8 + wsTab l.W) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (by unfold sIfma sFn slot hdrBytes; omega_using [])
    · exact .inr ⟨by omega_using [hA], by omega_using [hA, hv, hSt, hSv]⟩
    · exact .inr ⟨by omega_using [hA], by omega_using [hA, hv]⟩
  have hL : ∀ r ∈ [(8 * sIfma, 8), (oArea l + oSt l, 8), (oArea l + oSv l, 8)],
      r.1 + r.2 ≤ slot l.W 8 + wsTab l.W := fun r h => by
    rcases hr r h with h | h
    · have := slot_le (w := l.W) (show 0 < 8 by decide); omega_using [h, this]
    · exact h.2
  have arr : ∀ j < 8, wv t.mem (off B o) (slot l.W j) l.W = wv s.mem (off B o) (slot l.W j) l.W := fun j hj => by
    have := slot_le (w := l.W) hj
    have h0 : slot l.W 0 ≤ slot l.W j := by unfold slot; omega_using []
    refine ho.f.wv_eq (fun r h => ?_) (by omega_using [this, hnw, hT, hoZ])
    rcases hr r h with h | ⟨h, -⟩
    · exact .inr (by omega_using [h, h0])
    · exact .inl (by omega_using [h, this])
  have below : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.f.word_below hL (by omega_using [hnw, hT]) hoZ (by have := hdr_lt_slot w 8 hi; omega_using [this, hlo])
  have fW : Frm (off B o) (expRanges l.W) s.mem t.mem := ho.f.widen fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot l.W 8, tabBytes l.W 32), by simp [expRanges, crtExpRanges5, crtExpRanges],
        by simp only; omega_using [hA], by simp only; unfold wsTab at hv; omega_using [hA, hv, hSt, hSv]⟩
    · exact ⟨(slot l.W 8, tabBytes l.W 32), by simp [expRanges, crtExpRanges5, crtExpRanges],
        by simp only; omega_using [hA], by simp only; unfold wsTab at hv; omega_using [hA, hv]⟩
  have nw : word t.mem (off B o) (slot l.W Public.aN) = word s.mem (off B o) (slot l.W Public.aN) := by
    have := slot_le (w := l.W) (show Public.aN < 8 by decide)
    refine ho.f.word_eq (fun r h => ?_) (by omega_using [this, hnw, hT, hoZ])
    rcases hr r h with h | ⟨h, -⟩
    · exact .inr (by unfold Public.aN at *; omega_using [h])
    · exact .inl (by omega_using [h, this])
  have fB := ho.f.rebase hoZ fun r h => by have := hL r h; omega_using [this, hnw, hT]
  have iS : InScr B Z s.mem t.mem := InScr.of_frm fB fun r h => by
    simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only <;> unfold sIfma sFn at * <;> omega_using [hT, hA, hv, hSt, hSv, hS8, hT']
  exact ⟨⟨SubCtx.of_frmW hc hT fW (expRanges_ok l.W) k.2.2 (k.gpr (by decide)), ho, arr, nw, below sp hsp,
    below sl hsl, he.congr iS k.2.1 k.2.2, fW⟩, k⟩

/-! ## The pieces' hypotheses, in a chain

As `CrtIfma`'s `ifma_chain`: each piece's hypotheses about its public data
(`BPub`, as `EPre`), and that the piece leads to the next's (`C0` to `C4`),
to `Final`, which holds what the exponentiation gives for the ghost values
`Gh` that only correctness needs. The constant time follows the chain. -/

/-- The values only correctness needs: the start, the modulus, the base,
the claim of the congruences, and the exponent. -/
structure Gh where
  s₀ : State
  X : Nat
  x : Nat
  Q : Prop
  eb : List Byte

/-- The region's public data. -/
def regP (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) : RegPub :=
  ⟨p.x.B, p.x.Z, p.x.o, p.x.o + oArea l, p.ptr, p.len⟩

/-- The vector code's public data. -/
def vP (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) : Addr × Nat × Nat × Nat :=
  (p.x.B, p.x.Z, p.x.o, p.x.o + oArea l)

/-- The result's public data. -/
def resP (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) : ResPub := ⟨p.x.B, p.x.Z, p.x.o, p.x.o + oArea l⟩

/-- What `head` reads. -/
def HPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop :=
  Scr s p.x.B p.x.Z ∧ s.gpr .rdi = off p.x.B p.x.o ∧ word s.mem (off p.x.B p.x.o) (8 * sLink) = p.x.B ∧
    8 * 32 ≤ p.x.o ∧ p.x.o + slot l.W 8 ≤ p.x.Z

/-- What `bases` and the vector code read: as `CrtIfma`'s, and the first digit. -/
def VPreF (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop :=
  VPre (vP l p) s ∧ word s.mem p.x.B (p.x.o + oArea l + oSt l) = BitVec.ofNat 64 (2 * (l.P - p.len)) ∧
    p.x.o + oArea l + oSt l + 8 ≤ p.x.Z

/-- What `tail` reads. -/
def TPre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (s : State) : Prop :=
  Scr s p.x.B p.x.Z ∧ s.gpr .rdi = off p.x.B p.x.o ∧
    word s.mem (off p.x.B p.x.o) (8 * sIfma) = off p.x.B (p.x.o + oArea l) ∧ p.x.o + slot l.W 8 ≤ p.x.o + oArea l ∧
    p.x.o + oArea l + oSv l + 8 ≤ p.x.Z

/-- What the exponentiation gives. -/
def Final (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (g : Gh) (t : State) : Prop :=
  wv t.mem (off p.x.B p.x.o) (slot l.W Public.aY) l.W < g.X ∧
    (g.Q → wv t.mem (off p.x.B p.x.o) (slot l.W Public.aY) l.W % g.X =
      g.x ^ Spec.Rsa.os2ip g.eb * 2 ^ (64 * l.W) % g.X) ∧
    Frm (off p.x.B p.x.o) (expRanges l.W) g.s₀.mem t.mem ∧
    word t.mem (off p.x.B p.x.o) (8 * sCtr) = word g.s₀.mem (off p.x.B p.x.o) (8 * sCtr) ∧
    t.wr = g.s₀.wr ∧ t.gpr .rdi = g.s₀.gpr .rdi ∧ Keep mmRegs g.s₀ t

/-- Before `tail`. -/
def C4 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (g : Gh) (t : State) : Prop :=
  TPre l p t ∧ WP isa (.block (tail l)) t (Final l p g)

/-- Before the result. -/
def C3 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (g : Gh) (t : State) : Prop :=
  ResPre l 0 (resP l p) t ∧ WP isa (seqs (result l 0)) t (C4 l p g)

/-- Before the vector code. -/
def C2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : BPub) (g : Gh) (t : State) : Prop :=
  VPreF l p t ∧ WP isa (seqs [.block (Impl.Ffdh.X86_64.Ifma.bases l), Impl.Ffdh.X86_64.Ifma.vec l]) t (C3 l p g)

/-- Before the region. -/
def C1 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) (p : BPub) (g : Gh) (t : State) : Prop :=
  RegPre l 0 sp sl (regP l p) t ∧ WP isa (seqs (region l 0 sp sl)) t (C2 l p g)

/-- Before `head`. -/
def C0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) (p : BPub) (g : Gh) (t : State) : Prop :=
  HPre l p t ∧ WP isa (.block (head l sl)) t (C1 l sp sl p g)

theorem exp_eq (sp sl : Nat) : exp l sp sl = ([.block (head l sl)] : List (Prog isa)) ++ (region l 0 sp sl ++
    (([.block (Impl.Ffdh.X86_64.Ifma.bases l), Impl.Ffdh.X86_64.Ifma.vec l] : List (Prog isa)) ++
      (result l 0 ++ ([.block (tail l)] : List (Prog isa))))) := by
  simp only [exp, List.append_assoc]

/-- The chain runs the exponentiation. -/
theorem C0.wp {sp sl : Nat} {p : BPub} {g : Gh} {s : State} (h : C0 l sp sl p g s) :
    WP isa (seqs (exp l sp sl)) s (Final l p g) := by
  rw [exp_eq]
  refine wp_seqs_append (by simp) (by simp [region, k1, copyArr]) (WP.mono h.2 fun s₁ h₁ => ?_)
  refine wp_seqs_append (by simp [region, k1, copyArr]) (by simp) (WP.mono h₁.2 fun s₂ h₂ => ?_)
  refine wp_seqs_append (by simp) (by simp [result]) (WP.mono h₂.2 fun s₃ h₃ => ?_)
  exact wp_seqs_append (by simp [result]) (by simp) (WP.mono h₃.2 fun s₄ h₄ => h₄.2)

/-- The chain of `Ifma.exp` of a one-lane layout, for the prime's `W`
words and an exponent of at most `8 W` bytes. -/
theorem expW_chain (hl : PubOk l) {s : State} {B : Addr} {Z o w : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    (hc : SubCtx s B Z o w l.W minv) (hT : o + slot l.W 8 + wsTab l.W ≤ Z)
    (hn : wv s.mem (off B o) (slot l.W Public.aN) l.W = X)
    (hinv : ((word s.mem (off B o) (slot l.W Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot l.W Crt.aXc) l.W < X)
    (hxc : Q → wv s.mem (off B o) (slot l.W Crt.aXc) l.W % X = x * 2 ^ (64 * l.W) % X)
    (hyl : wv s.mem (off B o) (slot l.W Public.aY) l.W < X)
    (hyc : Q → wv s.mem (off B o) (slot l.W Public.aY) l.W % X = 2 ^ (64 * l.W) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hLW : eb.length ≤ 8 * l.W) (he : Src s B Z ep eb) :
    C0 l sp sl ⟨⟨B, Z, o, w, l.W⟩, ep, eb.length⟩ ⟨s, X, x, Q, eb⟩ s := by
  obtain ⟨hA, hn1, hw4, hE, hP, hND, hv, hSt, hSv, hW1, hW2, hP31, hD31⟩ := PubOk.sizes hl
  have hla := hl.amm
  have hs := hc.scr
  have hnw := hs.nowrap
  have hS8 : slot l.W 8 = 256 + 64 * (l.W + 2) := by unfold slot hdrBytes; omega_using []
  have hT' : wsTab l.W = 256 * (l.W + 2) := by unfold wsTab tabBytes; omega_using []
  have h8 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hlo := hc.lo
  have hw8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain ⟨hDb1, hDb2⟩ := hla.D_bounds
  have hnD : l.nl * l.D = l.D := by rw [hn1, Nat.one_mul]
  have haZ : o + oArea l + l.nl * l.D + 8 ≤ Z := by omega_using [hnD, hA, hT, hv, hSv]
  have hoZ : o < 2 ^ 64 := by omega_using [hnw, hT, hS8]
  have hER := expRanges_ok l.W
  dsimp only [C0, HPre]
  refine ⟨⟨hs, hc.rdi, hc.link, by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_using [this, hlo],
    by omega_using [hT]⟩, WP.mono (head_mid hl hc hT hsp hsl hel hLW he)
    fun s₁ ⟨mi₁, k₁⟩ => ?_⟩
  have hN₁ : wv s₁.mem (off B o) (slot l.W Public.aN) l.W = X := by rw [mi₁.arr _ (by decide)]; exact hn
  have hY₁ : wv s₁.mem (off B o) (slot l.W Public.aY) l.W = wv s.mem (off B o) (slot l.W Public.aY) l.W :=
    mi₁.arr _ (by decide)
  have hX₁ : wv s₁.mem (off B o) (slot l.W Crt.aXc) l.W = wv s.mem (off B o) (slot l.W Crt.aXc) l.W :=
    mi₁.arr _ (by decide)
  -- the region
  dsimp only [C1, regP]
  refine ⟨regPre_of (by omega_using [hA]) haZ (by omega_using [hn1]) hsp hsl hL1 (by omega_using [hLW, hE]) mi₁.sub
    mi₁.ho.ia hN₁ (by rw [hY₁]; exact hyl) (mi₁.pv.trans hep) (mi₁.lv.trans hel) mi₁.src, WP.mono
    (region_ok hla (p := 0) mi₁.sub mi₁.ho.ia (by omega_using [hA]) haZ (by omega_using [hn1]) hN₁
      (by rw [hY₁]; exact hyl) hsp hsl (mi₁.pv.trans hep) (mi₁.lv.trans hel) mi₁.src hL1 (by omega_using [hLW, hE]))
    fun s₂ ⟨ro, f₂, wr₂, di₂, k₂⟩ => ?_⟩
  have hdi₁ : s₁.gpr .rdi = off B o := mi₁.sub.rdi
  have hk1 : ∀ r ∈ k1Ranges l.W, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot l.W 8 := by
    have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
    have := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
    have := slot_le (w := l.W) (show Crt.aT < 8 by decide)
    have := hdr_lt_slot l.W 0 (show sCtr < 32 by decide)
    simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCtr, sFn] at * <;> unfold slot at * <;> omega_arith
  have f₂P : Frm (off B o) (k1Ranges l.W ++ [(oArea l, l.D)]) s₁.mem s₂.mem := by
    refine Frm.unshift ?_ hoZ
    rw [show shiftRanges o (k1Ranges l.W ++ [(oArea l, l.D)]) =
      shiftRanges o (k1Ranges l.W) ++ [(o + oArea l + l.D * 0, l.D)] by
        simp only [shiftRanges, List.map_append, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero]]
    exact f₂
  have f₂W : Frm (off B o) (expRanges l.W) s₁.mem s₂.mem := f₂P.widen fun r h => by
    rcases List.mem_append.mp h with h | h
    · simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;>
        first
        | exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
        | exact ⟨_, by simp [expRanges, crtExpRanges5, crtExpRanges, crtWinRanges], Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨(slot l.W 8, tabBytes l.W 32), by simp [expRanges, crtExpRanges5, crtExpRanges],
        by simp only; omega_using [hA], by simp only; unfold wsTab at hv; omega_using [hA, hv, hSv]⟩
  have sub₂ := SubCtx.of_frmW mi₁.sub hT f₂W hER wr₂ (di₂.trans hdi₁.symm)
  -- the words in the header and the area that the region keeps
  have kept₂ : ∀ d, (d + 8 ≤ 8 * sCtr ∨ slot l.W 8 ≤ d) → (d + 8 ≤ oArea l ∨ oArea l + l.D ≤ d) →
      d + 8 ≤ slot l.W 8 + wsTab l.W → word s₂.mem (off B o) d = word s₁.mem (off B o) d := fun d h1 h2 h3 => by
    refine f₂P.word_eq (fun r h => ?_) (by omega_using [h3, hnw, hT, hoZ])
    rcases List.mem_append.mp h with h | h
    · simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at h
      have := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
      have := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
      have := slot_le (w := l.W) (show Crt.aT < 8 by decide)
      have h0 := hdr_lt_slot l.W 0 (show sCtr < 32 by decide)
      rcases h with rfl | rfl | rfl | rfl <;> simp only [sCtr, sFn] at * <;> unfold slot at * <;> omega_arith
    · rw [List.mem_singleton.mp h]; simp only; omega_using [h2]
  have ia₂ : word s₂.mem (off B o) (8 * sIfma) = off B (o + oArea l) := by
    rw [kept₂ _ (.inl (by unfold sIfma sCtr sFn; omega_using [])) (.inl (by unfold sIfma sFn; omega_using [hA, hS8]))
      (by unfold sIfma sFn; omega_using [hS8, hT'])]
    exact mi₁.ho.ia
  have st₂ : word s₂.mem B (o + oArea l + oSt l) = BitVec.ofNat 64 (2 * (l.P - eb.length)) := by
    rw [Nat.add_assoc, ← word_off, kept₂ _ (.inr (by omega_using [hA])) (.inr (by omega_using [hSt]))
      (by omega_using [hA, hv, hSt, hSv]), word_off, ← Nat.add_assoc]
    exact mi₁.ho.st
  have sv₂ : word s₂.mem B (o + oArea l + oSv l) = word s.mem (off B o) (8 * sCtr) := by
    rw [Nat.add_assoc, ← word_off, kept₂ _ (.inr (by omega_using [hA])) (.inr (by omega_using [hSv]))
      (by omega_using [hA, hv, hSv]), word_off, ← Nat.add_assoc]
    exact mi₁.ho.sv
  -- the area's base into `rbx`
  have hs₂ := sub₂.scr
  have hld₂ : InRegions (s₂.rd ++ s₂.wr) (off (off B o) (8 * sIfma)) 8 := by
    rw [off_off]; exact hs₂.ld (by unfold sIfma sFn; omega_using [hT, hS8, hT'])
  have eS : off B (o + oArea l) + BitVec.ofNat 64 (oSt l) = off B (o + oArea l + oSt l) := off_off B _ _
  have hldS : InRegions (s₂.rd ++ s₂.wr) (off B (o + oArea l) + BitVec.ofNat 64 (oSt l)) 8 := by
    rw [eS]; exact hs₂.ld (by omega_using [hA, hv, hSt, hSv, hT])
  have sS := AmmSym.se_ofNat (show oSt l < 2 ^ 31 by omega_using [hSt, hD31])
  dsimp only [C2, VPreF, vP]
  refine ⟨⟨vPre_of hs₂ sub₂.rdi ia₂ (by omega_using [hT, hS8]), st₂, by omega_using [hA, hv, hSt, hSv, hT]⟩,
    WP.seq (WP.mono (WP.keep [.rbx, .rbp] (Q := fun u =>
    u.gpr .rbx = off B (o + oArea l) ∧ u.gpr .rbp = BitVec.ofNat 64 (2 * (l.P - eb.length)) ∧ u.mem = s₂.mem ∧
      u.mxcsr = s₂.mxcsr) (by
      unfold Impl.Ffdh.X86_64.Ifma.bases
      xrun [State.ea, hdr, at_, eaG', BitVec.ofInt_natCast, sub₂.rdi, hdrOff, hld₂, ia₂, hldS]
      rw [eS, show s₂.mem.readW (off B (o + oArea l + oSt l)) 64 = word s₂.mem B (o + oArea l + oSt l) from rfl, st₂]
      exact ⟨rfl, rfl⟩) rfl) fun s₃ ⟨⟨bx₃, bp₃, me₃, mx₃⟩, k₃⟩ => ?_)⟩
  have hs₃ : Scr s₃ B Z := hs₂.congr k₃.2.2
  have h0 : ∀ p < l.nl, p = 0 := fun p hp => by omega_using [hp, hn1]
  have hXp : 0 < X := by omega_using [hodd]
  have hMlt : X < 2 ^ (64 * l.W) := hn ▸ wv_lt _ _ _ _
  have hlimbs : ∀ {c v : Nat}, Limbs l s₂.mem (off B (o + oArea l)) (l.D * 0 + c) v →
      LimbsAt l s₃.mem (off B (o + oArea l)) c (fun _ => v) := fun h p hp => by
    obtain rfl := h0 p hp; rw [me₃]; exact h
  have hT16 : l.T = 16 := by simp only [Lay.T, hw4]
  refine WP.mono (vec_ok hla (x := fun _ => x) (e := fun _ => Spec.Rsa.os2ip eb) (Q := Q)
    (M := fun _ => X) (K1 := fun _ => 2 ^ l.dbls * wv s₁.mem (off B o) (slot l.W Public.aY) l.W % X)
    (Xc := fun _ => wv s₁.mem (off B o) (slot l.W Crt.aXc) l.W)
    (Y := fun _ => wv s₁.mem (off B o) (slot l.W Public.aY) l.W)
    (Fin := fun _ => wv s₁.mem (off B o) (slot l.W Public.aY) l.W) (mi := fun _ => minv)
    (i₀ := 2 * (l.P - eb.length)) rfl rfl bx₃
    (hs₃.sub (by omega_using [hT, hA, hv, hSt, hSv]) (by omega_using [])) (hlimbs ro.n) (hlimbs ro.k1) (hlimbs ro.x)
    (hlimbs ro.y) (hlimbs (by have := ro.fin; simp only [↓reduceIte] at this; exact this))
    (fun p hp t ht => by obtain rfl := h0 p hp; rw [me₃]; exact ro.k0 t ht)
    (fun _ _ => by rw [← hn, wv_mod64 _ _ _ (by omega_using [hW1])]; exact hinv) (fun _ _ => hMlt)
    (fun _ _ => hodd) (fun _ _ => Nat.mod_lt _ hXp) (fun _ _ => by rw [hX₁]; exact hxl)
    (fun _ _ => by rw [hY₁]; exact hyl) (fun _ _ => by rw [hY₁]; omega_using [hyl])
    (fun q _ _ => by rw [hX₁]; exact hxc q) (fun q _ _ => by rw [hY₁]; exact hyc q)
    (fun q _ _ => by rw [Nat.mod_mod, Nat.mul_mod, hY₁, hyc q, ← Nat.mul_mod])
    (by omega_using [hND]) bp₃
    (fun _ _ => Nat.div_eq_of_lt (by
      rw [hT16, show l.ND - 2 * (l.P - eb.length) = 2 * eb.length by omega_using [hND, hLW, hE, hP],
        Nat.pow_mul, show (16 : Nat) ^ 2 = 256 from rfl]
      exact VG.Proof.Bignum.os2ip_lt eb))
    (fun p hp i hi => by obtain rfl := h0 p hp; rw [me₃]; exact ro.d i hi))
    fun s₄ ⟨v₄, O₄, g₄, rd₄, wr₄, _⟩ => ?_
  -- what the vector code changes: its area
  have f₄ : Frm (off B o) [(oArea l + 0, l.nl * l.D + 8)] s₂.mem s₄.mem := by
    rw [← me₃]
    exact Frm.of_outside_off (by rw [off_off]; exact O₄) (by omega_using [hA, hS8, hnw, hT, hoZ, hW2])
      (by omega_using [hA, hS8, hnw, hT, hoZ, hnD, hv, hSv, hW2])
  have f₄W : Frm (off B o) (expRanges l.W) s₂.mem s₄.mem := f₄.widen fun r h => by
    rw [List.mem_singleton.mp h]
    exact ⟨(slot l.W 8, tabBytes l.W 32), by simp [expRanges, crtExpRanges5, crtExpRanges],
      by simp only; omega_using [hA], by simp only; unfold wsTab at hv; omega_using [hA, hv, hSv, hnD]⟩
  have rdi₄ : s₄.gpr .rdi = s₂.gpr .rdi := by
    rw [g₄ .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact k₃.gpr (by decide)
  have wr₄' : s₄.wr = s₂.wr := wr₄.trans k₃.2.2
  have sub₄ := SubCtx.of_frmW sub₂ hT f₄W hER wr₄' rdi₄
  have kept₄ : ∀ d, d + 8 ≤ oArea l → word s₄.mem (off B o) d = word s₂.mem (off B o) d := fun d h =>
    f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [h]))
      (by omega_using [h, hA, hS8, hnw, hT, hoZ])
  have ia₄ : word s₄.mem (off B o) (8 * sIfma) = off B (o + oArea l) := by
    rw [kept₄ _ (by unfold sIfma sFn; omega_using [hA, hS8])]; exact ia₂
  have lN := slot_le (w := l.W) (show Public.aN < 8 by decide)
  have lY := slot_le (w := l.W) (show Public.aY < 8 by decide)
  have hN₂ : wv s₂.mem (off B o) (slot l.W Public.aN) l.W = X := by
    rw [← hN₁]
    refine f₂P.wv_eq (fun r h => ?_) (by omega_using [lN, hnw, hT, hoZ])
    rcases List.mem_append.mp h with h | h
    · simp only [k1Ranges, List.mem_cons, List.not_mem_nil, or_false] at h
      have sA := slot_sep (w := l.W) (show Public.aAcc ≠ Public.aN by decide)
      have sT := slot_sep (w := l.W) (show Public.aTmp ≠ Public.aN by decide)
      have sC := slot_sep (w := l.W) (show Crt.aT ≠ Public.aN by decide)
      have h0 := hdr_lt_slot l.W Public.aN (show sCtr < 32 by decide)
      rcases h with rfl | rfl | rfl | rfl <;> simp only [sCtr, sFn] at * <;> omega_arith
    · rw [List.mem_singleton.mp h]; exact .inl (by simp only; omega_using [lN, hA])
  have hN₄ : wv s₄.mem (off B o) (slot l.W Public.aN) l.W = X := by
    rw [← hN₂]
    exact f₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_using [lN, hA]))
      (by omega_using [lN, hnw, hT, hoZ])
  obtain ⟨gY, cY⟩ := v₄ 0 (by omega_using [hn1])
  -- the result into `aY`
  dsimp only [C3, resP]
  refine ⟨resPre_of sub₄.scr sub₄.rdi sub₄.hdr ia₄ (by omega_using [hA]) haZ (by omega_using [hn1]) gY.lt
    (by rw [hN₄]; exact gY.v), WP.mono (result_ok hla (p := 0) sub₄.scr sub₄.rdi sub₄.hdr ia₄
    (by omega_using [hA]) haZ (by omega_using [hn1]) hN₄ gY.lt gY.v) fun s₅ ⟨vY, f₅, d₅, k₅⟩ => ?_⟩
  have f₅' : Frm (off B o) (resRanges l) s₄.mem s₅.mem := Frm.unshift f₅ hoZ
  have f₅W : Frm (off B o) (expRanges l.W) s₄.mem s₅.mem := f₅'.mono fun r h => by
    simp only [resRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [expRanges, crtExpRanges5, crtExpRanges, crtWinRanges]
  have sv₅ : word s₅.mem B (o + oArea l + oSv l) = word s.mem (off B o) (8 * sCtr) := by
    rw [Nat.add_assoc, ← word_off]
    rw [f₅'.word_eq (fun r hr => by
        simp only [resRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        have lA := slot_le (w := l.W) (show Public.aAcc < 8 by decide)
        have lT := slot_le (w := l.W) (show Public.aTmp < 8 by decide)
        rcases hr with rfl | rfl | rfl <;> exact .inr (by simp only; omega_using [lA, lT, lY, hA]))
      (by omega_using [hA, hv, hSv, hnw, hT, hoZ])]
    rw [f₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only; omega_using [hnD, hSv]))
      (by omega_using [hA, hv, hSv, hnw, hT, hoZ]), word_off, ← Nat.add_assoc]
    exact sv₂
  have ia₅ : word s₅.mem (off B o) (8 * sIfma) = off B (o + oArea l) := by
    rw [f₅'.word_eq (fun r hr => by
        simp only [resRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hdr_lt_slot l.W Public.aAcc (show sIfma < 32 by decide)
        have := hdr_lt_slot l.W Public.aTmp (show sIfma < 32 by decide)
        have := hdr_lt_slot l.W Public.aY (show sIfma < 32 by decide)
        rcases hr with rfl | rfl | rfl <;> exact .inl (by simp only; omega_arith))
      (by unfold sIfma sFn; omega_using [hnw, hT, hoZ, hS8])]
    exact ia₄
  have hs₅ : Scr s₅ B Z := sub₄.scr.congr k₅.2.2
  -- `sCtr` back
  dsimp only [C4, TPre]
  refine ⟨⟨hs₅, d₅.trans sub₄.rdi, ia₅, by omega_using [hA], by omega_using [hA, hv, hSv, hT]⟩,
    WP.mono (tail_ok hl hs₅ (d₅.trans sub₄.rdi) ia₅ sv₅ (by omega_using [hA]) (by omega_using [hA, hv, hSv, hT]))
    fun t ⟨me₆, k₆⟩ => ?_⟩
  have hC : 8 * sCtr + 8 ≤ 2 ^ 64 := by unfold sCtr sFn; omega_using []
  have f₆ : Frm (off B o) [(8 * sCtr, 8)] s₅.mem t.mem := by
    rw [me₆]; exact Frm.of_outside (writeW_outside _ _ _ hC) (List.mem_singleton.mpr rfl)
  have hY₆ : wv t.mem (off B o) (slot l.W Public.aY) l.W = wv s₅.mem (off B o) (slot l.W Public.aY) l.W :=
    f₆.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inr (by have := hdr_lt_slot l.W Public.aY (show sCtr < 32 by decide); simp only; omega_using [this]))
      (by omega_using [lY, hnw, hT, hoZ])
  have hk₄ : Keep mmRegs s₃ s₄ := ⟨fun r hr => g₄ r (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
    (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
    (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
    (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
    (fun h => hr (by subst h; decide)), rd₄, wr₄⟩
  dsimp only [Final]
  refine ⟨?_, fun q => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hY₆, vY]; exact Nat.mod_lt _ hXp
  · rw [hY₆, vY, Nat.mod_mod, cY q, Nat.mul_mod, hY₁, hyc q, ← Nat.mul_mod]
  · refine (((mi₁.fw.trans f₂W).trans (show Frm _ _ s₂.mem s₄.mem from f₄W)).trans f₅W).trans ?_
    exact f₆.mono fun r h => by rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..
  · rw [me₆, word_writeW_self]
  · rw [k₆.2.2, k₅.2.2, wr₄', wr₂, k₁.2.2]
  · rw [k₆.gpr (by decide), d₅, sub₄.rdi, hc.rdi]
  · exact ((((k₁.trans k₂).trans k₃).trans hk₄).trans k₅).trans k₆ |>.mono (by decide)


/-- `Ifma.exp` of a one-lane layout, for the prime's `W` words and an
exponent of at most `8 W` bytes: `CrtExpL.ok`'s claims, but its frame also
covers `sCtr` (which it restores: `exp_ok`). -/
theorem expW_ok (hl : PubOk l) {s : State} {B : Addr} {Z o w : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    (hc : SubCtx s B Z o w l.W minv) (hT : o + slot l.W 8 + wsTab l.W ≤ Z)
    (hn : wv s.mem (off B o) (slot l.W Public.aN) l.W = X)
    (hinv : ((word s.mem (off B o) (slot l.W Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot l.W Crt.aXc) l.W < X)
    (hxc : Q → wv s.mem (off B o) (slot l.W Crt.aXc) l.W % X = x * 2 ^ (64 * l.W) % X)
    (hyl : wv s.mem (off B o) (slot l.W Public.aY) l.W < X)
    (hyc : Q → wv s.mem (off B o) (slot l.W Public.aY) l.W % X = 2 ^ (64 * l.W) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hLW : eb.length ≤ 8 * l.W) (he : Src s B Z ep eb) :
    WP isa (seqs (exp l sp sl)) s fun t =>
      wv t.mem (off B o) (slot l.W Public.aY) l.W < X ∧
      (Q → wv t.mem (off B o) (slot l.W Public.aY) l.W % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * l.W) % X) ∧
      Frm (off B o) (expRanges l.W) s.mem t.mem ∧
      word t.mem (off B o) (8 * sCtr) = word s.mem (off B o) (8 * sCtr) ∧
      t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧ Keep mmRegs s t :=
  C0.wp (expW_chain hl hc hT hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hLW he)

/-- `fits`: ZF, whether the workspace has `l.W` words and the exponent at
most `8 l.W` bytes. -/
theorem fits_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    {sl L : Nat} (hsl : sl < 32) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 L) (hL : L < 2 ^ 31)
    (hwx : wx < 2 ^ 31) (hW : l.W < 2 ^ 24) :
    WP isa (.block (fits l sl)) s fun t =>
      t.mem = s.mem ∧ t.zf = some (decide (wx = l.W ∧ L ≤ 8 * l.W)) ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hs := hc.scr
  have hn := hs.nowrap
  have hlo := hc.lo
  have hT := hc.hi
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hw8 := hdr_lt_slot w 8 hsl
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi => by
    rw [off_off]; exact hs.ld (by have := hdr_lt_slot wx 8 hi; unfold tabBytes at hT; omega_using [this, hT])
  have hldL : InRegions (s.rd ++ s.wr) (off B (8 * sl)) 8 := hs.ld (by omega_using [hw8, hlo, hT])
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem ∧
    t.zf = some (decide (wx = l.W ∧ L ≤ 8 * l.W))) ?_ rfl) fun t ⟨⟨m, z⟩, k⟩ => ⟨m, z, k⟩
  unfold fits
  xrun [State.ea, hdr, ws, hc.rdi, hdrOff, hld sW (by decide), hld sLink (by decide), hc.hdr.hw, hc.link, hldL, hel]
  rw [AmmSym.se_ofNat (show l.W < 2 ^ 31 by omega_using [hW]),
    AmmSym.se_ofNat (show 8 * l.W + 1 < 2 ^ 31 by omega_using [hW]), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega_using [hL]),
    Nat.mod_eq_of_lt (show 8 * l.W + 1 < 2 ^ 64 by omega_using [hW])]
  have inj : ∀ {a b : Nat}, a < 2 ^ 64 → b < 2 ^ 64 → BitVec.ofNat 64 a = BitVec.ofNat 64 b → a = b :=
    fun ha hb h => by
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  by_cases h : L ≤ 8 * l.W
  · rw [decide_eq_true (show L < 8 * l.W + 1 by omega_using [h]),
      show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true) + 1) = 0 by decide,
      show ∀ x : BitVec 64, (x ||| 0) = x from fun x => by simp]
    by_cases hw : wx = l.W
    · subst hw; simp [h]
    · simp only [hw, false_and, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h0
      refine hw (inj (by omega_using [hwx]) (by omega_using [hW]) ?_)
      have := congrArg (· ^^^ BitVec.ofNat 64 l.W) h0
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      exact this.trans (BitVec.zero_xor (x := BitVec.ofNat 64 l.W))
  · rw [decide_eq_false (show ¬ L < 8 * l.W + 1 by omega_using [h]),
      show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false) + 1) = 1 by decide]
    simp [h]

/-- What `CrtExpL.ok` claims after an exponentiation from `s` to `t`. -/
def EPost (s : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) (X x : Nat) (Q : Prop) (eb : List Byte)
    (t : State) : Prop :=
  SubCtx t B Z o w wx minv ∧ wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
    (Q → wv t.mem (off B o) (slot wx Public.aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
    Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t

/-- `CrtExpL.ok`'s hypotheses. -/
structure EPre (s : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) (X x : Nat) (Q : Prop)
    (sp sl : Nat) (ep : Addr) (eb : List Byte) : Prop where
  hc : SubCtx s B Z o w wx minv
  hT : o + slot wx 8 + wsTab wx ≤ Z
  hw2 : 2 ≤ wx
  hwx : wx ≤ w
  hw30 : w < 2 ^ 30
  hn : wv s.mem (off B o) (slot wx Public.aN) wx = X
  hinv : ((word s.mem (off B o) (slot wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  hodd : X % 2 = 1
  hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X
  hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X
  hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X
  hyc : Q → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X
  hsp : sp < 32
  hsl : sl < 32
  hep : word s.mem B (8 * sp) = ep
  hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length
  hL1 : 1 ≤ eb.length
  hL2 : eb.length ≤ 1024
  he : Src s B Z ep eb

/-- The hypotheses after code that writes only `rax`, `rcx` and `rdx`. -/
theorem EPre.keep {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    {sp sl : Nat} {ep : Addr} {eb : List Byte} (h : EPre s B Z o w wx minv X x Q sp sl ep eb)
    (hm : t.mem = s.mem) (hk : Keep [.rax, .rcx, .rdx] s t) : EPre t B Z o w wx minv X x Q sp sl ep eb := by
  obtain ⟨hc, hT, hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hL1, hL2, he⟩ := h
  rw [← hm] at hn hinv hxl hxc hyl hyc hep hel
  exact ⟨SubCtx.of_frmW hc hT (rs := []) (fun x _ => by rw [hm]) (by simp) hk.2.2 (hk.gpr (by decide)), hT, hw2,
    hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hL1, hL2,
    he.congr (fun x _ => by rw [hm]) hk.2.1 hk.2.2⟩

/-- `EPost` from a state that code writing only `rax`, `rcx` and `rdx` left. -/
theorem EPost.keep {s t u : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    {eb : List Byte} (h : EPost t B Z o w wx minv X x Q eb u) (hm : t.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx] s t) : EPost s B Z o w wx minv X x Q eb u :=
  ⟨h.1, h.2.1, h.2.2.1, by rw [← hm]; exact h.2.2.2.1, (hk.trans h.2.2.2.2).mono (by decide)⟩

/-- A layout's vector code if it fits, else `rest`. -/
theorem disp_ok (hl : PubOk l) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    {sp sl : Nat} {ep : Addr} {eb : List Byte} (h : EPre s B Z o w wx minv X x Q sp sl ep eb) {rest : Prog isa}
    (hr : ∀ t, EPre t B Z o w wx minv X x Q sp sl ep eb → WP isa rest t (EPost t B Z o w wx minv X x Q eb)) :
    WP isa (.seq (.block (fits l sl)) (.ite .e (seqs (exp l sp sl)) rest)) s (EPost s B Z o w wx minv X x Q eb) := by
  have hW := (PubOk.sizes hl).2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (fits_ok h.hc h.hsl h.hel (by have := h.hL2; omega_using [this])
    (by have a := h.hwx; have b := h.hw30; omega_using [a, b]) (by omega_using [hW])) fun t ⟨m₁, z₁, k₁⟩ => ?_)
  have h₁ := h.keep m₁ k₁
  by_cases hf : wx = l.W ∧ eb.length ≤ 8 * l.W
  · refine WP.ite true (by simp [eval, z₁, hf]) (fun _ => ?_) (by intro h; cases h)
    obtain ⟨rfl, hLW⟩ := hf
    refine WP.mono (expW_ok hl h₁.hc h₁.hT h₁.hn h₁.hinv h₁.hodd h₁.hxl h₁.hxc h₁.hyl h₁.hyc h₁.hsp h₁.hsl h₁.hep
      h₁.hel h₁.hL1 hLW h₁.he) fun u ⟨a, b, f, wd, wr, di, k⟩ => ?_
    have f' : Frm (off B o) (crtExpRanges5 l.W) t.mem u.mem := Frm.drop_word f wd
    exact EPost.keep ⟨SubCtx.of_frmW h₁.hc h₁.hT f' (crtExpRanges5_ok l.W) wr di, a, b, f', k⟩ m₁ k₁
  · exact WP.ite false (by simp [eval, z₁, hf]) (by intro h; cases h)
      (fun _ => WP.mono (hr t h₁) fun u hu => hu.keep m₁ k₁)

/-- FFDH's exponentiation with AVX512_IFMA: `Ifma.code`, for the three
layouts that fit, else `CrtExpL.w4`. -/
def expL (M : Mont) : CrtExpL M where
  code := code M.mm
  ne _ _ := by simp [Impl.Ffdh.X86_64.Ifma.code]
  ok hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he := by
    have h := EPre.mk hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he
    exact disp_ok (.inl rfl) h fun _ h₁ => disp_ok (.inr (.inl rfl)) h₁ fun _ h₂ => disp_ok (.inr (.inr rfl)) h₂
      fun _ h₃ => (CrtExpL.w4 M).ok h₃.hc h₃.hT h₃.hw2 h₃.hwx h₃.hw30 h₃.hn h₃.hinv h₃.hodd h₃.hxl h₃.hxc h₃.hyl
        h₃.hyc h₃.hsp h₃.hsl h₃.hep h₃.hel h₃.hL1 h₃.hL2 h₃.he

end VG.Proof.Ffdh.X86_64.Ifma
