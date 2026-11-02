module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.DerivePublic
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore

import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Entry
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
/-! # FFDH public-value derivation on x86-64: entry, and zeros in y -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/DerivePublic/Context.lean`, which only this module imported.
section

/-! # FFDH public-value derivation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure DvCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  dl : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat ∨ (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat
  yl : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  hZ : 128 * (s.gpr .r8).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdx) (dvDom s)
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (dvX s)
  y : OutOk s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (s.gpr .r8).toNat
  yd : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .rdx) (s.gpr .rcx).toNat
  yx : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat
  ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8

theorem dvCtx_of {s : State} (h : dvPre s) : DvCtx s := by
  obtain ⟨_, hrd, hwr, dyd, dyx, dys, _, dds, dxs, _, wY, wD, wX, wS,
    _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hyl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds, hxl1, hxl2,
    src_of_region (by rw [hrd]; simp) (by omega) dxs, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyd (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyx (by omega) (by omega))
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
      congr 2
      omega]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Ffdh.X86_64.DerivePublic
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base)

/-- Private-key validation's parameters: y is the output, read as zeros
once zeroed. -/
def dvOf (s : State) : KpP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx,
    dvDom s, s.gpr .r9, (stackArg s 0).toNat, s.gpr .rdi, List.replicate (s.gpr .r8).toNat 0, s.gpr .rsp,
    Spec.Ffdh.privateValid (dvA s) (Spec.Rsa.os2ip (dvX s))⟩

/-- y may be written. -/
abbrev YOut (p : KpP) (s : State) : Prop := OutOk s p.B p.Z p.yp p.k

theorem YOut.of_wr {p : KpP} {s t : State} (h : YOut p s) (hw : t.wr = s.wr) : YOut p t :=
  ⟨fun i hi => by rw [hw]; exact h.wr i hi, h.sep⟩

/-- Before y is zeroed: `Base` but for y, which may be written. -/
structure Pre0 (p : KpP) (xb : List Byte) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  yb : p.yb = List.replicate p.k 0
  xlen : xb.length = p.xl
  xl1 : 1 ≤ p.xl
  xl2 : p.xl ≤ p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  dom : Src s p.B p.Z p.dp p.dom
  x : Src s p.B p.Z p.xp xb
  y : YOut p s
  yd : Apart p.yp p.k p.dp p.dl
  yx : Apart p.yp p.k p.xp p.xl
  hdr : Slots s.mem p.B p.headers
  valid : Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip xb) = p.sv

theorem entry_pre0 {s : State} (c : DvCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.entry) s fun t =>
      Pre0 (dvOf s) (dvX s) t ∧ t.gpr .rdi = (dvOf s).B ∧
      InScr (dvOf s).B (dvOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (dvEntry_ok rfl (fun i hi => c.hs.st (by omega)) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (dvOf s).B (dvOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [dvOf]; omega)
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, rfl, bytesAt_length _ _ _, c.xl1, c.xl2, c.hZ,
    c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k,
    ⟨fun i hi => by rw [k.2.2]; exact c.y.wr i hi, c.y.sep⟩, c.yd, c.yx, ?_, rfl⟩,
    hd, hi, hs, k.mono (by decide)⟩
  change Slots t.mem (stackArg s 1) (dvOf s).headers
  simp only [KpP.headers, dvOf, ofNat_toNat64]
  intro e he
  exact hh e he

/-- Zeros in y: private-key validation's inputs, with y read as zeros. -/
theorem zero_base {p : KpP} {xb : List Byte} {s : State} (h : Pre0 p xb s) (hd : s.gpr .rdi = p.B) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s fun t =>
      Base p xb t ∧ YOut p t ∧ t.gpr .rdi = p.B ∧
      (∀ a, (∀ i < p.k, a ≠ off p.yp i) → t.mem a = s.mem a) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  refine WP.mono (zeroOut_ok h.scr hd (by omega) (by decide) (by decide)
    (h.hdr (sY, p.yp) (by simp [KpP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) (by omega) (by omega) h.y)
    fun t ⟨hz, hf, k⟩ => ?_
  have hout : Outside p.B p.Z (2 ^ 64 - p.Z) s.mem t.mem := by
    intro a ha
    have ha64 : ofs p.B a < 2 ^ 64 := (a - p.B).isLt
    apply hf
    intro i hi he
    have := h.y.sep i hi
    rw [← he] at this
    omega
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d :=
    fun d hd => hout.word (Or.inl hd) (by have := h.scr.nowrap; omega)
  have hdom : Src t p.B p.Z p.dp p.dom := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.dom.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yd j hj i (by rw [← h.doml]; exact hi)))]; exact h.dom.val i hi,
    h.dom.out⟩
  have hx : Src t p.B p.Z p.xp xb := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.x.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yx j hj i (by rw [← h.xlen]; exact hi)))]; exact h.x.val i hi,
    h.x.out⟩
  have hy : Src t p.B p.Z p.yp p.yb := by
    rw [h.yb]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.k := by simpa only [List.length_replicate] using hi
      obtain ⟨r, hr, hc⟩ := h.y.wr i hi'
      exact ⟨r, List.mem_append_right _ (by rw [k.2.2]; exact hr), hc⟩
    · intro i hi
      rw [hz i (by simpa only [List.length_replicate] using hi)]
      exact (List.getElem_replicate hi).symm
    · intro i hi
      exact h.y.sep i (by simpa only [List.length_replicate] using hi)
  refine ⟨⟨h.k1, h.k2, h.dl, h.doml, by rw [h.yb, List.length_replicate], h.xlen, h.xl1, h.xl2, h.hZ,
    h.scr.congr k.2.2, hdom, hx, hy, ?_, h.valid⟩, h.y.of_wr k.2.2, (k.gpr (by decide)).trans hd,
    hf, fun i hi => hh _ (by omega), k.mono (by decide)⟩
  intro e he
  rw [hh _ (by
    simp only [KpP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sDom, sDomLen, sK, sY, sX, sXl, sFn] <;> omega)]
  exact h.hdr e he

end VG.Proof.Ffdh.X86_64.DerivePublic
