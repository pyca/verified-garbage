module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH exchange on x86-64: data retained across arithmetic -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Public inputs, including only the scalar-range status of the secret bytes. -/
structure KpP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  xp : Addr
  xl : Nat
  yp : Addr
  yb : List Byte
  sp : Addr
  sv : Bool

abbrev KpP.w (p : KpP) : Nat := (p.k + 7) / 8
abbrev KpP.pb (p : KpP) : List Byte := p.dom.take p.k
abbrev KpP.P (p : KpP) : Nat := Spec.Rsa.os2ip p.pb
abbrev KpP.mv (p : KpP) : Bool := Spec.Rsa.modulusValid p.P p.k
abbrev KpP.qb (p : KpP) : List Byte := (p.dom.drop (2 * p.k)).take p.k
abbrev KpP.Q (p : KpP) : Nat := Spec.Rsa.os2ip p.qb
abbrev KpP.gb (p : KpP) : List Byte := (p.dom.drop p.k).take p.k
abbrev KpP.G (p : KpP) : Nat := Spec.Rsa.os2ip p.gb

abbrev KpP.params (p : KpP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom

abbrev KpP.z (p : KpP) (xb : List Byte) : Nat := p.G ^ Spec.Rsa.os2ip xb % p.P
abbrev KpP.fl (p : KpP) (xb : List Byte) : Prop := 1 < p.z xb ∧ 2 * (p.z xb / 2) + 1 < p.P

/-- The outer argument header. -/
def KpP.headers (p : KpP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k), (sY, p.yp),
    (sX, p.xp), (sXl, BitVec.ofNat 64 p.xl)]

private theorem headers_lt (p : KpP) : ∀ e ∈ p.headers, e.1 < 32 := by
  simp [KpP.headers, sDom, sDomLen, sK, sY, sX, sXl, sFn]

structure Base (p : KpP) (xb : List Byte) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  ylen : p.yb.length = p.k
  xlen : xb.length = p.xl
  xl1 : 1 ≤ p.xl
  xl2 : p.xl ≤ p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  dom : Src s p.B p.Z p.dp p.dom
  x : Src s p.B p.Z p.xp xb
  y : Src s p.B p.Z p.yp p.yb
  hdr : Slots s.mem p.B p.headers
  valid : Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip xb) = p.sv

theorem Base.plen {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s) : p.pb.length = p.k := by
  simp only [KpP.pb, List.length_take, h.doml]
  rcases h.dl with hd | hd <;> rw [hd] <;> omega

theorem Base.params_none {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hd : p.dl = 2 * p.k) : p.params.q = none := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = none
  have hk := h.k1
  rw [h.doml, hd, ite_eq_right (by omega)]

theorem Base.params_some {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hd : p.dl = 3 * p.k) : p.params.q = some p.Q := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = some p.Q
  rw [h.doml, hd, ite_eq_left rfl]

theorem Base.keep {p : KpP} {xb : List Byte} {s t : State} {rs : List Reg} (h : Base p xb s)
    (hf : InScr p.B p.Z s.mem t.mem) (k : Keep rs s t)
    (hh : ∀ e ∈ p.headers, word t.mem p.B (8 * e.1) = word s.mem p.B (8 * e.1)) : Base p xb t :=
  ⟨h.k1, h.k2, h.dl, h.doml, h.ylen, h.xlen, h.xl1, h.xl2, h.hZ, h.scr.congr k.2.2,
    h.dom.congrK hf k, h.x.congrK hf k, h.y.congrK hf k,
    fun e he => (hh e he).trans (h.hdr e he), h.valid⟩

theorem Base.child {p : KpP} {xb : List Byte} {s t : State} {mi : BitVec 64} {rs : List (Nat × Nat)}
    {regs : List Reg} (h : Base p xb s)
    (hc : SubCtx s p.B p.Z (inner p.w) p.w p.w mi)
    (hf : Frm (off p.B (inner p.w)) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32) (k : Keep regs s t) :
    Base p xb t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  have hw := room_k h.k1 h.hZ
  obtain ⟨hh, hi⟩ := child_frm hc (by unfold inner at hw; omega) hf hr
  exact ⟨h.keep hi k (fun e he => hh e.1 (headers_lt p e he)), hi, fun i hi => hh i (by omega)⟩

/-- The setup writes only the layout and the inner workspace. -/
theorem setup_frame {p : KpP} {s t : State} (hk : 64 ≤ p.k) (hZ : 128 * p.k + 256 ≤ p.Z)
    (hf : Frm p.B (setupR p.w) s.mem t.mem) :
    InScr p.B p.Z s.mem t.mem ∧
      (∀ e ∈ p.headers, word t.mem p.B (8 * e.1) = word s.mem p.B (8 * e.1)) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
      (∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
        word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  have hw := room_k hk hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hw
  have hi8 : 8 * 32 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
  have hh : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 =>
    hf.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega) (by omega)
  refine ⟨InScr.of_frm hf ?_, ?_, ?_, hh⟩
  · simp only [setupR, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega
  · intro e he
    simp only [KpP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega) (by unfold sW; omega) (by unfold sWs sFn; omega) (by unfold sArr; omega)

end VG.Proof.Ffdh.X86_64.CheckPrivate
