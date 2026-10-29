module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH domain validation on x86-64: retained public data -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Domain bytes and all pointers are public under the domain-check contract. -/
structure CdP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  sp : Addr

abbrev CdP.w (p : CdP) : Nat := (p.k + 7) / 8
abbrev CdP.pb (p : CdP) : List Byte := p.dom.take p.k
abbrev CdP.P (p : CdP) : Nat := Spec.Rsa.os2ip p.pb
abbrev CdP.gb (p : CdP) : List Byte := (p.dom.drop p.k).take p.k
abbrev CdP.G (p : CdP) : Nat := Spec.Rsa.os2ip p.gb
abbrev CdP.qb (p : CdP) : List Byte := (p.dom.drop (2 * p.k)).take p.k
abbrev CdP.Q (p : CdP) : Nat := Spec.Rsa.os2ip p.qb
abbrev CdP.params (p : CdP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom
abbrev CdP.mv (p : CdP) : Bool := Spec.Rsa.modulusValid p.P p.k
abbrev CdP.gr (p : CdP) : Prop := 1 < p.G ∧ 2 * (p.G / 2) + 1 < p.P
abbrev CdP.qr (p : CdP) : Prop := p.Q % 2 = 1 ∧ 1 < p.Q ∧ 2 * (p.Q / 2) + 1 < p.P
abbrev CdP.ld (p : CdP) : Nat := lead p.qb
abbrev CdP.nq (p : CdP) : Nat := p.k - p.ld
abbrev CdP.eqp (p : CdP) : Addr := off (off p.dp (2 * p.k)) p.ld
abbrev CdP.eqb (p : CdP) : List Byte := p.qb.drop p.ld
abbrev CdP.wq (p : CdP) : Nat := wsWords p.nq

def CdP.headers (p : CdP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k)]

structure Base (p : CdP) (s : State) : Prop where
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  doml : p.dom.length = p.dl
  hZ : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  dom : Src s p.B p.Z p.dp p.dom
  hdr : Slots s.mem p.B p.headers

theorem Base.plen {p : CdP} {s : State} (h : Base p s) : p.pb.length = p.k := by
  simp only [CdP.pb, List.length_take, h.doml]
  rcases h.dl with hd | hd <;> rw [hd] <;> omega

theorem Base.glen {p : CdP} {s : State} (h : Base p s) : p.gb.length = p.k := by
  simp only [CdP.gb, List.length_take, List.length_drop, h.doml]
  rcases h.dl with hd | hd <;> rw [hd] <;> omega

theorem Base.qlen {p : CdP} {s : State} (h : Base p s) (hq : p.dl = 3 * p.k) : p.qb.length = p.k := by
  simp only [CdP.qb, List.length_take, List.length_drop, h.doml, hq]
  omega

theorem Base.keep {p : CdP} {s t : State} {rs : List Reg} (h : Base p s)
    (hf : InScr p.B p.Z s.mem t.mem) (k : Keep rs s t)
    (hh : ∀ e ∈ p.headers, word t.mem p.B (8 * e.1) = word s.mem p.B (8 * e.1)) : Base p t :=
  ⟨h.k1, h.k2, h.dl, h.doml, h.hZ, h.scr.congr k.2.2, h.dom.congrK hf k,
    fun e he => (hh e he).trans (h.hdr e he)⟩

/-- Changes inside either inner workspace preserve the outer header. -/
theorem child_frame {s t : State} {B : Addr} {Z o w wx L : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} (hc : SubCtx s B Z o w wx mi) (hL : o + L ≤ Z)
    (hf : Frm (off B o) rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) :
    (∀ d, d + 8 ≤ o → word t.mem B d = word s.mem B d) ∧ InScr B Z s.mem t.mem := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hLL : o + L ≤ 2 ^ 64 := by omega
  refine ⟨fun d hd => hf.word_below hr hLL (by omega) hd, ?_⟩
  refine InScr.of_frm (hf.rebase (by omega) (fun r he => by have := hr r he; omega)) ?_
  simp only [shiftRanges, List.mem_map]
  rintro r ⟨r', hr', rfl⟩
  have := hr r' hr'
  simp only
  omega

theorem Base.child {p : CdP} {s t : State} {wx L : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    {regs : List Reg} (h : Base p s) (hc : SubCtx s p.B p.Z (inner p.w) p.w wx mi)
    (hL : inner p.w + L ≤ p.Z) (hf : Frm (off p.B (inner p.w)) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (k : Keep regs s t) :
    Base p t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  obtain ⟨hh, hi⟩ := child_frame hc hL hf hr
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
  have hh' : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi => hh _ (by omega)
  refine ⟨h.keep hi k ?_, hi, hh'⟩
  intro e he
  simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact hh' _ (by dsimp only; decide)

end VG.Proof.Ffdh.X86_64.CheckDomain
