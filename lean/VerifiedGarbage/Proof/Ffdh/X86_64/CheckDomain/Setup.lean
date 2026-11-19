module

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Spec.Ffdh.Contract

/-! ### `Ffdh.X86_64.CheckDomain.Data`, which this module and modules that import it used -/

section

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
  rcases h.dl with hd | hd <;> rw [hd] <;> omega_using []

theorem Base.glen {p : CdP} {s : State} (h : Base p s) : p.gb.length = p.k := by
  simp only [CdP.gb, List.length_take, List.length_drop, h.doml]
  rcases h.dl with hd | hd <;> rw [hd] <;> omega_using []

theorem Base.qlen {p : CdP} {s : State} (h : Base p s) (hq : p.dl = 3 * p.k) : p.qb.length = p.k := by
  simp only [CdP.qb, List.length_take, List.length_drop, h.doml, hq]
  omega_using []

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
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hLL : o + L ≤ 2 ^ 64 := by omega_using [hL, hn]
  refine ⟨fun d hd => hf.word_below hr hLL (by omega_using [hn, hi, h256]) hd, ?_⟩
  refine InScr.of_frm (hf.rebase (by omega_using [hn, hi, h256]) (fun r he => by have := hr r he; omega_using [hLL, this])) ?_
  simp only [shiftRanges, List.mem_map]
  rintro r ⟨r', hr', rfl⟩
  have := hr r' hr'
  simp only
  omega_using [hL, this]

theorem Base.child {p : CdP} {s t : State} {wx L : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    {regs : List Reg} (h : Base p s) (hc : SubCtx s p.B p.Z (inner p.w) p.w wx mi)
    (hL : inner p.w + L ≤ p.Z) (hf : Frm (off p.B (inner p.w)) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (k : Keep regs s t) :
    Base p t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) := by
  obtain ⟨hh, hi⟩ := child_frame hc hL hf hr
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_using []
  have hh' : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi => hh _ (by omega_using [h256, hi])
  refine ⟨h.keep hi k ?_, hi, hh'⟩
  intro e he
  simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact hh' _ (by dsimp only; decide)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: initialize p's workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The p workspace, retaining its public domain pointers. -/
structure Work (p : CdP) (mi : BitVec 64) (s : State) : Prop where
  base : Base p s
  mem : SubMem s p.B p.Z (inner p.w) p.w p.w mi
  xv : XVals s p.B (inner p.w) p.w mi p.P
  ws : word s.mem p.B (8 * sWs) = off p.B (inner p.w)
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

/-- Each arithmetic stage changes only scratch and preserves the six saved registers. -/
def StepPost (p : CdP) (s : State) (P : State → Prop) (t : State) : Prop :=
  P t ∧ InScr p.B p.Z s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t

theorem StepPost.trans {p : CdP} {P Q : State → Prop} {s t u : State}
    (h : StepPost p s P t) (h' : StepPost p t Q u) : StepPost p s Q u :=
  ⟨h'.1, h.2.1.trans h'.2.1, fun i hi => (h'.2.2.1 i hi).trans (h.2.2.1 i hi),
    keep_trans h.2.2.2 h'.2.2.2⟩

theorem setup_work {p : CdP} {s : State} (h : Base p s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      (StepPost p s fun t => ∃ mi, Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w)) := by
  have hk := h.k1
  have hZ := h.hZ
  refine WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb)
    h.scr hd h.k1 h.k2 h.hZ (h.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (h.dom.take p.k) h.plen
    (valid_facts hm hk).1) fun t ⟨mi, hc, hv, hWs, hf, k⟩ => ?_
  change Frm p.B (setupR p.w) s.mem t.mem at hf
  have hw := room_k hk hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hw
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_using []
  have hh : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 =>
    hf.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith) (by omega_using [hi])
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [setupR, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith)
  have hb : Base p t := h.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide))
  refine ⟨⟨mi, ⟨hb, hc.toMem, hv, hWs, ?_, ?_⟩, hc.rdi⟩, hi, ?_, k⟩
  · rw [hh _ (by decide) (by decide) (by decide) (by decide)]; exact hG
  · rw [hh _ (by decide) (by decide) (by decide) (by decide)]; exact hQ
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sW; omega_using [hi]) (by unfold sWs sFn; omega_using [hi]) (by unfold sArr; omega_using [hi])

end VG.Proof.Ffdh.X86_64.CheckDomain
