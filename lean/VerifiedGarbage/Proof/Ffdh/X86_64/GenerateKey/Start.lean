module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead

/-! ### `Ffdh.X86_64.GenerateKey.Context`, which only this module used -/

section

/-! # FFDH key-generation attempts on x86-64: inputs and disjoint outputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure GkCtx (s : State) : Prop where
  k1 : 64 ≤ (stackArg s 0).toNat
  k2 : (stackArg s 0).toNat ≤ 1024
  dl : (s.gpr .r9).toNat = 2 * (stackArg s 0).toNat ∨ (s.gpr .r9).toNat = 3 * (stackArg s 0).toNat
  xl : (s.gpr .rsi).toNat = (stackArg s 0).toNat
  yl : (s.gpr .rcx).toNat = (stackArg s 0).toNat
  rl : (stackArg s 2).toNat = (stackArg s 0).toNat
  hZ : 128 * (stackArg s 0).toNat + 256 ≤ (stackArg s 4).toNat * 8
  hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8)
  dom : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .r8) (gkDom s)
  rand : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (stackArg s 1) (gkRand s)
  ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  x : OutOk s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdi) (stackArg s 0).toNat
  y : OutOk s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdx) (stackArg s 0).toNat
  xy : Apart (s.gpr .rdi) (stackArg s 0).toNat (s.gpr .rdx) (stackArg s 0).toNat
  xd : Apart (s.gpr .rdi) (stackArg s 0).toNat (s.gpr .r8) (s.gpr .r9).toNat
  xr : Apart (s.gpr .rdi) (stackArg s 0).toNat (stackArg s 1) (stackArg s 0).toNat
  yd : Apart (s.gpr .rdx) (stackArg s 0).toNat (s.gpr .r8) (s.gpr .r9).toNat
  yr : Apart (s.gpr .rdx) (stackArg s 0).toNat (stackArg s 1) (stackArg s 0).toNat

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end

/-! ### `Ffdh.X86_64.GenerateKey.Entry`, which only this module used -/

section

/-! # FFDH key-generation attempts on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * sX)) (s.gpr .rdi)).writeW (off B (8 * sY)) (s.gpr .rdx)).writeW (off B (8 * sDom)) (s.gpr .r8)).writeW (off B (8 * sDomLen)) (s.gpr .r9)).writeW (off B (8 * sK)) (stackArg s 0)).writeW (off B (8 * sRand)) (stackArg s 1))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .r8 ∧
    word m B (8 * sDomLen) = s.gpr .r9 ∧
    word m B (8 * sK) = stackArg s 0 ∧
    word m B (8 * sY) = s.gpr .rdx ∧
    word m B (8 * sX) = s.gpr .rdi ∧
    word m B (8 * sRand) = stackArg s 1 ∧ Outside B 0 (8 * 26) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem gkEntry_ok {s : State} {B : Addr} (hB : stackArg s 3 = B)
    (hw : ∀ i < 26, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .r8), (sDomLen, s.gpr .r9), (sK, stackArg s 0),
        (sY, s.gpr .rdx), (sX, s.gpr .rdi), (sRand, stackArg s 1)] ∧
      Outside B 0 (8 * 26) s.mem t.mem ∧ Keep [.rax, .r10, .r11, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 4)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .r11, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry save
      simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      dsimp only [VG.Impl.Rsa.X86_64.Crt.stk, stackArgAddr] at ha ⊢
      xrun [State.ea, ws, hdrOff, stackArg, stackArgAddr, hB',
        hw 0 (by decide),
        hw 1 (by decide),
        hw 2 (by decide),
        hw 3 (by decide),
        hw 4 (by decide),
        hw 5 (by decide),
        hw sDom (by decide),
        hw sDomLen (by decide),
        hw sK (by decide),
        hw sY (by decide),
        hw sX (by decide),
        hw sRand (by decide), ha 3 (by decide), ha 0 (by decide), ha 1 (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, hY, hX, hXl, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK hY hX hXl ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hD, hL, hK, hY, hX, hXl]

end VG.Proof.Ffdh.X86_64.GenerateKey

end

end


/-! # FFDH key-generation attempts on x86-64: entry and modulus checks -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def gkOf (s : State) : GkP :=
  ⟨stackArg s 3, (stackArg s 4).toNat * 8, (stackArg s 0).toNat, (s.gpr .r9).toNat,
    s.gpr .r8, gkDom s, s.gpr .rdi, s.gpr .rdx, stackArg s 1, s.gpr .rsp,
    Spec.Ffdh.privateValid (gkA s) (gkS s), lead (KeyScalar.bnd (stackArg s 0).toNat (gkDom s)),
    smear64 ((KeyScalar.bnd (stackArg s 0).toNat (gkDom s)).getD (lead (KeyScalar.bnd (stackArg s 0).toNat (gkDom s))) 0),
    Spec.Ffdh.scalarOfOctets (gkA s)⟩

theorem gkOf_bounded (s : State) : (gkOf s).Bounded := ⟨rfl, rfl⟩

theorem entry_base {s : State} (c : GkCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s fun t =>
      Base (gkOf s) (gkRand s) t ∧ t.gpr .rdi = (gkOf s).B ∧
      InScr (gkOf s).B (gkOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (gkOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (gkEntry_ok rfl (fun i hi => c.hs.st (by omega_using [hZ, hi])) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (gkOf s).B (gkOf s).Z s.mem t.mem :=
    InScr.of_outside hf (by dsimp only [gkOf]; omega_using [hZ])
  have hdom : (gkDom s).length = 2 * (stackArg s 0).toNat ∨ (gkDom s).length = 3 * (stackArg s 0).toNat := by
    rw [show (gkDom s).length = (s.gpr .r9).toNat from bytesAt_length _ _ _]; exact c.dl
  have hrl : (gkRand s).length = (stackArg s 0).toNat := by
    change (gkRand s).length = (stackArg s 0).toNat
    rw [bytesAt_length, c.rl]
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, c.hZ, c.hs.congr k.2.2,
    c.dom.congrK hi k, c.rand.congrK hi k,
    ⟨fun i hi => by rw [k.2.2]; exact c.x.wr i hi, c.x.sep⟩,
    ⟨fun i hi => by rw [k.2.2]; exact c.y.wr i hi, c.y.sep⟩,
    c.xy, c.xd, c.xr, c.yd, c.yr, ?_, rfl, ?_, fun hm => GkP.bounded_cut (gkOf_bounded s) hk hdom hrl hm⟩,
    hd, hi, hs, k.mono (by decide)⟩
  · exact hrl
  · change Slots t.mem (stackArg s 3) (gkOf s).headers
    simp only [GkP.headers, gkOf, ofNat_toNat64]
    exact hh
  · have hbl := KeyScalar.bnd_length hdom
    have hn : KeyScalar.bnd (stackArg s 0).toNat (gkDom s) ≠ [] := by
      intro he; rw [he] at hbl; simp at hbl; omega_using [hk, hbl]
    have := lead_lt hn
    rw [hbl] at this
    exact this

theorem dom_base {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p rb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega_using [hZ]) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [GkP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, hG, hQ, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_using [hZ])
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_using [hi])
  refine ⟨h.keep hi k ?_, hz, hd, hG, hQ, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sG sFn; omega_using [hi]) (by unfold sQ sFn; omega_using [hi])

end VG.Proof.Ffdh.X86_64.GenerateKey
