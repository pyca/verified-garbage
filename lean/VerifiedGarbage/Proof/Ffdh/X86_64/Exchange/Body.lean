module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Data
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! ### `Ffdh.X86_64.Exchange.Entry`, which only this module used -/

section

/-! # FFDH public-key validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  (((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut)) (s.gpr .rdi)).writeW (off B (8 * sDom)) (s.gpr .rdx)).writeW (off B (8 * sDomLen)) (s.gpr .rcx)).writeW (off B (8 * sK)) (s.gpr .r8)).writeW (off B (8 * sX)) (s.gpr .r9)).writeW (off B (8 * sXl)) (stackArg s 0)).writeW (off B (8 * sY)) (stackArg s 1))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut) = s.gpr .rdi ∧
    word m B (8 * sDom) = s.gpr .rdx ∧
    word m B (8 * sDomLen) = s.gpr .rcx ∧
    word m B (8 * sK) = s.gpr .r8 ∧
    word m B (8 * sX) = s.gpr .r9 ∧
    word m B (8 * sXl) = stackArg s 0 ∧
    word m B (8 * sY) = stackArg s 1 ∧ Outside B 0 (8 * 23) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem exEntry_ok {s : State} {B : Addr} (hB : stackArg s 3 = B)
    (hw : ∀ i < 23, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(VG.Impl.Ffdh.X86_64.Domain.sOut, s.gpr .rdi), (sDom, s.gpr .rdx), (sDomLen, s.gpr .rcx),
        (sK, s.gpr .r8), (sX, s.gpr .r9), (sXl, stackArg s 0), (sY, stackArg s 1)] ∧
      Outside B 0 (8 * 23) s.mem t.mem ∧ Keep [.rax, .r10, .r11, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 4)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .r11, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.entry save
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
          hw VG.Impl.Ffdh.X86_64.Domain.sOut (by decide),
          hw sDom (by decide),
          hw sDomLen (by decide),
          hw sK (by decide),
          hw sX (by decide),
          hw sXl (by decide),
          hw sY (by decide), ha 3 (by decide), ha 0 (by decide), ha 1 (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hD, hL, hK, hX, hXl, hY, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hO hD hL hK hX hXl hY ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hO, hD, hL, hK, hX, hXl, hY]

end VG.Proof.Ffdh.X86_64.Exchange

end

end

/-! # FFDH exchange on x86-64: entry and modulus validation -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Exchange/Context.lean`, which only this module imported.
section

/-! # FFDH exchange on x86-64: memory and lengths -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure ExCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  dl : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat ∨ (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat
  ol : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  yl : (stackArg s 2).toNat = (s.gpr .r8).toNat
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  hZ : 128 * (s.gpr .r8).toNat + 256 ≤ (stackArg s 4).toNat * 8
  hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8)
  dom : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdx) (exDom s)
  x : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .r9) (exX s)
  y : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (stackArg s 1) (exY s)
  ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  out : ∀ i < (s.gpr .r8).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i) 1
  sep : ∀ i < (s.gpr .r8).toNat, (stackArg s 4).toNat * 8 ≤
    ofs (stackArg s 3) (s.gpr .rdi + BitVec.ofNat 64 i)

theorem exCtx_of {s : State} (h : exPre s) : ExCtx s := by
  obtain ⟨hsp, hrd, hwr, _, _, _, dos, _, dds, dxs, dys, _, wO, wD, wX, wY, wS,
    _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hol, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hol, hyl, hxl1, hxl2, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dxs,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dys, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 40⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
      congr 2
      omega_using []]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega_using [hol, hi]) (by omega_using [])⟩
  · intro i hi
    exact out_scr dos (contains_byte _ (by omega_using [hol, hi]) (by omega_using []))

end VG.Proof.Ffdh.X86_64.Exchange
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def exOf (s : State) : ExP :=
  ⟨stackArg s 3, (stackArg s 4).toNat * 8, (s.gpr .r8).toNat, (s.gpr .rcx).toNat, s.gpr .rdx,
    exDom s, s.gpr .rdi, s.gpr .r9, (stackArg s 0).toNat, stackArg s 1, exY s, s.gpr .rsp⟩

theorem entry_base {s : State} (c : ExCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) s fun t =>
      Base (exOf s) (exX s) t ∧ t.gpr .rdi = (exOf s).B ∧
      InScr (exOf s).B (exOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (exOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exEntry_ok rfl (fun i hi => c.hs.st (by omega_using [hZ, hi])) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (exOf s).B (exOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [exOf]; omega_using [hZ])
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, bytesAt_length _ _ _,
    c.xl1, c.xl2, c.hZ, c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k, c.y.congrK hi k,
    ?_, (fun i hi => by rw [k.2.2]; exact c.out i hi), c.sep⟩, hd, hi, hs, k.mono (by decide)⟩
  · change (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat).length = (s.gpr .r8).toNat
    rw [bytesAt_length, c.yl]
  · change Slots t.mem (stackArg s 3) (exOf s).headers
    simp only [ExP.headers, exOf, ofNat_toNat64]
    intro e he
    apply hh e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem dom_base {p : ExP} {xb : List Byte} {s : State} (h : Base p xb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p xb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega_using [hZ]) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [ExP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, _, _, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_using [hZ])
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_using [hi])
  refine ⟨h.keep hi k ?_, hz, hd, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [ExP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sG sFn; omega_using [hi]) (by unfold sQ sFn; omega_using [hi])

end VG.Proof.Ffdh.X86_64.Exchange
