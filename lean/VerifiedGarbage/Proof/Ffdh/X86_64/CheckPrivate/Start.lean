module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ffdh.X86_64.CheckPrivate.Contract`, which this module and modules that import it used -/

section

/-! # FFDH private-key validation on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def kpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let y : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let x : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, args] ∧ s.wr = [scr] ∧
    dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint y ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint x ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .rdx).toNat ∧ domainLenValid (s.gpr .rdx).toNat (s.gpr .rsi).toNat ∧
    (s.gpr .r8).toNat = (s.gpr .rdx).toNat ∧ 1 ≤ (stackArg s 0).toNat ∧ (stackArg s 0).toNat ≤ (s.gpr .rdx).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .rdx).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev kpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat

/-- y on entry. -/
abbrev kpY (s : State) : List Byte := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat

/-- x on entry. -/
abbrev kpX (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

def kpPost (s s' : State) : Prop :=
  domainValid (s.gpr .rdx).toNat (kpDom s) →
    ((s'.gpr .rax).setWidth 32).toNat = privateStatus (domainOf (s.gpr .rdx).toNat (kpDom s)) (os2ip (kpY s))
      (os2ip (kpX s))

/-- What timing may depend on, beyond the arguments. -/
def kpLeak (s : State) : List Nat :=
  (kpDom s).map (·.toNat) ++ (kpY s).map (·.toNat) ++
    [privateStatus (domainOf (s.gpr .rdx).toNat (kpDom s)) (os2ip (kpY s)) (os2ip (kpX s))]

def kpPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ kpLeak s₁ = kpLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def kpContract : Contract isa where
  pre := kpPre
  post := kpPost
  pub := kpPub

def kpSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8008 then 1 else if a = 0x8011 then 0x40
    else if a = 0x8018 then 0x20 else if a = 0x8019 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x4000, 8448⟩]

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem kp_implies : kpContract.Implies (checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [kpContract, kpPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq]
    sig_reduce [kpContract, kpPost, kpDom, kpX, kpY] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid]
      [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

end VG.Proof.Ffdh.X86_64.CheckPrivate

end

end

/-! ### `Ffdh.X86_64.CheckPrivate.Entry`, which only this module used -/

section

/-! # FFDH public-key validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * sDom)) (s.gpr .rdi)).writeW (off B (8 * sDomLen)) (s.gpr .rsi)).writeW (off B (8 * sK)) (s.gpr .rdx)).writeW (off B (8 * sY)) (s.gpr .rcx)).writeW (off B (8 * sX)) (s.gpr .r9)).writeW (off B (8 * sXl)) (stackArg s 0))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdi ∧
    word m B (8 * sDomLen) = s.gpr .rsi ∧
    word m B (8 * sK) = s.gpr .rdx ∧
    word m B (8 * sY) = s.gpr .rcx ∧
    word m B (8 * sX) = s.gpr .r9 ∧
    word m B (8 * sXl) = stackArg s 0 ∧ Outside B 0 (8 * 22) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem kpEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdi), (sDomLen, s.gpr .rsi), (sK, s.gpr .rdx),
        (sY, s.gpr .rcx), (sX, s.gpr .r9), (sXl, stackArg s 0)] ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.rax, .r10, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 2)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry save
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
        hw sXl (by decide), ha 1 (by decide), ha 0 (by decide)]; rfl) rfl)
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

end VG.Proof.Ffdh.X86_64.CheckPrivate

end

end

/-! # FFDH private-key validation on x86-64: entry and modulus validation -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckPrivate/Context.lean`, which only this module imported.
section

/-! # FFDH private-key validation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure KpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  yl : (s.gpr .r8).toNat = (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (kpDom s)
  y : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rcx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .rdx).toNat
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (kpX s)
  ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8

theorem kpCtx_of {s : State} (h : kpPre s) : KpCtx s := by
  obtain ⟨hsp, hrd, hwr, dds, dys, dxs, _, wD, wY, wX, wS,
    _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hyl, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dys, hxl1, hxl2,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dxs, ?_⟩
  intro i hi
  refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
  rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega_using []]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

end VG.Proof.Ffdh.X86_64.CheckPrivate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def kpOf (s : State) : KpP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat, s.gpr .rdi,
    kpDom s, s.gpr .r9, (stackArg s 0).toNat, s.gpr .rcx, kpY s, s.gpr .rsp,
    Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .rdx).toNat (kpDom s)) (Spec.Rsa.os2ip (kpX s))⟩

theorem entry_base {s : State} (c : KpCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) s fun t =>
      Base (kpOf s) (kpX s) t ∧ t.gpr .rdi = (kpOf s).B ∧
      InScr (kpOf s).B (kpOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (kpEntry_ok rfl (fun i hi => c.hs.st (by omega_using [hZ, hi])) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (kpOf s).B (kpOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [kpOf]; omega_using [hZ])
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, bytesAt_length _ _ _,
    c.xl1, c.xl2, c.hZ, c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k, c.y.congrK hi k,
    ?_, rfl⟩, hd, hi, hs, k.mono (by decide)⟩
  · change (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .rdx).toNat
    rw [bytesAt_length, c.yl]
  · change Slots t.mem (stackArg s 1) (kpOf s).headers
    simp only [KpP.headers, kpOf, ofNat_toNat64]
    intro e he
    exact hh e he

theorem dom_base {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p xb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega_using [hZ]) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [KpP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) (h.dom.take p.k) h.plen)
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
    simp only [KpP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega_using [hi]) (by unfold sG sFn; omega_using [hi]) (by unfold sQ sFn; omega_using [hi])

/-- Setup and load the private scalar, preserving the domain's pointers. -/
theorem setup_work {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s
      (StepPost p s fun t => ∃ mi, Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w)) := by
  have hk := h.k1
  have hk' := h.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega_using []
  obtain ⟨hodd, _⟩ := valid_facts hm hk
  refine wp_seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb) h.scr hd hk hk' h.hZ
      (h.hdr (sDom, p.dp) (by simp [KpP.headers])) (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]))
      (h.dom.take p.k) h.plen hodd) fun u ⟨mi, hc, hv, hWs, hf, k⟩ => ?_)
  obtain ⟨hi, hh, hs, hhead⟩ := setup_frame hk h.hZ hf
  have hb := h.keep hi k hh
  have hGu : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hhead _ (by decide) (by decide) (by decide) (by decide)]; exact hG
  have hQu : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hhead _ (by decide) (by decide) (by decide) (by decide)]; exact hQ
  have hxl := hb.xl2
  refine WP.mono (primeLoad_ok hc (by omega_using [hk]) (Nat.le_refl _) (by omega_using [hk']) (show aXm < 8 by decide)
    (show sX < 32 by decide) (show sXl < 32 by decide)
    (hb.hdr (sX, p.xp) (by simp [KpP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [KpP.headers])) hb.x
    (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; omega_using [hk', hxl])
    (by rw [hb.xlen]; omega_using [hxl])) fun t ⟨hc', hx, ho, kk⟩ => ?_
  have ff : Frm (off p.B (inner p.w)) [(slot p.w aXm, 8 * (p.w + 2))] u.mem t.mem := Frm.of_outside ho (by simp)
  have hXmle := slot_le (w := p.w) (show aXm < 8 by decide)
  have hr : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 := by
    simp only [List.mem_singleton]; rintro r rfl; omega_using [hXmle]
  obtain ⟨hb', hi', hs'⟩ := hb.child hc ff hr kk
  have hroom := room_k hk h.hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hroom
  obtain ⟨hh', _⟩ := child_frm hc hroom ff hr
  have hn := hc.good.scr.nowrap
  have hv' := hv.of_frmA hn (show 1 ≤ p.w by omega_using [hk, ew]) ff (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off p.w (by decide) (by decide))
  exact ⟨⟨mi, ⟨hb', hc'.toMem, hv', (hh' _ (by decide)).trans hWs,
    (hh' _ (by decide)).trans hGu, (hh' _ (by decide)).trans hQu, hx⟩, hc'.rdi⟩,
    hi.trans hi', fun i hi => (hs' i hi).trans (hs i hi), keep_trans k (kk.mono (by decide))⟩

end VG.Proof.Ffdh.X86_64.CheckPrivate
