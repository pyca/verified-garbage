module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreCT
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTop
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.CachedSat
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks

/-! # `vg_ffdh_generate_key_precompute` on i686: constant time, and verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached.Pre

open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem pcFill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill pArgs)) (.block [])).isSome = true := by
  taint_decide

theorem pc_pub_facts {s t : State} (H : pcContract.pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 7, arg s i = arg t i) ∧ pcDom s = pcDom t ∧
      s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = t.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym := by
  obtain ⟨H, Hs⟩ := pub_consts.mp H
  have sy := Hs _ List.mem_cons_self
  sig_pub [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi,
    argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  refine ⟨SP, fun i hi => ?_, inj L, ?_⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · exact a6
  · have e := congrArg BitVec.toNat sy
    simp only [symAddr, BitVec.toNat_setWidth] at e
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))] at e
    exact BitVec.eq_of_toNat_eq e

theorem pc_hx {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) :
    PRd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
  have tr := VettedValidation.consts_read hc
  rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at tr
  refine ⟨⟨_, List.mem_append_left _ A.rdIn, Region.contains_self _ _⟩, ?_, ?_⟩
  · rw [A.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · obtain ⟨r, hr, hcn⟩ := tr
    refine ⟨r, ?_, hcn⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)

/-- The context's region, as the body names it. -/
abbrev pcOut (s : State) : List Region := [ctxR (synth pArgs (arg s)) (pLenOf pArgs s)]

theorem pc_ctxE {s : State} (A : PreABI s) :
    ctxR (synth pArgs (arg s)) (pLenOf pArgs s) = ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ := by
  rw [pcCtxBytes A]; rfl

theorem pc_ho {s f : State} (A : PreABI s) (Bf : BodyAt (PRd s) pArgs s f) : ∀ r ∈ pcOut s, r ∈ f.wr :=
  fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    rw [pc_ctxE A, Bf.2.2.2.1, A.wr]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem pc_in {s f : State} (A : PreABI s) (Bf : BodyAt (PRd s) pArgs s f) :
    In (PRd s) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s))
      (narrowed (wsBase pArgs s) (wsSize pArgs s) f (pcOut s)) := by
  obtain ⟨⟨r₁, h₁, c₁⟩, _, ⟨r₃, h₃, c₃⟩⟩ := Bf.1.extra
  refine VG.Proof.Ffdh.X86.In.narrow Bf.1 ⟨⟨r₁, List.mem_append_left _ h₁, c₁⟩, ?_, ⟨r₃, List.mem_append_left _ h₃, c₃⟩⟩
  rw [← pc_ctxE A]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The body's narrowed state, from the frame's. -/
theorem pe_of {s f : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) (Bf : BodyAt (PRd s) pArgs s f)
    (y : f.syms = s.syms) :
    PE (PRd s) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (arg s 3).toNat (pcDom s)
      (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)
      (narrowed (wsBase pArgs s) (wsSize pArgs s) f (pcOut s)) := by
  have I := pc_in A Bf
  obtain ⟨G, hb40, domC, C, tfit, tbytes, tws, t40, dd⟩ := pc_frame_facts A hc _ I Bf.2.1 Bf.2.2.2.2
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have espf : (narrowed (wsBase pArgs s) (wsSize pArgs s) f (pcOut s)).gpr .esp =
      s.gpr .esp - BitVec.ofNat 32 argsFrame := Bf.2.1
  rw [espf] at hb40 t40
  exact ⟨⟨I, G, hb40, congrFun y _, tfit, I.extra.2.2, tbytes, tws, t40, espf, dd⟩,
    Bf.argsOk (wrapABI' A) (Out := pcOut s) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [pc_ctxE A]; exact A.belowCtx.sub_left sub), domC, C, A.valid⟩

theorem pc_constantTime : ConstantTime isa pcContract.pre pcContract.pub Impl.Ffdh.X86.Cached.Precompute.code := by
  intro s t tr ur sf tf S T H E F
  obtain ⟨A, hcA⟩ := preABI_of S
  obtain ⟨B, hcB⟩ := preABI_of T
  obtain ⟨SP, args, dom, sy⟩ := pc_pub_facts H
  have hws : wsBase pArgs s = wsBase pArgs t := by
    show (arg s 5).setWidth 64 = (arg t 5).setWidth 64
    rw [args 5 (by decide)]
  have hwz : wsSize pArgs s = wsSize pArgs t := by
    show (arg s 6).toNat * 8 = (arg t 6).toNat * 8
    rw [args 6 (by decide)]
  have hpl : pLenOf pArgs s = pLenOf pArgs t := by
    show (arg s 4).toNat = (arg t 4).toNat
    rw [args 4 (by decide)]
  have hsy : synth pArgs (arg t) = synth pArgs (arg s) :=
    synth_congr (wrapABI' A).below fun i hi => (args i hi).symm
  have hRd : PRd t = PRd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        (⟨(arg t 0).setWidth 64, (arg t 1).toNat * 8⟩ : Region) ∈ wr ∧
        InRegions (rd ++ wr) ((t.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).setWidth 64) 17744) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        (⟨(arg s 0).setWidth 64, (arg s 1).toNat * 8⟩ : Region) ∈ wr ∧
        InRegions (rd ++ wr) ((s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).setWidth 64) 17744
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), sy]
  have hout : pcOut t = pcOut s := by
    show [ctxR (synth pArgs (arg t)) (pLenOf pArgs t)] = _; rw [hsy, ← hpl]
  have hl3 : (arg t 3).toNat = (arg s 3).toNat := by rw [args 3 (by decide)]
  refine wrap_trace_syms (wrapABI' A) (wrapABI' B) args SP (pc_hx A hcA) (pc_hx B hcB) pcFill_check
    (fun f Bf y => WP.mono (pc_frame_ok A hcA f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2)
    (fun f Bf y => WP.mono (pc_frame_ok B hcB f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2) ?_ E F
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun f => f.rd ++ f.wr)
    (fun _ => ⟨wsBase pArgs s, wsSize pArgs s⟩ :: pcOut s) (fun f g ⟨⟨B₁, y₁⟩, ⟨B₂, y₂⟩⟩ => ?_)
    (pcBody_trace (Ex := PRd s) (base := wsBase pArgs s) (bytes := wsSize pArgs s) (len := pLenOf pArgs s)
      (args := synth pArgs (arg s)) (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) (dlen := (arg s 3).toNat)
      (D := pcDom s) (T := s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym) A.valid A.pLen.2)
  have c₁ := B₁.covers (pc_ho A B₁)
  have c₂ := B₂.covers (pc_ho B B₂)
  have w₁ : ∃ F, WP isa Impl.Ffdh.X86.Cached.Precompute.body
      (narrowed (wsBase pArgs s) (wsSize pArgs s) f (pcOut s)) F :=
    ⟨_, pc_frame_ok A hcA _ (pc_in A B₁) B₁.2.1 B₁.2.2.2.2 y₁⟩
  have w₂ : ∃ F, WP isa Impl.Ffdh.X86.Cached.Precompute.body
      (narrowed (wsBase pArgs t) (wsSize pArgs t) g (pcOut t)) F :=
    ⟨_, pc_frame_ok B hcB _ (pc_in B B₂) B₂.2.1 B₂.2.2.2.2 y₂⟩
  have D₂ := pe_of B hcB B₂ y₂
  rw [← hws, ← hwz, hout] at c₂ w₂ D₂
  rw [hRd, ← hpl, hsy, ← SP, hl3, ← dom, ← sy] at D₂
  exact ⟨c₁.1, c₁.2, c₂.1, c₂.2, w₁, w₂, pe_of A hcA B₁ y₁, D₂⟩

/-! ## A caller that meets the contract -/

/-- The stack arguments: the context of 275 words at `0x100000`, the domain of 128 bytes
(`CachedSat.domain`), `p_len` 64 and the working space of 1056 words. -/
def pcSatBase (a : Addr) : Byte :=
  if a = 0x20006 then 0x10
  else if a = 0x20008 then 0x13
  else if a = 0x20009 then 1
  else if a = 0x2000d then 0x30
  else if a = 0x20010 then 128
  else if a = 0x20014 then 64
  else if a = 0x20019 then 0x90
  else if a = 0x2001c then 0x20
  else if a = 0x2001d then 4 else CachedSat.domainMem a

def pcSat0 : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pcSatBase
  rd := [⟨0x3000, 128⟩, ⟨0x200000, 17744⟩]
  wr := [⟨0x100000, 2200⟩, ⟨0x9000, 8448⟩, ⟨0x20004, 28⟩]

def pcSatState (words : List (BitVec 64)) : State :=
  { pcSat0 with
    mem := fun a => if a.toNat < 0x30000 then pcSatBase a else constMem 0x200000 words a
    syms := fun _ => 0x200000 }

theorem pcSat_arg (words : List (BitVec 64)) (i : Nat) (hi : i < 7) :
    arg (stripConsts pcConsts (pcSatState words)) i = Mem.readW pcSatBase (argAddr pcSat0 i) 32 := by
  show Mem.readW (pcSatState words).mem (argAddr pcSat0 i) 32 = _
  apply Mem.readW_congr
  intro j hj
  have small : ∀ i < 7, (argAddr pcSat0 i).toNat + 4 ≤ 0x30000 := by decide
  have := small i hi
  change (if _ then _ else _) = _
  refine ite_eq_left ?_
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (argAddr pcSat0 i).isLt
  have : j < 4 := hj
  omega

theorem pcSat_domain (words : List (BitVec 64)) :
    Spec.Rsa.bytesAt (pcSatState words).mem 0x3000 128 = CachedSat.domain := by
  apply CachedSat.bytesAt_eq
  intro i hi
  change (if _ then _ else _) = _
  rw [ite_eq_left (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; change (0x3000 + _ % _) % _ < _; omega)]
  have : ∀ i < 128, pcSatBase (0x3000 + BitVec.ofNat 64 i) = CachedSat.domainMem (0x3000 + BitVec.ofNat 64 i) := by
    decide
  exact this i hi

theorem pcSat_pre (words : List (BitVec 64)) :
    (Spec.Ffdh.generationPrecomputeContract abi stack).pre (stripConsts pcConsts (pcSatState words)) := by
  have a0 : arg (stripConsts pcConsts (pcSatState words)) 0 = 0x100000 := by rw [pcSat_arg _ 0 (by decide)]; decide
  have a1 : arg (stripConsts pcConsts (pcSatState words)) 1 = 275 := by rw [pcSat_arg _ 1 (by decide)]; decide
  have a2 : arg (stripConsts pcConsts (pcSatState words)) 2 = 0x3000 := by rw [pcSat_arg _ 2 (by decide)]; decide
  have a3 : arg (stripConsts pcConsts (pcSatState words)) 3 = 128 := by rw [pcSat_arg _ 3 (by decide)]; decide
  have a4 : arg (stripConsts pcConsts (pcSatState words)) 4 = 64 := by rw [pcSat_arg _ 4 (by decide)]; decide
  have a5 : arg (stripConsts pcConsts (pcSatState words)) 5 = 0x9000 := by rw [pcSat_arg _ 5 (by decide)]; decide
  have a6 : arg (stripConsts pcConsts (pcSatState words)) 6 = 1056 := by rw [pcSat_arg _ 6 (by decide)]; decide
  have e : argAddr (stripConsts pcConsts (pcSatState words)) 0 = 0x20004 := by
    change argAddr pcSat0 0 = 0x20004; decide
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi, argSlots, argVal,
    argBytes, stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, Spec.Ffdh.generationPrecomputedWords,
    Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.scratchWords]
  simp only [a0, a1, a2, a3, a4, a5, a6, e]
  repeat' apply And.intro
  all_goals first
    | (rw [show BitVec.setWidth 64 (12288 : BitVec 32) = (0x3000 : Addr) by decide,
         show BitVec.toNat (128 : BitVec 32) = 128 from rfl, show BitVec.toNat (64 : BitVec 32) = 64 from rfl]
       exact (pcSat_domain words) ▸ CachedSat.domain_valid)
    | (apply Region.disjoint_of_sep; decide)
    | decide
    | rfl

theorem pcSat_held (words : List (BitVec 64)) (size : words.length = 2218) :
    Abi.constsHeld (pcSatState words).mem (symAddr (pcSatState words)) [(VG.Impl.Ffdh.X86.VettedValidation.tableSym, words)] := by
  intro c hc i hi
  obtain rfl := List.mem_singleton.mp hc
  have same : (pcSatState words).mem.readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x200000 words).readW (0x200000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    change (if (0x200000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat < 0x30000 then _ else _) = _
    have n : i < 2218 := by rw [size] at hi; exact hi
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8 * i + j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (0x200000 : Addr).toNat + (8 * i + j) < 2 ^ 64 by change 2097152 + _ < _; omega)]
    simp only [show ¬ (0x200000 : Addr).toNat + (8 * i + j) < 0x30000 by change ¬ 2097152 + _ < _; omega,
      ↓reduceIte]
  exact same.trans (constMem_held 0x200000 words (by rw [size]; decide) i hi)

theorem pcSat_regions (words : List (BitVec 64)) (size : words.length = 2218) :
    ∀ r ∈ constRegs [(VG.Impl.Ffdh.X86.VettedValidation.tableSym, words)] (pcSatState words),
      r.base.toNat + r.len ≤ 2 ^ abi.ptrBits ∧
      (∀ q ∈ (pcSatState words).wr, r.Disjoint q) ∧
      ∀ q ∈ abi.reserved stack (pcSatState words), r.Disjoint q := by
  intro r hr
  simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
  obtain ⟨c, rfl, rfl⟩ := hr
  rw [size]
  change (0x200000 : Addr).toNat + 17744 ≤ 2 ^ 32 ∧
    (∀ q ∈ ([⟨0x100000, 2200⟩, ⟨0x9000, 8448⟩, ⟨0x20004, 28⟩] : List Region),
      (⟨0x200000, 17744⟩ : Region).Disjoint q) ∧
    ∀ q ∈ ([⟨0x20000, 4⟩, ⟨(0x20000 : Addr) - 172#64, 172⟩] : List Region),
      (⟨0x200000, 17744⟩ : Region).Disjoint q
  refine ⟨by decide, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals exact Region.disjoint_of_sep (by decide)

theorem pc_sat : ∃ s, pcContract.pre s := by
  have size := VG.Proof.Ffdh.VettedTableFacts.tableWords_length
  refine ⟨pcSatState VG.Impl.Ffdh.VettedGroups.tableWords, pre_consts.mpr ⟨pcSat_pre _, ?_, pcSat_held _ size,
    pcSat_regions _ size, fun r hr => ?_⟩⟩
  · simp only [constRegs, Abi.constRegions, pcSatState, List.map_cons, List.map_nil, size, symAddr]
    rfl
  · simp only [constRegs, Abi.constRegions, List.mem_map, List.mem_singleton] at hr
    obtain ⟨c, rfl, rfl⟩ := hr
    dsimp only [symAddr, pcSatState]
    decide

theorem pc_verified : Verified target Impl.Ffdh.X86.Cached.Precompute.code pcContract :=
  ⟨pc_correct, pc_constantTime, pc_sat⟩

end VG.Proof.Ffdh.X86.Cached.Pre
