module

public import VerifiedGarbage.Proof.AesCbc.X86.Call
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.AesXts.X86Unit
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesXts.X86.Steps
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.CmacAes.X86.Save
public import VerifiedGarbage.Proof.Framework.X86.Spill

/-! ### `AesXts.X86.Unit.Steps`, which only this module used -/

section

/-! ### `AesXts.X86.Unit.Pre`, which only this module used -/

section

/-! ### `AesXts.X86.Unit.Call`, which only this module used -/

section

/-!
# XTS-AES of data units on x86: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false) for an implementation of the block functions, in the frame of
its six arguments (`xcall`), on `N` blocks at `D`, from the tweak at `T`,
with working space `S`, from its contract (`WP.callWith`): the blocks are
then XTS of them, the tweak the one after them, and only the tweak, the
blocks, `S` and the 52 bytes below `esp` change. `xts_rel`: such calls, with
the same arguments and `esp` in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86
open VG.Proof.AesCbc.X86 (modeX86 toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeX86 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86 (AesXts.xtsMode enc)).post s s'

/-- The registers the call pushes, as the whole-block function's arguments. -/
abbrev xRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

theorem hrs : Reg.esp ∉ xRegs := by decide

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : BitVec 32) (N R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = T
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = BitVec.ofNat 32 N
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 28
  esp52 : 52 ≤ (s.gpr .esp).toNat
  wt : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨T.setWidth 64, 16⟩
  wd : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨D.setWidth 64, 16 * N⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  td : (⟨T.setWidth 64, 16⟩ : Region).Disjoint ⟨D.setWidth 64, 16 * N⟩
  ts : (⟨T.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  ds : (⟨D.setWidth 64, 16 * N⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bw : (below (s.gpr .esp) 52).Disjoint ⟨W.setWidth 64, 240⟩
  bt : (below (s.gpr .esp) 52).Disjoint ⟨T.setWidth 64, 16⟩
  bd : (below (s.gpr .esp) 52).Disjoint ⟨D.setWidth 64, 16 * N⟩
  bs : (below (s.gpr .esp) 52).Disjoint ⟨S.setWidth 64, 2176⟩
  fitW : W.toNat + 240 ≤ 2 ^ 32
  fitT : T.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * N ≤ 2 ^ 32
  fitS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨T.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * N⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : BitVec 32) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨T.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * N⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 52]
    s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (D.setWidth 64) N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))) (bytesAt s.mem (T.setWidth 64) 16)
      (Spec.Cbc.blocksAt s.mem (D.setWidth 64) N)
  tw : bytesAt s'.mem (T.setWidth 64) 16 = Spec.Xts.next (bytesAt s.mem (T.setWidth 64) 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 28) : (BitVec.ofNat 32 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

/-- The regions the callee is given. -/
abbrev xRd (E W : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev xWr (T D S : BitVec 32) (N : Nat) : List Region :=
  [⟨T.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * N⟩, ⟨S.setWidth 64, 2176⟩]

namespace XPre
variable {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R)
include h

theorem fit : 4 * xRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp52; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem args : arg (pushed xRegs s).callEntry 0 = W ∧ arg (pushed xRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed xRegs s).callEntry 2 = T ∧ arg (pushed xRegs s).callEntry 3 = D ∧
    arg (pushed xRegs s).callEntry 4 = BitVec.ofNat 32 N ∧ arg (pushed xRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 52) := below_sub (by omega_using []) h.esp52

theorem subRet : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 52) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 52) (k := 24) (by omega_using []) h.esp52
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem subStk : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    (below (s.gpr .esp) 52) := by
  have := below_inner (sp := s.gpr .esp) (a := 24) (b := 52) (k := 28) (by omega_using []) h.esp52
  rw [← Taint.sub_setWidth (by rw [sub_toNat (by have := h.esp52; omega_using [this])]; have := h.esp52; omega_using [this])]
  exact this

theorem callPre (enc : Bool) :
    CallPre (modeX86 (AesXts.xtsMode enc)) xRegs (xRd (s.gpr .esp) W) (xWr T D S N) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  obtain hR := toNat_rounds h.rounds
  obtain hN := toNat_n h.n
  obtain eA : argAddr (pushed xRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  obtain eSp : (pushed xRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hN]
    refine ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.bt.sub_left h.sub24, h.bd.sub_left h.sub24,
      h.bs.sub_left h.sub24, h.bt.sub_left h.subRet, h.bd.sub_left h.subRet, h.bs.sub_left h.subRet,
      h.bw.sub_left h.subStk, h.bt.sub_left h.subStk, h.bd.sub_left h.subStk, h.bs.sub_left h.subStk,
      h.fitW, h.fitT, h.fitD, h.fitS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by have := h.esp52; omega_using [this])]; have := h.esp52; omega_using [this]
    · rw [sub_toNat (by have := h.esp52; omega_using [this])]; have := (s.gpr .esp).isLt; omega_using []
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a n ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a n hi
    obtain ⟨r', hr', hc'⟩ := h.writes a n hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end XPre

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c) (nosp : NoSp c)
    (stack : stackUse c ≤ 24) {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.frame (.push xRegs) (.call n c) (.pop .eax 6)) s (XPost enc s W T D S N R) := by
  obtain hR := toNat_rounds h.rounds
  obtain hN := toNat_n h.n
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  refine WP.callWith (rs := xRegs) (k := modeX86 (AesXts.xtsMode enc)) ok nosp (by decide) hrs
    (by have := h.esp52; simp only [List.length_cons, List.length_nil]; omega_using [stack, this]) (h.callPre enc)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  obtain fE := callEntry_frame h.fit hrs
  rw [show 4 * xRegs.length + 4 = 28 from rfl] at fE
  obtain b28 : Region.Sub (below (s.gpr .esp) 28) (below (s.gpr .esp) 52) := below_sub (by omega_using []) h.esp52
  obtain keep : ∀ {X : Region}, (below (s.gpr .esp) 52).Disjoint X → X.len ≤ 2 ^ 64 →
      bytesAt (pushed xRegs s).callEntry.mem X.base X.len = bytesAt s.mem X.base X.len :=
    fun hd hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_left b28).symm) hn
  obtain eW := keep (X := ⟨W.setWidth 64, 16 * (R + 1)⟩) (h.bw.sub_right (Region.sub_prefix hRb)) (by dsimp only; omega_using [hR])
  obtain eT := keep (X := ⟨T.setWidth 64, 16⟩) h.bt (by simp)
  obtain eD : Spec.Cbc.blocksAt (pushed xRegs s).callEntry.mem (D.setWidth 64) N =
      Spec.Cbc.blocksAt s.mem (D.setWidth 64) N :=
    blocksAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bd.sub_left b28).symm) (by have := h.fitD; omega_using [hN])
  simp only [modeX86, AesXts.xtsMode, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hN,
    m₂, Proof.AesXts.Unit.length_blocksAt] at post
  rw [eW, eT, eD] at post
  refine ⟨rd', wr', cs', ?_, post.1, post.2⟩
  obtain f'' := Frame.below_mono f' (b := 52) (by simp only [List.length_cons, List.length_nil]; omega_using [stack]) h.esp52
  exact f''.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of a whole-block function, with the same arguments and `esp` in
both runs, are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (ct : ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : BitVec 32, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.gpr .esp = s₂.gpr .esp) :
    RelCT isa P (.frame (.push xRegs) (.call n c) (.pop .eax 6)) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun (q : (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) × (Nat × Nat) × BitVec 32)
      (a b : State) => XPre a q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧
        XPre b q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧ a.gpr .esp = q.2.2 ∧ b.gpr .esp = q.2.2)
      fun q => ?_).mono
    (fun a b hp => by
      obtain ⟨W, T, D, S, N, R, h₁, h₂, e⟩ := h a b hp
      exact ⟨((W, T, D, S), (N, R), a.gpr .esp), h₁, h₂, rfl, e.symm⟩) fun _ _ h => h
  obtain ⟨⟨W, T, D, S⟩, ⟨N, R⟩, E⟩ := q
  refine RelCT.callWith (rs := xRegs) ok ct (xRd E W) (xWr T D S N) fun s₁ s₂ ⟨h₁, h₂, e₁, e₂⟩ => ?_
  dsimp only at h₁ h₂ e₁ e₂
  obtain p₁ := h₁.callPre enc
  obtain p₂ := h₂.callPre enc
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

end VG.Proof.AesXts.X86.Unit

end

end

/-! ### `AesXts.X86.Unit.Contract`, which only this module used -/

section

/-!
# XTS-AES of data units on x86 (32-bit): the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean` with 52 bytes of stack, which
imply `unitX86` (`Verified.lean`): every argument on the stack, from
`[esp + 4]` (cdecl).

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev E : BitVec 32 := s.gpr .esp
abbrev W : BitVec 32 := arg s 0
abbrev K : BitVec 32 := arg s 1
abbrev R : Nat := (arg s 2).toNat
abbrev I : BitVec 32 := arg s 3
abbrev D : BitVec 32 := arg s 4
abbrev Len : Nat := (arg s 5).toNat
abbrev S : BitVec 32 := arg s 6

/-- The scratch buffer and the data, as addresses. -/
abbrev Sa : Addr := (S s).setWidth 64
abbrev Da : Addr := (D s).setWidth 64

abbrev schR : Region := ⟨(W s).setWidth 64, 240⟩
abbrev tschR : Region := ⟨(K s).setWidth 64, 240⟩
abbrev iR : Region := ⟨(I s).setWidth 64, 16⟩
abbrev dataR : Region := ⟨Da s, Len s⟩
abbrev scrR : Region := ⟨Sa s, 2432⟩
abbrev argsR : Region := ⟨argAddr s 0, 28⟩
abbrev retR : Region := ⟨(E s).setWidth 64, 4⟩
/-- The 52 bytes of stack below `esp` the calls use. -/
abbrev stkR : Region := ⟨(E s).setWidth 64 - BitVec.ofNat 64 52, 52⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.X86Unit.tO, 16⟩
abbrev zR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.X86Unit.zO, 16⟩
abbrev wkR : Region := ⟨Sa s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := Da s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, from the
arguments on the stack, the return address and the 52 bytes below it,
`rounds` of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  (52 ≤ (E s).toNat ∧ (E s).toNat + 4 + 28 ≤ 2 ^ 32) ∧
    s.rd = [schR s, tschR s, iR s, argsR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧ (dataR s).Disjoint (argsR s) ∧ (scrR s).Disjoint (argsR s) ∧
    (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (tschR s) ∧ (retR s).Disjoint (iR s) ∧
    (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (scrR s) ∧ (retR s).Disjoint (argsR s) ∧
    (stkR s).Disjoint (schR s) ∧ (stkR s).Disjoint (tschR s) ∧ (stkR s).Disjoint (iR s) ∧
    (stkR s).Disjoint (dataR s) ∧ (stkR s).Disjoint (scrR s) ∧ (stkR s).Disjoint (argsR s) ∧
    (W s).toNat + 240 ≤ 2 ^ 32 ∧ (K s).toNat + 240 ≤ 2 ^ 32 ∧ (I s).toNat + 16 ≤ 2 ^ 32 ∧
    (D s).toNat + Len s ≤ 2 ^ 32 ∧ (S s).toNat + 2432 ≤ 2 ^ 32 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitX86 (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem ((arg s 0).setWidth 64) ((arg s 1).setWidth 64)
      (arg s 2).toNat key →
    xtsOf enc key (bytesAt s.mem ((arg s 3).setWidth 64) 16)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      some (bytesAt s'.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  esp52 : 52 ≤ (E s).toNat
  esp_fit : (E s).toNat + 4 + 28 ≤ 2 ^ 32
  rd : s.rd = [schR s, tschR s, iR s, argsR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_args : (dataR s).Disjoint (argsR s)
  scr_args : (scrR s).Disjoint (argsR s)
  ret_sch : (retR s).Disjoint (schR s)
  ret_tsch : (retR s).Disjoint (tschR s)
  ret_i : (retR s).Disjoint (iR s)
  ret_data : (retR s).Disjoint (dataR s)
  ret_scr : (retR s).Disjoint (scrR s)
  ret_args : (retR s).Disjoint (argsR s)
  stk_sch : (stkR s).Disjoint (schR s)
  stk_tsch : (stkR s).Disjoint (tschR s)
  stk_i : (stkR s).Disjoint (iR s)
  stk_data : (stkR s).Disjoint (dataR s)
  stk_scr : (stkR s).Disjoint (scrR s)
  stk_args : (stkR s).Disjoint (argsR s)
  sch_fit : (W s).toNat + 240 ≤ 2 ^ 32
  tsch_fit : (K s).toNat + 240 ≤ 2 ^ 32
  i_fit : (I s).toNat + 16 ≤ 2 ^ 32
  data_fit : (D s).toNat + Len s ≤ 2 ^ 32
  scr_fit : (S s).toNat + 2432 ≤ 2 ^ 32
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨⟨a, b⟩, c, d, e, f, g, h, i, j, k, l, m, r₁, r₂, r₃, r₄, r₅, r₆, n, o, p, q, r, t, u, v, w, x, y, z, a',
    b'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, r₁, r₂, r₃, r₄, r₅, r₆, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

theorem addr_toNat (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_using [])

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

/-- An offset of the scratch buffer, as an address. -/
theorem UPre.scrA {d : Nat} (hd : d < 2432) : addr (S s) d = Sa s + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.scr_fit; omega_using [hd, this])

/-- An offset of the data, as an address. -/
theorem UPre.dataA {d : Nat} (hd : d < Len s) : addr (D s) d = Da s + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.data_fit; omega_using [hd, this])

theorem UPre.scr_wrap : (Sa s).toNat + 2432 ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.scr_fit

theorem UPre.data_wrap : (Da s).toNat + Len s ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.data_fit

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨Sa s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨Da s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.tO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.zO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.X86Unit.tO, Impl.AesXts.X86Unit.zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.X86Unit.zO]; omega_using [])

/-- Everything the code writes but the slots lies within the data, the
first 2208 bytes of the scratch buffer or the stack below `esp`. -/
theorem UPre.slots_disj {r : Region}
    (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨Sa s, 2208⟩ ∨ Region.Sub r (stkR s)) :
    (⟨Sa s + BitVec.ofNat 64 2208, 16⟩ : Region).Disjoint r := by
  obtain slot : Region.Sub ⟨Sa s + BitVec.ofNat 64 2208, 16⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])).sub_right h
  · exact (hp.stk_scr.symm.sub_left slot).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨Sa s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (Da s).toNat + 16 * M s + B s ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨Da s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = Da s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨Da s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨Da s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.X86.Unit

end

end


/-!
# XTS-AES of data units on x86: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions and
stack pointer of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86
open VG.Impl.AesXts.X86Unit (tO zO)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrN {d : Nat} (hd : d < 2432) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem UPre.dataN {d : Nat} (hd : d < Len s₀) : (D s₀ + BitVec.ofNat 32 d).toNat = (D s₀).toNat + d := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd, this]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

/-- The last whole block, as a register holds it. -/
abbrev Lv (s₀ : State) : BitVec 32 := D s₀ + BitVec.ofNat 32 (16 * (M s₀ - 1))

theorem UPre.lA : (Lv s₀).setWidth 64 = L s₀ :=
  hp.dataA (by have := len_eq s₀; have := hp.m_pos; omega_arith)

theorem UPre.scrW {d : Nat} (hd : d < 2432) : (S s₀ + BitVec.ofNat 32 d).setWidth 64 = Sa s₀ + BitVec.ofNat 64 d :=
  hp.scrA hd

theorem UPre.stk_eq {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) : below (s.gpr .esp) 52 = stkR s₀ := by
  rw [hsp]; simp only [below]; rw [Taint.sub_setWidth hp.esp52]

theorem UPre.cS (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (Sa s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by have := hp.scr_wrap; omega_using [h])

end

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = s₀.gpr .esp)
include hp hrd hwr hsp

theorem xpre_tweak (eax : s.gpr .eax = K s₀) (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀))
    (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 zO) (ebx : s.gpr .ebx = S s₀ + BitVec.ofNat 32 tO)
    (edi : s.gpr .edi = BitVec.ofNat 32 1) (ebp : s.gpr .ebp = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 32 zO) (S s₀ + BitVec.ofNat 32 tO) (S s₀) 1 (R s₀) := by
  obtain aT := hp.scrW (d := tO) (by decide)
  obtain aZ := hp.scrW (d := zO) (by decide)
  obtain stk := hp.stk_eq hsp
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by decide
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aZ]; exact hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
    wd := by rw [aT]; exact hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
    ws := hp.tsch_scr.sub_right wk_sub
    td := by rw [aZ, aT]; exact hp.t_z.symm
    ts := by rw [aZ]; exact hp.z_wk
    ds := by rw [aT]; exact hp.t_wk
    bw := by rw [stk]; exact hp.stk_tsch
    bt := by rw [stk, aZ]; exact hp.stk_scr.sub_right (sub_trans z_sub s_sub)
    bd := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.tsch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [zO]; omega_using [this]
    fitD := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega_using [this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aZ, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (eax : s.gpr .eax = W s₀)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)) (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 tO)
    (ebx : s.gpr .ebx = D s₀) (edi : s.gpr .edi = BitVec.ofNat 32 N) (ebp : s.gpr .ebp = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 tO) (D s₀) (S s₀) N (R s₀) := by
  obtain aT := hp.scrW (d := tO) (by decide)
  obtain stk := hp.stk_eq hsp
  obtain dS : Region.Sub ⟨(D s₀).setWidth 64, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aT]; exact hp.sch_scr.sub_right (sub_trans t_sub s_sub)
    wd := hp.sch_data.sub_right dS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aT]; exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right dS
    ts := by rw [aT]; exact hp.t_wk
    ds := (hp.data_scr.sub_left dS).sub_right wk_sub
    bw := by rw [stk]; exact hp.stk_sch
    bt := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    bd := by rw [stk]; exact hp.stk_data.sub_right dS
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega_using [this]
    fitD := by have := hp.data_fit; omega_using [hN, this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (eax : s.gpr .eax = W s₀)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)) (edx : s.gpr .edx = S s₀ + BitVec.ofNat 32 o)
    (ebx : s.gpr .ebx = Lv s₀) (edi : s.gpr .edi = BitVec.ofNat 32 1) (ebp : s.gpr .ebp = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀) := by
  obtain ol : o + 16 ≤ 2208 := by rcases ho with rfl | rfl <;> decide
  obtain aO := hp.scrW (d := o) (by omega_using [ol])
  have aL := hp.lA
  obtain stk := hp.stk_eq hsp
  obtain oS : Region.Sub ⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ ⟨Sa s₀, 2208⟩ := Offset.sub_base _ ol
  obtain oW : (⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    eax := eax
    ecx := ecx
    edx := edx
    ebx := ebx
    edi := edi
    ebp := ebp
    rounds := hp.rounds
    n := by decide
    esp52 := by rw [hsp]; exact hp.esp52
    wt := by rw [aO]; exact hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := by rw [aL]; exact hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aO, aL]; exact (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := by rw [aO]; exact oW
    ds := by rw [aL]; exact (hp.data_scr.sub_left lS).sub_right wk_sub
    bw := by rw [stk]; exact hp.stk_sch
    bt := by rw [stk, aO]; exact hp.stk_scr.sub_right (sub_trans oS s_sub)
    bd := by rw [stk, aL]; exact hp.stk_data.sub_right lS
    bs := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by omega_using [ol])]; have := hp.scr_fit; omega_using [ol, this]
    fitD := by
      have := hp.l_wrap
      rw [← aL, addr_toNat] at this
      omega_using [this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aO, aL]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simp; omega_using [ol]⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.X86.Unit

end

end


/-!
# XTS-AES of data units on x86: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`). The pieces reload the arguments from
the stack, which they need unchanged (`ArgsOk`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_sub wp_shr wp_movzx8
  wp_store8 ea_at)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg ea_at')
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

/-- `s'` is `s` with memory `m`, and only the registers `rs` changed (and the flags). -/
structure Chg (s s' : State) (rs : List Reg) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Chg.refl (s : State) (rs : List Reg) : Chg s s rs s.mem := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Chg.upd {s s₁ s' : State} {rs : List Reg} {m : Mem} (h : Chg s s₁ rs m) {d : Reg} {v : BitVec 32}
    (u : Upd s₁ s' d v) (hd : d ∈ rs) : Chg s s' rs m :=
  ⟨fun r hr => by rw [u.other r (fun e => hr (e ▸ hd)), h.gpr r hr], by rw [u.mem, h.mem], by rw [u.rd, h.rd],
    by rw [u.wr, h.wr]⟩

theorem Chg.mupd {s s₁ s' : State} {rs : List Reg} {m m' : Mem} (h : Chg s s₁ rs m) (u : Mupd s₁ s' m') :
    Chg s s' rs m' :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, by rw [u.rd, h.rd], by rw [u.wr, h.wr]⟩

/-- The stack arguments of the entry state `s₀`, readable and unchanged in `s`. -/
structure ArgsOk (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  inr : ∀ i < 7, InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4
  val : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem ArgsOk.upd {s₀ s s' : State} (h : ArgsOk s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .esp) : ArgsOk s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd), h.esp], by rw [u.rd, u.wr]; exact h.inr, by rw [u.mem]; exact h.val⟩

/-- `mov d, [esp + 4 + 4 i]`. -/
theorem wp_argA {is : List Instr} {s₀ s : State} {Q : State → Prop} {d : Reg} {i : Nat} (h : ArgsOk s₀ s)
    (hi : i < 7) (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  wp_arg h.esp (h.inr i hi) (h.val i hi) k

/-- `add d, [esp + 4 + 4 i]`. -/
theorem wp_addArgA {is : List Instr} {s₀ s : State} {Q : State → Prop} {d : Reg} {i : Nat} (h : ArgsOk s₀ s)
    (hi : i < 7) (k : ∀ s', Upd s s' d (s.gpr d + arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (argOp i) :: is)) s Q :=
  wp_addArg h.esp (h.inr i hi) (h.val i hi) k

/-- `and d, imm`, and ZF. -/
theorem wp_andiZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.X86.WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _) rfl)

/-! ## The arguments, from the precondition -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.argA {i : Nat} (hi : i < 7) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by simp only [E] at this; omega_arith), addr_eq (by simp only [E] at this; omega_arith), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega_arith)

theorem UPre.arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The arguments, where only the data, the scratch buffer and the stack
below `esp` have changed. -/
theorem UPre.argsOk {s : State} (hesp : s.gpr .esp = s₀.gpr .esp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem) : ArgsOk s₀ s where
  esp := hesp
  inr i hi := by rw [hrd, hwr]; exact hp.arg_in hi
  val i hi := hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.scr_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.stk_args.symm.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.argsOk₀ : ArgsOk s₀ s₀ := ⟨rfl, fun _ hi => hp.arg_in hi, fun _ _ => rfl⟩

/-- The arguments, across writes to regions apart from them. -/
theorem UPre.argsOk_frame {s s' : State} (h : ArgsOk s₀ s) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (argsR s₀).Disjoint r) :
    ArgsOk s₀ s' where
  esp := by rw [hesp, h.esp]
  inr i hi := by rw [hrd, hwr]; exact h.inr i hi
  val i hi := by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (hp.arg_sub hi)) (by decide)]
    exact h.val i hi

end

theorem r_ofNat (s₀ : State) : BitVec.ofNat 32 (R s₀) = arg s₀ 2 := by simp [R]

/-! ## Blocks of words -/

/-- The block at `Q` copied to `P`, a word at a time, read before any is written. -/
def copy4 (m : Mem) (P Q : Addr) : Mem :=
  Proof.Cmac.store4 m P (m.readW Q 32) (m.readW (Q + BitVec.ofNat 64 4) 32) (m.readW (Q + BitVec.ofNat 64 8) 32)
    (m.readW (Q + BitVec.ofNat 64 12) 32)

theorem copy4_frame (m : Mem) (P Q : Addr) : Frame [⟨P, 16⟩] m (copy4 m P Q) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem copy4_bytes (m : Mem) (P Q : Addr) : bytesAt (copy4 m P Q) P 16 = bytesAt m Q 16 := by
  rw [copy4, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

/-- A write within a block keeps the words of a disjoint one. -/
theorem readW_sep {m : Mem} {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) {k : Nat} (hk : k ≤ 12)
    (w : BitVec 32) {j : Nat} (hj : j ≤ 12) :
    (m.writeW (P + BitVec.ofNat 64 j) w).readW (Q + BitVec.ofNat 64 k) 32 = m.readW (Q + BitVec.ofNat 64 k) 32 := by
  refine ((Frame.refl _ _).writeW (rs := [⟨P, 16⟩]) (List.mem_singleton_self _) w
    (Offset.contains_base P (d := j) (n := 4) (k := 16) (by omega_arith) (by omega_arith))).readW
    (r := ⟨Q + BitVec.ofNat 64 k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (hpq.symm.sub_left (Offset.sub_base Q (d := k) (n := 4) (k := 16) (by omega_arith)))

theorem readW_sep0 {m : Mem} {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) {k : Nat} (hk : k ≤ 12)
    (w : BitVec 32) : (m.writeW P w).readW (Q + BitVec.ofNat 64 k) 32 = m.readW (Q + BitVec.ofNat 64 k) 32 := by
  have := readW_sep (m := m) hpq hk w (j := 0) (by decide); simpa using this

/-- `copy r dst d src e` of disjoint blocks: the source's words through `r`. -/
theorem copy_wp {s : State} {r dst src : Reg} {d e : Nat} {P Q : Addr} {is : List Instr} {Φ : State → Prop}
    (hr₁ : r ≠ dst) (hr₂ : r ≠ src)
    (hq : (s.gpr src).setWidth 64 + BitVec.ofNat 64 e = Q) (hqf : (s.gpr src).toNat + e + 16 ≤ 2 ^ 32)
    (hp : (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d = P) (hpf : (s.gpr dst).toNat + d + 16 ≤ 2 ^ 32)
    (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩)
    (hrd : ∀ k n, k + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 k) n)
    (hwr : ∀ k n, k + n ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 k) n)
    (k : ∀ s', Chg s s' [r] (copy4 s.mem P Q) → WP isa (.block is) s' Φ) :
    WP isa (.block (copy r dst d src e ++ is)) s Φ := by
  have a (k : Nat) (hk : k ≤ 12) : addr (s.gpr src) (e + k) = Q + BitVec.ofNat 64 k := by
    rw [addr_eq (by omega_arith), ← Offset.add_add, hq]
  have b (k : Nat) (hk : k ≤ 12) : addr (s.gpr dst) (d + k) = P + BitVec.ofNat 64 k := by
    rw [addr_eq (by omega_arith), ← Offset.add_add, hp]
  obtain a0 : addr (s.gpr src) e = Q := by rw [addr_eq (by omega_arith), hq]
  obtain b0 : addr (s.gpr dst) d = P := by rw [addr_eq (by omega_arith), hp]
  have rq (k : Nat) (hk : k ≤ 12) : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 k) 4 := hrd k 4 (by omega_arith)
  have wp (k : Nat) (hk : k ≤ 12) : InRegions s.wr (P + BitVec.ofNat 64 k) 4 := hwr k 4 (by omega_arith)
  obtain r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using rq 0 (by decide)
  obtain w0 : InRegions s.wr P 4 := by simpa using wp 0 (by decide)
  simp only [copy, List.cons_append, List.nil_append]
  refine wp_movm (a := Q) (by rw [ea_at']; exact a0) r0 fun s₁ u₁ => ?_
  obtain c₁ := (Chg.refl s [r]).upd u₁ (List.mem_singleton_self _)
  refine wp_store (a := P) (by rw [ea_at', c₁.gpr _ (by simpa using hr₁.symm)]; exact b0)
    (by rw [c₁.wr]; exact w0) fun s₂ u₂ => ?_
  obtain c₂ := c₁.mupd u₂
  obtain m₂ : s₂.mem = s.mem.writeW P (s.mem.readW Q 32) := by rw [u₂.mem, u₁.gpr, u₁.mem]
  refine wp_movm (a := Q + BitVec.ofNat 64 4) (by rw [ea_at', c₂.gpr _ (by simpa using hr₂.symm)]; exact a 4 (by decide))
    (by rw [c₂.rd, c₂.wr]; exact rq 4 (by decide)) fun s₃ u₃ => ?_
  obtain c₃ := c₂.upd u₃ (List.mem_singleton_self _)
  obtain v₃ : s₃.gpr r = s.mem.readW (Q + BitVec.ofNat 64 4) 32 := by rw [u₃.gpr, m₂, readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 4) (by rw [ea_at', c₃.gpr _ (by simpa using hr₁.symm)]; exact b 4 (by decide))
    (by rw [c₃.wr]; exact wp 4 (by decide)) fun s₄ u₄ => ?_
  obtain c₄ := c₃.mupd u₄
  obtain m₄ : s₄.mem = (s.mem.writeW P (s.mem.readW Q 32)).writeW (P + BitVec.ofNat 64 4)
      (s.mem.readW (Q + BitVec.ofNat 64 4) 32) := by rw [u₄.mem, v₃, u₃.mem, m₂]
  refine wp_movm (a := Q + BitVec.ofNat 64 8) (by rw [ea_at', c₄.gpr _ (by simpa using hr₂.symm)]; exact a 8 (by decide))
    (by rw [c₄.rd, c₄.wr]; exact rq 8 (by decide)) fun s₅ u₅ => ?_
  obtain c₅ := c₄.upd u₅ (List.mem_singleton_self _)
  obtain v₅ : s₅.gpr r = s.mem.readW (Q + BitVec.ofNat 64 8) 32 := by
    rw [u₅.gpr, m₄, readW_sep hpq (by decide) _ (by decide), readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 8) (by rw [ea_at', c₅.gpr _ (by simpa using hr₁.symm)]; exact b 8 (by decide))
    (by rw [c₅.wr]; exact wp 8 (by decide)) fun s₆ u₆ => ?_
  obtain c₆ := c₅.mupd u₆
  obtain m₆ : s₆.mem = ((s.mem.writeW P (s.mem.readW Q 32)).writeW (P + BitVec.ofNat 64 4)
      (s.mem.readW (Q + BitVec.ofNat 64 4) 32)).writeW (P + BitVec.ofNat 64 8)
      (s.mem.readW (Q + BitVec.ofNat 64 8) 32) := by rw [u₆.mem, v₅, u₅.mem, m₄]
  refine wp_movm (a := Q + BitVec.ofNat 64 12) (by rw [ea_at', c₆.gpr _ (by simpa using hr₂.symm)]; exact a 12 (by decide))
    (by rw [c₆.rd, c₆.wr]; exact rq 12 (by decide)) fun s₇ u₇ => ?_
  obtain c₇ := c₆.upd u₇ (List.mem_singleton_self _)
  obtain v₇ : s₇.gpr r = s.mem.readW (Q + BitVec.ofNat 64 12) 32 := by
    rw [u₇.gpr, m₆, readW_sep hpq (by decide) _ (by decide), readW_sep hpq (by decide) _ (by decide),
      readW_sep0 hpq (by decide)]
  refine wp_store (a := P + BitVec.ofNat 64 12) (by rw [ea_at', c₇.gpr _ (by simpa using hr₁.symm)]; exact b 12 (by decide))
    (by rw [c₇.wr]; exact wp 12 (by decide)) fun s₈ u₈ => k s₈ ?_
  refine ⟨(c₇.mupd u₈).gpr, ?_, (c₇.mupd u₈).rd, (c₇.mupd u₈).wr⟩
  rw [u₈.mem, v₇, u₇.mem, m₆]; rfl

/-! ## The arguments of the calls -/

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_arith)]

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : BitVec 32) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 32 (16 * m) - 16 = p + BitVec.ofNat 32 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem UPre.lv_eq {s₀ : State} (hp : UPre s₀) : arg s₀ 5 - BitVec.ofNat 32 (B s₀) + D s₀ - 16 = Lv s₀ := by
  have hm := hp.m_pos
  obtain e := len_eq s₀
  rw [show arg s₀ 5 = BitVec.ofNat 32 (Len s₀) by simp [Len], MdStream.X86.sub_ofNat (by omega_arith),
    show Len s₀ - B s₀ = 16 * M s₀ by omega_arith, BitVec.add_comm, Lv, last_eq _ hm]

section
variable {s₀ s : State} {is : List Instr} {Φ : State → Prop} (h : ArgsOk s₀ s)
include h

/-- The arguments of a call on the `len / 16` whole blocks from the tweak. -/
theorem argsAll_wp
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 tO → s'.gpr .ebx = D s₀ → s'.gpr .edi = BitVec.ofNat 32 (M s₀) →
      s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsAll ++ is)) s Φ := by
  simp only [argsAll, List.cons_append, List.nil_append]
  refine wp_argA h (i := 6) (by decide) fun s₁ u₁ => ?_
  obtain h₁ := h.upd u₁ (by decide)
  refine wp_argA h₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  obtain h₂ := h₁.upd u₂ (by decide)
  refine wp_argA h₂ (i := 2) (by decide) fun s₃ u₃ => ?_
  obtain h₃ := h₂.upd u₃ (by decide)
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  obtain h₅ := (h₃.upd u₄ (by decide)).upd u₅ (by decide)
  refine wp_argA h₅ (i := 4) (by decide) fun s₆ u₆ => ?_
  obtain h₆ := h₅.upd u₆ (by decide)
  refine wp_argA h₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  refine wp_shr (n := 4) (by decide) fun s₈ u₈ => ?_
  obtain c := (((((((((Chg.refl s xRegs).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide))
  refine k s₈ c ?_ ?_ ?_ ?_ ?_ ?_
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.gpr]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr]
  · rw [u₈.gpr, u₇.gpr, shr4]
  · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]

/-- The arguments of a call on all but the last whole block. -/
theorem argsHead_wp (hm : 1 ≤ M s₀)
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 tO → s'.gpr .ebx = D s₀ →
      s'.gpr .edi = BitVec.ofNat 32 (M s₀ - 1) → s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsHead ++ is)) s Φ := by
  rw [argsHead, List.append_assoc, List.cons_append, List.nil_append]
  refine argsAll_wp h fun s₁ c₁ ax cx dx bx di bp => wp_subi fun s₂ u₂ _ => ?_
  refine k s₂ (c₁.upd u₂ (by decide)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u₂.other _ (by decide), ax]
  · rw [u₂.other _ (by decide), cx]
  · rw [u₂.other _ (by decide), dx]
  · rw [u₂.other _ (by decide), bx]
  · rw [u₂.gpr, di]; exact MdStream.X86.ofNat_pred hm
  · rw [u₂.other _ (by decide), bp]

/-- `b = len mod 16` into `esi`, and ZF set if it is zero. -/
theorem split_wp
    (k : ∀ s', Chg s s' [.esi] s.mem → s'.gpr .esi = BitVec.ofNat 32 (B s₀) → s'.zf = some (decide (B s₀ = 0)) →
      WP isa (.block is) s' Φ) :
    WP isa (.block (split ++ is)) s Φ := by
  simp only [split, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_andiZ fun s₂ u₂ z₂ => ?_
  obtain e : s₁.gpr .esi &&& 15 = BitVec.ofNat 32 (B s₀) := by rw [u₁.gpr, and15]
  refine k s₂ (((Chg.refl s _).upd u₁ (by decide)).upd u₂ (by decide)) (by rw [u₂.gpr, e]) ?_
  rw [z₂, e, MdStream.X86.ofNat_beq_zero (by simp only [B]; omega_arith)]

variable (hp : UPre s₀) (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀))
include hp hsi

/-- The address of the last whole block into `edx`, and `b` into `ecx`. -/
theorem lastAddr_wp
    (k : ∀ s', Chg s s' [.edx, .ecx] s.mem → s'.gpr .edx = Lv s₀ → s'.gpr .ecx = BitVec.ofNat 32 (B s₀) →
      WP isa (.block is) s' Φ) :
    WP isa (.block (lastAddr ++ is)) s Φ := by
  simp only [lastAddr, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => ?_
  obtain h₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_argA h₂ (i := 4) (by decide) fun s₃ u₃ => MdStream.X86.wp_add fun s₄ u₄ => wp_subi fun s₅ u₅ _ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  refine k s₆ ((((((Chg.refl s _).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide) |>.upd u₅ (by decide)).upd u₆ (by decide)) ?_ ?_
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), hsi]
    exact hp.lv_eq
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hsi]

/-- The arguments of a call on the last whole block, from the tweak at `o`. -/
theorem argsL_wp {o : Nat}
    (k : ∀ s', Chg s s' xRegs s.mem → s'.gpr .eax = W s₀ → s'.gpr .ecx = arg s₀ 2 →
      s'.gpr .edx = S s₀ + BitVec.ofNat 32 o → s'.gpr .ebx = Lv s₀ → s'.gpr .edi = BitVec.ofNat 32 1 →
      s'.gpr .ebp = S s₀ → WP isa (.block is) s' Φ) :
    WP isa (.block (argsL o ++ is)) s Φ := by
  simp only [argsL, List.cons_append, List.nil_append]
  refine wp_argA h (i := 5) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => ?_
  obtain h₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_addArgA h₂ (i := 4) (by decide) fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  obtain h₄ := (h₂.upd u₃ (by decide)).upd u₄ (by decide)
  refine wp_argA h₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  obtain h₅ := h₄.upd u₅ (by decide)
  refine wp_argA h₅ (i := 0) (by decide) fun s₆ u₆ => ?_
  obtain h₆ := h₅.upd u₆ (by decide)
  refine wp_argA h₆ (i := 2) (by decide) fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_addi fun s₉ u₉ => ?_
  refine wp_movi fun s₁₀ u₁₀ => ?_
  obtain c := (((((((((((Chg.refl s xRegs).upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄
    (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉
    (by decide)).upd u₁₀ (by decide))
  refine k s₁₀ c ?_ ?_ ?_ ?_ u₁₀.gpr ?_
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.gpr, u₈.gpr, u₇.other, u₆.other, u₅.gpr]
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.other]
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hsi]
    exact hp.lv_eq
  · simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, u₅.gpr]

end

/-! ## The swap -/

theorem in_wr {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) : InRegions (rs ++ ws) a n :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

theorem byte_rt (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem addr_k {x : BitVec 32} {L : Addr} (hx : x.setWidth 64 = L) {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = L + BitVec.ofNat 64 (k + d) := by
  rw [show addr (x + BitVec.ofNat 32 k) d = addr x (k + d) by simp only [addr, MdStream.X86.ofNat_add_add],
    addr_eq (by omega_arith), hx]

/-- The first `b` bytes of the block at `L` (in `edx`) swapped with the `b`
bytes after it (`b` in `ecx`). -/
theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : (s.gpr .edx).setWidth 64 = L)
    (hxf : (s.gpr .edx).toNat + 16 + b ≤ 2 ^ 32) (hc : s.gpr .ecx = BitVec.ofNat 32 b)
    (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => Chg s s' [.eax, .ebx, .ecx, .edx] (swapMem s.mem L b) := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .edx = s.gpr .edx + BitVec.ofNat 32 k ∧
      t.gpr .ecx = BitVec.ofNat 32 (b - k) ∧ Chg s t [.eax, .ebx, .ecx, .edx] (swapMem s.mem L k)) ?_ (b - 0) _
    ⟨0, rfl, hb₀, (BitVec.add_zero _).symm, hc,
      ⟨fun _ _ => rfl, (Proof.AesXts.Unit.swapMem_zero _ _).symm, rfl, rfl⟩⟩
  rintro n t ⟨k, rfl, hk, xdx, xcx, ct⟩
  obtain hlo : t.mem (L + BitVec.ofNat 64 k) = s.mem (L + BitVec.ofNat 64 k) := by
    rw [ct.mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_arith)]
  obtain hhi : t.mem (L + BitVec.ofNat 64 (16 + k)) = s.mem (L + BitVec.ofNat 64 (16 + k)) := by
    rw [ct.mem, swapMem_hi _ _ (Nat.le_refl k) (by omega_arith)]
  obtain in₀ : InRegions t.wr (L + BitVec.ofNat 64 k) 1 := by rw [ct.wr]; exact hw k (by omega_arith)
  obtain in₁ : InRegions t.wr (L + BitVec.ofNat 64 (16 + k)) 1 := by rw [ct.wr]; exact hw (16 + k) (by omega_arith)
  obtain a₀ : t.ea (at_ .edx 0) = L + BitVec.ofNat 64 k := by
    rw [ea_at', xdx, addr_k hx (by omega_arith), Nat.add_zero]
  have a₁ (t' : State) (he : t'.gpr .edx = t.gpr .edx) : t'.ea (at_ .edx 16) = L + BitVec.ofNat 64 (16 + k) := by
    rw [ea_at', he, xdx, addr_k hx (by omega_arith), Nat.add_comm]
  refine wp_movzx8 a₀ (in_wr in₀) fun t₁ u₁ => ?_
  refine wp_movzx8 (a₁ t₁ (u₁.other _ (by decide))) (by rw [u₁.rd, u₁.wr]; exact in_wr in₁) fun t₂ u₂ => ?_
  refine wp_store8 (a := L + BitVec.ofNat 64 k) (by rw [ea_at', u₂.other _ (by decide), u₁.other _ (by decide)]; exact a₀)
    (by rw [u₂.wr, u₁.wr]; exact in₀) fun t₃ v₃ => ?_
  refine wp_store8 (a₁ t₃ (by rw [v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]))
    (by rw [v₃.wr, u₂.wr, u₁.wr]; exact in₁) fun t₄ v₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_subi fun t₆ u₆ z₆ => WP.block_nil ?_
  obtain bl : t₂.gpr Reg8.bl.reg = (t.mem (L + BitVec.ofNat 64 (16 + k))).setWidth 32 := by
    rw [show Reg8.bl.reg = Reg.ebx from rfl, u₂.gpr, u₁.mem]
  obtain al : t₃.gpr Reg8.al.reg = (t.mem (L + BitVec.ofNat 64 k)).setWidth 32 := by
    rw [show Reg8.al.reg = Reg.eax from rfl, v₃.gpr, u₂.other _ (by decide), u₁.gpr]
  obtain hmem : t₆.mem = swapMem s.mem L (k + 1) := by
    rw [u₆.mem, u₅.mem, v₄.mem, al, v₃.mem, bl, u₂.mem, u₁.mem, byte_rt, byte_rt, hlo, hhi, ct.mem,
      swapMem_step _ _ (by omega_arith)]
  obtain cx₅ : t₅.gpr .ecx = BitVec.ofNat 32 (b - k) := by
    rw [u₅.other _ (by decide), v₄.gpr, v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), xcx]
  obtain ev : isa.eval .ne t₆ = some !decide (b - (k + 1) = 0) := by
    show VG.X86.eval .ne t₆ = _
    rw [MdStream.X86.eval_ne, z₆, cx₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.X86.sub_ofNat (by omega_arith), Nat.sub_sub, MdStream.X86.ofNat_beq_zero (by omega_arith)]
    rfl
  obtain c₆ : Chg s t₆ [.eax, .ebx, .ecx, .edx] (swapMem s.mem L (k + 1)) :=
    ⟨fun r hr => by
      obtain h₁ : r ≠ .eax := fun e => hr (by simp [e])
      obtain h₂ : r ≠ .ebx := fun e => hr (by simp [e])
      obtain h₃ : r ≠ .ecx := fun e => hr (by simp [e])
      obtain h₄ : r ≠ .edx := fun e => hr (by simp [e])
      rw [u₆.other _ h₃, u₅.other _ h₄, v₄.gpr, v₃.gpr, u₂.other _ h₂, u₁.other _ h₁, ct.gpr r hr], hmem,
      by rw [u₆.rd, u₅.rd, v₄.rd, v₃.rd, u₂.rd, u₁.rd, ct.rd], by rw [u₆.wr, u₅.wr, v₄.wr, v₃.wr, u₂.wr, u₁.wr, ct.wr]⟩
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [ev]; simp [he], ?_⟩
    rw [← he]; exact c₆
  · right
    refine ⟨by rw [ev]; simp; omega_arith, b - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, ?_, ?_, c₆⟩
    · rw [u₆.other _ (by decide), u₅.gpr, v₄.gpr, v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), xdx,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
    · rw [u₆.gpr, cx₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega_arith),
        Nat.sub_sub]

/-! ## The next tweak -/

section
variable (s₀ : State)

/-- The tweak and the second tweak, as addresses and as register values. -/
abbrev Tp : Addr := Sa s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := Sa s₀ + BitVec.ofNat 64 zO
abbrev Tv : BitVec 32 := S s₀ + BitVec.ofNat 32 tO
abbrev Zv : BitVec 32 := S s₀ + BitVec.ofNat 32 zO

end

theorem nextT_wp {s₀ s : State} {is : List Instr} {Φ : State → Prop} (hp : UPre s₀) (h : ArgsOk s₀ s)
    (hwr : s.wr = s₀.wr)
    (k : ∀ s', Chg s s' [.eax, .ecx, .edx, .ebx, .edi, .ebp] (Proof.AesXts.X86.alphaMem (copy4 s.mem (Zp s₀) (Tp s₀))
      (Zp s₀)) → WP isa (.block is) s' Φ) :
    WP isa (.block (nextT ++ is)) s Φ := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [nextT, List.append_assoc, List.append_assoc, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_argA h (i := 6) (by decide) fun s₁ u₁ => ?_
  have inS (d n : Nat) (hd : d + n ≤ 2432) : InRegions s₁.wr (Sa s₀ + BitVec.ofNat 64 d) n := by
    rw [u₁.wr, hwr, hp.wr]; exact ⟨scrR s₀, by simp, hp.cS d n hd⟩
  refine copy_wp (P := Zp s₀) (Q := Tp s₀) (by decide) (by decide) (by rw [u₁.gpr]) (by rw [u₁.gpr]; simp only [tO]; omega_arith)
    (by rw [u₁.gpr]) (by rw [u₁.gpr]; simp only [zO]; omega_arith) hp.t_z.symm
    (fun d n hd => by
      obtain ⟨r, hr, c⟩ := inS (tO + d) n (by simp only [tO]; omega_arith)
      exact ⟨r, List.mem_append_right _ hr, by rw [Offset.add_add]; exact c⟩)
    (fun d n hd => by rw [Offset.add_add]; exact inS (zO + d) n (by simp only [zO]; omega_arith)) fun s₂ c₂ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  obtain bx : s₄.gpr .ebx = Zv s₀ := by
    rw [u₄.gpr, u₃.gpr, c₂.gpr _ (by decide), u₁.gpr]
  obtain wr₄ : s₄.wr = s₁.wr := by rw [u₄.wr, u₃.wr, c₂.wr]
  obtain rd₄ : s₄.rd = s₁.rd := by rw [u₄.rd, u₃.rd, c₂.rd]
  obtain ⟨s₅, run₅, g₅, m₅, rd₅, wr₅⟩ := Proof.AesXts.X86.mulA_ok s₄ (Q := Zp s₀) (by rw [bx]; exact hp.scrW (by decide))
    (by rw [bx, hp.scrN (by decide)]; have := hp.scr_fit; simp only [zO]; omega_arith)
    (fun d n hd => by
      rw [rd₄, wr₄]
      obtain ⟨r, hr, c⟩ := inS (zO + d) n (by simp only [zO]; omega_arith)
      exact ⟨r, List.mem_append_right _ hr, by rw [Offset.add_add]; exact c⟩)
    (fun d n hd => by rw [wr₄, Offset.add_add]; exact inS (zO + d) n (by simp only [zO]; omega_arith))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, run₅, k s₅ ⟨fun r hr => ?_, ?_, ?_, ?_⟩⟩)
  · have h₁ : r ≠ .eax := fun e => hr (by simp [e])
    obtain h₂ : r ≠ .ecx := fun e => hr (by simp [e])
    obtain h₃ : r ≠ .edx := fun e => hr (by simp [e])
    obtain h₄ : r ≠ .ebx := fun e => hr (by simp [e])
    obtain h₅ : r ≠ .edi := fun e => hr (by simp [e])
    obtain h₆ : r ≠ .ebp := fun e => hr (by simp [e])
    rw [g₅ r h₁ h₂ h₃ h₅ h₆, u₄.other _ h₄, u₃.other _ h₄, c₂.gpr r (by simpa using h₁), u₁.other _ h₆]
  · rw [m₅, u₄.mem, u₃.mem, c₂.mem, u₁.mem]
  · rw [rd₅, rd₄, u₁.rd]
  · rw [wr₅, wr₄, u₁.wr]

end VG.Proof.AesXts.X86.Unit

end

end


/-!
# XTS-AES of data units on x86: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps `esp` and the permissions, its
caller's callee-saved registers in their slots, and changes memory only in
the data, the scratch buffer and the 52 bytes below `esp` (`Inv.step`, for
any code whose frame is in those); the arguments stay readable on the stack
(`Inv.args`). `tweak_wp`: the prologue and the call enciphering the tweak
value leave `T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the
epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86 (modeX86)
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_addi)
open VG.Spec.Aes (bytesAt)

/-- A whole-block function, verified. -/
structure XFn (enc : Bool) (f : Impl.Aes.X86.Blocks) : Prop where
  ok : XtsOk enc f.code
  ct : ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub f.code
  nosp : NoSp f.code
  stack : stackUse f.code ≤ 24

section
variable (s₀ : State)

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1))) (bytesAt s₀.mem ((I s₀).setWidth 64) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher :=
  ciphOf enc (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))

/-- The memory after the saves. -/
def sMem : Mem := Spill.saveMem s₀.mem (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saved_fits : Spill.Fits 2224 saved := by decide
theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 4 ≤ 2224 := by decide
theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide
theorem save_eq : save = Spill.saveCode .eax saved := rfl
theorem restore_eq : restore = .mov .eax (argOp 6) :: (Spill.restoreCode .eax saved ++ []) := rfl

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem slot_in {p : Reg × Nat} (h : p ∈ saved) :
    (⟨Sa s₀ + BitVec.ofNat 64 2208, 16⟩ : Region).Contains (Sa s₀ + BitVec.ofNat 64 p.2) 4 :=
  Offset.contains _ (saved_bound p h).1 (by have := saved_bound p h; omega_using [this]) (by decide)

theorem UPre.cvS {d n : Nat} (h : d + n ≤ 2432) : Covers [⟨Sa s₀ + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem Inv.args {s : State} (h : Inv s₀ s) : ArgsOk s₀ s := hp.argsOk h.esp h.rd h.wr h.frame

/-- `Inv` across code that keeps `esp` and writes only within `rs`, each in
the data, the first 2208 bytes of the scratch buffer or the stack below
`esp`. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨Sa s₀, 2208⟩ ∨ Region.Sub r (stkR s₀))
    (hf : Frame rs s.mem s'.mem) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv s₀ s' where
  esp := by rw [hesp, h.esp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stkR s₀, by simp, h⟩)
  saved := h.saved.of_frame hf (fun _ hp' => slot_in hp') fun r hr => hp.slots_disj (hrs r hr)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : BitVec 32} {N Rr : Nat}
    (hT : Region.Sub ⟨T.setWidth 64, 16⟩ ⟨Sa s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd.setWidth 64, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd.setWidth 64, 16 * N⟩ ⟨Sa s₀, 2208⟩)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h
    (rs := [⟨T.setWidth 64, 16⟩, ⟨Dd.setWidth 64, 16 * N⟩, ⟨(S s₀).setWidth 64, 2176⟩, below (s.gpr .esp) 52])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [hp.stk_eq h.esp]; exact fun _ h => h)))
    c.frame (c.saved .esp (by simp [calleeSaved])) c.rd c.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zv s₀) (Tv s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem ((I s₀).setWidth 64) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem sMem_frame : Frame [scrR s₀] s₀.mem (sMem s₀) :=
  Spill.saveMem_frame (List.mem_singleton_self _) _ _ saved s₀.mem fun p hp' =>
    hp.cS _ _ (by have := saved_bound p hp'; omega_using [this])

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  have hif : (arg s₀ 3).toNat + 16 ≤ 2 ^ 32 := hp.i_fit
  have hsc' : (S s₀).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, save_eq, List.cons_append,
    List.nil_append]
  refine wp_argA hp.argsOk₀ (i := 6) (by decide) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [e₁]; omega_using [hsc']) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [e₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, hp.cS _ _ (by omega_using [hb])⟩
  obtain m₂ : s₂.mem = sMem s₀ := by
    rw [u₂.mem, u₁.mem, e₁, sMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by rw [m₂]; exact sMem_frame hp
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  obtain rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  obtain h₂ : ArgsOk s₀ s₂ := hp.argsOk esp₂ rd₂ wr₂ (f₂.mono (by simp))
  rw [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => ?_
  obtain bp₃ : s₃.gpr .ebp = S s₀ := by rw [u₃.gpr, u₂.gpr, e₁]
  obtain h₃ := h₂.upd u₃ (by decide)
  rw [copyI, List.cons_append]
  refine wp_argA h₃ (i := 3) (by decide) fun s₄ u₄ => ?_
  obtain h₄ := h₃.upd u₄ (by decide)
  obtain bp₄ : s₄.gpr .ebp = S s₀ := by rw [u₄.other _ (by decide), bp₃]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂]
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine copy_wp (P := Tp s₀) (Q := (I s₀).setWidth 64) (by decide) (by decide) (by rw [u₄.gpr]; simp)
    (by rw [u₄.gpr]; omega_using [hif]) (by rw [bp₄]) (by rw [bp₄]; simp only [tO]; omega_using [hsc'])
    (hp.i_scr.symm.sub_left (sub_trans t_sub s_sub))
    (fun d n hd => by
      rw [rd₄, wr₄, hp.rd]; exact ⟨iR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩)
    (fun d n hd => by
      rw [wr₄, hp.wr]
      exact ⟨scrR s₀, by simp, by rw [Offset.add_add]; exact hp.cS _ _ (by simp only [tO]; omega_using [hd])⟩)
    fun s₅ c₅ => ?_
  obtain bp₅ : s₅.gpr .ebp = S s₀ := by rw [c₅.gpr _ (by decide), bp₄]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [c₅.wr, wr₄]
  obtain h₅ : ArgsOk s₀ s₅ := hp.argsOk_frame h₄ (c₅.gpr _ (by decide)) c₅.rd c₅.wr
    (by rw [c₅.mem]; exact copy4_frame _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_right (sub_trans t_sub s_sub)
  rw [zeroZ]
  refine VG.Proof.CmacAes.X86.zero4_ok (b := .ebp) (d := zO) (by decide)
    (by rw [bp₅]; simp only [zO]; omega_using [hsc']) (by rw [bp₅, wr₅]; exact hp.cvS (by simp only [zO]; omega_using []))
    fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  rw [bp₅] at m₆
  obtain h₆ : ArgsOk s₀ s₆ := hp.argsOk_frame h₅ (g₆ _ (by decide)) rd₆ wr₆
    (by rw [m₆]; exact Proof.Cmac.frame_store4 _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_right (sub_trans z_sub s_sub)
  obtain bp₆ : s₆.gpr .ebp = S s₀ := by rw [g₆ _ (by decide), bp₅]
  simp only [tArgs]
  refine wp_argA h₆ (i := 1) (by decide) fun s₇ u₇ => ?_
  obtain h₇ := h₆.upd u₇ (by decide)
  refine wp_argA h₇ (i := 2) (by decide) fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => wp_addi fun s₁₂ u₁₂ => ?_
  refine wp_movi fun s₁₃ u₁₃ => WP.block_nil ?_
  obtain c := ((((((Chg.refl s₆ [.eax, .ecx, .edx, .ebx, .edi]).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉
    (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide) |>.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  obtain bp : s₁₃.gpr .ebp = S s₀ := by rw [c.gpr _ (by decide), bp₆]
  obtain esp : s₁₃.gpr .esp = s₀.gpr .esp := by
    rw [c.gpr _ (by decide), g₆ _ (by decide), c₅.gpr _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), esp₂]
  obtain rd : s₁₃.rd = s₀.rd := by rw [c.rd, rd₆, c₅.rd, rd₄]
  obtain wr : s₁₃.wr = s₀.wr := by rw [c.wr, wr₆, wr₅]
  obtain mem : s₁₃.mem = Proof.Cmac.zero4 (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) (Zp s₀) := by
    rw [c.mem, m₆, c₅.mem, m₄, m₂]
  obtain fT : Frame [⟨Tp s₀, 16⟩] (sMem s₀) (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) := copy4_frame _ _ _
  obtain fZ : Frame [⟨Zp s₀, 16⟩] (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64))
      (Proof.Cmac.zero4 (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) (Zp s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  obtain frame : Frame [scrR s₀] s₀.mem s₁₃.mem := by
    rw [mem]
    refine (sMem_frame hp).trans ((fT.sub fun r hr => ?_).trans (fZ.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
  obtain sv : Spill.Saved (sMem s₀) (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved :=
    Spill.saveMem_saved_ofNat _ _ _ saved_fits (by decide)
  obtain sdisj : ∀ (r : Region), Region.Sub r ⟨Sa s₀, 2208⟩ → ∀ r' ∈ [r],
      Region.Disjoint ⟨Sa s₀ + BitVec.ofNat 64 2208, 16⟩ r' := fun r hr r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hp.slots_disj (.inr (.inl hr))
  refine ⟨⟨esp, rd, wr, frame.mono (by simp), ?_⟩, ?_, frame, ?_, ?_⟩
  · rw [mem]
    exact (sv.of_frame fT (fun _ h => slot_in h) (sdisj _ t_sub)).of_frame fZ (fun _ h => slot_in h)
      (sdisj _ z_sub)
  · refine xpre_tweak hp rd wr esp ?_ ?_ ?_ ?_ ?_ bp
    · simp (disch := decide) only [u₁₃.other, u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.gpr]
    · simp (disch := decide) only [u₁₃.other, u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, r_ofNat]
    · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr,
        u₈.other _ (by decide), u₇.other _ (by decide), bp₆]
    · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), bp₆]
    · exact u₁₃.gpr
  · rw [mem, Proof.Cmac.bytesAt_frame fZ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), copy4_bytes,
      Proof.Cmac.bytesAt_frame (sMem_frame hp) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem, Proof.Cmac.zero4_bytes]; rfl

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stkR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stkR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (xcall f) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true hf.ok hf.nosp hf.stack h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain stk := hp.stk_eq h₂.inv.esp
  obtain aT := hp.scrW (d := tO) (by decide)
  obtain aZ := hp.scrW (d := zO) (by decide)
  obtain eK : bytesAt s₂.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1)) =
      bytesAt s₀.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv (by rw [aZ]; exact z_sub) (.inr (by rw [aT]; exact t_sub)) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aZ]; exact sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩
  · have o := c.out
    rw [aZ, aT] at o
    have := Proof.AesXts.Unit.tweak_of (R := R s₀)
      (w := bytesAt s₂.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1))) o h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) : WP isa (tweak f) s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp hf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (Da s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem s.mem

theorem blocks_call {enc : Bool} {f : Impl.Aes.X86.Blocks} (hf : XFn enc f) {N : Nat} (hN : 16 * N ≤ Len s₀)
    {s : State} (h : TwPost s₀ s) (hpre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (xcall f) s fun s' => AllPost enc s₀ N s' ∧ s'.gpr .esi = s.gpr .esi := by
  refine WP.mono (xts_call enc hf.ok hf.nosp hf.stack hpre) fun s' x => ⟨?_, x.saved .esi (by simp [calleeSaved])⟩
  obtain aT := hp.scrW (d := tO) (by decide)
  obtain stk := hp.stk_eq h.inv.esp
  obtain dS : Region.Sub ⟨Da s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (Da s₀) N = Spec.Cbc.blocksAt s₀.mem (Da s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_fit; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl dS) x, ?_, ?_, ?_⟩
  · have o := x.out
    rw [aT] at o
    rw [o, eW, h.t, eD]
  · have o := x.tw
    rw [aT] at o
    rw [o, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩

/-- `TwPost` across code that keeps `esp` and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hesp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hesp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [restore_eq]
  refine wp_argA (Inv.args hp h) (i := 6) (by decide) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega_using [hsc]) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact h.saved p hp') fun s₂ r₂ => WP.block_nil
      ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, h.rd, h.wr, hp.wr]
    exact ⟨scrR s₀, by simp, hp.cS _ _ (by omega_using [hb])⟩
  · rw [r₂.mem, u₁.mem]
    have := hp.esp_fit
    obtain rs : (retR s₀).Disjoint (stkR s₀) := Offset.base_disjoint_below _ (by decide)
    exact h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_data
      · exact hp.ret_scr
      · exact rs) (by decide)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : BitVec 32} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd.setWidth 64, 16 * N⟩)
    (hT : Region.Sub ⟨T.setWidth 64, 16⟩ (scrR s₀)) (hesp : s.gpr .esp = s₀.gpr .esp)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [hp.stk_eq hesp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.X86.Unit
