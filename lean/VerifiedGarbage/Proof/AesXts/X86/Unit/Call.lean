module
public import VerifiedGarbage.Proof.AesCbc.X86.Call
public import VerifiedGarbage.Proof.AesXts.Spec

import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCbc.X86.Body
import VerifiedGarbage.Proof.AesXts.Batch
import VerifiedGarbage.Proof.AesXts.X86.Unit.Contract

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
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The regions the callee is given. -/
abbrev xRd (E W : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev xWr (T D S : BitVec 32) (N : Nat) : List Region :=
  [⟨T.setWidth 64, 16⟩, ⟨D.setWidth 64, 16 * N⟩, ⟨S.setWidth 64, 2176⟩]

namespace XPre
variable {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R)
include h

theorem fit : 4 * xRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp52; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed xRegs s).callEntry 0 = W ∧ arg (pushed xRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed xRegs s).callEntry 2 = T ∧ arg (pushed xRegs s).callEntry 3 = D ∧
    arg (pushed xRegs s).callEntry 4 = BitVec.ofNat 32 N ∧ arg (pushed xRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 52) := below_sub (by omega) h.esp52

theorem subRet : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 52) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 52) (k := 24) (by omega) h.esp52
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem subStk : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    (below (s.gpr .esp) 52) := by
  have := below_inner (sp := s.gpr .esp) (a := 24) (b := 52) (k := 28) (by omega) h.esp52
  rw [← Taint.sub_setWidth (by rw [sub_toNat (by have := h.esp52; omega)]; have := h.esp52; omega)]
  exact this

theorem callPre (enc : Bool) :
    CallPre (modeX86 (AesXts.xtsMode enc)) xRegs (xRd (s.gpr .esp) W) (xWr T D S N) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  have eA : argAddr (pushed xRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed xRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hN]
    refine ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.bt.sub_left h.sub24, h.bd.sub_left h.sub24,
      h.bs.sub_left h.sub24, h.bt.sub_left h.subRet, h.bd.sub_left h.subRet, h.bs.sub_left h.subRet,
      h.bw.sub_left h.subStk, h.bt.sub_left h.subStk, h.bd.sub_left h.subStk, h.bs.sub_left h.subStk,
      h.fitW, h.fitT, h.fitD, h.fitS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by have := h.esp52; omega)]; have := h.esp52; omega
    · rw [sub_toNat (by have := h.esp52; omega)]; have := (s.gpr .esp).isLt; omega
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
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  refine WP.callWith (rs := xRegs) (k := modeX86 (AesXts.xtsMode enc)) ok nosp (by decide) hrs
    (by have := h.esp52; simp only [List.length_cons, List.length_nil]; omega) (h.callPre enc)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have fE := callEntry_frame h.fit hrs
  rw [show 4 * xRegs.length + 4 = 28 from rfl] at fE
  have b28 : Region.Sub (below (s.gpr .esp) 28) (below (s.gpr .esp) 52) := below_sub (by omega) h.esp52
  have keep : ∀ {X : Region}, (below (s.gpr .esp) 52).Disjoint X → X.len ≤ 2 ^ 64 →
      bytesAt (pushed xRegs s).callEntry.mem X.base X.len = bytesAt s.mem X.base X.len :=
    fun hd hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_left b28).symm) hn
  have eW := keep (X := ⟨W.setWidth 64, 16 * (R + 1)⟩) (h.bw.sub_right (Region.sub_prefix hRb)) (by dsimp only; omega)
  have eT := keep (X := ⟨T.setWidth 64, 16⟩) h.bt (by simp)
  have eD : Spec.Cbc.blocksAt (pushed xRegs s).callEntry.mem (D.setWidth 64) N =
      Spec.Cbc.blocksAt s.mem (D.setWidth 64) N :=
    blocksAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bd.sub_left b28).symm) (by have := h.fitD; omega)
  simp only [modeX86, AesXts.xtsMode, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hN,
    m₂, Proof.AesXts.Unit.length_blocksAt] at post
  rw [eW, eT, eD] at post
  refine ⟨rd', wr', cs', ?_, post.1, post.2⟩
  have f'' := Frame.below_mono f' (b := 52) (by simp only [List.length_cons, List.length_nil]; omega) h.esp52
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
  have p₁ := h₁.callPre enc
  have p₂ := h₂.callPre enc
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

end VG.Proof.AesXts.X86.Unit
