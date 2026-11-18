module

public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.SignCached
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init

/-! ### `Ed25519.X86_64.SignCached.Args`, which only this module used -/

section

/-! ### `Ed25519.X86_64.SignCached.Layout`, which only this module used -/

section

/-! The frame and memory invariant of complete Ed25519 signing. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.SignCached

open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within within_base within_off)
open VG.Impl.Ed25519.X86_64 (combSym combWords combWordCount)

structure Lay where
  out : Addr
  seed : Addr
  pk : Addr
  msg : Addr
  len : BitVec 64
  scr : Addr
  B : Addr
  /-- The comb's tables (the static `combSym`). -/
  T : Addr
  /-- The bytes read at `seed`: the seed (32), or its cached SHA-512 digest (64). -/
  seedLen : Nat

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 64⟩
abbrev SEED : Region := ⟨L.seed, L.seedLen⟩
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.B, 264⟩
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 248⟩
abbrev DATA : Region := ⟨L.B + BitVec.ofNat 64 16, 192⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 264, 8⟩
abbrev TBL : Region := combRegion L.T
/-- The regions only read: the seed (or its digest), the public key, the message and the comb's tables. -/
def inputs : List Region := [L.SEED, L.PK, L.MSG, L.TBL]
structure Ok : Prop where
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ro : L.RET.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 64
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 64
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  ns : L.seed.toNat + L.seedLen ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  nt : L.T.toNat + 8 * combWordCount ≤ 2 ^ 64
  sl : 32 ≤ L.seedLen
end Lay

namespace Lay.Ok
variable {L : Lay}
theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 264) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)
theorem stk_input (h : L.Ok) {r : Region} (hr : r ∈ L.inputs) {d n : Nat} (hd : d + n ≤ 264) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  (h.ks r hr).sub_left (Offset.sub_base _ hd)
end Lay.Ok

structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.inputs
  wr : t.wr = [L.FR, L.OUT, L.SCR]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.B + BitVec.ofNat 64 216) 64 = L.scr
  pLen : t.mem.readW (L.B + BitVec.ofNat 64 224) 64 = L.len
  pMsg : t.mem.readW (L.B + BitVec.ofNat 64 232) 64 = L.msg
  pPk : t.mem.readW (L.B + BitVec.ofNat 64 240) 64 = L.pk
  pSeed : t.mem.readW (L.B + BitVec.ofNat 64 248) 64 = L.seed
  pOut : t.mem.readW (L.B + BitVec.ofNat 64 256) 64 = L.out
  frame : Frame [L.OUT, L.SCR, L.STK] m₀ t.mem
  sym : t.syms combSym = L.T
  held : ∀ i < combWordCount, m₀.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) :
    Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pPk,
    by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut, by rw [hm]; exact hc.frame,
    by rw [hsy]; exact hc.sym, hc.held⟩
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [PublicKey.sub8']
theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩
theorem inFrW (hc : Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩
theorem ea_fr (hc : Ctx L g mx m₀ t) (d : Nat) :
    t.ea (Impl.Ed25519.X86_64.stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [PublicKey.ea_stk, hc.rsp, PublicKey.add_add]
theorem input_byte (hL : L.Ok) (hc : Ctx L g mx m₀ t) {r : Region} (hr : r ∈ L.inputs)
    (hn : r.len ≤ 2 ^ 64) {i : Nat} (hi : i < r.len) :
    t.mem (r.base + BitVec.ofNat 64 i) = m₀ (r.base + BitVec.ofNat 64 i) :=
  Frame.bytes hc.frame (by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.os r hr).symm
    · exact hL.sc r hr
    · exact (hL.ks r hr).symm) hn hi
end Ctx

/-- Calls may overwrite scratch, output and frame data, but not the saved arguments. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    refine Covers.of_sub fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hw⟩
  have hcovw : Covers wr t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [hc.wr]
    rcases hwsub r hr with h | h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, by exact Nat.le_trans hn (by show 192 ≤ 248; decide)⟩
    · exact ⟨L.OUT, by simp, h⟩
    · exact ⟨L.SCR, by simp, h⟩
  refine WP.of_syms (WP.call_mx hv hsp (by omega_using [hd]) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx hsy => ?_)
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact PublicKey.below_call_sub _ (by omega)
  have hdisj : ∀ d, 216 ≤ d → d + 8 ≤ 264 → ∀ r ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ r := by
    intro d h₁ h₂ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h | h
      · exact (Offset.disjoint L.B (d := d) (n := 8) (e := 16) (k := 192)
          (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])).sub_right h.sub
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
  have keep : ∀ d, 216 ≤ d → d + 8 ≤ 264 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 216 (by omega_using []) (by omega_using [])).trans hc.pScr,
    (keep 224 (by omega_using []) (by omega_using [])).trans hc.pLen, (keep 232 (by omega_using []) (by omega_using [])).trans hc.pMsg,
    (keep 240 (by omega_using []) (by omega_using [])).trans hc.pPk, (keep 248 (by omega_using []) (by omega_using [])).trans hc.pSeed,
    (keep 256 (by omega_using []) (by omega_using [])).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_), hsy.symm ▸ hc.sym, hc.held⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h | h
      · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base L.B (by decide : 16 + 192 ≤ 264) a (h.sub a ha)⟩
      · exact ⟨L.OUT, by simp, h.sub⟩
      · exact ⟨L.SCR, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 264) (by omega_using [])
      simpa using this

end VG.Proof.Ed25519.X86_64.SignCached

end

end


/-! Short symbolic executions for the complete signer's call arguments. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk shaScratch)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add sx32 zx32 ne_cs)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def InitArgs (L : Lay) (t : State) : Prop := t.gpr .rdi = L.scr

theorem initArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block initArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ InitArgs L t' := by
  have hin := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  refine WP.of_runBlock ⟨t.setReg .rdi L.scr, ?_, ?_⟩
  · simp only [initArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, hc.ea_fr, hin, ite_true, Option.map_some, hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide)), rfl,
    RegUpd.gpr_setReg_self _ _ _⟩

def UpdArgs (L : Lay) (count : BitVec 64) (p : Addr) (n : BitVec 64) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = count ∧ t.gpr .rdx = p ∧ t.gpr .rcx = n ∧
    t.gpr .r8 = L.scr + BitVec.ofNat 64 192

theorem inputArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (source count : Nat)
    (hs : source + 8 ≤ 248) (hcount : count < 2 ^ 32) (p : Addr)
    (hp : t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p) :
    WP isa (.block (inputArgs source count)) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      UpdArgs L (BitVec.ofNat 64 count) p 32 t' := by
  have h216 := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  have hsrc := hc.inFr (d := 16 + source) (by omega_using []) (by omega_using [hs])
  apply WP.of_runBlock
  simp only [inputArgs, scrPtr, shaScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h216, hsrc, Option.some.injEq, exists_eq_left', hc.pScr, hp, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 hcount,
    trivial, rfl, by rw [sx32 (by omega_using [])]⟩

theorem messageArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (count : Nat)
    (hcount : count < 2 ^ 32) :
    WP isa (.block (messageArgs count)) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      UpdArgs L (BitVec.ofNat 64 count) L.msg L.len t' := by
  have h216 := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  have h224 := hc.inFr (d := 224) (by omega_using []) (by omega_using [])
  have h232 := hc.inFr (d := 232) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [messageArgs, scrPtr, shaScratch, fScratch, fMessage, fLength,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, readSrc32, State.load64, State.setReg32, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h216, h224, h232,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pMsg, hc.pLen, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 hcount,
    trivial, trivial, by rw [sx32 (by omega_using [])]⟩


theorem prefixArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block prefixArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      UpdArgs L 0 (L.B + BitVec.ofNat 64 48) 32 t' := by
  have hin := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  apply WP.of_runBlock
  simp only [prefixArgs, framePtr, scrPtr, shaScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hin, Option.some.injEq, exists_eq_left', hc.pScr, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl,
    by rw [sx32 (by decide : 32 < 2 ^ 31), add_add],
    rfl, by rw [sx32 (by omega_using [])]⟩

def FinArgs (L : Lay) (count : BitVec 64) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = count ∧ t.gpr .rdx = L.B + BitVec.ofNat 64 144 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 192

theorem finalizeArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (prefixLen : Nat)
    (hp : prefixLen < 2 ^ 31) (withMessage : Bool) :
    WP isa (.block (finalizeArgs prefixLen withMessage)) t fun t' => Ctx L g mx m₀ t' ∧
      t'.mem = t.mem ∧ FinArgs L
        (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen) t' := by
  have hs := hc.inFr (d := 216) (by omega_using []) (by omega_using [])
  have hl := hc.inFr (d := 224) (by omega_using []) (by omega_using [])
  cases withMessage <;> apply WP.of_runBlock <;>
    simp only [finalizeArgs, framePtr, scrPtr, shaScratch, fScratch, fLength, Bool.false_eq_true,
      ite_false, ite_true, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, readSrc32, State.load64, State.setReg32, ea_stk,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
      Nat.reduceAdd, hs, hl, Option.some.injEq, exists_eq_left', hc.pScr, hc.pLen, FinArgs]
  · exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 (by omega_using [hp]),
      by rw [sx32 (by decide : 128 < 2 ^ 31), add_add],
      by rw [sx32 (by omega_using [])]⟩
  · exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, by rw [sx32 hp],
      by rw [sx32 (by decide : 128 < 2 ^ 31), add_add],
      by rw [sx32 (by omega_using [])]⟩

end VG.Proof.Ed25519.X86_64.SignCached

end

end


/-! Merged from `Proof.Ed25519.X86_64.SignCached.Prune`. -/

@[expose] public section

section
/-! Pruning and saving the expanded signing scalar. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (pkPruneStores stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add prune_words decode_words take_bytesAt)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Frame stores cannot overwrite the saved arguments. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) {d n : Nat}
    (_hd : 16 ≤ d) (hn : d + n ≤ 208)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr) (hsy : t'.syms = t.syms)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 d, n⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ e, 216 ≤ e → e + 8 ≤ 264 →
      t'.mem.readW (L.B + BitVec.ofNat 64 e) 64 = t.mem.readW (L.B + BitVec.ofNat 64 e) 64 := by
    intro e h₁ h₂
    exact hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr h => (hg r hr).trans (hc.cs r hr h), by rw [hmx]; exact hc.mx,
    (keep 216 (by omega_arith) (by omega_arith)).trans hc.pScr,
    (keep 224 (by omega_arith) (by omega_arith)).trans hc.pLen,
    (keep 232 (by omega_arith) (by omega_arith)).trans hc.pMsg,
    (keep 240 (by omega_arith) (by omega_arith)).trans hc.pPk,
    (keep 248 (by omega_arith) (by omega_arith)).trans hc.pSeed,
    (keep 256 (by omega_arith) (by omega_arith)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf ?_), by rw [hsy]; exact hc.sym, hc.held⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_arith)⟩

abbrev dw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.B + BitVec.ofNat 64 (144 + 8 * k)) 64

theorem pruneRegs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pruneRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = dw t L 1 ∧
      t'.gpr .r10 = dw t L 2 ∧
      t'.gpr .r11 = ((dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  have s0 := hc.inFr (d := 144) (by omega_arith) (by omega_arith)
  have s1 := hc.inFr (d := 152) (by omega_arith) (by omega_arith)
  have s2 := hc.inFr (d := 160) (by omega_arith) (by omega_arith)
  have s3 := hc.inFr (d := 168) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [pruneRegs, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, 
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-8)) = BitVec.ofNat 64 (2 ^ 64 - 8)),
    trivial, trivial, trivial⟩

theorem stores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega_arith) (by omega_arith)
  have w1 := hc.inFrW (d := 24) (by omega_arith) (by omega_arith)
  have w2 := hc.inFrW (d := 32) (by omega_arith) (by omega_arith)
  have w3 := hc.inFrW (d := 40) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = h) :
    WP isa (.block (pruneRegs ++ pkPruneStores)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (pruneRegs_ok hc) fun u ⟨hcu, hmu, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (stores_ok hcu) fun u' ⟨hcu', hf, _, r0, r1, r2, r3⟩ => ?_
  refine ⟨hcu', hmu ▸ hf, ?_⟩
  rw [Spec.Ed25519.prune, ← hh, take_bytesAt]
  simp only [decode_words, add_add, Nat.reduceAdd, r0, r1, r2, r3, h8, h9, h10, h11]
  exact (prune_words _ _ _ _).symm

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Hash`. -/
section
/-! Modular SHA-512 calls used by the complete signer. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 sub88 nosp_init upd_verified upd_nosp upd_depth
   fin_verified fin_nosp fin_depth ce_byte)
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- A hash input can be a caller buffer or a saved value in the frame. -/
structure Input (L : Lay) (r : Region) : Prop where
  cover : ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  scratch : r.Disjoint L.SCR
  below : (⟨L.B, 16⟩ : Region).Disjoint r

theorem Input.scr {r : Region} (hi : Input L r) {d n : Nat} (h : d + n ≤ 8192) :
    r.Disjoint ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  hi.scratch.sub_right (Offset.sub_base _ h)

theorem Input.stk {r : Region} (hi : Input L r) {d n : Nat} (h : d + n ≤ 16) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hi.below.sub_left (Offset.sub_base _ h)

theorem Ctx.ce_bytes {t : State} (hc : Ctx L g mx m₀ t)
    {r : Region} (hi : Input L r) (hn : r.len ≤ 2 ^ 64) :
    Spec.Sha512.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt t.mem r.base r.len := by
  unfold Spec.Sha512.bytesAt Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => ?_
  exact ce_byte t (by rw [hc.ret]; exact hi.stk (by omega_arith)) hn (List.mem_range.mp h)

theorem Ctx.ce_repr (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {iv : Spec.Sha512.HashValue}
    {m : List Byte} (hr : Spec.Sha512.Repr iv t.mem L.scr m) :
    Spec.Sha512.Repr iv t.callEntry.mem L.scr m :=
  Proof.Sha512.Stream.repr_congr (fun i hi => ce_byte t (R := ⟨L.scr, 192⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith))
    (by show (192 : Nat) ≤ 2 ^ 64; decide) hi) hr

abbrev initRd : List Region := []
abbrev initWr (L : Lay) : List Region := [⟨L.scr, 192⟩]

theorem init_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    (Proof.Sha512.initX86_64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions initRd (initWr L)) := by
  have hrdi := (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha
  refine ⟨rfl, by rw [hrdi]; rfl, ?_⟩
  rw [rsp_ce, hrdi, hc.rsp, sub8]
  simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith)

theorem init_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : InitArgs L t) :
    WP isa (.call "vg_sha512_init_core" (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ Frame (initWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (nosp_init _) (by decide) hc
    (init_pre hL hc ha) ?_ ?_ fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · rintro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
  · rintro r hr
    simp only [initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (.inr (within_base _ (by omega_arith)))
  · have := hpost
    simp only [Proof.Sha512.initX86_64, (gpr_ce t initRd (initWr L) (r := .rdi) (by decide)).trans ha] at this
    rwa [← hm]

abbrev updWr (L : Lay) : List Region := [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem upd_regs {t : State} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : UpdArgs L count p n t) (rd wr : List Region) :
    UpdArgs L count p n (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem upd_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {count : BitVec 64} {p : Addr} {n : BitVec 64} (ha : UpdArgs L count p n t)
    (hi : Input L ⟨p, n.toNat⟩) :
    Proof.Sha512.updateX86_64.pre (t.callEntry.withRegions [⟨p, n.toNat⟩] (updWr L)) := by
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := upd_regs ha [⟨p, n.toNat⟩] (updWr L)
  simp only [Proof.Sha512.updateX86_64, rsp_ce, hdi, hdx, hcx, h8, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    by simpa using hi.scr (d := 0) (n := 192) (by omega_arith), hi.scr (by omega_arith),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith),
    hL.stk_scr (d := 8) (n := 8) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith),
    by simpa using hi.stk (d := 0) (n := 8) (by omega_arith),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega_arith) (by omega_arith)⟩

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {prev : List Byte} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : UpdArgs L count p n t) (hi : Input L ⟨p, n.toNat⟩)
    (hcount : count = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (.call ("vg_sha512_update_scratch" ++ v.suffix) (Impl.Sha512.X86_64.Stream.updateOwn v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧
        Frame (updWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (upd_verified v).1 (upd_nosp v) (upd_depth v) hc (upd_pre hL hc ha hi) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
  · intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega_arith)))
    · exact .inr (.inr (within_off _ (by omega_arith)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := upd_regs ha [⟨p, n.toNat⟩] (updWr L)
    have h := hpost Spec.Sha512.H0_512 prev
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (hsi.trans hcount)
    simp only [State.withRegions_mem, hdi, hdx, hcx, hm] at h
    rw [hc.ce_bytes hi (Nat.le_of_lt n.isLt)] at h
    exact h


abbrev finWr (L : Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} {count : BitVec 64} (ha : FinArgs L count t) (rd wr : List Region) :
    FinArgs L count (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {count : BitVec 64} (ha : FinArgs L count t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions [] (finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := fin_regs ha [] (finWr L)
  simp only [Proof.Sha512.finalizeX86_64, rsp_ce, hdi, hdx, hcx, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using (hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 192) (by omega_arith) (by omega_arith)).symm,
    Offset.base_disjoint _ (by omega_arith) (by omega_arith), hL.stk_scr (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith),
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith),
    hL.stk_scr (d := 8) (n := 8) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega_arith) (by omega_arith),
    Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega_arith) (by omega_arith)⟩

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {count : BitVec 64} (ha : FinArgs L count t)
    {message : List Byte} (hmess : message.length < 2 ^ 64)
    (hlen : count = BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (.call ("vg_sha512_finalize_scratch" ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalizeOwn v.callee)) t
      fun t' => Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 message ∧ Frame (finWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (fin_verified v).1 (fin_nosp v) (fin_depth v) hc (fin_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.FR, by simp, 128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
  · intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega_arith)))
    · exact .inl ⟨128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega_arith)))
  · obtain ⟨hdi, hsi, hdx, -⟩ := fin_regs ha [] (finWr L)
    have h := hpost Spec.Sha512.H0_512 message
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) hmess (hsi.trans hlen)
    rw [hdx, hm] at h
    exact h

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.MulAdd`. -/
section
/-! The final scalar multiply-add in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32 ce_byte)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def MulArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out + BitVec.ofNat 64 32 ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rdx = L.B + BitVec.ofNat 64 112 ∧ t.gpr .rcx = L.B + BitVec.ofNat 64 16 ∧ t.gpr .r8 = L.scr

theorem mulArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block mulAddArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ MulArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  have ho := hc.inFr (d := 256) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [mulAddArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, MulArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, rfl,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 96 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 0 < 2 ^ 31), BitVec.add_zero], trivial⟩

abbrev mulRd (L : Lay) : List Region :=
  [⟨L.B + BitVec.ofNat 64 80, 32⟩, ⟨L.B + BitVec.ofNat 64 112, 32⟩, ⟨L.B + BitVec.ofNat 64 16, 32⟩]
abbrev mulWr (L : Lay) : List Region := [⟨L.out + BitVec.ofNat 64 32, 32⟩, L.SCR]

theorem mul_regs {t : State} (ha : MulArgs L t) (rd wr : List Region) :
    MulArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem mul_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : MulArgs L t) :
    scalarMulAddLocal.pre (t.callEntry.withRegions (mulRd L) (mulWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8⟩ := mul_regs ha (mulRd L) (mulWr L)
  simp only [scalarMulAddLocal, rsp_ce, hdi, hsi, hdx, hcx, h8, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 112) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 16) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (Offset.sub_base L.out (d := 32) (n := 32) (by decide)),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega_arith) (by omega_arith), hL.nc,
    hL.oc.sub_left (Offset.sub_base L.out (d := 32) (n := 32) (by decide))⟩

theorem mul_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : MulArgs L t) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.out + BitVec.ofNat 64 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) ∧
      Frame (mulWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL scalarMulAdd_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (mul_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega_arith)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega_arith)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
  · intro r hr
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega_arith)))
    · exact .inr (.inr (within_base _ (by omega_arith)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := mul_regs ha (mulRd L) (mulWr L)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarMulAdd _ _ _ at hpost
    rw [hdi, hsi, hdx, hcx, State.withRegions_mem, hm] at hpost
    have he (d : Nat) (hd : 16 ≤ d) (hn : d + 32 ≤ 264) :
        Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 d) 32 =
          Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 d) 32 := by
      apply List.map_congr_left
      intro i hi
      exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 d, 32⟩) (i := i)
        (by rw [hc.ret]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he 80 (by decide) (by decide), he 112 (by decide) (by decide), he 16 (by decide) (by decide)] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Prefix`. -/
section
/-! Save the expanded key's nonce prefix without changing its pruned scalar. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add decode_words)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem prefixRegs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block prefixRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = dw t L 4 ∧ t'.gpr .r9 = dw t L 5 ∧
      t'.gpr .r10 = dw t L 6 ∧ t'.gpr .r11 = dw t L 7 := by
  have h0 := hc.inFr (d := 176) (by omega_arith) (by omega_arith)
  have h1 := hc.inFr (d := 184) (by omega_arith) (by omega_arith)
  have h2 := hc.inFr (d := 192) (by omega_arith) (by omega_arith)
  have h3 := hc.inFr (d := 200) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [prefixRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, Nat.reduceAdd,
    h0, h1, h2, h3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial⟩

theorem prefixStores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block prefixStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 56) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 64) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 72) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 48) (by omega_arith) (by omega_arith)
  have w1 := hc.inFrW (d := 56) (by omega_arith) (by omega_arith)
  have w2 := hc.inFrW (d := 64) (by omega_arith) (by omega_arith)
  have w3 := hc.inFrW (d := 72) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [prefixStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok (L.B + BitVec.ofNat 64 32) u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  simp only [add_add, Nat.reduceAdd] at hf h0 h1 h2 h3
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prefix_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (prefixRegs ++ prefixStores)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 =
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64).drop 32 := by
  rw [WP.block_append_iff]
  refine WP.mono (prefixRegs_ok hc) fun u ⟨hu, hm, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (prefixStores_ok hu) fun w ⟨hw, hf, _, h0, h1, h2, h3⟩ => ?_
  refine ⟨hw, hm ▸ hf, ?_⟩
  rw [Proof.Ed25519.signatureBytes_drop, add_add]
  rw [Proof.Ed25519.bytesAt_encodeLE w.mem, Proof.Ed25519.bytesAt_encodeLE t.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  simp only [decode_words, add_add, Nat.reduceAdd, h0, h1, h2, h3, h8, h9, h10, h11, dw,
    Nat.reduceMul]

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Wipe`. -/
section
/-! The frame wipe preserves the signature and the calling convention. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem wipe_word {t : State} (hc : Ctx L g mx m₀ t) (i : Nat) (hi : i < 24) :
    WP isa (.block [.store (stk (8 * i)) .rax]) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  have hw := hc.inFrW (d := 16 + 8 * i) (by omega_arith) (by omega_arith)
  have hf : Frame [L.DATA] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * i)) (t.gpr .rax)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp,
    add_add, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl rfl (fun _ _ => rfl) hf, hf⟩

theorem wipe_words (is : List Nat) (hi : ∀ i ∈ is, i < 24) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (is.map fun i => .store (stk (8 * i)) .rax)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  induction is generalizing t with
  | nil => exact WP.of_runBlock ⟨t, rfl, hc, Frame.refl _ _⟩
  | cons i is ih =>
    change WP isa (.block (([.store (stk (8 * i)) .rax] : List Instr) ++
      is.map (fun j => .store (stk (8 * j)) .rax))) t _
    rw [WP.block_append_iff]
    refine WP.mono (wipe_word hc i (hi i (by simp))) fun u ⟨hu, hf⟩ => ?_
    exact WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem i hj)) hu)
      fun w ⟨hw, hf'⟩ => ⟨hw, hf.trans hf'⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block wipe) t fun t' => Ctx L g mx m₀ t' ∧ Frame [L.DATA] t.mem t'.mem := by
  rw [wipe, WP.block_append_iff]
  have hz : WP isa (.block [.alu32 .xor .rax (.reg .rax)]) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
      State.setReg32,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), rfl⟩
  refine WP.mono hz fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (wipe_words (List.range 24) (fun _ h => List.mem_range.mp h) hu)
    fun w ⟨hw, hf⟩ => ⟨hw, hm ▸ hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Reduce`. -/
section
/-! Reduce a digest into the nonce or challenge slot. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32)
variable {out : Nat} {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def ReduceArgs (L : Lay) (out : Nat) (t : State) : Prop :=
  t.gpr .rdi = L.B + BitVec.ofNat 64 (16 + out) ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 144 ∧
    t.gpr .rdx = L.scr

theorem reduceArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (ho : out + 32 ≤ 128) :
    WP isa (.block (reduceArgs out)) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ ReduceArgs L out t' := by
  have h216 := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [reduceArgs, framePtr, fScratch, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h216,
    Option.some.injEq, exists_eq_left', hc.pScr, ReduceArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, by rw [sx32 (by omega_arith), add_add],
    by rw [sx32 (by decide : 128 < 2 ^ 31), add_add], trivial⟩

abbrev reduceRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 144, 64⟩]
abbrev reduceWr (L : Lay) (out : Nat) : List Region := [⟨L.B + BitVec.ofNat 64 (16 + out), 32⟩, L.SCR]

theorem reduce_regs {t : State} (ha : ReduceArgs L out t) (rd wr : List Region) :
    ReduceArgs L out (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem reduce_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L out t) (ho : out + 32 ≤ 128) :
    scalarReduceLocal.pre (t.callEntry.withRegions (reduceRd L) (reduceWr L out)) := by
  obtain ⟨hdi, hsi, hdx⟩ := reduce_regs ha (reduceRd L) (reduceWr L out)
  simp only [scalarReduceLocal, rsp_ce, hdi, hsi, hdx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    by simpa using hL.stk_scr (d := 16 + out) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith)⟩

theorem reduce_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L out t) (ho : out + 32 ≤ 128)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = digest) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + out)) 32 = Spec.Ed25519.scalarReduce digest ∧
      Frame (reduceWr L out ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL scalarReduce_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (reduce_pre hL hc ha ho) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega_arith⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega_arith⟩
    · exact .inr (.inr (within_base _ (by omega_arith)))
  · obtain ⟨hdi, hsi, -⟩ := reduce_regs ha (reduceRd L) (reduceWr L out)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt _ _ 64) at hpost
    rw [hdi, hsi, State.withRegions_mem, hm] at hpost
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 144, 64⟩) (i := i) (by rw [hc.ret]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he, hh] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Base`. -/
section
/-! The nonce's base-point multiplication in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {bs : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdBase bs] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarBaseName)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base gpr_ce rsp_ce sub8 ea_stk add_add sx32 ce_byte)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block baseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega_arith) (by omega_arith)
  have ho := hc.inFr (d := 256) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [baseArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by cs_tac), trivial, trivial,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add], trivial⟩

theorem base_nosp : NoSp bs := PublicKey.base_nosp

theorem base_depth : bs.depth ≤ 1 := PublicKey.base_depth

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 80, 32⟩, L.TBL]
abbrev baseWr (L : Lay) : List Region := [⟨L.out, 32⟩, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem tbl_input : L.TBL ∈ L.inputs := by simp [Lay.inputs]

/-- The tables, as on entry, on entry to a call from the frame. -/
theorem ce_tbl (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {i : Nat} (hi : i < Impl.Ed25519.X86_64.combWordCount) :
    t.callEntry.mem.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = Impl.Ed25519.X86_64.combWords.getD i 0 := by
  rw [← hc.held i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : L.T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b = L.TBL.base + BitVec.ofNat 64 (8 * i + b) := by
    rw [Offset.add_add]
  rw [e, ce_byte t (R := L.TBL) (by rw [hc.ret]; exact hL.stk_input tbl_input (by omega_arith))
    (by show 8 * Impl.Ed25519.X86_64.combWordCount ≤ 2 ^ 64; decide) (by
      show 8 * i + b < 8 * Impl.Ed25519.X86_64.combWordCount
      simp only [Impl.Ed25519.X86_64.combWordCount] at hi ⊢; omega_arith)]
  exact hc.input_byte hL tbl_input (by show 8 * Impl.Ed25519.X86_64.combWordCount ≤ 2 ^ 64; decide) (by
      show 8 * i + b < 8 * Impl.Ed25519.X86_64.combWordCount
      simp only [Impl.Ed25519.X86_64.combWordCount] at hi ⊢; omega_arith)

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  have hsy : (t.callEntry.withRegions (baseRd L) (baseWr L)).syms Impl.Ed25519.X86_64.combSym = L.T :=
    hc.sym
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, Proof.Ed25519.X86_64.CombHeld, g1, g2, g3, rsp_ce,
    hc.rsp, sub8, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hsy]
  refine ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (within_base L.out (by decide : 32 ≤ 64)).sub,
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega_arith) (by omega_arith), hL.nc,
    fun i hi => ce_tbl hL hc hi, hL.nt, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact (hL.os _ tbl_input).symm.sub_right (within_base L.out (by decide : 32 ≤ 64)).sub
  · exact hL.sc _ tbl_input
  · exact (hL.stk_input tbl_input (d := 8) (n := 8) (by omega_arith)).symm

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, ⟨64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩⟩
  · exact ⟨L.TBL, List.mem_append_left _ tbl_input, within_base _ (by omega_arith)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega_arith)⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inl (within_base _ (by omega_arith)))
  · exact .inr (.inr (within_base _ (by omega_arith)))

/-- The callee's buffers are apart from the 8 bytes below its `rsp`, the stack's lowest. -/
theorem base_clear (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    Clear (hole ((t.callEntry.withRegions (baseRd L) (baseWr L)).gpr .rsp))
      (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  rw [rsp_ce, hc.rsp, sub8, Proof.Ed25519.X86_64.hole_add8]
  have k8 : Region.Sub ⟨L.B, 8⟩ L.STK := Region.sub_prefix (by omega_arith)
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact ((hL.ks _ (by simp [Lay.inputs])).sub_left k8).symm
  · exact ((hL.ko.sub_left k8).sub_right (within_base L.out (by decide : 32 ≤ 64)).sub).symm
  · exact (hL.kc.sub_left k8).symm

theorem base_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {scalar : List Byte}
    (hs : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = scalar) :
    WP isa (.call (scalarBaseName fs) bs) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.scalarBase scalar ∧ Frame (baseWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL (VG.Proof.Ed25519.X86_64.EdBase.ok (bs := bs)) base_nosp base_depth hc
    ⟨base_pre hL hc ha, base_clear hL hc⟩ base_sub base_wsub fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ =>
      ⟨hc', ?_, hf⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Contract.clear, Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 80) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 80, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by show (32 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, hs]

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Hashes`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.HashSteps`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.HashFrame`. -/
section
/-! Memory preserved across a complete signing hash. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (Within within_base within_off)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

abbrev hashWr (L : Lay) : List Region := [L.SCR, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.B, 16⟩]
abbrev HashFrame (L : Lay) (m m' : Mem) := Frame (hashWr L) m m'

theorem init_frame {m m' : Mem} (hf : Frame (initWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem upd_frame {m m' : Mem} (hf : Frame (updWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem fin_frame {m m' : Mem} (hf : Frame (finWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [finWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

structure Stable (L : Lay) (r : Region) : Prop extends Input L r where
  digest : r.Disjoint ⟨L.B + BitVec.ofNat 64 144, 64⟩

theorem Stable.bytes {r : Region} (hi : Stable L r) {m m' : Mem} (hf : HashFrame L m m')
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => Frame.bytes hf ?_ hn (List.mem_range.mp h)
  intro R hR
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact hi.scratch
  · exact hi.digest
  · exact hi.below.symm

theorem stable_input (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : Stable L r := by
  refine ⟨⟨⟨r, List.mem_append_left _ hr, within_base _ (by omega_arith)⟩, hL.sc r hr,
    by simpa using hL.stk_input hr (d := 0) (n := 16) (by omega_arith)⟩,
    (hL.stk_input hr (d := 144) (n := 64) (by omega_arith)).symm⟩

theorem stable_out (hL : L.Ok) : Stable L ⟨L.out, 32⟩ := by
  have hs : Within (⟨L.out, 32⟩ : Region) L.OUT := within_base _ (by decide)
  exact ⟨⟨⟨L.OUT, by simp, hs⟩, hL.oc.sub_left hs.sub,
    (hL.ko.sub_left ((within_base _ (by decide : 16 ≤ 264)).sub)).sub_right hs.sub⟩,
    ((hL.ko.sub_left (Offset.sub_base L.B (d := 144) (n := 64) (by decide))).sub_right hs.sub).symm⟩

theorem stable_prefix (hL : L.Ok) : Stable L ⟨L.B + BitVec.ofNat 64 48, 32⟩ := by
  refine ⟨⟨⟨L.FR, by simp, 32, by rw [PublicKey.add_add], by show 32 + 32 ≤ 248; decide⟩,
    ?_, ?_⟩, ?_⟩
  · simpa using hL.stk_scr (d := 48) (n := 32) (e := 0) (k := 8192) (by omega_arith) (by omega_arith)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Hash calls with explicit preservation of the signer's other buffers. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa init t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (initArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (init_call hL hu ha) fun w ⟨hw, hr, hf⟩ => ⟨hw, hr, hm ▸ init_frame hf⟩

theorem update_step (v : Compress) (hL : L.Ok) {t : State} (_hc : Ctx L g mx m₀ t)
    {prev : List Byte} {p : Addr} {n : BitVec 64} {args : List Instr}
    (hi : Input L ⟨p, n.toNat⟩)
    (ha : WP isa (.block args) t fun u => Ctx L g mx m₀ u ∧ u.mem = t.mem ∧
      UpdArgs L (BitVec.ofNat 64 prev.length) p n u)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (update v.callee v.suffix args) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧ HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono ha fun u ⟨hu, hm, hau⟩ => ?_)
  exact WP.mono (upd_call v hL hu hau hi rfl (hm ▸ hr)) fun w ⟨hw, hrw, hf⟩ =>
    ⟨hw, hm ▸ hrw, hm ▸ upd_frame hf⟩

theorem finalize_step (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {message : List Byte} (prefixLen : Nat) (hp : prefixLen < 2 ^ 31) (withMessage : Bool)
    (hmess : message.length < 2 ^ 64)
    (hlen : (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen) =
      BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (finalize v.callee v.suffix prefixLen withMessage) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 = Spec.Sha512.sha512 message ∧
      HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc prefixLen hp withMessage) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (fin_call v hL hu ha hmess hlen (hm ▸ hr)) fun w ⟨hw, hd, hf⟩ =>
    ⟨hw, hd, hm ▸ fin_frame hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! The signer's two hashes, using any verified SHA-512 backend. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem hashNonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 32 + L.len.toNat < 2 ^ 64) :
    WP isa (hashNonce v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 ++
          Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧ HashFrame L t.mem t'.mem := by
  have hi := stable_prefix hL
  have hm := stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (update_step v hL hc₁ (prev := []) (n := 32) hi.toInput (prefixArgs_ok hc₁) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32 = Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 at he
  rw [he] at hr₂
  have ha := messageArgs_ok hc₂ 32 (by decide)
  rw [← PublicKey.bytesAt_length t.mem (L.B + BitVec.ofNat 64 48) 32] at ha
  refine WP.seq (WP.mono (update_step v hL hc₂ (n := L.len) hm.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heM := hm.bytes (hf₁.trans hf₂) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₃
  refine WP.mono (finalize_step v hL hc₃ 32 (by decide) true ?_ ?_ hr₃)
    fun t₄ ⟨hc₄, hd₄, hf₄⟩ => ⟨hc₄, hd₄, hf₁.trans (hf₂.trans (hf₃.trans hf₄))⟩
  · simpa only [List.length_append, PublicKey.bytesAt_length] using hlen
  · simp only [List.length_append, PublicKey.bytesAt_length, ite_true,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]


theorem hashChallenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (hashChallenge v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
          Spec.Ed25519.bytesAt t.mem L.pk 32 ++ Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧
      HashFrame L t.mem t'.mem := by
  have hi := stable_out hL
  have hk := stable_input hL (r := L.PK) (by simp [Lay.inputs])
  have hm := stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (update_step v hL hc₁ (prev := []) (n := 32) hi.toInput
    (inputArgs_ok hc₁ fOut 0 (by decide) (by decide) L.out hc₁.pOut) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem L.out 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 at he
  rw [he] at hr₂
  have ha := inputArgs_ok hc₂ fPublicKey 32 (by decide) (by decide) L.pk hc₂.pPk
  rw [← PublicKey.bytesAt_length t.mem L.out 32] at ha
  refine WP.seq (WP.mono (update_step v hL hc₂ (n := 32) hk.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heK := hk.bytes (hf₁.trans hf₂) (by decide : 32 ≤ 2 ^ 64)
  change Spec.Ed25519.bytesAt t₂.mem L.pk 32 = Spec.Ed25519.bytesAt t.mem L.pk 32 at heK
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₃.mem L.scr
    (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t₂.mem L.pk 32) at hr₃
  rw [heK] at hr₃
  have haM := messageArgs_ok hc₃ 64 (by decide)
  have hn : (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t.mem L.pk 32).length = 64 := by
    simp only [List.length_append, PublicKey.bytesAt_length]
  have haM' : WP isa (.block (messageArgs 64)) t₃ fun u => Ctx L g mx m₀ u ∧ u.mem = t₃.mem ∧
      UpdArgs L (BitVec.ofNat 64 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
        Spec.Ed25519.bytesAt t.mem L.pk 32).length) L.msg L.len u := by
    rw [hn]; exact haM
  refine WP.seq (WP.mono (update_step v hL hc₃ (n := L.len) hm.toInput haM' hr₃)
    fun t₄ ⟨hc₄, hr₄, hf₄⟩ => ?_)
  have heM := hm.bytes (hf₁.trans (hf₂.trans hf₃)) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₄
  refine WP.mono (finalize_step v hL hc₄ 64 (by decide) true ?_ ?_ hr₄)
    fun t₅ ⟨hc₅, hd₅, hf₅⟩ => ⟨hc₅, hd₅, hf₁.trans (hf₂.trans (hf₃.trans (hf₄.trans hf₅)))⟩
  · simpa only [List.length_append, PublicKey.bytesAt_length] using hlen
  · simp only [List.length_append, PublicKey.bytesAt_length, ite_true,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
    rfl

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Byte-level consequences of each call's exact memory frame. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (within_base)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem Ctx.input_bytes (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {r : Region}
    (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  apply List.map_congr_left
  intro i hi
  exact hc.input_byte hL hr hn (List.mem_range.mp hi)

theorem single_stk_bytes {m m' : Mem} {d n e k : Nat}
    (hf : Frame [⟨L.B + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 264) (he : e + k ≤ 264) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  exact frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ hsep (by omega_arith) (by omega_arith)) (by change n ≤ 2 ^ 64; omega_arith)

theorem hash_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : HashFrame L m m') {d n : Nat}
    (hd : 16 ≤ d) (hn : d + n ≤ 144) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega_arith)
  intro r hr
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

theorem reduce_stk_bytes (hL : L.Ok) {m m' : Mem} {out d n : Nat}
    (hf : Frame (reduceWr L out ++ [⟨L.B, 16⟩]) m m')
    (hd : 16 ≤ d) (hn : d + n ≤ 264) (ho : out + 32 ≤ 128)
    (hsep : d + n ≤ 16 + out ∨ 16 + out + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega_arith)
  intro r hr
  simp only [reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ hsep (by omega_arith) (by omega_arith)
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

theorem base_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (baseWr L ++ [⟨L.B, 16⟩]) m m')
    {d n : Nat} (hd : 16 ≤ d) (hn : d + n ≤ 264) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega_arith)
  intro r hr
  simp only [baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.ko.sub_left (Offset.sub_base _ hn)).sub_right (within_base _ (by decide : 32 ≤ 64)).sub
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

theorem reduce_out_bytes (hL : L.Ok) {m m' : Mem} {out : Nat}
    (hf : Frame (reduceWr L out ++ [⟨L.B, 16⟩]) m m') (ho : out + 32 ≤ 128) :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  have hs := (within_base L.out (by decide : 32 ≤ 64)).sub
  refine frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((hL.ko.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hs).symm
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right hs).symm

theorem mul_out_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (mulWr L ++ [⟨L.B, 16⟩]) m m') :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  refine frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (within_base _ (by decide : 32 ≤ 64)).sub
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right
      (within_base _ (by decide : 32 ≤ 64)).sub).symm

end VG.Proof.Ed25519.X86_64.SignCached
