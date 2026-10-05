import VerifiedGarbage.Impl.Ed25519.X86_64.SignCached
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Layout`. -/
section

/-! The frame and memory invariant of complete Ed25519 signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within within_base within_off)

structure Lay where
  out : Addr
  seed : Addr
  pk : Addr
  msg : Addr
  len : BitVec 64
  scr : Addr
  B : Addr

namespace Lay
variable (L : VG.Proof.Ed25519.X86_64.SignCached.Lay)
abbrev OUT : Region := ⟨L.out, 64⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev PK : Region := ⟨L.pk, 32⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev STK : Region := ⟨L.B, 264⟩
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 248⟩
abbrev DATA : Region := ⟨L.B + BitVec.ofNat 64 16, 192⟩
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 264, 8⟩
def inputs : List Region := [L.SEED, L.PK, L.MSG]
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
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
end Lay

namespace Lay.Ok
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay}
theorem stk_scr (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 264) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)
theorem stk_input (h : L.Ok) {r : Region} (hr : r ∈ L.inputs) {d n : Nat} (hd : d + n ≤ 264) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  (h.ks r hr).sub_left (Offset.sub_base _ hd)
theorem input_scr (h : L.Ok) {r : Region} (hr : r ∈ L.inputs) {e k : Nat} (he : e + k ≤ 8192) :
    Region.Disjoint r ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.sc r hr).sub_right (Offset.sub_base _ he)
end Lay.Ok

structure Ctx (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
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

namespace Ctx
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
theorem regs (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pPk,
    by rw [hm]; exact hc.pSeed, by rw [hm]; exact hc.pOut, by rw [hm]; exact hc.frame⟩
theorem ret (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [PublicKey.sub8']
theorem inFr (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
theorem inFrW (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 264) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
theorem ea_fr (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (d : Nat) :
    t.ea (Impl.Ed25519.X86_64.stk d) = L.B + BitVec.ofNat 64 (16 + d) := by
  rw [PublicKey.ea_stk, hc.rsp, PublicKey.add_add]
theorem input_byte (hL : L.Ok) (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {r : Region} (hr : r ∈ L.inputs)
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
theorem call_ok {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
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
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
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
          (by omega) (by omega) (by omega)).sub_right h.sub
      · exact (hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
      · exact (hL.kc.sub_left (Offset.sub_base _ (by omega))).sub_right h.sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, 216 ≤ d → d + 8 ≤ 264 →
      s'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf'.readW (Region.contains_self _ _) (hdisj d h₁ h₂) (by decide)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 216 (by omega) (by omega)).trans hc.pScr,
    (keep 224 (by omega) (by omega)).trans hc.pLen, (keep 232 (by omega) (by omega)).trans hc.pMsg,
    (keep 240 (by omega) (by omega)).trans hc.pPk, (keep 248 (by omega) (by omega)).trans hc.pSeed,
    (keep 256 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hwsub r hr with h | h | h
      · exact ⟨L.STK, by simp, fun a ha => Offset.sub_base L.B (by decide : 16 + 192 ≤ 264) a (h.sub a ha)⟩
      · exact ⟨L.OUT, by simp, h.sub⟩
      · exact ⟨L.SCR, by simp, h.sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 16) (k := 264) (by omega)
      simpa using this

end VG.Proof.Ed25519.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Args`. -/
section

/-! Short symbolic executions for the complete signer's call arguments. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk shaScratch)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add sx32 zx32 ne_cs)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def InitArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (t : State) : Prop := t.gpr .rdi = L.scr

theorem initArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block initArgs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.SignCached.InitArgs L t' := by
  have hin := hc.inFr (d := 216) (by omega) (by omega)
  refine WP.of_runBlock ⟨t.setReg .rdi L.scr, ?_, ?_⟩
  · simp only [initArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, hc.ea_fr, hin, ite_true, Option.map_some, hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide)), rfl,
    RegUpd.gpr_setReg_self _ _ _⟩

def UpdArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (count : BitVec 64) (p : Addr) (n : BitVec 64) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = count ∧ t.gpr .rdx = p ∧ t.gpr .rcx = n ∧
    t.gpr .r8 = L.scr + BitVec.ofNat 64 192

theorem inputArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (source count : Nat)
    (hs : source + 8 ≤ 248) (hcount : count < 2 ^ 32) (p : Addr)
    (hp : t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p) :
    WP isa (.block (inputArgs source count)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 count) p 32 t' := by
  have h216 := hc.inFr (d := 216) (by omega) (by omega)
  have hsrc := hc.inFr (d := 16 + source) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [inputArgs, scrPtr, shaScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h216, hsrc, Option.some.injEq, exists_eq_left', hc.pScr, hp, VG.Proof.Ed25519.X86_64.SignCached.UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 hcount,
    trivial, rfl, by rw [sx32 (by omega)]⟩

theorem messageArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (count : Nat)
    (hcount : count < 2 ^ 32) :
    WP isa (.block (messageArgs count)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 count) L.msg L.len t' := by
  have h216 := hc.inFr (d := 216) (by omega) (by omega)
  have h224 := hc.inFr (d := 224) (by omega) (by omega)
  have h232 := hc.inFr (d := 232) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [messageArgs, scrPtr, shaScratch, fScratch, fMessage, fLength,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, readSrc32, State.load64, State.setReg32, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h216, h224, h232,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pMsg, hc.pLen, VG.Proof.Ed25519.X86_64.SignCached.UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 hcount,
    trivial, trivial, by rw [sx32 (by omega)]⟩


theorem prefixArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block prefixArgs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L 0 (L.B + BitVec.ofNat 64 48) 32 t' := by
  have hin := hc.inFr (d := 216) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixArgs, framePtr, scrPtr, shaScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hin, Option.some.injEq, exists_eq_left', hc.pScr, VG.Proof.Ed25519.X86_64.SignCached.UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl,
    by rw [sx32 (by decide : 32 < 2 ^ 31), add_add],
    rfl, by rw [sx32 (by omega)]⟩

def FinArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (count : BitVec 64) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = count ∧ t.gpr .rdx = L.B + BitVec.ofNat 64 144 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 192

theorem finalizeArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (prefixLen : Nat)
    (hp : prefixLen < 2 ^ 31) (withMessage : Bool) :
    WP isa (.block (finalizeArgs prefixLen withMessage)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.SignCached.FinArgs L
        (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen) t' := by
  have hs := hc.inFr (d := 216) (by omega) (by omega)
  have hl := hc.inFr (d := 224) (by omega) (by omega)
  cases withMessage <;> apply WP.of_runBlock <;>
    simp only [finalizeArgs, framePtr, scrPtr, shaScratch, fScratch, fLength, Bool.false_eq_true,
      ite_false, ite_true, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, readSrc32, State.load64, State.setReg32, ea_stk,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
      Nat.reduceAdd, hs, hl, Option.some.injEq, exists_eq_left', hc.pScr, hc.pLen, VG.Proof.Ed25519.X86_64.SignCached.FinArgs]
  · exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 (by omega),
      by rw [sx32 (by decide : 128 < 2 ^ 31), add_add],
      by rw [sx32 (by omega)]⟩
  · exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, by rw [sx32 hp],
      by rw [sx32 (by decide : 128 < 2 ^ 31), add_add],
      by rw [sx32 (by omega)]⟩

end VG.Proof.Ed25519.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Preserve`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Prune`. -/
section
/-! Pruning and saving the expanded signing scalar. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (pkPruneStores stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add prune_words decode_words take_bytesAt)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Frame stores cannot overwrite the saved arguments. -/
theorem Ctx.store {t t' : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {d n : Nat}
    (_hd : 16 ≤ d) (hn : d + n ≤ 208)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 d, n⟩] t.mem t'.mem) : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' := by
  have keep : ∀ e, 216 ≤ e → e + 8 ≤ 264 →
      t'.mem.readW (L.B + BitVec.ofNat 64 e) 64 = t.mem.readW (L.B + BitVec.ofNat 64 e) 64 := by
    intro e h₁ h₂
    exact hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr h => (hg r hr).trans (hc.cs r hr h), by rw [hmx]; exact hc.mx,
    (keep 216 (by omega) (by omega)).trans hc.pScr,
    (keep 224 (by omega) (by omega)).trans hc.pLen,
    (keep 232 (by omega) (by omega)).trans hc.pMsg,
    (keep 240 (by omega) (by omega)).trans hc.pPk,
    (keep 248 (by omega) (by omega)).trans hc.pSeed,
    (keep 256 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf ?_)⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

abbrev dw (t : State) (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.B + BitVec.ofNat 64 (144 + 8 * k)) 64

theorem pruneRegs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block pruneRegs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (VG.Proof.Ed25519.X86_64.SignCached.dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 1 ∧
      t'.gpr .r10 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 2 ∧
      t'.gpr .r11 = ((VG.Proof.Ed25519.X86_64.SignCached.dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  have s0 := hc.inFr (d := 144) (by omega) (by omega)
  have s1 := hc.inFr (d := 152) (by omega) (by omega)
  have s2 := hc.inFr (d := 160) (by omega) (by omega)
  have s3 := hc.inFr (d := 168) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pruneRegs, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-8)) = BitVec.ofNat 64 (2 ^ 64 - 8)),
    trivial, trivial, trivial⟩

theorem stores_ok {u : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega) (by omega)
  have w1 := hc.inFrW (d := 24) (by omega) (by omega)
  have w2 := hc.inFrW (d := 32) (by omega) (by omega)
  have w3 := hc.inFrW (d := 40) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prune_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = h) :
    WP isa (.block (pruneRegs ++ pkPruneStores)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.pruneRegs_ok hc) fun u ⟨hcu, hmu, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.stores_ok hcu) fun u' ⟨hcu', hf, _, r0, r1, r2, r3⟩ => ?_
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- A hash input can be a caller buffer or a saved value in the frame. -/
structure Input (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (r : Region) : Prop where
  cover : ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  scratch : r.Disjoint L.SCR
  below : (⟨L.B, 16⟩ : Region).Disjoint r

theorem Input.scr {r : Region} (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L r) {d n : Nat} (h : d + n ≤ 8192) :
    r.Disjoint ⟨L.scr + BitVec.ofNat 64 d, n⟩ :=
  hi.scratch.sub_right (Offset.sub_base _ h)

theorem Input.stk {r : Region} (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L r) {d n : Nat} (h : d + n ≤ 16) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hi.below.sub_left (Offset.sub_base _ h)

theorem Ctx.ce_bytes {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {r : Region} (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L r) (hn : r.len ≤ 2 ^ 64) :
    Spec.Sha512.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt t.mem r.base r.len := by
  unfold Spec.Sha512.bytesAt Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => ?_
  exact ce_byte t (by rw [hc.ret]; exact hi.stk (by omega)) hn (List.mem_range.mp h)

theorem Ctx.ce_repr (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {iv : Spec.Sha512.HashValue}
    {m : List Byte} (hr : Spec.Sha512.Repr iv t.mem L.scr m) :
    Spec.Sha512.Repr iv t.callEntry.mem L.scr m :=
  Proof.Sha512.Stream.repr_congr (fun i hi => ce_byte t (R := ⟨L.scr, 192⟩)
    (by rw [hc.ret]; simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega))
    (by show (192 : Nat) ≤ 2 ^ 64; decide) hi) hr

abbrev initRd : List Region := []
abbrev initWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.scr, 192⟩]

theorem init_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.InitArgs L t) :
    (Proof.Sha512.initX86_64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L)) := by
  have hrdi := (gpr_ce t VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L) (r := .rdi) (by decide)).trans ha
  refine ⟨rfl, by rw [hrdi]; rfl, ?_⟩
  rw [rsp_ce, hrdi, hc.rsp, sub8]
  simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega)

theorem init_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.InitArgs L t) :
    WP isa (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) t
      fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ Frame (VG.Proof.Ed25519.X86_64.SignCached.initWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL (Proof.Sha512.X86_64.Stream.init_verified _).1 (nosp_init _) (by decide) hc
    (VG.Proof.Ed25519.X86_64.SignCached.init_pre hL hc ha) ?_ ?_ fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · rintro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.initRd, VG.Proof.Ed25519.X86_64.SignCached.initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · rintro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (.inr (within_base _ (by omega)))
  · have := hpost
    simp only [Proof.Sha512.initX86_64, (gpr_ce t VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L) (r := .rdi) (by decide)).trans ha] at this
    rwa [← hm]

abbrev updWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.scr, 192⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem upd_regs {t : State} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L count p n t) (rd wr : List Region) :
    VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L count p n (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem upd_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {count : BitVec 64} {p : Addr} {n : BitVec 64} (ha : VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L count p n t)
    (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p, n.toNat⟩) :
    Proof.Sha512.updateX86_64.pre (t.callEntry.withRegions [⟨p, n.toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L)) := by
  obtain ⟨hdi, -, hdx, hcx, h8⟩ := VG.Proof.Ed25519.X86_64.SignCached.upd_regs ha [⟨p, n.toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L)
  simp only [Proof.Sha512.updateX86_64, rsp_ce, hdi, hdx, hcx, h8, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hi.scr (d := 0) (n := 192) (by omega), hi.scr (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    by simpa using hi.stk (d := 0) (n := 8) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem upd_call (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {prev : List Byte} {count : BitVec 64} {p : Addr} {n : BitVec 64}
    (ha : VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L count p n t) (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p, n.toNat⟩)
    (hcount : count = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
        Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧
        Frame (VG.Proof.Ed25519.X86_64.SignCached.updWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL (upd_verified v).1 (upd_nosp v) (upd_depth v) hc (VG.Proof.Ed25519.X86_64.SignCached.upd_pre hL hc ha hi) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inr (.inr (within_off _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := VG.Proof.Ed25519.X86_64.SignCached.upd_regs ha [⟨p, n.toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L)
    have h := hpost Spec.Sha512.H0_512 prev
      (by rw [State.withRegions_mem, hdi]; exact hc.ce_repr hL hr) (hsi.trans hcount)
    simp only [State.withRegions_mem, hdi, hdx, hcx, hm] at h
    rw [hc.ce_bytes hi (Nat.le_of_lt n.isLt)] at h
    exact h


abbrev finWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region :=
  [⟨L.scr, 192⟩, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.scr + BitVec.ofNat 64 192, 1376⟩]

theorem fin_regs {t : State} {count : BitVec 64} (ha : VG.Proof.Ed25519.X86_64.SignCached.FinArgs L count t) (rd wr : List Region) :
    VG.Proof.Ed25519.X86_64.SignCached.FinArgs L count (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem fin_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {count : BitVec 64} (ha : VG.Proof.Ed25519.X86_64.SignCached.FinArgs L count t) :
    Proof.Sha512.finalizeX86_64.pre (t.callEntry.withRegions [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L)) := by
  obtain ⟨hdi, -, hdx, hcx⟩ := VG.Proof.Ed25519.X86_64.SignCached.fin_regs ha [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L)
  simp only [Proof.Sha512.finalizeX86_64, rsp_ce, hdi, hdx, hcx, hc.rsp, sub8, sub88,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using (hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 192) (by omega) (by omega)).symm,
    Offset.base_disjoint _ (by omega) (by omega), hL.stk_scr (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    hL.stk_scr (d := 8) (n := 8) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 0) (k := 192) (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    by simpa using hL.stk_scr (d := 0) (n := 8) (e := 192) (k := 1376) (by omega) (by omega)⟩

theorem fin_call (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {count : BitVec 64} (ha : VG.Proof.Ed25519.X86_64.SignCached.FinArgs L count t)
    {message : List Byte} (hmess : message.length < 2 ^ 64)
    (hlen : count = BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (.call (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.finalize v.callee)) t
      fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 message ∧ Frame (VG.Proof.Ed25519.X86_64.SignCached.finWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL (fin_verified v).1 (fin_nosp v) (fin_depth v) hc (VG.Proof.Ed25519.X86_64.SignCached.fin_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inl ⟨128, by rw [PublicKey.add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, -⟩ := VG.Proof.Ed25519.X86_64.SignCached.fin_regs ha [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L)
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def MulArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out + BitVec.ofNat 64 32 ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rdx = L.B + BitVec.ofNat 64 112 ∧ t.gpr .rcx = L.B + BitVec.ofNat 64 16 ∧ t.gpr .r8 = L.scr

theorem mulArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block mulAddArgs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.SignCached.MulArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega) (by omega)
  have ho := hc.inFr (d := 256) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [mulAddArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, VG.Proof.Ed25519.X86_64.SignCached.MulArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, rfl,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 96 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 0 < 2 ^ 31), BitVec.add_zero], trivial⟩

abbrev mulRd (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region :=
  [⟨L.B + BitVec.ofNat 64 80, 32⟩, ⟨L.B + BitVec.ofNat 64 112, 32⟩, ⟨L.B + BitVec.ofNat 64 16, 32⟩]
abbrev mulWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.out + BitVec.ofNat 64 32, 32⟩, L.SCR]

theorem mul_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.SignCached.MulArgs L t) (rd wr : List Region) :
    VG.Proof.Ed25519.X86_64.SignCached.MulArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem mul_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.MulArgs L t) :
    scalarMulAddLocal.pre (t.callEntry.withRegions (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8⟩ := VG.Proof.Ed25519.X86_64.SignCached.mul_regs ha (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L)
  simp only [scalarMulAddLocal, rsp_ce, hdi, hsi, hdx, hcx, h8, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 112) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 16) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (Offset.sub_base L.out (d := 32) (n := 32) (by decide)),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc,
    hL.oc.sub_left (Offset.sub_base L.out (d := 32) (n := 32) (by decide))⟩

theorem mul_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.MulArgs L t) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.out + BitVec.ofNat 64 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) ∧
      Frame (VG.Proof.Ed25519.X86_64.SignCached.mulWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL scalarMulAdd_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (VG.Proof.Ed25519.X86_64.SignCached.mul_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.mulRd, VG.Proof.Ed25519.X86_64.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega)))
    · exact .inr (.inr (within_base _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := VG.Proof.Ed25519.X86_64.SignCached.mul_regs ha (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarMulAdd _ _ _ at hpost
    rw [hdi, hsi, hdx, hcx, State.withRegions_mem, hm] at hpost
    have he (d : Nat) (hd : 16 ≤ d) (hn : d + 32 ≤ 264) :
        Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 d) 32 =
          Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 d) 32 := by
      apply List.map_congr_left
      intro i hi
      exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 d, 32⟩) (i := i)
        (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem prefixRegs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block prefixRegs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 4 ∧ t'.gpr .r9 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 5 ∧
      t'.gpr .r10 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 6 ∧ t'.gpr .r11 = VG.Proof.Ed25519.X86_64.SignCached.dw t L 7 := by
  have h0 := hc.inFr (d := 176) (by omega) (by omega)
  have h1 := hc.inFr (d := 184) (by omega) (by omega)
  have h2 := hc.inFr (d := 192) (by omega) (by omega)
  have h3 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, Nat.reduceAdd,
    h0, h1, h2, h3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial⟩

theorem prefixStores_ok {u : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u) :
    WP isa (.block prefixStores) u fun u' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 56) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 64) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 72) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 48) (by omega) (by omega)
  have w1 := hc.inFrW (d := 56) (by omega) (by omega)
  have w2 := hc.inFrW (d := 64) (by omega) (by omega)
  have w3 := hc.inFrW (d := 72) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok (L.B + BitVec.ofNat 64 32) u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  simp only [add_add, Nat.reduceAdd] at hf h0 h1 h2 h3
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prefix_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block (prefixRegs ++ prefixStores)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 =
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64).drop 32 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.prefixRegs_ok hc) fun u ⟨hu, hm, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.prefixStores_ok hu) fun w ⟨hw, hf, _, h0, h1, h2, h3⟩ => ?_
  refine ⟨hw, hm ▸ hf, ?_⟩
  rw [Proof.Ed25519.signatureBytes_drop, add_add]
  rw [Proof.Ed25519.bytesAt_encodeLE w.mem, Proof.Ed25519.bytesAt_encodeLE t.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  simp only [decode_words, add_add, Nat.reduceAdd, h0, h1, h2, h3, h8, h9, h10, h11, VG.Proof.Ed25519.X86_64.SignCached.dw,
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem wipe_word {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (i : Nat) (hi : i < 24) :
    WP isa (.block [.store (VG.Impl.Ed25519.X86_64.stk (8 * i)) .rax]) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  have hw := hc.inFrW (d := 16 + 8 * i) (by omega) (by omega)
  have hf : Frame [L.DATA] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * i)) (t.gpr .rax)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp,
    add_add, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf⟩

theorem wipe_words (is : List Nat) (hi : ∀ i ∈ is, i < 24) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block (is.map fun i => .store (VG.Impl.Ed25519.X86_64.stk (8 * i)) .rax)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  induction is generalizing t with
  | nil => exact WP.of_runBlock ⟨t, rfl, hc, Frame.refl _ _⟩
  | cons i is ih =>
    change WP isa (.block (([.store (VG.Impl.Ed25519.X86_64.stk (8 * i)) .rax] : List Instr) ++
      is.map (fun j => .store (VG.Impl.Ed25519.X86_64.stk (8 * j)) .rax))) t _
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.wipe_word hc i (hi i (by simp))) fun u ⟨hu, hf⟩ => ?_
    exact WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem i hj)) hu)
      fun w ⟨hw, hf'⟩ => ⟨hw, hf.trans hf'⟩

theorem wipe_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block wipe) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Frame [L.DATA] t.mem t'.mem := by
  rw [wipe, WP.block_append_iff]
  have hz : WP isa (.block [.alu32 .xor .rax (.reg .rax)]) t
      fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
      State.setReg32,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩
  refine WP.mono hz fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.wipe_words (List.range 24) (fun _ h => List.mem_range.mp h) hu)
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
variable {out : Nat} {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def ReduceArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (out : Nat) (t : State) : Prop :=
  t.gpr .rdi = L.B + BitVec.ofNat 64 (16 + out) ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 144 ∧
    t.gpr .rdx = L.scr

theorem reduceArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ho : out + 32 ≤ 128) :
    WP isa (.block (reduceArgs out)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out t' := by
  have h216 := hc.inFr (d := 216) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [reduceArgs, framePtr, fScratch, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h216,
    Option.some.injEq, exists_eq_left', hc.pScr, VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, by rw [sx32 (by omega), add_add],
    by rw [sx32 (by decide : 128 < 2 ^ 31), add_add], trivial⟩

abbrev reduceRd (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.B + BitVec.ofNat 64 144, 64⟩]
abbrev reduceWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (out : Nat) : List Region := [⟨L.B + BitVec.ofNat 64 (16 + out), 32⟩, L.SCR]

theorem reduce_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out t) (rd wr : List Region) :
    VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem reduce_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out t) (ho : out + 32 ≤ 128) :
    scalarReduceLocal.pre (t.callEntry.withRegions (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out)) := by
  obtain ⟨hdi, hsi, hdx⟩ := VG.Proof.Ed25519.X86_64.SignCached.reduce_regs ha (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out)
  simp only [scalarReduceLocal, rsp_ce, hdi, hsi, hdx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 16 + out) (n := 32) (e := 0) (k := 8192) (by omega) (by omega)⟩

theorem reduce_call (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out t) (ho : out + 32 ≤ 128)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = digest) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + out)) 32 = Spec.Ed25519.scalarReduce digest ∧
      Frame (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL scalarReduce_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (VG.Proof.Ed25519.X86_64.SignCached.reduce_pre hL hc ha ho) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceRd, VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega⟩
    · exact .inr (.inr (within_base _ (by omega)))
  · obtain ⟨hdi, hsi, -⟩ := VG.Proof.Ed25519.X86_64.SignCached.reduce_regs ha (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt _ _ 64) at hpost
    rw [hdi, hsi, State.withRegions_mem, hm] at hpost
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 144, 64⟩) (i := i) (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he, hh] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Base`. -/
section
/-! The nonce's base-point multiplication in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarBaseName scalarBase_precomputed)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base gpr_ce rsp_ce sub8 ea_stk add_add sx32 ce_byte)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def BaseArgs (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.block baseArgs) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega) (by omega)
  have ho := hc.inFr (d := 256) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [baseArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, VG.Proof.Ed25519.X86_64.SignCached.BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add], trivial⟩

theorem base_nosp : NoSp (scalarBase_precomputed fld) := PublicKey.base_nosp

theorem base_depth : (scalarBase_precomputed fld).depth ≤ 1 := PublicKey.base_depth

abbrev baseRd (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.B + BitVec.ofNat 64 80, 32⟩]
abbrev baseWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [⟨L.out, 32⟩, L.SCR]

theorem base_regs {t : State} (ha : VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := VG.Proof.Ed25519.X86_64.SignCached.base_regs ha (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L)
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, g3, rsp_ce, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (within_base L.out (by decide : 32 ≤ 64)).sub,
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc⟩

theorem base_sub : ∀ r ∈ VG.Proof.Ed25519.X86_64.SignCached.baseRd L ++ VG.Proof.Ed25519.X86_64.SignCached.baseWr L, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, ⟨64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ VG.Proof.Ed25519.X86_64.SignCached.baseWr L, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inl (within_base _ (by omega)))
  · exact .inr (.inr (within_base _ (by omega)))

theorem base_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (ha : VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L t) {scalar : List Byte}
    (hs : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = scalar) :
    WP isa (.call (scalarBaseName fs) (scalarBase_precomputed fld)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.scalarBase scalar ∧ Frame (VG.Proof.Ed25519.X86_64.SignCached.baseWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine VG.Proof.Ed25519.X86_64.SignCached.call_ok hL Proof.Ed25519.X86_64.scalarBase_precomputed_ok VG.Proof.Ed25519.X86_64.SignCached.base_nosp VG.Proof.Ed25519.X86_64.SignCached.base_depth hc
    (VG.Proof.Ed25519.X86_64.SignCached.base_pre hL hc ha) VG.Proof.Ed25519.X86_64.SignCached.base_sub VG.Proof.Ed25519.X86_64.SignCached.base_wsub fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  obtain ⟨g1, g2, -⟩ := VG.Proof.Ed25519.X86_64.SignCached.base_regs ha (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L)
  have h := hpost
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 80) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 80, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

abbrev hashWr (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) : List Region := [L.SCR, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.B, 16⟩]
abbrev HashFrame (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m m' : Mem) := Frame (VG.Proof.Ed25519.X86_64.SignCached.hashWr L) m m'

theorem init_frame {m m' : Mem} (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.initWr L ++ [⟨L.B, 16⟩]) m m') :
    VG.Proof.Ed25519.X86_64.SignCached.HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [VG.Proof.Ed25519.X86_64.SignCached.initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem upd_frame {m m' : Mem} (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.updWr L ++ [⟨L.B, 16⟩]) m m') :
    VG.Proof.Ed25519.X86_64.SignCached.HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [VG.Proof.Ed25519.X86_64.SignCached.updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem fin_frame {m m' : Mem} (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.finWr L ++ [⟨L.B, 16⟩]) m m') :
    VG.Proof.Ed25519.X86_64.SignCached.HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [VG.Proof.Ed25519.X86_64.SignCached.finWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

structure Stable (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (r : Region) : Prop extends VG.Proof.Ed25519.X86_64.SignCached.Input L r where
  digest : r.Disjoint ⟨L.B + BitVec.ofNat 64 144, 64⟩

theorem Stable.bytes {r : Region} (hi : VG.Proof.Ed25519.X86_64.SignCached.Stable L r) {m m' : Mem} (hf : VG.Proof.Ed25519.X86_64.SignCached.HashFrame L m m')
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => Frame.bytes hf ?_ hn (List.mem_range.mp h)
  intro R hR
  simp only [VG.Proof.Ed25519.X86_64.SignCached.hashWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact hi.scratch
  · exact hi.digest
  · exact hi.below.symm

theorem stable_input (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : VG.Proof.Ed25519.X86_64.SignCached.Stable L r := by
  refine ⟨⟨⟨r, List.mem_append_left _ hr, within_base _ (by omega)⟩, hL.sc r hr,
    by simpa using hL.stk_input hr (d := 0) (n := 16) (by omega)⟩,
    (hL.stk_input hr (d := 144) (n := 64) (by omega)).symm⟩

theorem stable_out (hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Stable L ⟨L.out, 32⟩ := by
  have hs : Within (⟨L.out, 32⟩ : Region) L.OUT := within_base _ (by decide)
  exact ⟨⟨⟨L.OUT, by simp, hs⟩, hL.oc.sub_left hs.sub,
    (hL.ko.sub_left ((within_base _ (by decide : 16 ≤ 264)).sub)).sub_right hs.sub⟩,
    ((hL.ko.sub_left (Offset.sub_base L.B (d := 144) (n := 64) (by decide))).sub_right hs.sub).symm⟩

theorem stable_prefix (hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Stable L ⟨L.B + BitVec.ofNat 64 48, 32⟩ := by
  refine ⟨⟨⟨L.FR, by simp, 32, by rw [PublicKey.add_add], by show 32 + 32 ≤ 248; decide⟩,
    ?_, ?_⟩, ?_⟩
  · simpa using hL.stk_scr (d := 48) (n := 32) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Hash calls with explicit preservation of the signer's other buffers. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem init_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa init t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.initArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.init_call hL hu ha) fun w ⟨hw, hr, hf⟩ => ⟨hw, hr, hm ▸ VG.Proof.Ed25519.X86_64.SignCached.init_frame hf⟩

theorem update_step (v : Compress) (hL : L.Ok) {t : State} (_hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {prev : List Byte} {p : Addr} {n : BitVec 64} {args : List Instr}
    (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p, n.toNat⟩)
    (ha : WP isa (.block args) t fun u => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u ∧ u.mem = t.mem ∧
      VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 prev.length) p n u)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (update v.callee v.suffix args) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧ VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono ha fun u ⟨hu, hm, hau⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.upd_call v hL hu hau hi rfl (hm ▸ hr)) fun w ⟨hw, hrw, hf⟩ =>
    ⟨hw, hm ▸ hrw, hm ▸ VG.Proof.Ed25519.X86_64.SignCached.upd_frame hf⟩

theorem finalize_step (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    {message : List Byte} (prefixLen : Nat) (hp : prefixLen < 2 ^ 31) (withMessage : Bool)
    (hmess : message.length < 2 ^ 64)
    (hlen : (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen) =
      BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (finalize v.callee v.suffix prefixLen withMessage) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 = Spec.Sha512.sha512 message ∧
      VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.finalizeArgs_ok hc prefixLen hp withMessage) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.fin_call v hL hu ha hmess hlen (hm ▸ hr)) fun w ⟨hw, hd, hf⟩ =>
    ⟨hw, hd, hm ▸ VG.Proof.Ed25519.X86_64.SignCached.fin_frame hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! The signer's three hashes, using any verified SHA-512 backend. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem hashSeed_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (hashSeed v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem L.seed 32) ∧ VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  have hi := VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (r := L.SEED) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₁ (prev := []) (n := 32) hi.toInput
    (VG.Proof.Ed25519.X86_64.SignCached.inputArgs_ok hc₁ fSeed 0 (by decide) (by decide) L.seed hc₁.pSeed) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem L.seed 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem L.seed 32 = Spec.Ed25519.bytesAt t.mem L.seed 32 at he
  rw [he] at hr₂
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.finalize_step v hL hc₂ 32 (by decide) false ?_ ?_ hr₂)
    fun t₃ ⟨hc₃, hd₃, hf₃⟩ => ⟨hc₃, hd₃, hf₁.trans (hf₂.trans hf₃)⟩
  · rw [PublicKey.bytesAt_length]; decide
  · rw [PublicKey.bytesAt_length]; rfl

theorem hashNonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    (hlen : 32 + L.len.toNat < 2 ^ 64) :
    WP isa (hashNonce v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 ++
          Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧ VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  have hi := VG.Proof.Ed25519.X86_64.SignCached.stable_prefix hL
  have hm := VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₁ (prev := []) (n := 32) hi.toInput (VG.Proof.Ed25519.X86_64.SignCached.prefixArgs_ok hc₁) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem (L.B + BitVec.ofNat 64 48) 32 = Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 at he
  rw [he] at hr₂
  have ha := VG.Proof.Ed25519.X86_64.SignCached.messageArgs_ok hc₂ 32 (by decide)
  rw [← PublicKey.bytesAt_length t.mem (L.B + BitVec.ofNat 64 48) 32] at ha
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₂ (n := L.len) hm.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heM := hm.bytes (hf₁.trans hf₂) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₃
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.finalize_step v hL hc₃ 32 (by decide) true ?_ ?_ hr₃)
    fun t₄ ⟨hc₄, hd₄, hf₄⟩ => ⟨hc₄, hd₄, hf₁.trans (hf₂.trans (hf₃.trans hf₄))⟩
  · simpa only [List.length_append, PublicKey.bytesAt_length] using hlen
  · simp only [List.length_append, PublicKey.bytesAt_length, ite_true,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]


theorem hashChallenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (hashChallenge v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
          Spec.Ed25519.bytesAt t.mem L.pk 32 ++ Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat) ∧
      VG.Proof.Ed25519.X86_64.SignCached.HashFrame L t.mem t'.mem := by
  have hi := VG.Proof.Ed25519.X86_64.SignCached.stable_out hL
  have hk := VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (r := L.PK) (by simp [Lay.inputs])
  have hm := VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (r := L.MSG) (by simp [Lay.inputs])
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.init_step hL hc) fun t₁ ⟨hc₁, hr₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₁ (prev := []) (n := 32) hi.toInput
    (VG.Proof.Ed25519.X86_64.SignCached.inputArgs_ok hc₁ fOut 0 (by decide) (by decide) L.out hc₁.pOut) hr₁)
    fun t₂ ⟨hc₂, hr₂, hf₂⟩ => ?_)
  have he := hi.bytes hf₁ (by decide : 32 ≤ 2 ^ 64)
  simp only [List.nil_append] at hr₂
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₂.mem L.scr (Spec.Ed25519.bytesAt t₁.mem L.out 32) at hr₂
  change Spec.Ed25519.bytesAt t₁.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 at he
  rw [he] at hr₂
  have ha := VG.Proof.Ed25519.X86_64.SignCached.inputArgs_ok hc₂ fPublicKey 32 (by decide) (by decide) L.pk hc₂.pPk
  rw [← PublicKey.bytesAt_length t.mem L.out 32] at ha
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₂ (n := 32) hk.toInput ha hr₂)
    fun t₃ ⟨hc₃, hr₃, hf₃⟩ => ?_)
  have heK := hk.bytes (hf₁.trans hf₂) (by decide : 32 ≤ 2 ^ 64)
  change Spec.Ed25519.bytesAt t₂.mem L.pk 32 = Spec.Ed25519.bytesAt t.mem L.pk 32 at heK
  change Spec.Sha512.Repr Spec.Sha512.H0_512 t₃.mem L.scr
    (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t₂.mem L.pk 32) at hr₃
  rw [heK] at hr₃
  have haM := VG.Proof.Ed25519.X86_64.SignCached.messageArgs_ok hc₃ 64 (by decide)
  have hn : (Spec.Ed25519.bytesAt t.mem L.out 32 ++ Spec.Ed25519.bytesAt t.mem L.pk 32).length = 64 := by
    simp only [List.length_append, PublicKey.bytesAt_length]
  have haM' : WP isa (.block (messageArgs 64)) t₃ fun u => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ u ∧ u.mem = t₃.mem ∧
      VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 (Spec.Ed25519.bytesAt t.mem L.out 32 ++
        Spec.Ed25519.bytesAt t.mem L.pk 32).length) L.msg L.len u := by
    rw [hn]; exact haM
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.update_step v hL hc₃ (n := L.len) hm.toInput haM' hr₃)
    fun t₄ ⟨hc₄, hr₄, hf₄⟩ => ?_)
  have heM := hm.bytes (hf₁.trans (hf₂.trans hf₃)) (Nat.le_of_lt L.len.isLt)
  rw [heM] at hr₄
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.finalize_step v hL hc₄ 64 (by decide) true ?_ ?_ hr₄)
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
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem Ctx.input_bytes (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {r : Region}
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
  exact VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ hsep (by omega) (by omega)) (by change n ≤ 2 ^ 64; omega)

theorem hash_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : VG.Proof.Ed25519.X86_64.SignCached.HashFrame L m m') {d n : Nat}
    (hd : 16 ≤ d) (hn : d + n ≤ 144) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [VG.Proof.Ed25519.X86_64.SignCached.hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem reduce_stk_bytes (hL : L.Ok) {m m' : Mem} {out d n : Nat}
    (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out ++ [⟨L.B, 16⟩]) m m')
    (hd : 16 ≤ d) (hn : d + n ≤ 264) (ho : out + 32 ≤ 128)
    (hsep : d + n ≤ 16 + out ∨ 16 + out + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ hsep (by omega) (by omega)
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem base_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.baseWr L ++ [⟨L.B, 16⟩]) m m')
    {d n : Nat} (hd : 16 ≤ d) (hn : d + n ≤ 264) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [VG.Proof.Ed25519.X86_64.SignCached.baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.ko.sub_left (Offset.sub_base _ hn)).sub_right (within_base _ (by decide : 32 ≤ 64)).sub
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem reduce_out_bytes (hL : L.Ok) {m m' : Mem} {out : Nat}
    (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out ++ [⟨L.B, 16⟩]) m m') (ho : out + 32 ≤ 128) :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  have hs := (within_base L.out (by decide : 32 ≤ 64)).sub
  refine VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right hs).symm
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right hs).symm

theorem mul_out_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (VG.Proof.Ed25519.X86_64.SignCached.mulWr L ++ [⟨L.B, 16⟩]) m m') :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  refine VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [VG.Proof.Ed25519.X86_64.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (within_base _ (by decide : 32 ≤ 64)).sub
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right
      (within_base _ (by decide : 32 ≤ 64)).sub).symm

end VG.Proof.Ed25519.X86_64.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Verified`. -/
section

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Finish`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Nonce`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Secret`. -/
section
/-! Expand the seed and save both the pruned scalar and the nonce prefix. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem saveSecret_ok {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {expanded : List Byte}
    (he : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = expanded) :
    WP isa (.block saveSecret) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 = expanded.drop 32 := by
  rw [saveSecret, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.prune_ok hc he) fun u ⟨hu, hf, hs⟩ => ?_
  have hd : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 144) 64 = expanded :=
    (VG.Proof.Ed25519.X86_64.SignCached.single_stk_bytes hf (by decide) (by decide) (by decide)).trans he
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.prefix_ok hu) fun w ⟨hw, hfw, hp⟩ => ⟨hw, ?_, ?_⟩
  · rw [VG.Proof.Ed25519.X86_64.SignCached.single_stk_bytes hfw (by decide : 16 + 32 ≤ 48 ∨ 48 + 32 ≤ 16) (by decide) (by decide)]
    rw [Proof.Ed25519.bytesAt_encodeLE u.mem, hs]
  · rw [hp, hd]

def expanded (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m L.seed 32)
def scalar (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (VG.Proof.Ed25519.X86_64.SignCached.expanded L m))
def nonce (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((VG.Proof.Ed25519.X86_64.SignCached.expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure SecretReady (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = VG.Proof.Ed25519.X86_64.SignCached.scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 = (VG.Proof.Ed25519.X86_64.SignCached.expanded L m).drop 32

theorem secret_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (.seq (hashSeed v.callee v.suffix) (.block saveSecret)) t fun t' =>
      VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Proof.Ed25519.X86_64.SignCached.SecretReady L m₀ t' := by
  have he : Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 :=
    hc.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.hashSeed_ok v hL hc) fun u ⟨hu, hd, _⟩ => ?_)
  rw [he] at hd
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.saveSecret_ok hu hd) fun w ⟨hw, hs, hp⟩ => ⟨hw, hs, hp⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Calls`. -/
section
/-! Argument blocks composed with the signer's scalar and group calls. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem reduce_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (out : Nat)
    (ho : out + 32 ≤ 128) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = digest) :
    WP isa (reduce out) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + out)) 32 = Spec.Ed25519.scalarReduce digest ∧
      Frame (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.reduceArgs_ok hc ho) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.reduce_call hL hu ha ho (hm ▸ hh)) fun w ⟨hw, h, hf⟩ => ⟨hw, h, hm ▸ hf⟩

theorem base_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {scalar : List Byte}
    (hs : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = scalar) :
    WP isa (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 = Spec.Ed25519.scalarBase scalar ∧
      Frame (VG.Proof.Ed25519.X86_64.SignCached.baseWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.baseArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.base_ok hL hu ha (hm ▸ hs)) fun w ⟨hw, h, hf⟩ => ⟨hw, h, hm ▸ hf⟩

theorem mul_step (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.out + BitVec.ofNat 64 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) ∧
      Frame (VG.Proof.Ed25519.X86_64.SignCached.mulWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.mulArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.X86_64.SignCached.mul_call hL hu ha) fun w ⟨hw, h, hf⟩ => ⟨hw, hm ▸ h, hm ▸ hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Hash and reduce the deterministic nonce, then encode its base-point multiple. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

structure NonceReady (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = VG.Proof.Ed25519.X86_64.SignCached.scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = VG.Proof.Ed25519.X86_64.SignCached.nonce L m
  point : Spec.Ed25519.bytesAt t.mem L.out 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

def nonceCode (fld : VG.Impl.Ed25519.X86_64.Arith) (fs : String) (v : Compress) : Prog isa :=
  .seq (hashNonce v.callee v.suffix) (.seq (reduce 64)
    (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)))

theorem nonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    (hs : VG.Proof.Ed25519.X86_64.SignCached.SecretReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (VG.Proof.Ed25519.X86_64.SignCached.nonceCode fld fs v) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Proof.Ed25519.X86_64.SignCached.NonceReady L m₀ t' := by
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.hashNonce_ok v hL hc (by omega)) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.prefixBytes, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = VG.Proof.Ed25519.X86_64.SignCached.scalar L m₀ :=
    (VG.Proof.Ed25519.X86_64.SignCached.hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.reduce_step hL hu 64 (by decide) hd) fun w ⟨hw, hn, hfw⟩ => ?_)
  change Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 80) 32 = VG.Proof.Ed25519.X86_64.SignCached.nonce L m₀ at hn
  have hsw : Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 16) 32 = VG.Proof.Ed25519.X86_64.SignCached.scalar L m₀ :=
    (VG.Proof.Ed25519.X86_64.SignCached.reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.base_step hL hw hn) fun z ⟨hz, hp, hfz⟩ => ⟨hz, ?_, ?_, hp⟩
  · exact (VG.Proof.Ed25519.X86_64.SignCached.base_stk_bytes hL hfz (d := 16) (n := 32) (by decide) (by decide)).trans hsw
  · exact (VG.Proof.Ed25519.X86_64.SignCached.base_stk_bytes hL hfz (d := 80) (n := 32) (by decide) (by decide)).trans hn

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Bind the nonce point, cached public key and message into the signing challenge. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def challenge (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Spec.Ed25519.scalarBase (VG.Proof.Ed25519.X86_64.SignCached.nonce L m) ++
    Spec.Ed25519.bytesAt m L.pk 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure ChallengeReady (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (m : Mem) (t : State) : Prop extends VG.Proof.Ed25519.X86_64.SignCached.NonceReady L m t where
  challenge : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32 = VG.Proof.Ed25519.X86_64.SignCached.challenge L m

def challengeCode (v : Compress) : Prog isa := .seq (hashChallenge v.callee v.suffix) (reduce 96)

theorem challenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    (hs : VG.Proof.Ed25519.X86_64.SignCached.NonceReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (VG.Proof.Ed25519.X86_64.SignCached.challengeCode v) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ VG.Proof.Ed25519.X86_64.SignCached.ChallengeReady L m₀ t' := by
  have hp : Spec.Ed25519.bytesAt t.mem L.pk 32 = Spec.Ed25519.bytesAt m₀ L.pk 32 :=
    hc.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.hashChallenge_ok v hL hc hlen) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.point, hp, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = VG.Proof.Ed25519.X86_64.SignCached.scalar L m₀ :=
    (VG.Proof.Ed25519.X86_64.SignCached.hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  have hnu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 80) 32 = VG.Proof.Ed25519.X86_64.SignCached.nonce L m₀ :=
    (VG.Proof.Ed25519.X86_64.SignCached.hash_stk_bytes hL hf (d := 80) (n := 32) (by decide) (by decide)).trans hs.nonce
  have hpu : Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.scalarBase (VG.Proof.Ed25519.X86_64.SignCached.nonce L m₀) :=
    ((VG.Proof.Ed25519.X86_64.SignCached.stable_out hL).bytes hf (by decide : 32 ≤ 2 ^ 64)).trans hs.point
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.reduce_step hL hu 96 (by decide) hd) fun w ⟨hw, hk, hfw⟩ =>
    ⟨hw, ⟨?_, ?_, ?_⟩, hk⟩
  · exact (VG.Proof.Ed25519.X86_64.SignCached.reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  · exact (VG.Proof.Ed25519.X86_64.SignCached.reduce_stk_bytes hL hfw (d := 80) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hnu
  · exact (VG.Proof.Ed25519.X86_64.SignCached.reduce_out_bytes hL hfw (by decide)).trans hpu

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete the signature and clear the secret frame values. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def finishCode : Prog isa := .seq (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (.block wipe)

theorem finish_ok (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) (hs : VG.Proof.Ed25519.X86_64.SignCached.ChallengeReady L m₀ t)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa VG.Proof.Ed25519.X86_64.SignCached.finishCode t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.mul_step hL hc) fun u ⟨hu, ho, hf⟩ => ?_)
  rw [hs.nonce, hs.challenge, hs.scalar] at ho
  have hp := (VG.Proof.Ed25519.X86_64.SignCached.mul_out_bytes hL hf).trans hs.point
  have hout : Spec.Ed25519.bytesAt u.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
    rw [Proof.Ed25519.signatureBytes_split, hp, ho]
    exact Proof.Ed25519.sign_pipeline _ _ _ hpk
  refine WP.mono (VG.Proof.Ed25519.X86_64.SignCached.wipe_ok hu) fun w ⟨hw, hfw⟩ => ⟨hw, ?_⟩
  have he := VG.Proof.Ed25519.X86_64.SignCached.frame_bytes hfw L.OUT (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hL.ko.sub_left (Offset.sub_base L.B (d := 16) (n := 192) (by decide))).symm)
    (by decide : 64 ≤ 2 ^ 64)
  exact he.trans hout

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete RFC 8032 signing, including all three SHA-512 computations. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (body fld fs v.callee v.suffix) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  apply WP.assoc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.secret_ok v hL hc) fun u ⟨hu, hs⟩ => ?_)
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (VG.Proof.Ed25519.X86_64.SignCached.nonce_ok v hL hu hs hlen)) fun w ⟨hw, hn⟩ => ?_)
  apply WP.assoc
  exact WP.seq (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.challenge_ok v hL hw hn hlen) fun z ⟨hz, hk⟩ => VG.Proof.Ed25519.X86_64.SignCached.finish_ok hL hz hk hpk)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Entry`. -/
section
/-! Entry contract and stack frame of complete cached-key signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega

def signLocal : Contract isa where
  pre s := 264 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .r9, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rdi, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 64⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 8192⟩ ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 8192 ≤ 2 ^ 64 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .rdi) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9

def lay (s : State) : VG.Proof.Ed25519.X86_64.SignCached.Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, s.gpr .rsp - BitVec.ofNat 64 264⟩

theorem lay_ret (s : State) : (VG.Proof.Ed25519.X86_64.SignCached.lay s).B + BitVec.ofNat 64 264 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : signLocal.pre s) : (VG.Proof.Ed25519.X86_64.SignCached.lay s).Ok := by
  obtain ⟨-, -, -, os, op, om, oc, ko, ro, no, sc, pc, mc, ks, kp, km, rs, rp, rm, kc, rc, np, nm, ns, nc, -⟩ := h
  have e : (VG.Proof.Ed25519.X86_64.SignCached.lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, VG.Proof.Ed25519.X86_64.SignCached.lay_ret]
  refine ⟨?_, oc, ko, e ▸ ro, no, ?_, ?_, ?_, kc, e ▸ rc, np, nm, ns, nc⟩
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact os
    · exact op
    · exact om
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sc
    · exact pc
    · exact mc
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ks
    · exact kp
    · exact km
  · intro r hr
    rw [e]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact rs
    · exact rp
    · exact rm

theorem cached_key {s : State} (h : signLocal.pre s) :
    Spec.Ed25519.bytesAt s.mem (VG.Proof.Ed25519.X86_64.SignCached.lay s).pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (VG.Proof.Ed25519.X86_64.SignCached.lay s).seed 32) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩
  exact hk

def pushRs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9] ++ List.replicate 25 .rax

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 31) = sp - BitVec.ofNat 64 264 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 6) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 264 + BitVec.ofNat 64 (256 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : signLocal.pre s) :
    VG.Proof.Ed25519.X86_64.SignCached.Ctx (VG.Proof.Ed25519.X86_64.SignCached.lay s) s.gpr s.mxcsr s.mem (pushed VG.Proof.Ed25519.X86_64.SignCached.pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 31 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s VG.Proof.Ed25519.X86_64.SignCached.pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 6), (pushed VG.Proof.Ed25519.X86_64.SignCached.pushRs s).mem.readW
      ((VG.Proof.Ed25519.X86_64.SignCached.lay s).B + BitVec.ofNat 64 (256 - 8 * j)) 64 = s.gpr (VG.Proof.Ed25519.X86_64.SignCached.pushRs[j]'(by show j < 31; omega)) := fun j hj => by
    rw [← hw j (by show j < 31; omega)]; simp only [VG.Proof.Ed25519.X86_64.SignCached.lay]; rw [VG.Proof.Ed25519.X86_64.SignCached.push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 5 (by omega), hw' 4 (by omega), hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [show pushRs.length = 31 from rfl, VG.Proof.Ed25519.X86_64.SignCached.lay]; rw [VG.Proof.Ed25519.X86_64.SignCached.push_base]
  · rw [pushed_rsp]; simp only [show pushRs.length = 31 from rfl, VG.Proof.Ed25519.X86_64.SignCached.lay]; rw [VG.Proof.Ed25519.X86_64.SignCached.push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(VG.Proof.Ed25519.X86_64.SignCached.lay s).STK, by simp, ?_⟩
    simp only [show pushRs.length = 31 from rfl]
    rw [VG.Proof.Ed25519.X86_64.SignCached.push_base]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTAccess`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTFramework`. -/
section
/-! Relating complete signing runs with equal pointers and lengths; all input bytes remain secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within)

abbrev Two.Env := VG.Proof.Ed25519.X86_64.SignCached.Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

def Two (Φ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧
    VG.Proof.Ed25519.X86_64.SignCached.Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧ VG.Proof.Ed25519.X86_64.SignCached.Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2.2.2 b

theorem two_wp {c : Prog isa} {Φ Ψ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop}
    (hct : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) c fun _ _ => True)
    (hw : ∀ (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) c (VG.Proof.Ed25519.X86_64.SignCached.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_block {is : List Instr} {Φ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ ⟨_, _, c₁, c₂, _, _⟩ =>
    Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact c₁.rsp.trans c₂.rsp.symm)) h

theorem two_blk {is : List Instr} {Φ Ψ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) (.block is) (VG.Proof.Ed25519.X86_64.SignCached.Two Ψ) := VG.Proof.Ed25519.X86_64.SignCached.two_wp (VG.Proof.Ed25519.X86_64.SignCached.two_block h) hw

structure Access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (rd wr : List Region) : Prop where
  sub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  wsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR

theorem covers {L : VG.Proof.Ed25519.X86_64.SignCached.Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t) {rd wr : List Region} (ha : VG.Proof.Ed25519.X86_64.SignCached.Access L rd wr) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  constructor <;> apply Covers.of_sub <;> intro r hr
  · obtain ⟨R, hR, hs⟩ := ha.sub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hs⟩
  · rw [hc.wr]
    rcases ha.wsub r hr with h | h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, Nat.le_trans hn (by show 192 ≤ 248; decide)⟩
    · exact ⟨L.OUT, by simp, h⟩
    · exact ⟨L.SCR, by simp, h⟩

theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : VG.Proof.Ed25519.X86_64.SignCached.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      VG.Proof.Ed25519.X86_64.SignCached.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Access L (rd L) (wr L)) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ hL c₁ c₂ f₁ f₂,
      (VG.Proof.Ed25519.X86_64.SignCached.covers c₁ (ha L hL)).1, (VG.Proof.Ed25519.X86_64.SignCached.covers c₁ (ha L hL)).2, (VG.Proof.Ed25519.X86_64.SignCached.covers c₂ (ha L hL)).1, (VG.Proof.Ed25519.X86_64.SignCached.covers c₂ (ha L hL)).2,
      c₁.rsp.trans c₂.rsp.symm⟩

theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : VG.Proof.Ed25519.X86_64.SignCached.Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : VG.Proof.Ed25519.X86_64.SignCached.Lay → List Region)
    (hpre : ∀ (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) g mx m₀ (t : State), L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      VG.Proof.Ed25519.X86_64.SignCached.Ctx L g₁ mx₁ m₁ t₁ → VG.Proof.Ed25519.X86_64.SignCached.Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Access L (rd L) (wr L)) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two Φ) (.call n c) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) :=
  VG.Proof.Ed25519.X86_64.SignCached.two_wp (VG.Proof.Ed25519.X86_64.SignCached.two_call hv hct rd wr hpre hpub ha) fun L _ _ _ _ hL hc hf =>
    VG.Proof.Ed25519.X86_64.SignCached.call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (ha L hL).sub (ha L hL).wsub
      fun _ hc' _ _ _ => ⟨hc', trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Memory coverage for modular constant-time calls in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (within_base within_off add_add)

theorem init_access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (_hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Access L VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L) := by
  constructor
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.initRd, VG.Proof.Ed25519.X86_64.SignCached.initWr, List.nil_append, List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.initWr, List.mem_singleton] at hr; subst hr
    exact .inr (.inr (within_base _ (by omega)))

theorem upd_access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (p : Addr) (n : BitVec 64) (hi : VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p, n.toNat⟩) :
    VG.Proof.Ed25519.X86_64.SignCached.Access L [⟨p, n.toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L) := by
  constructor
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inr (.inr (within_off _ (by omega)))

theorem fin_access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (_hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Access L [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L) := by
  constructor
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inl ⟨128, by rw [add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega)))

theorem reduce_access (out : Nat) (ho : out + 32 ≤ 128) (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (_hL : L.Ok) :
    VG.Proof.Ed25519.X86_64.SignCached.Access L (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out) := by
  constructor
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceRd, VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega⟩
    · exact .inr (.inr (within_base _ (by omega)))

theorem base_access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (_hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Access L (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L) := ⟨VG.Proof.Ed25519.X86_64.SignCached.base_sub, VG.Proof.Ed25519.X86_64.SignCached.base_wsub⟩

theorem mul_access (L : VG.Proof.Ed25519.X86_64.SignCached.Lay) (_hL : L.Ok) : VG.Proof.Ed25519.X86_64.SignCached.Access L (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L) := by
  constructor
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.mulRd, VG.Proof.Ed25519.X86_64.SignCached.mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [VG.Proof.Ed25519.X86_64.SignCached.mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega)))
    · exact .inr (.inr (within_base _ (by omega)))

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTHashes`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTHash`. -/
section
/-! SHA-512's trace depends only on the input pointers and length. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (gpr_ce rsp_ce nosp_init upd_verified upd_nosp upd_depth fin_verified fin_nosp fin_depth within_base)
open VG.Proof.Sha512.X86_64 (Compress)

theorem init_ct : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block initArgs) (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.InitArgs L) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.SignCached.initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := VG.Proof.Ed25519.X86_64.SignCached.two_callP (n := Spec.Sha512.init512Api.name) (Φ := fun L _ => VG.Proof.Ed25519.X86_64.SignCached.InitArgs L)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (nosp_init _) (by decide) (fun _ => VG.Proof.Ed25519.X86_64.SignCached.initRd) VG.Proof.Ed25519.X86_64.SignCached.initWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((gpr_ce t₁ VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L) (by decide)).trans a₁).trans
        ((gpr_ce t₂ VG.Proof.Ed25519.X86_64.SignCached.initRd (VG.Proof.Ed25519.X86_64.SignCached.initWr L) (by decide)).trans a₂).symm) VG.Proof.Ed25519.X86_64.SignCached.init_access
  exact b.seq c

theorem upd_ct (v : Compress) (count : VG.Proof.Ed25519.X86_64.SignCached.Lay → BitVec 64) (p : VG.Proof.Ed25519.X86_64.SignCached.Lay → Addr) (n : VG.Proof.Ed25519.X86_64.SignCached.Lay → BitVec 64)
    (hi : ∀ L, L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p L, (n L).toNat⟩) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (count L) (p L) (n L))
      (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee))
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  exact VG.Proof.Ed25519.X86_64.SignCached.two_callP (upd_verified v).1 (upd_verified v).2.1 (upd_nosp v) (upd_depth v)
    (fun L => [⟨p L, (n L).toNat⟩]) VG.Proof.Ed25519.X86_64.SignCached.updWr
    (fun L _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.upd_pre hL hc ha (hi L hL))
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := VG.Proof.Ed25519.X86_64.SignCached.upd_regs a₁ [⟨p L, (n L).toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := VG.Proof.Ed25519.X86_64.SignCached.upd_regs a₂ [⟨p L, (n L).toNat⟩] (VG.Proof.Ed25519.X86_64.SignCached.updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩)
    (fun L hL => VG.Proof.Ed25519.X86_64.SignCached.upd_access L (p L) (n L) (hi L hL))

theorem finalize_ct (v : Compress) (prefixLen : Nat) (hp : prefixLen < 2 ^ 31) (withMessage : Bool)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (finalizeArgs prefixLen withMessage)) hint).isSome = true) : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith (finalizeArgs prefixLen withMessage) (Spec.Sha512.finalizeScratchApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block (finalizeArgs prefixLen withMessage)) (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.FinArgs L (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen)) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk ht fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.SignCached.finalizeArgs_ok hc prefixLen hp withMessage) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := VG.Proof.Ed25519.X86_64.SignCached.two_callP (n := Spec.Sha512.finalizeScratchApi.name ++ v.suffix) (Φ := fun L _ => VG.Proof.Ed25519.X86_64.SignCached.FinArgs L (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen))
    (fin_verified v).1 (fin_verified v).2.1 (fin_nosp v) (fin_depth v) (fun _ => []) VG.Proof.Ed25519.X86_64.SignCached.finWr
    (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := VG.Proof.Ed25519.X86_64.SignCached.fin_regs a₁ [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := VG.Proof.Ed25519.X86_64.SignCached.fin_regs a₂ [] (VG.Proof.Ed25519.X86_64.SignCached.finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩) VG.Proof.Ed25519.X86_64.SignCached.fin_access
  exact b.seq c

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! All three signing hashes leak only their pointers and lengths. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem input_ct (v : Compress) (source count : Nat) (hs : source + 8 ≤ 248) (hc : count < 2 ^ 32)
    (p : VG.Proof.Ed25519.X86_64.SignCached.Lay → Addr) (hi : ∀ L, L.Ok → VG.Proof.Ed25519.X86_64.SignCached.Input L ⟨p L, 32⟩)
    (hp : ∀ L g mx m (t : State), VG.Proof.Ed25519.X86_64.SignCached.Ctx L g mx m t →
      t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p L)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (inputArgs source count)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (update v.callee v.suffix (inputArgs source count))
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block (inputArgs source count))
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 count) (p L) 32) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk ht fun L g mx m t _ h _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.inputArgs_ok h source count hs hc (p L) (hp L g mx m t h))
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (VG.Proof.Ed25519.X86_64.SignCached.upd_ct v (fun _ => BitVec.ofNat 64 count) p (fun _ => 32) hi)

theorem message_ct (v : Compress) (count : Nat) (hc : count < 2 ^ 32)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (messageArgs count)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (update v.callee v.suffix (messageArgs count))
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block (messageArgs count))
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L (BitVec.ofNat 64 count) L.msg L.len) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk ht fun _ _ _ _ _ _ h _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.messageArgs_ok h count hc)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (VG.Proof.Ed25519.X86_64.SignCached.upd_ct v (fun _ => BitVec.ofNat 64 count) Lay.msg Lay.len
    (fun _ hL => (VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (by simp [Lay.inputs])).toInput))

theorem hashSeed_ct (v : Compress) : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (hashSeed v.callee v.suffix) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) :=
  init_ct.seq ((VG.Proof.Ed25519.X86_64.SignCached.input_ct v fSeed 0 (by decide) (by decide) Lay.seed
    (fun _ hL => (VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (by simp [Lay.inputs])).toInput)
    (fun _ _ _ _ _ h => h.pSeed) (by taint_decide)).seq
    (VG.Proof.Ed25519.X86_64.SignCached.finalize_ct v 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (v : Compress) : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (hashNonce v.callee v.suffix) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block prefixArgs)
      (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.UpdArgs L 0 (L.B + BitVec.ofNat 64 48) 32) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ h _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.prefixArgs_ok h)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact init_ct.seq ((b.seq (VG.Proof.Ed25519.X86_64.SignCached.upd_ct v (fun _ => 0) (fun L => L.B + BitVec.ofNat 64 48) (fun _ => 32)
    (fun _ hL => (VG.Proof.Ed25519.X86_64.SignCached.stable_prefix hL).toInput))).seq
    ((VG.Proof.Ed25519.X86_64.SignCached.message_ct v 32 (by decide) (by taint_decide)).seq (VG.Proof.Ed25519.X86_64.SignCached.finalize_ct v 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (v : Compress) : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (hashChallenge v.callee v.suffix) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) :=
  init_ct.seq ((VG.Proof.Ed25519.X86_64.SignCached.input_ct v fOut 0 (by decide) (by decide) Lay.out
    (fun _ hL => (VG.Proof.Ed25519.X86_64.SignCached.stable_out hL).toInput) (fun _ _ _ _ _ h => h.pOut) (by taint_decide)).seq
    ((VG.Proof.Ed25519.X86_64.SignCached.input_ct v fPublicKey 32 (by decide) (by decide) Lay.pk
      (fun _ hL => (VG.Proof.Ed25519.X86_64.SignCached.stable_input hL (by simp [Lay.inputs])).toInput)
      (fun _ _ _ _ _ h => h.pPk) (by taint_decide)).seq
    ((VG.Proof.Ed25519.X86_64.SignCached.message_ct v 64 (by decide) (by taint_decide)).seq (VG.Proof.Ed25519.X86_64.SignCached.finalize_ct v 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTCalls`. -/
section
/-! The signer's scalar and point operations keep all operand bytes secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed scalarReduce scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (rsp_ce)

theorem reduce_ct (out : Nat) (ho : out + 32 ≤ 128)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (reduceArgs out)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (reduce out) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block (reduceArgs out)) (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk ht fun _ _ _ _ _ _ hc _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.reduceArgs_ok hc ho)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := VG.Proof.Ed25519.X86_64.SignCached.two_callP (n := "vg_ed25519_scalar_reduce") (Φ := fun L _ => VG.Proof.Ed25519.X86_64.SignCached.ReduceArgs L out)
    scalarReduce_ok scalarReduce_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    VG.Proof.Ed25519.X86_64.SignCached.reduceRd (fun L => VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out) (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.reduce_pre hL hc ha ho)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := VG.Proof.Ed25519.X86_64.SignCached.reduce_regs a₁ (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out)
      obtain ⟨d₂, s₂, x₂⟩ := VG.Proof.Ed25519.X86_64.SignCached.reduce_regs a₂ (VG.Proof.Ed25519.X86_64.SignCached.reduceRd L) (VG.Proof.Ed25519.X86_64.SignCached.reduceWr L out)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (VG.Proof.Ed25519.X86_64.SignCached.reduce_access out ho)
  exact b.seq c

theorem base_ct : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block baseArgs) (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.baseArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := VG.Proof.Ed25519.X86_64.SignCached.two_callP (n := (scalarBaseName fs)) (Φ := fun L _ => VG.Proof.Ed25519.X86_64.SignCached.BaseArgs L)
    (scalarBase_precomputed_ok (fld := fld)) (scalarBase_precomputed_ct (fld := fld)) VG.Proof.Ed25519.X86_64.SignCached.base_nosp VG.Proof.Ed25519.X86_64.SignCached.base_depth
    VG.Proof.Ed25519.X86_64.SignCached.baseRd VG.Proof.Ed25519.X86_64.SignCached.baseWr
    (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := VG.Proof.Ed25519.X86_64.SignCached.base_regs a₁ (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := VG.Proof.Ed25519.X86_64.SignCached.base_regs a₂ (VG.Proof.Ed25519.X86_64.SignCached.baseRd L) (VG.Proof.Ed25519.X86_64.SignCached.baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    VG.Proof.Ed25519.X86_64.SignCached.base_access
  exact b.seq c

theorem mul_ct : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have b : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block mulAddArgs) (VG.Proof.Ed25519.X86_64.SignCached.Two fun L _ => VG.Proof.Ed25519.X86_64.SignCached.MulArgs L) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (VG.Proof.Ed25519.X86_64.SignCached.mulArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := VG.Proof.Ed25519.X86_64.SignCached.two_callP (n := "vg_ed25519_scalar_mul_add") (Φ := fun L _ => VG.Proof.Ed25519.X86_64.SignCached.MulArgs L)
    scalarMulAdd_ok scalarMulAdd_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    VG.Proof.Ed25519.X86_64.SignCached.mulRd VG.Proof.Ed25519.X86_64.SignCached.mulWr (fun _ _ _ _ _ hL hc ha => VG.Proof.Ed25519.X86_64.SignCached.mul_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := VG.Proof.Ed25519.X86_64.SignCached.mul_regs a₁ (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L)
      obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := VG.Proof.Ed25519.X86_64.SignCached.mul_regs a₂ (VG.Proof.Ed25519.X86_64.SignCached.mulRd L) (VG.Proof.Ed25519.X86_64.SignCached.mulWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm,
        x₁.trans x₂.symm, k₁.trans k₂.symm, r₁.trans r₂.symm⟩) VG.Proof.Ed25519.X86_64.SignCached.mul_access
  exact b.seq c

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Correct`. -/
section
/-! Complete signing meets its functional contract and preserves the ABI. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
open VG.Proof.Ed25519.X86_64.PublicKey (add_add ne_cs)

theorem sign_ok (v : Compress) {s : State} (h : signLocal.pre s) :
    WP isa (code fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ signLocal.post s s' := by
  have hL := VG.Proof.Ed25519.X86_64.SignCached.lay_ok h
  have hc := VG.Proof.Ed25519.X86_64.SignCached.push_ctx h
  refine WP.frame (rs := VG.Proof.Ed25519.X86_64.SignCached.pushRs) (by decide) (by decide) (by decide) (by show 8 * 31 ≤ _; have := h.1; omega)
    (WP.mono (VG.Proof.Ed25519.X86_64.SignCached.body_ok v hL hc hL.message_bound (VG.Proof.Ed25519.X86_64.SignCached.cached_key h))
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 31 from rfl, add_add, VG.Proof.Ed25519.X86_64.SignCached.lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (VG.Proof.Ed25519.X86_64.SignCached.lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, VG.Proof.Ed25519.X86_64.SignCached.lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (VG.Proof.Ed25519.X86_64.SignCached.lay s).out 64 = _
    rw [popped_mem, ho]
    rfl

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete signing is constant-time with respect to seed, key and message bytes. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem body_ct (v : Compress) : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True)
    (body fld fs v.callee v.suffix) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) := by
  have s : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block saveSecret) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.SignCached.saveSecret_ok hc rfl) fun _ ⟨hc', _, _⟩ => ⟨hc', trivial⟩
  have w : RelCT isa (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) (.block wipe) (VG.Proof.Ed25519.X86_64.SignCached.Two fun _ _ _ => True) :=
    VG.Proof.Ed25519.X86_64.SignCached.two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (VG.Proof.Ed25519.X86_64.SignCached.wipe_ok hc) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact (VG.Proof.Ed25519.X86_64.SignCached.hashSeed_ct v).seq (s.seq ((VG.Proof.Ed25519.X86_64.SignCached.hashNonce_ct v).seq ((VG.Proof.Ed25519.X86_64.SignCached.reduce_ct 64 (by decide) (by taint_decide)).seq
    (base_ct.seq ((VG.Proof.Ed25519.X86_64.SignCached.hashChallenge_ct v).seq ((VG.Proof.Ed25519.X86_64.SignCached.reduce_ct 96 (by decide) (by taint_decide)).seq (mul_ct.seq w)))))))

theorem sign_ct (v : Compress) : ConstantTime isa signLocal.pre signLocal.pub (code fld fs v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (VG.Proof.Ed25519.X86_64.SignCached.body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, h9⟩, rfl, rfl⟩
  have e : VG.Proof.Ed25519.X86_64.SignCached.lay s₂ = VG.Proof.Ed25519.X86_64.SignCached.lay s₁ := by simp only [VG.Proof.Ed25519.X86_64.SignCached.lay, hsp, hdi, hsi, hdx, hcx, h8, h9]
  exact ⟨⟨VG.Proof.Ed25519.X86_64.SignCached.lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, VG.Proof.Ed25519.X86_64.SignCached.lay_ok h₁,
    VG.Proof.Ed25519.X86_64.SignCached.push_ctx h₁, e ▸ VG.Proof.Ed25519.X86_64.SignCached.push_ctx h₂, trivial, trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey VG.Proof.Ed25519.X86_64.SignCached.satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [VG.Proof.Ed25519.X86_64.SignCached.satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else VG.Proof.Ed25519.X86_64.SignCached.satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86_64.SignCached.satMem 0x2000 32 = VG.Proof.Ed25519.X86_64.SignCached.satSeed := by
  unfold VG.Proof.Ed25519.X86_64.SignCached.satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold VG.Proof.Ed25519.X86_64.SignCached.satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt VG.Proof.Ed25519.X86_64.SignCached.satMem 0x3000 32 = VG.Proof.Ed25519.X86_64.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, VG.Proof.Ed25519.X86_64.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed25519.X86_64.SignCached.satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0 | .r9 => 0x5000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed25519.X86_64.SignCached.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract X86_64.abi 264).pre s := by
  refine ⟨VG.Proof.Ed25519.X86_64.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.SignCached.satState]
    sig_and_intros
    · decide +kernel
    · rw [VG.Proof.Ed25519.X86_64.SignCached.sat_seed, VG.Proof.Ed25519.X86_64.SignCached.sat_key]
      rfl

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete signing satisfies the reviewed cached-key signing contract. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce scalarBase_precomputed scalarMulAdd callWith)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies : signLocal.Implies (Spec.Ed25519.signCachedContract X86_64.abi 264) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.SignCached.signLocal]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.SignCached.signLocal]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, VG.Proof.Ed25519.X86_64.SignCached.signLocal]
  sat := VG.Proof.Ed25519.X86_64.SignCached.sat

theorem verified (v : Compress) : Verified X86_64.target (code fld fs v.callee v.suffix)
    (Spec.Ed25519.signCachedContract X86_64.abi 264) :=
  Verified.of_correct (fun _ h => VG.Proof.Ed25519.X86_64.SignCached.sign_ok v h) (VG.Proof.Ed25519.X86_64.SignCached.sign_ct v) VG.Proof.Ed25519.X86_64.SignCached.implies

theorem spSafe (v : Compress) : (code fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : scalarReduce.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hb : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true :=
    PublicKey.base_spSafe
  have hm : scalarMulAdd.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [code, body, hashSeed, hashNonce, hashChallenge, init, update, finalize, reduce, callWith,
    Code.all, hu, hf, hr, hb, hm, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.SignCached

end
