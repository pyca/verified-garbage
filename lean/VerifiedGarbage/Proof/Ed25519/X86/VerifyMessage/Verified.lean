module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
meta import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTEquation`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTHash`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_esp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans h.2.1.esp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

/-- Runs keep their statics' addresses: each run's address of `bSym` stays `L.tbl`. -/
theorem two_syms {P Q : State → Prop} {c : Prog isa}
    (h : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => P t ∧ t.syms Impl.Ed25519.X86.bSym = L.tbl) c
      (Two L g₁ g₂ m₁ m₂ fun t => Q t ∧ t.syms Impl.Ed25519.X86.bSym = L.tbl) := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ht, hq⟩ := h a b ta tb a' b' ⟨hp.1, hp.2.1, hp.2.2.1.1, hp.2.2.2.1⟩ ea eb
  exact ⟨ht, hq.1, hq.2.1, ⟨hq.2.2.1, (congrFun (VG.X86.Exec.syms ea) _).trans hp.2.2.1.2⟩,
    ⟨hq.2.2.2, (congrFun (VG.X86.Exec.syms eb) _).trans hp.2.2.2.2⟩⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup 0 vs))
      (Two L g₁ g₂ m₁ m₂ (OutArgs L vs)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (hL : L.Ok) {vs : List Value} (hn : vs.length ≤ 6)
    {a b : State} (h : Two L g₁ g₂ m₁ m₂ (OutArgs L vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  have H := hashSpace hL
  rw [Whole.call_arg h.1.esp H.below H.frameFit (by omega),
    Whole.call_arg h.2.1.esp H.below H.frameFit (by omega),
    h.2.2.1.slot hL hj hn, h.2.2.2.slot hL hj hn]

theorem call_ct (hL : L.Ok) {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb, two_esp h⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono ((ready hc hs).wp hc correct sp stack hL.below) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTReady`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def init_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  have ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  exact ⟨_, _, Whole.init_pre hc.esp H a0, cov, ws⟩

def update_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {c p n : BitVec 32}
    (hi : Input L p n) (ha : UpdateArgs L c p n s) :
    Whole.CallReady Proof.Sha512.updateX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, _, _, a3, a4, a5⟩ := ha
  have H := hashSpace hL
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def finalize_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {count : BitVec 64}
    (ha : FinArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, a3, a4, _⟩ := ha
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def reduce_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.E + 128)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have wo : Whole.Within ⟨(L.E + 128).setWidth 64, 32⟩ L.FR :=
    ⟨128, Whole.frame_addr H.frameFit (by decide), by change 128 + 32 ≤ 256; decide⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr 128)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (digestWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inl wo
    · exact scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr 128,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H (by decide) (by decide) a0 a1 a2, cov, ws⟩

def equation_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) (ht : TblAt L s.mem)
    (hy : s.syms Impl.Ed25519.X86.bSym = L.tbl) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs s := by
  have wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  have wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  have cov : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [equationRd, equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (challengeWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.TBL, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact scratch_covered wz
    · exact scratch_covered wsc
  have ws : ∀ r ∈ equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    hash_writes (by
      simp only [equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  exact ⟨_, _, equation_pre hc hL ha ht hy, cov, ws⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 4 0]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL (Proof.Sha512.X86.Stream.init_verified _).1
    (Proof.Sha512.X86.Stream.init_verified _).2.1 Whole.init_nosp (by rw [Whole.init_stack]; decide)
  · intro g m t hc hs
    apply init_ready hc hL
    exact (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 1)⟩

theorem update_call_ct (hL : L.Ok) {vs : List Value} (hn : vs.length = 6)
    {c p n : BitVec 32} (hi : Input L p n)
    (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L vs))
      (.call "vg_sha512_update_scratch" Impl.Sha512.X86.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Update.update_verified.1
    Proof.Sha512.X86.Stream.Update.update_verified.2.1 Whole.update_nosp (by rw [Whole.update_stack])
  · intro g m t hc hs
    exact update_ready hc hL hi (hargs t hs)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), fun j hj => call_args_eq hL (by omega) h (by omega)⟩

theorem append_pair_eq {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have e := congrArg (BitVec.extractLsb' 32 32) h
    simpa only [BitVec.extractLsb'_append_eq_left] using e
  · have e := congrArg (BitVec.extractLsb' 0 32) h
    simpa only [BitVec.extractLsb'_append_eq_right] using e

theorem finalize_call_ct (hL : L.Ok) (count : BitVec 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (FinArgs L count))
      (.call "vg_sha512_finalize_scratch" Impl.Sha512.X86.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Finalize.finalize_verified.1
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1 Whole.finalize_nosp (by rw [Whole.finalize_stack])
  · intro g m t hc hs
    exact finalize_ready hc hL hs
  · intro a b ar aw br bw h
    refine ⟨congrArg (· - 4) (two_esp h), ?_⟩
    intro j hj
    have H := hashSpace hL
    rw [arg_withRegions, arg_withRegions, Whole.call_arg h.1.esp H.below H.frameFit (by omega),
      Whole.call_arg h.2.1.esp H.below H.frameFit (by omega)]
    obtain ⟨a0, a3, a4, ac⟩ := h.2.2.1
    obtain ⟨b0, b3, b4, bc⟩ := h.2.2.2
    have pair := append_pair_eq (ac.trans bc.symm)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact a0.trans b0.symm
    · exact pair.2
    · exact pair.1
    · exact a3.trans b3.symm
    · exact a4.trans b4.symm

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block finalizeArgs)
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by native_taint_decide)) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem update_outArgs (hL : L.Ok) {source count : Nat} {nv : Value} {s : State}
    (hs : OutArgs L [.caller 4 0, .const count, .const 0, .caller source 0, nv, .caller 4 192] s) :
    UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (value L nv) s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 1) (by simp) (by simp)
  · exact hs.slot hL (j := 2) (by simp) (by simp)
  · exact (hs.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 4) (by simp) (by simp)
  · exact hs.slot hL (j := 5) (by simp) (by simp)

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ini := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0] (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  have rs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]
    (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  have ps := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]
    (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  have ms := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]
    (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  have r := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]) rfl
    (input_sig hL) (fun _ hs => update_outArgs hL hs)
  have p := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]) rfl
    (input_pk hL) (fun _ hs => update_outArgs hL hs)
  have m := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]) rfl
    (input_msg hL) (fun _ hs => by
      have h := update_outArgs hL hs
      simpa only [value, Lay.value, BitVec.add_zero] using h)
  exact (ini.seq (init_call_ct hL)).seq ((rs.seq r).seq ((ps.seq p).seq
    ((ms.seq m).seq ((finalize_args_ct hL ha hb).seq (finalize_call_ct hL _)))))

theorem hash_ct_result (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (he : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun _ ⟨hu, hd⟩ => ⟨hu, ?_⟩
    rw [he]
    exact hd

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame 128, .frame 192, .caller 4 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL (hs.slot hL (j := 0) (by decide) (by decide))
      (hs.slot hL (j := 1) (by decide) (by decide))
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = digest)
      (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) := by
  have ct := (setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.frame 128, .frame 192, .caller 4 0]
    (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)).seq (reduce_call_ct hL)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono (reduce_step hc hL ha) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr
  · intro t hc hd
    refine WP.mono (reduce_step hc hL hb) fun _ ⟨hu, hr⟩ => ⟨hu, ?_⟩
    rw [hd] at hr
    exact hr

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  exact two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by native_taint_decide))
    (fun _ hc hd => extend_step hc hL hd) (fun _ hc hd => extend_step hc hL hd)

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def equationValues : List Value := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0]
def EqState (L : Lay) (ch : List Byte) (s : State) : Prop :=
  OutArgs L equationValues s ∧ Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch ∧
    TblAt L s.mem ∧ s.syms Impl.Ed25519.X86.bSym = L.tbl

theorem eq_args (hL : L.Ok) {s : State} (hs : OutArgs L equationValues s) : EqArgs L s :=
  ⟨(hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _),
    (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _),
    hs.slot hL (j := 2) (by decide) (by decide),
    (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)⟩

theorem ce_input {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt s.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  have e := Whole.callEntry_bytes (t := s) (r := r) (by
    rw [hc.esp]
    exact ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by decide))).symm) hn
  exact e.trans (hc.input_bytes hL hr hn)

theorem ce_challenge {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {ch : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch) :
    Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 = ch := by
  have e := Whole.callEntry_bytes (t := s) (r := challenge L) (by
    rw [hc.esp]
    exact (Whole.frame_below hL.below (hashSpace hL).frameFit
      (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm) (by change 64 ≤ 2 ^ 64; decide)
  have ea : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide : 128 < 256)
  change Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
    Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 at e
  rw [ea] at e ⊢
  exact e.trans he

theorem equation_call_ct (hL : L.Ok) (ch : List Byte)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (EqState L ch))
      (.call "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL equation_correct_result verify_ct equation_nosp (by rw [equation_stack]; decide)
  · intro g m t hc hh
    exact equation_ready hc hL (eq_args hL hh.1) hh.2.2.1 hh.2.2.2
  · intro a b ar aw br bw h
    have hargs : Two L g₁ g₂ m₁ m₂ (OutArgs L equationValues) a b := ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2.1⟩
    have hj {j : Nat} (hh : j < 4) := call_args_eq hL (by decide) hargs hh
    have H := hashSpace hL
    have ea := eq_args hL h.2.2.1.1
    have eb := eq_args hL h.2.2.2.1
    have a0 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 0 < 64)).trans ea.1
    have a1 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 1 < 64)).trans ea.2.1
    have a2 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 2 < 64)).trans ea.2.2.1
    have b0 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 0 < 64)).trans eb.1
    have b1 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 1 < 64)).trans eb.2.1
    have b2 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 2 < 64)).trans eb.2.2.1
    refine ⟨congrArg (· - 4) (two_esp h), hj (by decide), hj (by decide), hj (by decide), hj (by decide), ?_, ?_, ?_,
      (h.2.2.1.2.2.2 : _).trans (h.2.2.2.2.2.2 : _).symm⟩
    · simp only [arg_withRegions, State.withRegions_mem, a0, b0]
      exact (ce_input h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).trans
        (hp.trans (ce_input h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a1, b1]
      exact (ce_input h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).trans
        (hs.trans (ce_input h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a2, b2]
      exact (ce_challenge h.1 hL h.2.2.1.2.1).trans (ce_challenge h.2.1 hL h.2.2.2.2.1).symm

theorem equation_setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (ch : List Byte)
    (ht₁ : TblAt L m₁) (ht₂ : TblAt L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 = ch ∧
        t.syms Impl.Ed25519.X86.bSym = L.tbl)
      (.block equationArgs) (Two L g₁ g₂ m₁ m₂ (EqState L ch)) := by
  have ct := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb equationValues
    (by decide) (Whole.valid_all (by decide)) (by native_taint_decide)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono_syms (args_ok hc hL ha (vs := equationValues) (by decide)
      (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ yu =>
        ⟨hu, hs, ?_, hu.tbl hL ht₁, by rw [yu]; exact hd.2⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd.1
  · intro t hc hd
    refine WP.mono_syms (args_ok hc hL hb (vs := equationValues) (by decide)
      (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ yu =>
        ⟨hu, hs, ?_, hu.tbl hL ht₂, by rw [yu]; exact hd.2⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd.1

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Entry`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
    ⟨(arg s 3).setWidth 64, 64⟩, ⟨argAddr s 0, 20⟩, ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩]

/-- The static of `-[1]B … -[15]B`: its words, not wrapping around, apart from the scratch space,
the stack and the return address. -/
def MsgTbl (s : State) : Prop :=
  let tbl : Region := ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩
  (∀ i < 240, s.mem.readW ((s.syms Impl.Ed25519.X86.bSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.Ed25519.X86.bWords.getD i 0) ∧
    (s.syms Impl.Ed25519.X86.bSym).toNat + 1920 ≤ 2 ^ 32 ∧
    tbl.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ∧
    (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ : Region).Disjoint tbl ∧
    (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint tbl
def verifyWr (s : State) : List Region := [⟨(arg s 4).setWidth 64, 8192⟩]

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = verifyRd s ∧ s.wr = verifyWr s ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ MsgTbl s
  post s t := t.gpr .eax = signWord (Spec.Ed25519.verify
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) (arg t 2).toNat ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 3).setWidth 64) 64 ∧
    s.syms Impl.Ed25519.X86.bSym = t.syms Impl.Ed25519.X86.bSym

def lay (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, s.gpr .esp - BitVec.ofNat 32 256, s.syms Impl.Ed25519.X86.bSym⟩

theorem entry_bounds {s : State} (h : verifyMessageLocal.pre s) :
    280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem entry_tbl {s : State} (h : verifyMessageLocal.pre s) : MsgTbl s :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem lay_base {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).E.setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 :=
  Taint.sub_setWidth (by have := (entry_bounds h).1; omega)

theorem lay_args {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).ARGS = ⟨argAddr s 0, 20⟩ := by
  rw [Lay.ARGS, lay_base h]
  have ha : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := (entry_bounds h).2; omega)
  rw [ha]
  congr 1
  change _ - 256#64 + 260#64 = _ + 4#64
  rw [show BitVec.ofNat 64 260 = BitVec.ofNat 64 256 + BitVec.ofNat 64 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem lay_ret {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [Lay.RET, lay_base h]
  change (⟨(s.gpr .esp).setWidth 64 - 256#64 + 256#64, 4⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem lay_stack {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ := by
  rw [Lay.STK, Whole.STK, lay_base h, BitVec.sub_sub]
  rfl

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na, mt⟩ := h
  have h : verifyMessageLocal.pre s :=
    ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na, mt⟩
  obtain ⟨_, tf, ts, tk, tr⟩ := mt
  have top : (lay s).E.toNat + 280 ≤ 2 ^ 32 := by
    change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 280 ≤ _
    rw [sub_toNat (by omega)]
    omega
  refine ⟨?_, top, ?_, ?_, ?_, ?_, ?_, np, nm, ns, nc, tf⟩
  · change 24 ≤ (s.gpr .esp - BitVec.ofNat 32 256).toNat
    rw [sub_toNat (by omega)]
    omega
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact pc
    · exact mc
    · exact sc
    · rw [lay_args h]; exact ac
    · exact ts
  · intro r hr
    rw [lay_stack h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact kp
    · exact km
    · exact ks
    rotate_left
    · exact tk
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact Offset.disjoint_below_above _ (by decide)
  · intro r hr
    rw [lay_ret h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rp
    · exact rm
    · exact rs
    rotate_left
    · exact tr
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · rw [lay_stack h]; exact kc
  · rw [lay_ret h]; exact rc

theorem lay_arguments {s : State} (h : verifyMessageLocal.pre s) : Arguments (lay s) s.mem := by
  intro j hj
  have hb := lay_ok h
  have e : (lay s).E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j) = argAddr s j := by
    rw [← addr_eq (by have := hb.top; omega)]
    simp only [addr, lay, argAddr]
    rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  change arg s j = (lay s).value j
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_ctx {s : State} (h : verifyMessageLocal.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed (List.replicate 64 .eax) s) := by
  have hn := (entry_bounds h).1
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨?_, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_rd, h.1]
    rw [Lay.inputs, lay_args h]
    rfl
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate, Whole.FR, Lay.outputs, Lay.SCR, lay, verifyWr]
  · rw [pushed_esp, List.length_replicate]
    rfl
  · refine Frame.sub hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine ⟨(lay s).STK, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [lay_stack h, ← Taint.sub_setWidth hn]
    exact below_sub (by simp) hn

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.VerifyMessage
materialize_code code
end VG.Impl.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have np0 : NoSp (.block (prefixArgs 3 0)) := NoSp.of_all (by decide +kernel)
  have np1 : NoSp (.block (prefixArgs 0 32)) := NoSp.of_all (by decide +kernel)
  have nm : NoSp (.block messageArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nr : NoSp (.block reduceArgs) := NoSp.of_all (by decide +kernel)
  have ne : NoSp (.block extendChallenge) := NoSp.of_all (by decide +kernel)
  have nq : NoSp (.block equationArgs) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq np0 Whole.update_nosp)
      (noSp_seq (noSp_seq np1 Whole.update_nosp)
      (noSp_seq (noSp_seq nm Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))))
    (noSp_seq (noSp_seq nr Whole.reduce_nosp)
      (noSp_seq ne (noSp_seq nq equation_nosp)))

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ verifyMessageLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h) (entry_tbl h).1
      (by rw [show (pushed (List.replicate 64 .eax) s).syms = s.syms from pushRegs_syms s _]; rfl))
      fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [lay_ret h]; exact Region.contains_self _ _
    · simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change (popped .edx (List.replicate 64 .eax).length u).gpr .eax = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    exact ho

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (ht₁ : TblAt L m₁) (ht₂ : TblAt L m₂)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hm : Spec.Ed25519.bytesAt m₁ (L.msg.setWidth 64) L.len.toNat =
      Spec.Ed25519.bytesAt m₂ (L.msg.setWidth 64) L.len.toNat)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => True ∧ t.syms Impl.Ed25519.X86.bSym = L.tbl) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hi : hashInput L m₁ = hashInput L m₂ := by
    rw [hashInput_eq, hashInput_eq, hp, hm, hs]
  exact (two_syms (hash_ct_result hL ha hb hi)).seq ((two_syms (reduce_ct hL ha hb _)).seq
    ((two_syms (extend_ct hL _)).seq ((equation_setup_ct hL ha hb _ ht₁ ht₂).seq (equation_call_ct hL _ hp hs))))

theorem verifyMessage_ct : ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub code := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  obtain ⟨esp, a0, a1, a2, a3, a4, pk, msg, sig, hsy⟩ := hp
  have eqL : lay s₁ = lay s₂ := by simp only [lay, esp, a0, a1, a2, a3, a4, hsy]
  have tb₂ : TblAt (lay s₁) s₂.mem := eqL.symm ▸ (entry_tbl p₂).1
  have h₂ : Ctx (lay s₁) s₂.gpr s₂.mem (pushed (List.replicate 64 .eax) s₂) := eqL.symm ▸ push_ctx p₂
  have arg₂ : Arguments (lay s₁) s₂.mem := eqL.symm ▸ lay_arguments p₂
  have pk' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).pk.setWidth 64) 32 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 0).setWidth 64) 32 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 0).setWidth 64) 32
    rw [← a0] at pk
    with_reducible exact pk
  have msg' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).msg.setWidth 64) (lay s₁).len.toNat := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 1).setWidth 64) (arg s₁ 2).toNat
    rw [← a1, ← a2] at msg
    with_reducible exact msg
  have sig' : Spec.Ed25519.bytesAt s₁.mem ((lay s₁).sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s₂.mem ((lay s₁).sig.setWidth 64) 64 := by
    change Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 3).setWidth 64) 64 = Spec.Ed25519.bytesAt s₂.mem ((arg s₁ 3).setWidth 64) 64
    rw [← a3] at sig
    with_reducible exact sig
  have sy₁ : (pushed (List.replicate 64 .eax) s₁).syms Impl.Ed25519.X86.bSym = (lay s₁).tbl := by
    rw [show (pushed (List.replicate 64 .eax) s₁).syms = s₁.syms from pushRegs_syms s₁ _]; rfl
  have sy₂ : (pushed (List.replicate 64 .eax) s₂).syms Impl.Ed25519.X86.bSym = (lay s₁).tbl := by
    rw [show (pushed (List.replicate 64 .eax) s₂).syms = s₂.syms from pushRegs_syms s₂ _]; exact hsy.symm
  exact ⟨(body_ct (lay_ok p₁) (lay_arguments p₁) arg₂ (entry_tbl p₁).1 tb₂ pk' msg' sig' _ _ _ _ _ _
    ⟨push_ctx p₁, h₂, ⟨trivial, sy₁⟩, ⟨trivial, sy₂⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyWide : Contract isa := { verifyMessageLocal with
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    let tbl : Region := ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩
    s.rd = [pk, msg, sig, tbl] ∧ s.wr = [scr, args] ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ MsgTbl s }

theorem verifyWide_pre (s : State) (h : verifyWide.pre s) :
    verifyMessageLocal.pre (s.withRegions (verifyRd s) (verifyWr s)) := by
  simp only [verifyMessageLocal, verifyRd, verifyWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_syms]
  exact ⟨True.intro, True.intro, h.2.2⟩

/-- The arguments `0x1000, 0x2000, 64, 0x3000, 0x4000` at `0x8004`, and the static at `0x100000`. -/
def verifySatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 1920 then bSatMem a else
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else
    if a = 0x800c then 0x40 else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else 0

theorem verifySatMem_held : ∀ i < 240,
    verifySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Ed25519.X86.bWords.getD i 0 :=
  fun i hi => by
  rw [← bSatMem_held i hi]
  refine Mem.readW_congr fun j hj => ?_
  have e : (0x100000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000 : Addr).toNat = 8 * i + j := by
    rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [verifySatMem, e, show 8 * i + j < 1920 by omega, ↓reduceIte]

def verifySatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := verifySatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x100000, 1920⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 20⟩]
  syms _ := 0x100000

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

/-- The shared contract's precondition, from its facts (for the witness, whose memory the
contract's tactics must not evaluate). -/
theorem verifyMessage_spec_pre {s : State} (lo : 280 ≤ (s.gpr .esp).toNat)
    (sp : (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32)
    (hrd : s.rd = [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
      ⟨(arg s 3).setWidth 64, 64⟩, ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩])
    (held : ∀ i < 240, s.mem.readW ((s.syms Impl.Ed25519.X86.bSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Ed25519.X86.bWords.getD i 0)
    (fit : (s.syms Impl.Ed25519.X86.bSym).toNat + 1920 ≤ 2 ^ 32)
    (hw : s.wr = [⟨(arg s 4).setWidth 64, 8192⟩, ⟨argAddr s 0, 20⟩])
    (ts : Region.Disjoint ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ta : Region.Disjoint ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩ ⟨argAddr s 0, 20⟩)
    (tr : Region.Disjoint ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩ ⟨(s.gpr .esp).setWidth 64, 4⟩)
    (tk : Region.Disjoint ⟨(s.syms Impl.Ed25519.X86.bSym).setWidth 64, 1920⟩ ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩)
    (hal : ((s.syms Impl.Ed25519.X86.bSym).setWidth 64).toNat % 64 = 0)
    (d0s : Region.Disjoint ⟨(arg s 0).setWidth 64, 32⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (d0a : Region.Disjoint ⟨(arg s 0).setWidth 64, 32⟩ ⟨argAddr s 0, 20⟩)
    (d1s : Region.Disjoint ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (d1a : Region.Disjoint ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ ⟨argAddr s 0, 20⟩)
    (d3s : Region.Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (d3a : Region.Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ⟨argAddr s 0, 20⟩)
    (dsa : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨argAddr s 0, 20⟩)
    (r0 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 32⟩)
    (r1 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩)
    (r3 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 64⟩)
    (r4 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ra : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨argAddr s 0, 20⟩)
    (k0 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩ ⟨(arg s 0).setWidth 64, 32⟩)
    (k1 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩ ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩)
    (k3 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩ ⟨(arg s 3).setWidth 64, 64⟩)
    (k4 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ka : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 280#64, 280⟩ ⟨argAddr s 0, 20⟩)
    (f0 : (arg s 0).toNat + 32 ≤ 2 ^ 32) (f1 : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32)
    (f3 : (arg s 3).toNat + 64 ≤ 2 ^ 32) (f4 : (arg s 4).toNat + 8192 ≤ 2 ^ 32) :
    (Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280).pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, bConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld]
  simp only [bWords_length, Nat.reduceMul]
  refine ⟨lo, sp, by rw [hrd]; rfl, held, fit, fun r hr => ?_, tr, tk, hal, by rw [hrd]; rfl, hw, d0s, d0a, d1s,
    d1a, d3s, d3a, dsa, r0, r1, r3, r4, ra, k0, k1, k3, k4, ka, f0, f1, f3, f4⟩
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [ts, ta]

theorem verifyMessage_sat :
    (Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280).pre verifySatState := by
  have a0 : arg verifySatState 0 = 0x1000 := by decide
  have a1 : arg verifySatState 1 = 0x2000 := by decide
  have a2 : arg verifySatState 2 = 64 := by decide
  have a3 : arg verifySatState 3 = 0x3000 := by decide
  have a4 : arg verifySatState 4 = 0x4000 := by decide
  have e : argAddr verifySatState 0 = 0x8004 := by decide
  have esp : verifySatState.gpr .esp = 0x8000 := rfl
  have sy : verifySatState.syms Impl.Ed25519.X86.bSym = 0x100000 := rfl
  refine verifyMessage_spec_pre ?_ ?_ ?_ (by rw [sy]; exact verifySatMem_held) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [a0, a1, a2, a3, a4, e, esp, sy] <;>
    first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem verifyWide_implies :
    verifyWide.Implies (Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280) where
  pre s h := by
    sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, bConsts_eq,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld] at h
    obtain ⟨lo, sp, hd, held, fit, dw, tr, tk, -, ht, hw, d0s, -, d1s, -, d3s, -, dsa, r0, r1, r3, r4, -,
      k0, k1, k3, k4, -, f0, f1, f3, f4⟩ := h
    simp only [bWords_length, Nat.reduceMul] at hd held fit dw tr tk
    simp only [verifyWide, verifyMessageLocal, MsgTbl]
    refine ⟨?_, hw, d0s, d1s, d3s, dsa.symm, r0, r1, r3, r4, k0, k1, k3, k4, f0, f1, f3, f4, lo,
      by omega, held, fit, dw _ (by rw [hw]; simp), tk.symm, tr.symm⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, bConsts_eq, Abi.withConsts]
    change t.gpr .eax = signWord _ at h
    rw [h, BitVec.setWidth_append_eq_right]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, bConsts_eq,
      Abi.withConsts] at h
    obtain ⟨sp, hsy, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last, hsy⟩
  sat := ⟨verifySatState, verifyMessage_sat⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

theorem verifyMessage_verified :
    Verified X86.target code (Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyMessageLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target code verifyMessageLocal :=
    Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    ?_ ?_ ?_ ?_ hsat) verifyWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyWr, List.mem_singleton] at hr
    subst hr
    simp
  · intro s t _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_mem,
      State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_mem, State.withRegions_syms] using h

end VG.Proof.Ed25519.X86.VerifyMessage
