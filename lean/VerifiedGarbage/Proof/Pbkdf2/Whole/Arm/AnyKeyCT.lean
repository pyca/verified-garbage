module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.AnyKey
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.CT
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# HMAC's `init` for a key of any length on 32-bit ARM: constant time, and in a frame of its own

As for `pbkdf2` (`CT.lean`): the pieces of code between the calls are checked
by the taint analysis (`AnyChecks`, which the kernel evaluates for each hash
function), with the stack argument and the registers holding pointers and
lengths public (`piece`); the calls are related by their contracts
(`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`), whose public arguments are the
same in two runs with the same public arguments (`PubEq`). The only branch,
whether the key is hashed, depends only on `key_len`.

The function that allocates the working space in a frame of its own and
wipes it (`withStackScratchWiped`) is verified against
`VG.Spec.Hmac.initAnyKeyContract` (`anyFramed`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Any

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK count FinArgs init_rel fin_rel)
open VG.Proof.MdStream.Arm (eval_eq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the stack argument and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs 4) c hc).isSome = true

/-- The taint checks of the pieces of `initAny` between its calls. -/
structure AnyChecks (F : Fns) : Prop where
  pro : Ck inRegs (.block F.anyPrologue)
  cmp : Ck kkRegs (.block F.cmpPw)
  hk1 : Ck kkRegs (.block (scrAt .r4 F.stWO))
  hk2 : Ck hkRegs (.block [.mov .r0 (.reg .r4)])
  hk3 : Ck hkRegs (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
    .mov .r2 (.imm 0), .mov .r3 (.imm 0)])
  hk5 : Ck hkRegs (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
    .mov .r3 (.imm 0)]))
  hk7 : Ck krRegs (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)]))
  short : Ck kkRegs (.block [.mov .r2 (.reg .r8), .mov .r3 (.reg .r9)])
  args : Ck krRegs (.block Fns.anyArgs)
  restore : Ck krRegs (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a0.symm
theorem PubEq.keyEq : key s₀' = key s₀ := hq.r2.symm
theorem PubEq.innEq : inn s₀' = inn s₀ := hq.r0.symm
theorem PubEq.outEq : out s₀' = out s₀ := hq.r1.symm
theorem PubEq.klnEq : kln s₀' = kln s₀ := by show (s₀'.gpr .r3).toNat = _; rw [← hq.r3]
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by show scr s₀' + _ = _; rw [hq.scrEq]
theorem PubEq.kpEq : kp F s₀' = kp F s₀ := by
  show (if kln s₀' < F.H.B + 1 then key s₀' else dO s₀' F.hkO) = _
  rw [hq.klnEq, hq.keyEq, hq.dOEq]
theorem PubEq.klEq : kl F s₀' = kl F s₀ := by
  show (if kln s₀' < F.H.B + 1 then kln s₀' else F.H.D) = _
  rw [hq.klnEq]

end

/-- The stack argument lies outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.sp = t.sp) (hwr : s.wr = t.wr) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr, hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.i_a.symm
  · exact h.o_a.symm
  · exact h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- Two states agree on the taint `argTaint rs 4`. -/
theorem agree {rs : List Reg} {s s' : State} (hk : KR F s₀ s) (hk' : KR F s₀' s')
    (hag : ∀ r ∈ rs, s.gpr r = s'.gpr r) : VG.Arm.Taint.Agree (argTaint rs 4) s s' :=
  agree_argTaint hag (by rw [hk.sp, hk'.sp, hq.sp]) (args_out hp hk.sp hk.wr) (args_out hp' hk'.sp hk'.wr)
    (argMem_of (j := 1) (by rw [hk.sp, hk'.sp, hq.sp]) (by rw [hk.sp]; exact hp.spf) fun i hi => by
      obtain rfl : i = 0 := by omega_arith
      rw [hk.stackArg0 hp, hk'.stackArg0 hp', hq.a0])

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree hp hp' hq (hk h) (hk h') (hag s s' h h')) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_kr {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ krRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, hq.innEq]
  · rw [h.r6, h'.r6, hq.outEq]
  · rw [h.r11, h'.r11, hq.scrEq]

omit hp hp' in
theorem ag_kk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') : ∀ r ∈ kkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · rw [h.r8, h'.r8, hq.keyEq]
  · rw [h.r9, h'.r9, hq.r3]
  · exact ag_kr hq h.kr h'.kr _ (by simp)

omit hp hp' in
theorem ag_hk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') (h4 : s.gpr .r4 = dO s₀ F.stWO)
    (h4' : s'.gpr .r4 = dO s₀' F.stWO) : ∀ r ∈ hkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [hkRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h4, h4', hq.dOEq]
  · exact ag_kk hq h h' _ (by simpa using hr)

end

/-! ## The key -/

/-- The key is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ kln t₀

/-- The pieces of hashing the key. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2a (F : Fns) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = key t₀ ∧
    s.gpr .r7 = t₀.gpr .r3 ∧ s.gpr .r10 = scr t₀ ∧ count s = BitVec.ofNat 64 0 ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.hkO ∧ s.gpr .r12 = scr t₀ ∧
    count s = BitVec.ofNat 64 (kln t₀) ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop := KK F t₀ s ∧ s.z = decide (kln t₀ < F.H.B + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : AnyChecks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KK F s₀ s ∧ Long F s₀) ∧ (KK F s₀' s' ∧ Long F s₀')) F.hashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D; have := hz.S; have := hz.reach
  unfold Fns.hashKey Hash.callInit
  have r1 := piece hp hp' hq (fun t₀ s => KK F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1.kr)
    (fun s s' h h' => ag_kk hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1 hz.stWO_lt16) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2a := piece hp hp' hq (Hk1 F) (Hk2a F) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2 h'.1.2) hc.hk2
    (fun _ s h => WP.mono (hk2a_ok h.1.1 h.1.2) fun t ⟨k, d, a⟩ => ⟨⟨k, d, a⟩, h.2⟩)
  have cw : ∀ {t₀ : State}, Pre F t₀ → ∀ {s : State}, KR F t₀ s →
      Covers [⟨State.addr (dO t₀ F.stWO), F.H.S⟩] s.wr := fun {t₀} hp₀ {s} k => by
    rw [dO_addr hp₀ hz.stWO_lt]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp₀ k hz.stWO_S
  have r2 : RelCT isa (fun s s' => Hk2a F s₀ s ∧ Hk2a F s₀' s') (.call F.H.initN F.H.initC)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, _, a⟩, _⟩, ⟨⟨k', _, a'⟩, _⟩⟩ =>
        ⟨a, by rw [a', hq.dOEq], by rw [dO_toNat hp hz.stWO_lt]; have := hp.nsc; omega_arith, cw hp k.kr,
          by have := cw hp' k'.kr; rw [hq.dOEq] at this; exact this⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp hz hF.hH k d a) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp' hz hF.hH k d a) fun t h => ⟨h, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.2 h'.1.2.2) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok k d) fun t ⟨k', d', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', d', a₀, a₁, a₇, a₁₀, c, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨k, _, a₀, a₁, a₇, a₁₀, c, _⟩, _⟩, ⟨⟨k', _, a₀', a₁', a₇', a₁₀', c', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k a₀ a₁ a₇ a₁₀,
          by have := hk4_args hp' hz hF.hH k' a₀' a₁' a₇' a₁₀'; rwa [hq.dOEq, hq.keyEq, hq.scrEq, hq.klnEq] at this,
          by rw [c, c'], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.1 h'.1.2.1) hc.hk5
    (fun hp₀ s ⟨⟨k, d, r⟩, l⟩ => WP.mono (hk5_ok k d hz.hkO_lt16) fun t ⟨k', a₀, a₁, a₁₂, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₁₂, c, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₁₂, c, _⟩, _⟩, ⟨⟨k', a₀', a₁', a₁₂', c', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k a₀ a₁ a₁₂,
          by have := hk6_args hp' hz hF.hH k' a₀' a₁' a₁₂'; rwa [hq.dOEq, hq.dOEq, hq.scrEq] at this,
          by rw [c, c', hq.klnEq], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_kr hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k hz.hkO_lt16 hz.D_lt16) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ kln t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ hz.hkO_lt, m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega_arith)
        (hash_len hF.hH b)])
  exact (r1.seq ((r2a.seq r2).seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ h => h

theorem key_rel :
    RelCT isa (fun s s' => KK F s₀ s ∧ KK F s₀' s') F.key fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := piece hp hp' hq (fun t₀ s => KK F t₀ s) (Cmp F) (fun h => h.kr) (fun s s' h h' => ag_kk hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hz k) fun t ⟨k', z, _⟩ => ⟨k', z⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .eq t = some (decide (kln t₀ < F.H.B + 1)) := by
    intro t₀ t h
    show eval .eq t = _
    rw [eval_eq, h.2]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.klnEq]) ?_ ?_)
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ kln t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1.kr)
      (fun s s' h h' => ag_kk hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = key t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = kln t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ =>
        VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => WP.block_nil
          ⟨(k.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, k.r8, ekp]
      · rw [u₃.gpr, u₂.other _ (by decide), k.r9, ekl, ofNat_toNat32]
      · rw [u₃.mem, u₂.mem, ekp, ekl, k.kr.keyBytes hp₀]
    · have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      exact ⟨⟨h.1.1, this⟩, h.1.2, by rw [hq.klnEq]; exact this⟩
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, by omega_arith⟩, h.1.2.1, by show F.H.B + 1 ≤ kln s₀'; rw [hq.klnEq]; omega_arith⟩

/-- After `anyArgs`. -/
abbrev Ag (hF : FnsOK F) (t₀ t : State) : Prop :=
  Keyed hF t₀ t ∧ t.gpr .r0 = inn t₀ ∧ t.gpr .r1 = out t₀ ∧ t.gpr .r12 = scr t₀

/-- After HMAC's `init`. -/
abbrev Done (hF : FnsOK F) (t₀ t : State) : Prop :=
  KR F t₀ t ∧ hF.hH.SH.Repr t.mem (State.addr (inn t₀)) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr t.mem (State.addr (out t₀)) (xorPad (K0 hF t₀) opad)

include hF in
/-- `initAny` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.hmacInitAny fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KK F s₀) (G' := KK F s₀')
    (argTaint inRegs 4) (fun s s' e e' => by
        subst e e'
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by obtain rfl : i = 0 := by omega_arith
                                                          exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have ra := piece hp hp' hq (Keyed hF) (Ag hF) (fun h => h.kr) (fun s s' h h' => ag_kr hq h.kr h'.kr) hc.args
    (fun _ s h => args_ok hF h)
  have rc : RelCT isa (fun s s' => Ag hF s₀ s ∧ Ag hF s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
      fun s s' => Done hF s₀ s ∧ Done hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := s₀.sp) fun s s' ⟨⟨h, a₀, a₁, a₁₂⟩, ⟨h', a₀', a₁', a₁₂'⟩⟩ =>
        ⟨call_args hp hz hF h a₀ a₁ a₁₂,
          by have := call_args hp' hz hF h' a₀' a₁' a₁₂'
             rwa [hq.innEq, hq.outEq, hq.kpEq, hq.scrEq, hq.klEq] at this,
          h.kr.sp, by rw [h'.kr.sp, hq.sp]⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => call_ok hp hz hF h a₀ a₁ a₁₂)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => call_ok hp' hz hF h a₀ a₁ a₁₂)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Done hF s₀ s ∧ Done hF s₀' s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint krRegs 4)
      (fun s s' h => agree hp hp' hq h.1.1 h.2.1 (ag_kr hq h.1.1 h.2.1)) hr
  unfold Fns.hmacInitAny
  exact pro.seq ((key_rel hp hp' hq hc).seq (ra.seq (rc.seq restore)))

end

/-- The public arguments of the contract. -/
theorem pub_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State}
    (h : (anyScratchContract S W).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `initAny` is verified against `anyScratchContract`, given the taint
checks and a state satisfying it. -/
theorem verified (hF : FnsOK F) (hc : AnyChecks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (anyScratchContract S W).pre s) :
    Verified Arm.target F.hmacInitAny (anyScratchContract S W) := by
  subst hS hW
  exact ⟨fun s hs => correct (pre_of hF hs) hF.sizes hF,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) (pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

/-! ## In a frame of its own, wiped -/

/-- The bytes of `init`'s frame: the saved registers and the working space,
rounded up to a multiple of 32, which an ARM immediate encodes. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := (8 + 8 * I.initAnyKeyScratch + 31) / 32 * 32

/-- `initAny` in a frame holding its working space, which it wipes before
returning: verified against `initAnyKeyContract`, from the locality of its
postcondition (`Proof/Hmac/AnyKey.lean`). -/
theorem anyFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified Arm.target c (anyScratchContract I.S I.initAnyKeyScratch))
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi (24 + anyFrame I)).pre s)
    (hb : Fits 0 (anyFrame I) .u64 I.initAnyKeyScratch := by decide) :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame I) 0 (2 * I.initAnyKeyScratch) c)
      (I.initAnyKeyContract Arm.abi (24 + anyFrame I)) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S Arm.abi.ptrBits) (wa := true) (stack := 24)
    (m := 0) (words := 2 * I.initAnyKeyScratch) h rfl rfl rfl hb
    (by change 4 * (2 * I.initAnyKeyScratch) ≤ I.initAnyKeyScratch * 8; omega_arith)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.initPost_local I.S _) (Hmac.initPostOut_local I.S _ hR hS) hsat rfl

end VG.Proof.Pbkdf2.Whole.Arm.Any
