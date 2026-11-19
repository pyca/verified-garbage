module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecLay
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPkcs1Enc.AArch64.DecD`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecPost`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: after the private-key operation

From the call of the private-key operation to the output, the function
writes only the first `scrBytes` bytes of `scratch`, its slots from `oI` on
and the stack below its frame (`Safe`): through all of it, `Ctx`, the result
`R` in its slot and `EM` in `out` stay as they are (`Post`, `Post.step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (bytesAt_eq)

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

/-- That part. -/
abbrev Lay.SC (L : Lay) : Region := ⟨L.scr, scrBytes⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem Lay.Ok.sc_sub {L : Lay} (hL : L.Ok) : Region.Sub L.SC L.SCR :=
  Region.sub_prefix (by have := hL.s8192; unfold scrBytes; omega_using [this])

/-- What a step after the private-key operation may write. -/
def Safe (L : Lay) (r : Region) : Prop :=
  Region.Sub r L.SC ∨ Region.Sub r L.LOW ∨
    ∃ d, oI ≤ d ∧ d + r.len ≤ frameBytes ∧ r.base = L.Q + BitVec.ofNat 64 d

/-- After the private-key operation: `Ctx`, its result `R` in its slot and
`EM` in `out`. -/
structure Post (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  r : t.mem.readW (L.Q + BitVec.ofNat 64 oR) 64 = R
  em : Spec.Rsa.bytesAt t.mem L.out L.k.toNat = EM

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}
  {t t' : State}

/-- A step that writes only where it may keeps `Post`. -/
theorem Post.step (hL : L.Ok) (hc : Post L g vv m₀ R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) {ws : List Region} (hf : Frame ws t.mem t'.mem)
    (hs : ∀ r ∈ ws, Safe L r) : Post L g vv m₀ R EM t' := by
  have hnQ := hL.nQ
  have hb := hL.bO
  have hcx := hc.ctx
  refine ⟨⟨hrd.trans hcx.rd, hwr.trans hcx.wr, hsp.trans hcx.sp, fun r hr hr' => (hg r hr hr').trans (hcx.cs r hr hr'),
    fun r hr => (hv r hr).trans (hcx.vs r hr), hcx.kept.frame hf fun d hd X hX => ?_,
    hcx.frame.trans (hf.sub fun r hr => ?_)⟩, ?_, ?_⟩
  · rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
    · exact hL.kept_buf hd (.inr (.inr (sub_trans h hL.sc_sub)))
    · exact (hL.fr_low (by unfold keptOff at hd; omega_using [hd])).sub_right h
    · obtain ⟨b, n⟩ := X
      simp only at hb h₂; subst hb
      unfold keptOff at hd; unfold oI at h₁; unfold frameBytes at h₂
      exact hL.fr_sep (by omega_using [hd, h₁, h₂]) (by omega_using [hd]) (by omega_using [h₂])
  · rcases hs r hr with h | h | ⟨d', h₁, h₂, hb⟩
    · exact ⟨L.SCR, by simp, sub_trans h hL.sc_sub⟩
    · exact ⟨L.STK, by simp, sub_trans h Lay.Ok.low_stk⟩
    · obtain ⟨b, n⟩ := r
      simp only at hb h₂; subst hb
      unfold frameBytes at h₂
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega_using [h₂])⟩
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => ?_) (by decide)]
    · exact hc.r
    · rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
      · exact hL.stk_buf (by decide) (.inr (.inr (sub_trans h hL.sc_sub)))
      · exact (hL.fr_low (by decide)).sub_right h
      · obtain ⟨b, n⟩ := X
        simp only at hb h₂; subst hb
        unfold oI at h₁; unfold frameBytes at h₂
        exact hL.fr_sep (by unfold oR; omega_using [h₁]) (by decide) (by omega_using [h₂])
  · rw [← hc.em]
    refine bytesAt_eq fun i hi => hf.bytes (R := L.OUT) (fun X hX => ?_) (by show L.k.toNat ≤ 2 ^ 64; omega_using []) hi
    rcases hs X hX with h | h | ⟨d', h₁, h₂, hb⟩
    · exact hL.oS.sub_right (sub_trans h hL.sc_sub)
    · exact hL.kO.symm.sub_right (sub_trans h Lay.Ok.low_stk)
    · obtain ⟨b, n⟩ := X
      simp only at hb h₂; subst hb
      unfold frameBytes at h₂
      exact (hL.kO.sub_left (Lay.Ok.sub_stk (by omega_using [h₂]))).symm

/-- Code that changes only registers but the callee-saved ones keeps `Post`. -/
theorem Post.regs (hc : Post L g vv m₀ R EM t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) :
    Post L g vv m₀ R EM t' :=
  ⟨hc.ctx.regs hrd hwr hsp hm hv hg, by rw [hm]; exact hc.r, by rw [hm]; exact hc.em⟩

/-- What a call leaves, for writes in `scratch` (and the 16 bytes below the frame). -/
theorem Post.after (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : Proof.Pbkdf2.Md.AArch64.Calls.After t ws t') (hs : ∀ r ∈ ws, Region.Sub r L.SC) :
    Post L g vv m₀ R EM t' :=
  hc.step hL h.rd h.wr h.sp h.vec h.cs h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (hs r hr)
    · rw [List.mem_singleton.mp hr, hc.ctx.sp]
      exact .inr (.inl (Offset.sub_below _ hP (by have := hL.pQ; omega_using [hP])))

end

/-! ## Ranges of `scratch` -/

section
variable {L : Lay}

/-- `scratch + a`. -/
abbrev scA (L : Lay) (a : Nat) : Addr := L.scr + BitVec.ofNat 64 a

theorem scD (hL : L.Ok) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint ⟨scA L a, n⟩ ⟨scA L b, m⟩ :=
  Offset.disjoint L.scr h (by have := hL.bS; have := hL.s8192; unfold scrBytes at ha; omega_using [ha])
    (by have := hL.bS; have := hL.s8192; unfold scrBytes at hb; omega_using [hb])

theorem scSub {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA L a, n⟩ L.SC :=
  Offset.sub_base _ ha

/-- The 16 bytes below the frame miss `scratch`. -/
theorem stkD (hL : L.Ok) (hP : 16 ≤ L.P) {a m : Nat} (ha : a + m ≤ scrBytes) :
    (below L.Q 16).Disjoint ⟨scA L a, m⟩ :=
  (hL.kS.sub_left (sub_trans (Offset.sub_below _ hP (by have := hL.pQ; omega_using [hP])) Lay.Ok.low_stk)).sub_right
    (sub_trans (scSub ha) hL.sc_sub)

theorem scCov (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {a n : Nat} (ha : a + n ≤ scrBytes) : Covers [⟨scA L a, n⟩] t.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨L.SCR, by rw [hc.wr]; simp, a, rfl, by
      have := hL.s8192; unfold scrBytes at ha; dsimp only; omega_using [ha, this]⟩

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-! ### `RsaPkcs1Enc.AArch64.DecPriv`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.AArch64.DecEntry`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: entering the frames

The layout of a call (`lay`), what the shared contract says of it
(`lay_ok`), and the first block (`setup`), run from the state in which the
inner frame's body starts (`entered`): it saves our register arguments to
their slots (`Spill.save_wp`), moves our stack arguments to theirs and to the
private-key operation's (`moves_ok`), and sets the call's registers,
establishing `Ctx` (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (add_add read8 write8 toNat_sub_k)

/-- The shared contract, with `P + 240` bytes of stack. -/
abbrev decSpec (P : Nat) : Contract isa := Spec.RsaPkcs1Enc.decryptContract AArch64.abi (P + 240)

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
def lay (P : Nat) (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13,
    stackArg s 14, s.sp - BitVec.ofNat 64 240, P, [], 0, 0⟩

/-- The layout of a call that may also read `X`, with `pre` and `pre_len`. -/
def layW (P : Nat) (s : State) (X : List Region) (pre : Addr := 0) (prl : BitVec 64 := 0) : Lay :=
  { lay P s with X := X, pre := pre, prl := prl }

theorem Lay.Ok.withX {L : Lay} (h : L.Ok) (X : List Region) (pre : Addr) (prl : BitVec 64) :
    ({ L with X := X, pre := pre, prl := prl } : Lay).Ok := { h with }

theorem lay_Q (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 240 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 240 = stackArgAddr s 0 := by
  rw [lay_Q, stackArgAddr]; exact (BitVec.add_zero _).symm

theorem lay_stk (P : Nat) (s : State) :
    (lay P s).Q - BitVec.ofNat 64 P = s.sp - BitVec.ofNat 64 (P + 240) := by
  simp only [lay]
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, Nat.add_comm 240 P]

theorem forall_ro {L : Lay} {F : Region → Prop}
    (h : F L.N ∧ F L.E ∧ F L.D ∧ F L.INP ∧ F L.PP ∧ F L.QQ ∧ F L.DP ∧ F L.DQ ∧ F L.QI) : ∀ R ∈ L.ro, F R := by
  intro R hR
  simp only [Lay.ro, List.mem_cons, List.not_mem_nil, or_false] at hR
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem lay_ok {P : Nat} {s : State} (h : (decSpec P).pre s) : (lay P s).Ok := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  sig_split h
  rename_i hsp hsp2 _ _ oM oN oE oD oI oP oQ oDP oDQ oQI oS oA mN mE mD mI mP mQ mDP mDQ mQI mS mA nS eS dS iS
    pS qS dpS dqS qiS sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS _ bO bM bN bE bD bI bP bQ bDP bDQ bQI bS kv
    hk1 hk2 el1 elk dl1 dlk pl1 plk ql1 qlk hdp hqi hdq
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oD oI oP oQ oDP oDQ oQI oS oM mI mDP mDQ mQI iS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kI kDP kDQ kQI bO bI bDP bDQ bQI
  obtain eA : (lay P s).ARGS = ⟨stackArgAddr s 0, 120⟩ := by simp only [Lay.ARGS, lay_args]
  obtain eK : (lay P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 240⟩ : Region) = _
    rw [lay_stk]
  obtain hQ : (lay P s).Q.toNat = s.sp.toNat - 240 := toNat_sub_k (by omega_arith)
  refine ⟨oM, oS, mS, forall_ro ⟨oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI⟩,
    forall_ro ⟨mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI⟩,
    forall_ro ⟨nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm⟩, eA ▸ oA, eA ▸ mA,
    eA ▸ sA, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kD, eK ▸ kI, eK ▸ kP, eK ▸ kQ, eK ▸ kDP,
    eK ▸ kDQ, eK ▸ kQI⟩, bO, bM, bS, forall_ro ⟨bN, bE, bD, bI, bP, bQ, bDP, bDQ, bQI⟩, by omega_arith,
    by simp only [lay] at hQ ⊢; omega_arith, kv, hk1, hk2, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, hdp, hqi, hdq, h⟩

/-! ## Moving the stack arguments -/

/-- The memory after moving the word at `B + arg j` (as in `m₀`) to `B + d`
for each `(j, d)`, in order. -/
def moveMem (m : Mem) (B : Addr) (m₀ : Mem) : List (Nat × Nat) → Mem
  | [] => m
  | (j, d) :: l => moveMem (m.writeW (B + BitVec.ofNat 64 d) (m₀.readW (B + BitVec.ofNat 64 (arg j)) 64)) B m₀ l

/-- The moves' destinations are words of the frame, and their sources our
stack arguments. -/
def MoveOk (l : List (Nat × Nat)) : Prop := ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 + 8 ≤ frameBytes ∧ p.1 < 15

instance (l : List (Nat × Nat)) : Decidable (MoveOk l) := by unfold MoveOk; infer_instance

theorem moveMem_frame {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) : Frame [⟨B, frameBytes⟩] m (moveMem m B m₀ l) := by
  suffices h : ∀ m', Frame [⟨B, frameBytes⟩] m m' → Frame [⟨B, frameBytes⟩] m (moveMem m' B m₀ l) from
    h m (Frame.refl _ _)
  induction l with
  | nil => exact fun _ h => h
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro m' h
    obtain hd := hl (j, d) List.mem_cons_self
    have hd2 : d + 8 ≤ 224 := hd.2.1
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      (h.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold frameBytes; omega_arith) (by omega_arith)))

theorem moveMem_read {l : List (Nat × Nat)} (hl : MoveOk l) {B : Addr} (m m₀ : Mem) {a : Nat} (ha : ∀ p ∈ l, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2) (ha' : a + 8 ≤ 360) :
    (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 a) 64 = m.readW (B + BitVec.ofNat 64 a) 64 := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    obtain hd := hl (j, d) List.mem_cons_self
    rw [moveMem, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ (fun q hq => ha q (List.mem_cons_of_mem _ hq)),
      Mem.readW_writeW_sep (Offset.sep _ (by have := ha (j, d) List.mem_cons_self; dsimp only at this; omega_arith)
        (by omega_arith) (by unfold frameBytes at hd; omega_arith)) (by decide)]

theorem moveMem_moved {l : List (Nat × Nat)} (hl : MoveOk l) (hn : (l.map Prod.snd).Nodup) {B : Addr}
    (m m₀ : Mem) :
    ∀ p ∈ l, (moveMem m B m₀ l).readW (B + BitVec.ofNat 64 p.2) 64 = m₀.readW (B + BitVec.ofNat 64 (arg p.1)) 64 := by
  induction l generalizing m with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hd := hl (j, d) List.mem_cons_self
      obtain hne : ∀ q ∈ l, q.2 ≠ d := fun q hq e =>
        (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨q, hq, e⟩)
      rw [moveMem, moveMem_read (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ (fun q hq => by
        have := hl q (List.mem_cons_of_mem _ hq); have := hne q hq
        obtain h8 : q.2 % 8 = 0 := (hl q (List.mem_cons_of_mem _ hq)).1
        have h8' : d % 8 = 0 := hd.1
        omega_arith) (by unfold frameBytes at hd; dsimp only; omega_arith), Mem.readW_writeW_self64]
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hn).2 _ q hq

/-- After the moves, from `t`. -/
structure Moved (t u : State) (l : List (Nat × Nat)) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = moveMem t.mem t.sp t.mem l
  other : ∀ r, r ≠ .x10 → u.gpr r = t.gpr r

/-- One move. -/
theorem mv_step {u : State} {j d : Nat} (ho : arg j % 8 = 0 ∧ arg j < 32768) (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (arg j)) 8)
    (hw : InRegions u.wr (u.gpr .x9 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (mvArg j d)) u fun u₁ => u₁.rd = u.rd ∧ u₁.wr = u.wr ∧ u₁.sp = u.sp ∧ u₁.v = u.v ∧
      u₁.mem = u.mem.writeW (u.gpr .x9 + BitVec.ofNat 64 d) (u.mem.readW (u.sp + BitVec.ofNat 64 (arg j)) 64) ∧
      ∀ r, r ≠ .x10 → u₁.gpr r = u.gpr r := by
  apply WP.of_runBlock
  rw [mvArg, runBlock_cons, Bytes.exec_ldrSp ho hr, runStep_some, runBlock_cons,
    exec_str_x hd (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact hw),
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩
  show (u.mem.writeW _ _) = _
  rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]

theorem moves_ok {l : List (Nat × Nat)} (hl : MoveOk l) {t : State} (h9 : t.gpr .x9 = t.sp)
    (hw : ∀ p ∈ l, InRegions t.wr (t.sp + BitVec.ofNat 64 p.2) 8)
    (hr : ∀ p ∈ l, InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) :
    WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) t fun u => Moved t u l := by
  suffices h : ∀ (l : List (Nat × Nat)), MoveOk l → ∀ (u : State), u.gpr .x9 = t.sp → u.sp = t.sp →
      u.rd = t.rd → u.wr = t.wr →
      (∀ p ∈ l, u.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64 = t.mem.readW (t.sp + BitVec.ofNat 64 (arg p.1)) 64) →
      (∀ p ∈ l, InRegions u.wr (t.sp + BitVec.ofNat 64 p.2) 8) →
      (∀ p ∈ l, InRegions (u.rd ++ u.wr) (t.sp + BitVec.ofNat 64 (arg p.1)) 8) →
      WP isa (.block (l.flatMap fun p => mvArg p.1 p.2)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
        u'.sp = u.sp ∧ u'.v = u.v ∧ u'.mem = moveMem u.mem t.sp t.mem l ∧ ∀ r, r ≠ .x10 → u'.gpr r = u.gpr r by
    exact WP.mono (h l hl t h9 rfl rfl rfl (fun _ _ => rfl) hw hr) fun u ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩
  intro l
  induction l with
  | nil => exact fun _ u _ _ _ _ _ _ _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons p l ih =>
    obtain ⟨j, d⟩ := p
    intro hl u h9 hsp hrd hwr hsrc hw hr
    obtain hd := hl (j, d) List.mem_cons_self
    obtain hw₀ := hw (j, d) List.mem_cons_self
    obtain hr₀ := hr (j, d) List.mem_cons_self
    obtain hs₀ := hsrc (j, d) List.mem_cons_self
    dsimp only at hd hw₀ hr₀ hs₀
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ho : arg j % 8 = 0 ∧ arg j < 32768 := by unfold arg frameBytes; omega_arith
    obtain hd' : d % 8 = 0 ∧ d < 32768 := ⟨hd.1, by unfold frameBytes at hd; omega_arith⟩
    refine WP.mono (mv_step ho hd' (by rw [hsp]; exact hr₀) (by rw [h9]; exact hw₀))
      fun u₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
    obtain e₁ : ∀ a, a < 15 → u₁.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 =
        u.mem.readW (t.sp + BitVec.ofNat 64 (arg a)) 64 := fun a ha => by
      rw [m₁, h9]
      exact Mem.readW_writeW_sep (Offset.sep _ (by unfold arg frameBytes at *; omega_arith)
        (by unfold arg frameBytes; omega_arith) (by unfold frameBytes at hd; omega_arith)) (by decide)
    refine WP.mono (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) u₁
      (by rw [g₁ .x9 (by decide), h9]) (s₁.trans hsp) (r₁.trans hrd) (w₁.trans hwr)
      (fun q hq => (e₁ q.1 (hl q (List.mem_cons_of_mem _ hq)).2.2).trans (hsrc q (List.mem_cons_of_mem _ hq)))
      (fun q hq => by rw [w₁]; exact hw q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [r₁, w₁]; exact hr q (List.mem_cons_of_mem _ hq)))
      fun u' ⟨a, b, c, e, f, g⟩ => ⟨a.trans r₁, b.trans w₁, c.trans s₁, e.trans v₁, ?_, fun r hr =>
        (g r hr).trans (g₁ r hr)⟩
    rw [f, m₁, moveMem, h9, hsp, hs₀]

/-! ## The setup -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (P : Nat) (s : State) : (entered s).sp = (lay P s).Q := by
  show s.sp - 16 - BitVec.ofNat 64 224 = s.sp - BitVec.ofNat 64 240
  rw [BitVec.sub_sub]; rfl

theorem lr_slot (P : Nat) (s : State) : s.sp - 16 = (lay P s).Q + BitVec.ofNat 64 224 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 240 + BitVec.ofNat 64 224
  bv_omega

theorem entered_wr (P : Nat) (s : State) :
    (entered s).wr = (lay P s).FR :: (lay P s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 224, 224⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 224 = (lay P s).Q from entered_sp P s, lr_slot P]
  rfl

theorem entered_mem (P : Nat) (s : State) :
    (entered s).mem = s.mem.writeW ((lay P s).Q + BitVec.ofNat 64 224) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot P, write8]

theorem ourArg_lay (P : Nat) (s : State) : ∀ j, j < 15 → ourArg (lay P s) j = stackArg s j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl

theorem saves_eq : saves = ([.addSp .x9 0] : List Instr) ++ Spill.saveCode .x9
    [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] := rfl

/-- The call's registers once the slots are written. -/
structure Ready (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.inp
  x7 : t.gpr .x7 = L.k

theorem privRegs_ok {t : State} (ha : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (arg 1)) 8) :
    WP isa (.block privRegs) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x0 = t.gpr .x0 ∧ u.gpr .x1 = t.gpr .x4 ∧ u.gpr .x2 = t.gpr .x3 ∧ u.gpr .x3 = t.gpr .x4 ∧
      u.gpr .x4 = t.gpr .x5 ∧ u.gpr .x5 = t.gpr .x6 ∧ u.gpr .x6 = t.mem.readW (t.sp + BitVec.ofNat 64 (arg 1)) 64 ∧
      u.gpr .x7 = t.gpr .x4 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  have ha' : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 248) 8 := ha
  show WP isa (.block privRegs) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x0 = t.gpr .x0 ∧ u.gpr .x1 = t.gpr .x4 ∧ u.gpr .x2 = t.gpr .x3 ∧ u.gpr .x3 = t.gpr .x4 ∧
      u.gpr .x4 = t.gpr .x5 ∧ u.gpr .x5 = t.gpr .x6 ∧ u.gpr .x6 = t.mem.readW (t.sp + BitVec.ofNat 64 248) 64 ∧
      u.gpr .x7 = t.gpr .x4 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r
  apply WP.of_runBlock
  simp only [privRegs, mov, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    Size.bits, BitVec.setWidth_eq, BitVec.or_self, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, ha',
    read8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
         simp only [RegUpd.gpr_write, reduceCtorEq, ite_false])
    | simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]

/-- The regions the contract grants. -/
theorem spec_rdwr {P : Nat} {s : State} (h : (decSpec P).pre s) :
    s.rd = [(lay P s).N, (lay P s).E, (lay P s).D, (lay P s).INP, (lay P s).PP, (lay P s).QQ, (lay P s).DP,
      (lay P s).DQ, (lay P s).QI, (lay P s).ARGS] ∧ s.wr = [(lay P s).OUT, (lay P s).ML, (lay P s).SCR] := by
  obtain hL := lay_ok h
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  obtain ⟨-, -, hrd, hwr, -⟩ := h
  have hk1 : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
  have hk2 : (stackArg s 2).toNat = (s.gpr .x4).toNat := hL.ilk
  have hdp : (stackArg s 8).toNat = (stackArg s 4).toNat := hL.dpl
  have hqi : (stackArg s 12).toNat = (stackArg s 4).toNat := hL.qil
  have hdq : (stackArg s 10).toNat = (stackArg s 6).toNat := hL.dql
  rw [hrd, hwr, hk1, hk2, hdp, hqi, hdq, ← lay_args P]
  exact ⟨rfl, rfl⟩

theorem argMoves_ok : MoveOk argMoves := by decide

theorem argMoves_nodup : (argMoves.map Prod.snd).Nodup := by decide

theorem mem_argMoves {j : Nat} (hj : j < 12) : (j + 3, 8 * j) ∈ argMoves :=
  List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The saves' slots are not the moves'. -/
theorem argMoves_apart {a : Nat} (ha : a ∈ [oOut, oML, oN, oK, oE, oEl, oD]) :
    ∀ p ∈ argMoves, p.2 + 8 ≤ a ∨ a + 8 ≤ p.2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem entry_ok {P : Nat} {s : State} (h : (decSpec P).pre s) :
    WP isa (.block setup) (entered s) fun t => Ctx (lay P s) s.gpr s.v s.mem t ∧ Ready (lay P s) t := by
  obtain hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ : P ≤ (lay P s).Q.toNat := hL.pQ
  obtain ⟨hrd, hwr⟩ := spec_rdwr h
  obtain hfr : ∀ (u : State) d n, u.wr = (entered s).wr → d + n ≤ frameBytes →
      InRegions u.wr ((lay P s).Q + BitVec.ofNat 64 d) n :=
    fun u d n hu hd => ⟨(lay P s).FR, by rw [hu, entered_wr P]; simp,
      Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)⟩
  obtain harg : ∀ (u : State) d, u.rd = s.rd → 240 ≤ d → d + 8 ≤ 360 →
      InRegions (u.rd ++ u.wr) ((lay P s).Q + BitVec.ofNat 64 d) 8 :=
    fun u d hu h₁ h₂ => ⟨(lay P s).ARGS, by rw [hu, hrd]; simp, Offset.contains _ h₁ (by omega_arith) (by omega_arith)⟩
  obtain eLr : (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 224) 64 = s.gpr .x30 := by
    rw [entered_mem P, Mem.readW_writeW_self64]
  obtain eArg : ∀ j, j < 15 → (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 (240 + 8 * j)) 64 =
      stackArg s j := by
    intro j hj
    rw [entered_mem P, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      stackArg, stackArgAddr, ← lay_Q P s, add_add]
  obtain eFr : Frame [(lay P s).STK] s.mem (entered s).mem := by
    rw [entered_mem P]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 240⟩ : Region).Contains
      ((lay P s).Q + BitVec.ofNat 64 224) (64 / 8)
    rw [Enc.q_add (lay P s).Q P 224]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [setup, saves_eq, List.append_assoc, WP.block_append_iff]
  -- `x9 = sp`.
  obtain h0 : WP isa (.block [.addSp .x9 0]) (entered s) fun t₀ => t₀ = (entered s).write .x .x9 (lay P s).Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, entered_sp P,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  obtain h9 : ((entered s).write .x .x9 (lay P s).Q).gpr .x9 = (lay P s).Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) (fun p hp => ?_)) fun t₂ hs => ?_
  · rw [h9]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfr _ _ _ (RegUpd.wr_write ..) (by decide)
  obtain hsp₂ : t₂.sp = (lay P s).Q := hs.sp.trans ((RegUpd.sp_write ..).trans (entered_sp P s))
  obtain hrd₂ : t₂.rd = s.rd := hs.rd.trans (RegUpd.rd_write ..)
  obtain hwr₂ : t₂.wr = (entered s).wr := hs.wr.trans (RegUpd.wr_write ..)
  rw [WP.block_append_iff]
  refine WP.mono (moves_ok argMoves_ok (t := t₂) (by rw [hs.gpr, h9, hsp₂])
    (fun p hp => by rw [hsp₂]; exact hfr _ _ _ hwr₂ (argMoves_ok p hp).2.1)
    (fun p hp => by
      have := (argMoves_ok p hp).2.2
      rw [hsp₂]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega_arith) (by unfold arg frameBytes; omega_arith)))
    fun t₃ hm => ?_
  obtain hsp₃ : t₃.sp = (lay P s).Q := hm.sp.trans hsp₂
  refine WP.mono (privRegs_ok (t := t₃) (by
    rw [hsp₃, hm.rd, hm.wr]; exact harg _ _ hrd₂ (by unfold arg frameBytes; omega_arith)
      (by unfold arg frameBytes; omega_arith))) fun u hu => ?_
  obtain ⟨urd, uwr, usp, uv, um, u0, u1, u2, u3, u4, u5, u6, u7, upr⟩ := hu
  -- The memory.
  obtain M2 : t₂.mem = Spill.saveMem (entered s).mem (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr
      [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] := by
    rw [hs.mem, h9, RegUpd.mem_write]
  obtain F2 : Frame [⟨(lay P s).Q, 168⟩] (entered s).mem t₂.mem := by
    rw [M2]
    exact Spill.saveMem_frame_base (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) _ _ _
  obtain S2 : Spill.Saved (lay P s).Q ((entered s).write .x .x9 (lay P s).Q).gpr
      [(.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] t₂.mem := by
    rw [M2]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain U : u.mem = moveMem t₂.mem (lay P s).Q t₂.mem argMoves := by rw [um, hm.mem, hsp₂]
  obtain hi₂ : ∀ d, 168 ≤ d → d + 8 ≤ 360 → t₂.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 =
      (entered s).mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    F2.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  -- Our stack arguments, unchanged.
  obtain uArg : ∀ j, j < 15 → u.mem.readW ((lay P s).Q + BitVec.ofNat 64 (240 + 8 * j)) 64 = stackArg s j := by
    intro j hj
    rw [U, moveMem_read argMoves_ok _ _ (fun p hp => by
      have := (argMoves_ok p hp).2.1; unfold frameBytes at this; omega_arith) (by omega_arith),
      hi₂ _ (by omega_arith) (by omega_arith), eArg j hj]
  obtain uMv : ∀ p ∈ argMoves, u.mem.readW ((lay P s).Q + BitVec.ofNat 64 p.2) 64 = stackArg s p.1 := by
    intro p hp
    have := (argMoves_ok p hp).2.2
    rw [U, moveMem_moved argMoves_ok argMoves_nodup _ _ p hp, show arg p.1 = 240 + 8 * p.1 from rfl,
      hi₂ _ (by omega_arith) (by omega_arith), eArg _ this]
  obtain uSv : ∀ r d, (r, d) ∈ [(Reg.x0, oOut), (.x2, oML), (.x3, oN), (.x4, oK), (.x5, oE), (.x6, oEl), (.x7, oD)] →
      u.mem.readW ((lay P s).Q + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hrd
    rw [U, moveMem_read argMoves_ok _ _ (argMoves_apart (List.mem_map_of_mem (f := Prod.snd) hrd))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
          rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> (dsimp only; decide)),
      S2 (r, d) hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
    rcases hrd with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact RegUpd.gpr_write_of_ne _ _ _ (by dsimp only; decide)
  obtain F : Frame [⟨(lay P s).Q, 224⟩] (entered s).mem u.mem := by
    rw [U]
    refine Frame.trans (F2.sub fun r hr => ?_) ((moveMem_frame argMoves_ok _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold frameBytes; omega_arith)⟩
  obtain go : ∀ r, r ≠ .x9 → r ≠ .x10 → t₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [hm.other r h₂, hs.gpr]; exact RegUpd.gpr_write_of_ne _ _ _ h₁
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [urd, hm.rd, hrd₂, hrd]; exact (List.append_nil _).symm
  · rw [uwr, hm.wr, hwr₂, entered_wr P, hwr]
  · rw [usp, hsp₃]
  · intro r hr _
    rw [upr r hr, go r (Enc.preserved_ne hr (by decide)) (Enc.preserved_ne hr (by decide))]
  · intro r _
    rw [uv, hm.v, hs.v, RegUpd.v_write, entered_v]
  · intro j hj
    rw [uMv _ (mem_argMoves hj), ourArg_lay P s (j + 3) (by omega_arith)]
  · exact uSv .x0 oOut (by simp)
  · exact uSv .x2 oML (by simp)
  · exact uSv .x3 oN (by simp)
  · exact uSv .x4 oK (by simp)
  · exact uSv .x5 oE (by simp)
  · exact uSv .x6 oEl (by simp)
  · exact uSv .x7 oD (by simp)
  · exact uMv (0, oDl) (by decide)
  · exact uMv (1, oIn) (by decide)
  · exact uMv (13, oScr) (by decide)
  · rw [U, moveMem_read argMoves_ok _ _ (by decide) (by omega_arith), hi₂ 224 (by omega_arith) (by omega_arith), eLr]
  · intro j hj
    rw [uArg j hj, ourArg_lay P s j hj]
  · have hk : (lay P s).STK ∈ [(lay P s).OUT, (lay P s).ML, (lay P s).SCR, (lay P s).STK] := by simp
    refine Frame.trans (eFr.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact hk) (F.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    obtain h224 := Lay.Ok.sub_stk (L := lay P s) (d := 0) (n := 224) (by omega_arith)
    rw [show (lay P s).Q + BitVec.ofNat 64 0 = (lay P s).Q from BitVec.add_zero _] at h224
    exact ⟨(lay P s).STK, hk, h224⟩
  · rw [u0]; exact go .x0 (by decide) (by decide)
  · rw [u1]; exact go .x4 (by decide) (by decide)
  · rw [u2]; exact go .x3 (by decide) (by decide)
  · rw [u3]; exact go .x4 (by decide) (by decide)
  · rw [u4]; exact go .x5 (by decide) (by decide)
  · rw [u5]; exact go .x6 (by decide) (by decide)
  · rw [u6, ← um, hsp₃]; exact uArg 1 (by decide)
  · rw [u7]; exact go .x4 (by decide) (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the private-key operation

Once `setup` has run (`Ready`), `priv_pre'` is the precondition of
`vg_rsa_private_checked` on the call's entry, which it is given `n`, `e`,
the input, the key's factors and its stack arguments (the frame's first 96
bytes) to read and `out` and `scratch` to write; and `priv_call` runs it:
`Ctx` holds again, and `out` holds `EM` (or zeros) as `privOut` says.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq)

theorem ro_N (L : Lay) : L.N ∈ L.ro := List.mem_cons_self ..
theorem ro_E (L : Lay) : L.E ∈ L.ro := List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem ro_D (L : Lay) : L.D ∈ L.ro := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem ro_INP (L : Lay) : L.INP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem ro_PP (L : Lay) : L.PP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
theorem ro_QQ (L : Lay) : L.QQ ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
theorem ro_DP (L : Lay) : L.DP ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
theorem ro_DQ (L : Lay) : L.DQ ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
theorem ro_QI (L : Lay) : L.QI ∈ L.ro :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))))))

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

/-- A byte of a buffer the function only reads, as on entry. -/
theorem byte_ro {R : Region} (hR : R ∈ L.ro) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [(hL.oR R hR).symm, (hL.mR R hR).symm, (hL.sR R hR).symm, (hL.kR R hR).symm])
    (by have := hL.bR R hR; omega_arith) hi

/-- The bytes of a buffer the function only reads, as on entry. -/
theorem bytes_ro {R : Region} (hR : R ∈ L.ro) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m₀ R.base R.len :=
  bytesAt_eq fun _ hi => hc.byte_ro hL hR hi

end Ctx

/-- The regions the call reads and writes. -/
abbrev privRd (L : Lay) : List Region :=
  [L.N, L.E, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.Q + BitVec.ofNat 64 0, 96⟩]
abbrev privWr (L : Lay) : List Region := [L.OUT, L.SCR]

/-- What the private-key operation gives, from the buffers on entry. -/
def privOut (L : Lay) (m₀ : Mem) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
    (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.dp L.pl.toNat)
    (Spec.Rsa.bytesAt m₀ L.dq L.ql.toNat) (Spec.Rsa.bytesAt m₀ L.qi L.pl.toNat)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- The call's stack arguments are the frame's first twelve words. -/
theorem priv_args (hc : Ctx L g vv m₀ t) (rd wr : List Region) :
    stackArg (t.callEntry.withRegions rd wr) 0 = L.p ∧ stackArg (t.callEntry.withRegions rd wr) 1 = L.pl ∧
    stackArg (t.callEntry.withRegions rd wr) 2 = L.q ∧ stackArg (t.callEntry.withRegions rd wr) 3 = L.ql ∧
    stackArg (t.callEntry.withRegions rd wr) 4 = L.dp ∧ stackArg (t.callEntry.withRegions rd wr) 5 = L.dpl ∧
    stackArg (t.callEntry.withRegions rd wr) 6 = L.dq ∧ stackArg (t.callEntry.withRegions rd wr) 7 = L.dql ∧
    stackArg (t.callEntry.withRegions rd wr) 8 = L.qi ∧ stackArg (t.callEntry.withRegions rd wr) 9 = L.qil ∧
    stackArg (t.callEntry.withRegions rd wr) 10 = L.scr ∧ stackArg (t.callEntry.withRegions rd wr) 11 = L.sl := by
  simp only [stackArg_ce, hc.sp]
  exact ⟨hc.kept.call 0 (by decide), hc.kept.call 1 (by decide), hc.kept.call 2 (by decide),
    hc.kept.call 3 (by decide), hc.kept.call 4 (by decide), hc.kept.call 5 (by decide),
    hc.kept.call 6 (by decide), hc.kept.call 7 (by decide), hc.kept.call 8 (by decide),
    hc.kept.call 9 (by decide), hc.kept.call 10 (by decide), hc.kept.call 11 (by decide)⟩

theorem priv_pre' (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    (privK S).pre (t.callEntry.withRegions (privRd L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := priv_args hc (privRd L) (privWr L)
  obtain aa : stackArgAddr (t.callEntry.withRegions (privRd L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  obtain arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 96⟩ L.STK := Lay.Ok.sub_stk (by omega_arith)
  obtain lS := Lay.Ok.low_stk (L := L)
  simp only [privK, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    aa, hlow, hL.dpl, hL.qil, hL.dql]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
    hL.oR _ (ro_N L), hL.oR _ (ro_E L), hL.oR _ (ro_INP L), hL.oR _ (ro_PP L), hL.oR _ (ro_QQ L),
    hL.oR _ (ro_DP L), hL.oR _ (ro_DQ L), hL.oR _ (ro_QI L), hL.oS, (hL.kO.sub_left arS).symm,
    (hL.sR _ (ro_N L)).symm, (hL.sR _ (ro_E L)).symm, (hL.sR _ (ro_INP L)).symm, (hL.sR _ (ro_PP L)).symm,
    (hL.sR _ (ro_QQ L)).symm, (hL.sR _ (ro_DP L)).symm, (hL.sR _ (ro_DQ L)).symm, (hL.sR _ (ro_QI L)).symm,
    (hL.kS.sub_left arS).symm,
    hL.kO.sub_left lS, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_INP L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    hL.kS.sub_left lS, (hL.fr_low (by omega_arith)).symm,
    hL.bO, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_INP L), hL.bR _ (ro_PP L), hL.bR _ (ro_QQ L),
    hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L), hL.bS,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial, hL.slk⟩

theorem covers_priv (hc : Ctx L g vv m₀ t) :
    Covers (privRd L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  rw [hc.rd, hc.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.INP, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 96 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩

/-- After the call. -/
structure Called (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  out : Spec.Rsa.writtenOutcome t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32) (privOut L m₀)

theorem priv_call (v : PrivImpl) (hL : L.Ok) (hP : L.P = v.S + 1) (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    WP isa (.call v.name v.code) t (Called L g vv m₀) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_priv hc
  refine WP.callFV v.correct (priv_pre' hL hP hc hr) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  -- What the call may change: `out`, `scratch` and the stack below the frame.
  obtain hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega_arith)
  obtain hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl fun _ h => h)
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  obtain hkept : ∀ d, keptOff d → ∀ R ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with (hs | hs) | hs
    · exact hL.kept_buf hd (.inl hs)
    · exact hL.kept_buf hd (.inr (.inr hs))
    · exact (hL.fr_low (by unfold keptOff at hd; omega_arith)).sub_right hs
  obtain hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with (hs | hs) | hs
        · exact ⟨L.OUT, by simp, hs⟩
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, -, -, -⟩ := priv_args hc (privRd L) (privWr L)
  have hp := hpost
  simp only [privK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_INP L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `D = I2OSP(d, k)`

The result of the private-key operation to its slot (`dPtrs₁`), `k` zeros at
`scratch + sD` (`zeroLoop`), and `d` copied to their end (`dPtrs₂`,
`copyLoop`): `dBuild_ok`, from `Called` to `DB`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (bytesAt_eq add_add)

/-- The result's 32 bits, zero-extended. -/
def rOf (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem dPtrs₁_ok {t : State} {Q : Addr} (hsp : t.sp = Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 192) 8) (h1 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 184) 8)
    (h2 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 136) 8) :
    WP isa (.block dPtrs₁) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0)) ∧
      u.gpr .x11 = (t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (Q + BitVec.ofNat 64 oScr) 64 +
        BitVec.ofNat 64 sD ∧
      u.gpr .x12 = (t.mem.writeW (Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (Q + BitVec.ofNat 64 oK) 64 ∧
      u.gpr .x13 = 0 ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [dPtrs₁, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, BitVec.or_self,
    Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, hsp, BitVec.add_zero, oR, oScr, oK, sD,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq,
    ite_false, hw, h1, h2]
  refine ⟨trivial, trivial, trivial, trivial, rfl, rfl, rfl, by decide, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_false]

/-- After `j` zeros of `D`. -/
structure ZInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  x11 : t.gpr .x11 = scA L (sD + j)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - j)
  x13 : t.gpr .x13 = 0
  z : ∀ i < j, t.mem (scA L (sD + i)) = 0

/-- The private-key operation's result to its slot. -/
theorem dPtrs₁_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : Called L g vv m₀ t) :
    WP isa (.block dPtrs₁) t (ZInv L g vv m₀ (rOf (t.gpr .x0)) (Spec.Rsa.bytesAt t.mem L.out L.k.toNat) 0) := by
  have hc := h.ctx
  have hnQ := hL.nQ
  have hb := hL.bO
  refine WP.mono (dPtrs₁_ok hc.sp (hc.inFr (d := 192) (by decide)) (hc.inFrR (d := 184) (by decide))
    (hc.inFrR (d := 136) (by decide))) fun u ⟨hrd, hwr, hsp, hv, hm, h11, h12, h13, hpr⟩ => ?_
  obtain rd : ∀ d, d + 8 ≤ 360 → (d + 8 ≤ oR ∨ oR + 8 ≤ d) →
      (t.mem.writeW (L.Q + BitVec.ofNat 64 oR) (rOf (t.gpr .x0))).readW (L.Q + BitVec.ofNat 64 d) 64 =
        t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    unfold oR at h₂ ⊢
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  obtain hf : Frame [⟨L.Q + BitVec.ofNat 64 oR, 8⟩] t.mem u.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨⟨hc.store hL hrd hwr hsp hv (fun r hr _ => hpr r hr) hf fun r hr => ?_, ?_, ?_⟩, ?_, ?_, h13,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · rw [List.mem_singleton.mp hr]
    exact .inr ⟨oR, Nat.le_refl _, by show oR + 8 ≤ frameBytes; decide, rfl⟩
  · rw [hm, Mem.readW_writeW_self64]
  · refine bytesAt_eq fun i hi => hf.bytes (R := L.OUT) (fun X hX => ?_) (by show L.k.toNat ≤ 2 ^ 64; omega_arith) hi
    rw [List.mem_singleton.mp hX]
    exact (hL.kO.sub_left (Lay.Ok.sub_stk (by decide))).symm
  · rw [h11, rd oScr (by decide) (by decide), hc.kept.scr]; rfl
  · rw [h12, rd oK (by decide) (by decide), hc.kept.k, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zBody_ok {t : State} (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.strb .x13 .x11 0, .addImm .x .x11 .x11 1, .subImm .x .x12 .x12 1]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.write (t.gpr .x11) 1 ((t.gpr .x13).setWidth 8) ∧
      u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      ∀ r, r ≠ .x11 → r ≠ .x12 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  rw [runBlock_cons, Bytes.exec_strb0 hw, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    Nat.reduceLT, ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, fun r h11 h12 => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h11, h12, ite_false]

theorem zeroLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : ZInv L g vv m₀ R EM 0 t) :
    WP isa zeroLoop t (ZInv L g vv m₀ R EM L.k.toNat) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  refine Bytes.count_loop (by omega_arith) (ZInv L g vv m₀ R EM) (fun j hj u hu => ?_) h
  obtain hin : InRegions u.wr (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]
    exact (scCov hL hu.post.ctx (a := sD + j) (n := 1) (by unfold sD scrBytes; omega_arith)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (zBody_ok hin) fun w ⟨hrd, hwr, hsp, hv, hm, h11, h12, ho⟩ => ?_
  obtain hm' : w.mem = u.mem.write (scA L (sD + j)) 1 0 := by rw [hm, hu.x11, hu.x13]; rfl
  obtain hf : Frame [⟨scA L (sD + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - (j + 1)) := by
    rw [h12, hu.x12, Bytes.counter_step hj L.k.isLt]
  refine ⟨⟨hu.post.step hL hrd hwr hsp (fun r _ => by rw [hv]) (fun r hr _ => ho r (mem_ne hr (by decide))
    (mem_ne hr (by decide))) hf fun r hr => ?_, ?_, hx12, ?_, fun i hi => ?_⟩, ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega_arith))
  · rw [h11, hu.x11, add_add, Nat.add_assoc]
  · rw [ho .x13 (by decide) (by decide), hu.x13]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by unfold sD; omega_arith) (by have := hL.bS; have := hL.s8192; unfold sD; omega_arith)
        (by have := hL.bS; have := hL.s8192; unfold sD; omega_arith)), hu.z i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.k.isLt

theorem dPtrs₂_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h1 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 160) 8)
    (h2 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 168) 8) (h3 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 184) 8)
    (h4 : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 136) 8) :
    WP isa (.block dPtrs₂) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.mem = t.mem ∧
      u.gpr .x14 = t.mem.readW (Q + BitVec.ofNat 64 oD) 64 ∧ u.gpr .x12 = t.mem.readW (Q + BitVec.ofNat 64 oDl) 64 ∧
      u.gpr .x11 = t.mem.readW (Q + BitVec.ofNat 64 oScr) 64 + BitVec.ofNat 64 sD +
        t.mem.readW (Q + BitVec.ofNat 64 oK) 64 - t.mem.readW (Q + BitVec.ofNat 64 oDl) 64 ∧
      ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [dPtrs₂, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, hsp, oD, oDl,
    oScr, oK, sD, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq, ite_false,
    h1, h2, h3, h4]
  refine ⟨trivial, trivial, trivial, trivial, trivial, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_false]

theorem x11_eq (p : Addr) (a : Nat) (k dl : BitVec 64) (h : dl.toNat ≤ k.toNat) :
    p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 (a + (k.toNat - dl.toNat)) := by
  obtain ek : k = BitVec.ofNat 64 k.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ed : dl = BitVec.ofNat 64 dl.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show p + BitVec.ofNat 64 a + k - dl = p + BitVec.ofNat 64 a + BitVec.ofNat 64 k.toNat -
    BitVec.ofNat 64 dl.toNat by rw [← ek, ← ed], add_add, Offset.add_ofNat_sub _ (by omega_arith), Nat.add_sub_assoc h]

/-- After the zeros of `D` and `j` bytes of `d`. -/
structure CInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (j : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  x14 : t.gpr .x14 = L.d + BitVec.ofNat 64 j
  x11 : t.gpr .x11 = scA L (sD + (L.k.toNat - L.dl.toNat) + j)
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.dl.toNat - j)
  z : ∀ i < L.k.toNat - L.dl.toNat, t.mem (scA L (sD + i)) = 0
  c : ∀ i < j, t.mem (scA L (sD + (L.k.toNat - L.dl.toNat) + i)) = m₀ (L.d + BitVec.ofNat 64 i)

theorem dPtrs₂_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : ZInv L g vv m₀ R EM L.k.toNat t) :
    WP isa (.block dPtrs₂) t (CInv L g vv m₀ R EM 0) := by
  have hc := h.post.ctx
  refine WP.mono (dPtrs₂_ok hc.sp (hc.inFrR (d := 160) (by decide)) (hc.inFrR (d := 168) (by decide))
    (hc.inFrR (d := 184) (by decide)) (hc.inFrR (d := 136) (by decide)))
    fun u ⟨hrd, hwr, hsp, hv, hm, h14, h12, h11, hpr⟩ => ?_
  refine ⟨h.post.regs hrd hwr hsp hm hv fun r hr _ => hpr r hr, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [h14, hc.kept.d, BitVec.add_zero]
  · rw [h11, hc.kept.scr, hc.kept.k, hc.kept.dl, x11_eq _ _ _ _ hL.dlk]; rfl
  · rw [h12, hc.kept.dl, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hm]; exact h.z i (by omega_arith)
  · exact absurd hi (Nat.not_lt_zero _)

theorem cBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x14 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block [.ldrb .x10 .x14 0, .strb .x10 .x11 0, .addImm .x .x14 .x14 1, .addImm .x .x11 .x11 1,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧ u.v = t.v ∧
      u.mem = t.mem.write (t.gpr .x11) 1 (t.mem (t.gpr .x14)) ∧
      u.gpr .x14 = t.gpr .x14 + BitVec.ofNat 64 1 ∧ u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧
      u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → u.gpr r = t.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hr, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, trivial, trivial, trivial, fun r h10 h11 h12 h14 => ?_⟩
  · simp only [BitVec.add_zero, Bytes.read_one, Bytes.byte_rt]
  · simp only [h10, h11, h12, h14, ite_false]

theorem copyLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : CInv L g vv m₀ R EM 0 t) :
    WP isa copyLoop t (CInv L g vv m₀ R EM L.dl.toNat) := by
  have hk := hL.k1024
  have hdk := hL.dlk
  have hbS := hL.bS
  have h8 := hL.s8192
  refine Bytes.count_loop (by have := hL.dl1; omega_arith) (CInv L g vv m₀ R EM) (fun j hj u hu => ?_) h
  have hc := hu.post.ctx
  obtain hin : InRegions u.wr (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]
    exact (scCov hL hc (a := sD + (L.k.toNat - L.dl.toNat) + j) (n := 1) (by unfold sD scrBytes; omega_arith)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain hrd : InRegions (u.rd ++ u.wr) (u.gpr .x14 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x14, BitVec.add_zero]
    exact ⟨L.D, by rw [hc.rd]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.mono (cBody_ok hrd hin) fun w ⟨hrd', hwr, hsp, hv, hm, h14, h11, h12, ho⟩ => ?_
  obtain hm' : w.mem = u.mem.write (scA L (sD + (L.k.toNat - L.dl.toNat) + j)) 1 (m₀ (L.d + BitVec.ofNat 64 j)) := by
    rw [hm, hu.x11, hu.x14, hc.byte_ro hL (ro_D L) hj]
  obtain hf : Frame [⟨scA L (sD + (L.k.toNat - L.dl.toNat) + j), 1⟩] u.mem w.mem := by
    rw [hm']; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.dl.toNat - (j + 1)) := by
    rw [h12, hu.x12, Bytes.counter_step hj L.dl.isLt]
  obtain hne : ∀ a, a < sD + (L.k.toNat - L.dl.toNat) + j →
      scA L a ≠ scA L (sD + (L.k.toNat - L.dl.toNat) + j) := fun a ha =>
    Offset.add_ofNat_ne _ (by unfold sD at *; omega_arith) (by unfold sD; omega_arith) (by omega_arith)
  refine ⟨⟨hu.post.step hL hrd' hwr hsp (fun r _ => by rw [hv]) (fun r hr _ => ho r (mem_ne hr (by decide))
    (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_, ?_, ?_, hx12,
    fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [List.mem_singleton.mp hr]; exact .inl (scSub (by unfold sD scrBytes; omega_arith))
  · rw [h14, hu.x14, add_add]
  · rw [h11, hu.x11, add_add, Nat.add_assoc]
  · rw [hm', Bytes.write1_ne _ _ (hne _ (by omega_arith)), hu.z i hi]
  · rw [hm']
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega_arith)), hu.c i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.dl.isLt

/-- After `dBuild`: `R` in its slot, `EM` in `out`, and `D = I2OSP(d, k)` at `scratch + sD`. -/
structure DB (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  D : Spec.Rsa.bytesAt t.mem (scA L sD) L.k.toNat =
    Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.d L.dl.toNat)) L.k.toNat

theorem cinv_db {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM : List Byte} {u : State} (hu : CInv L g vv m₀ R EM L.dl.toNat u) : DB L g vv m₀ R EM u := by
  refine ⟨hu.post, ?_⟩
  have hdk := hL.dlk
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by simp [Spec.Rsa.bytesAt]; exact hdk)]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine List.ext_getElem (by simp; omega_arith) fun i h₁ _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < L.k.toNat - L.dl.toNat
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate, add_add, hu.z i hi]
  · rw [List.getElem_append_right (by simp; omega_arith)]
    simp only [List.length_replicate, List.getElem_map, List.getElem_range]
    have := hu.c (i - (L.k.toNat - L.dl.toNat)) (by simp at h₁; omega_arith)
    rw [add_add, show sD + i = sD + (L.k.toNat - L.dl.toNat) + (i - (L.k.toNat - L.dl.toNat)) by omega_arith, this]

theorem dBuild_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : Called L g vv m₀ t) :
    WP isa dBuild t (DB L g vv m₀ (rOf (t.gpr .x0)) (Spec.Rsa.bytesAt t.mem L.out L.k.toNat)) := by
  refine WP.seq (WP.mono (dPtrs₁_inv hL h) fun _ h₁ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hL h₁) fun _ h₂ => ?_)
  refine WP.seq (WP.mono (dPtrs₂_inv hL h₂) fun _ h₃ => ?_)
  exact WP.mono (copyLoop_ok hL h₃) fun u hu => cinv_db hL hu

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-! ### `RsaPkcs1Enc.AArch64.DecHash`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `DH = SHA256(D)`

SHA-256's functions, with an implementation `v` of its compression function
(`HH v`), and what is proven of them; the blocks setting the calls'
arguments, and the hash of `D` (`hashD_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After)

variable (v : Compress)

/-- SHA-256's functions, and what is proven of them. -/
abbrev HH : Impl.Pbkdf2.Md.AArch64.Hash := Proof.Pbkdf2.Md.AArch64.Sha256.hash v
abbrev OK : HashOK (HH v) := Proof.Pbkdf2.Md.AArch64.Sha256.ok v

theorem hI : Verified AArch64.target (HH v).hmacInit (initG (OK v).SH (HH v).W) :=
  Proof.Pbkdf2.Md.AArch64.hmacInit_ok (OK v) Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
    Proof.Pbkdf2.Md.AArch64.Sha256.satI

theorem hF : Verified AArch64.target (HH v).hmacFin (finG (OK v).SH (HH v).W) :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_ok (OK v) Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
    Proof.Pbkdf2.Md.AArch64.Sha256.satF

theorem hId : (HH v).hmacInit.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacInit_fdepth (OK v).stream.initDepth v.noFrames

theorem hFd : (HH v).hmacFin.aarch64Depth ≤ 1 :=
  Proof.Pbkdf2.Md.AArch64.hmacFin_fdepth (OK v).stream.finDepth v.noFrames

/-- The sizes. -/
theorem sizes : (HH v).S = 96 ∧ (HH v).W = 104 ∧ (HH v).D = 32 ∧ (HH v).P.B = 64 ∧ (HH v).stream.S = 96 ∧
    (HH v).stream.F = 32 ∧ (HH v).stream.D = 32 ∧ (OK v).stream.Wb = 160 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {v}

/-! ## The arguments -/

/-- A block that changes only argument registers: what stays. -/
structure Same (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  cs : ∀ r ∈ preserved, u.gpr r = t.gpr r

theorem Post.same {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM : List Byte} {t u : State} (hc : Post L g vv m₀ R EM t) (h : Same t u) : Post L g vv m₀ R EM u :=
  hc.regs h.rd h.wr h.sp h.mem h.v fun r hr _ => h.cs r hr

theorem preserved_cases {P : Reg → Prop} (h19 : P .x19) (h20 : P .x20) (h21 : P .x21) (h22 : P .x22)
    (h23 : P .x23) (h24 : P .x24) (h25 : P .x25) (h26 : P .x26) (h27 : P .x27) (h28 : P .x28) (h30 : P .x30) :
    ∀ r ∈ preserved, P r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The frame's slots are readable. -/
abbrev Slots (t : State) (Q : Addr) : Prop := ∀ d, d + 8 ≤ 224 → InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 d) 8

theorem shaInitArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaInitArgs) t fun u => Same t u ∧
      u.gpr .x0 = t.mem.readW (Q + BitVec.ofNat 64 oScr) 64 + BitVec.ofNat 64 sSt := by
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [shaInitArgs, scr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oScr, sSt, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

/-- A word of the frame. -/
abbrev slot (t : State) (Q : Addr) (d : Nat) : BitVec 64 := t.mem.readW (Q + BitVec.ofNat 64 d) 64

theorem shaUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaUpdArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = 0 ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sD ∧ u.gpr .x3 = slot t Q oK ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  have h136 := h 136 (by decide)
  apply WP.of_runBlock
  simp only [shaUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sD, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h136]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem shaFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block shaFinArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oK ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sDH ∧
      u.gpr .x3 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  have h136 := h 136 (by decide)
  apply WP.of_runBlock
  simp only [shaFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sDH, sWork, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h136]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## The hash of `D` -/

theorem bytes_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n :=
  Enc.bytesAt_eq fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}

theorem Post.slots {t : State} (hc : Post L g vv m₀ R EM t) : Slots t L.Q := fun _ hd =>
  hc.ctx.inFrR (by unfold frameBytes; omega_using [hd])

theorem Post.sp16 (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) : 16 ≤ t.sp.toNat := by
  rw [hc.ctx.sp]; have := hL.pQ; omega_using [hP, this]

/-- The 16 bytes below the stack pointer, from `Post`, miss a range of `scratch`. -/
theorem Post.stk (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {a m : Nat}
    (ha : a + m ≤ scrBytes) : (below t.sp 16).Disjoint ⟨scA L a, m⟩ := by
  rw [hc.ctx.sp]; exact stkD hL hP ha

/-- A range of `scratch` that a call changing only `ws` and the stack misses keeps its bytes. -/
theorem Post.keep (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') {a n : Nat} (ha : a + n ≤ scrBytes) (hd : ∀ r ∈ ws, Region.Disjoint ⟨scA L a, n⟩ r) :
    Spec.Rsa.bytesAt t'.mem (scA L a) n = Spec.Rsa.bytesAt t.mem (scA L a) n :=
  bytes_keep h.frame (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hd r hr
    · rw [List.mem_singleton.mp hr]; exact (hc.stk hL hP ha).symm) (by unfold scrBytes at ha; omega_using [ha])

end

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure HD (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA L sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.d L.dl.toNat)) L.k.toNat)

theorem hashD_ok {L : Lay} (hL : L.Ok) (hP : 16 ≤ L.P) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {R : BitVec 64} {EM : List Byte} {t : State} (h : DB L g vv m₀ R EM t) :
    WP isa (hashD (HH v)) t (HD L g vv m₀ R EM) := by
  have hk := hL.k1024
  have hc := h.post
  -- `init`
  refine WP.seq (WP.mono (shaInitArgs_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x0₁⟩ => ?_)
  have hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr] at x0₁
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Calls.init_call (OK v).stream x0₁
    (scCov hL hc₁.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl)) fun t₂ a₂ hr₂ => ?_)
  have hc₂ := hc₁.after hL hP a₂ fun r hr => by rw [List.mem_singleton.mp hr]; exact scSub (Nat.le_of_ble_eq_true rfl)
  have hD₂ : Spec.Rsa.bytesAt t₂.mem (scA L sD) L.k.toNat = Spec.Rsa.bytesAt t.mem (scA L sD) L.k.toNat := by
    rw [hc₁.keep hL hP a₂ (by unfold sD scrBytes; omega_using [hk]) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl),
      S₁.mem]
  -- `update`
  refine WP.seq (WP.mono (shaUpdArgs_ok hc₂.ctx.sp hc₂.slots) fun t₃ ⟨S₃, x0₃, x1₃, x2₃, x3₃, x4₃⟩ => ?_)
  have hc₃ := hc₂.same S₃
  simp only [slot, hc₂.ctx.kept.scr, hc₂.ctx.kept.k] at x0₃ x2₃ x3₃ x4₃
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream (len := L.k.toNat)
    { x0 := x0₃, x2 := x2₃, x3 := by rw [x3₃], x4 := x4₃
      cd := Covers.right (scCov hL hc₃.ctx (by unfold sD scrBytes; omega_using [hk]))
      cw := Covers.pair (scCov hL hc₃.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl))
        (scCov hL hc₃.ctx (a := sWork) (n := 160) (Nat.le_of_ble_eq_true rfl))
      st_sc := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      d_st := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl)
      d_sc := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (by unfold sD scrBytes; omega_using [hk]) (Nat.le_of_ble_eq_true rfl)
      sp16 := hc₃.sp16 hL hP
      stk_st := hc₃.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_d := hc₃.stk hL hP (by unfold sD scrBytes; omega_using [hk])
      stk_sc := hc₃.stk hL hP (Nat.le_of_ble_eq_true rfl) } fun t₄ a₄ hu₄ => ?_)
  have hc₄ := hc₃.after hL hP a₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
  have hr₄ := hu₄ [] (by rw [S₃.mem]; exact hr₂) (by rw [x1₃]; rfl)
  -- `finalize`
  refine WP.seq (WP.mono (shaFinArgs_ok hc₄.ctx.sp hc₄.slots) fun t₅ ⟨S₅, x0₅, x1₅, x2₅, x3₅⟩ => ?_)
  have hc₅ := hc₄.same S₅
  simp only [slot, hc₄.ctx.kept.scr, hc₄.ctx.kept.k] at x0₅ x1₅ x2₅ x3₅
  refine Proof.Pbkdf2.Md.AArch64.Calls.fin_call (OK v).stream
    { x0 := x0₅, x2 := x2₅, x3 := x3₅
      cw := (scCov hL hc₅.ctx (a := sSt) (n := 96) (Nat.le_of_ble_eq_true rfl)).cons
        ((scCov hL hc₅.ctx (a := sDH) (n := 32) (Nat.le_of_ble_eq_true rfl)).cons
          ((scCov hL hc₅.ctx (a := sWork) (n := 160) (Nat.le_of_ble_eq_true rfl)).cons Covers.nil))
      st_o := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      st_sc := scD hL (.inl (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      o_sc := scD hL (.inr (Nat.le_of_ble_eq_true rfl)) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      sp16 := hc₅.sp16 hL hP
      stk_st := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_o := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl)
      stk_sc := hc₅.stk hL hP (Nat.le_of_ble_eq_true rfl) } fun t₆ a₆ hf₆ => ?_
  have hc₆ := hc₅.after hL hP a₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
    · exact scSub (Nat.le_of_ble_eq_true rfl)
  refine ⟨hc₆, ?_⟩
  have := hf₆ _ (by rw [S₅.mem]; exact hr₄) (by simp [Spec.Sha256.bytesAt]; omega_using [])
    (by rw [x1₅]; simp [Spec.Sha256.bytesAt])
  obtain ⟨-, -, -, -, -, hF, hD, -⟩ := sizes v
  rw [hF, hD, List.take_of_length_le (by simp [Spec.Sha256.bytesAt])] at this
  rw [show Spec.Rsa.bytesAt t₆.mem (scA L sDH) 32 = Spec.Sha256.bytesAt t₆.mem (scA L sDH) 32 from rfl, this]
  show Spec.Sha256.hash ([] ++ Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat) = _
  rw [List.nil_append, show Spec.Sha256.bytesAt t₃.mem (scA L sD) L.k.toNat =
    Spec.Rsa.bytesAt t₃.mem (scA L sD) L.k.toNat from rfl, S₃.mem, hD₂, h.D]

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the HMACs

The calls of an HMAC with a 32-byte key in `scratch`, as the key derivation
key and each block of IRPRF make them: HMAC's `init` (`mac_init`), the
streaming `update` (`mac_upd`) and HMAC's `finalize` (`mac_fin`). They write
the first 1024 bytes of `scratch` (the states and the working space) and the
output; every other range of `scratch` keeps its bytes (`Keep`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- The ranges of `scratch` from 1024 on, but the output `[o, o + n)`, keep their bytes, and the frame's
words from `oI` on theirs. -/
structure Keep (L : Lay) (o n : Nat) (m m' : Mem) : Prop where
  scr : ∀ a l, 1024 ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + n ≤ a) →
    Spec.Rsa.bytesAt m' (scA L a) l = Spec.Rsa.bytesAt m (scA L a) l
  slot : ∀ d, oI ≤ d → d + 8 ≤ frameBytes →
    m'.readW (L.Q + BitVec.ofNat 64 d) 64 = m.readW (L.Q + BitVec.ofNat 64 d) 64

theorem Keep.trans {o n : Nat} {m m' m'' : Mem} (h : Keep L o n m m') (h' : Keep L o n m' m'') : Keep L o n m m'' :=
  ⟨fun a l h₁ h₂ h₃ => (h'.scr a l h₁ h₂ h₃).trans (h.scr a l h₁ h₂ h₃),
    fun d h₁ h₂ => (h'.slot d h₁ h₂).trans (h.slot d h₁ h₂)⟩

theorem Keep.of_eq {o n : Nat} {m m' : Mem} (h : m' = m) : Keep L o n m m' :=
  ⟨fun _ _ _ _ _ => by rw [h], fun _ _ _ => by rw [h]⟩

/-- The frame's words miss what a call writing only in `scratch` (and below the frame) writes. -/
theorem Post.slotKeep (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') (hs : ∀ r ∈ ws, Region.Sub r L.SC) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    t'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
  h.frame.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hL.stk_buf (by unfold frameBytes at hd; omega_arith) (.inr (.inr (sub_trans (hs r hr) hL.sc_sub)))
    · rw [List.mem_singleton.mp hr, hc.ctx.sp]
      exact (hL.fr_low (by unfold frameBytes at hd; omega_arith)).sub_right
        (Offset.sub_below _ hP (by have := hL.pQ; omega_arith))) (by decide)

/-- A call writing below 1024 in `scratch` keeps the rest. -/
theorem Post.keepLow (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') (hs : ∀ r ∈ ws, ∃ a n, a + n ≤ 1024 ∧ r = ⟨scA L a, n⟩) (o n : Nat) :
    Keep L o n t.mem t'.mem :=
  ⟨fun a l h₁ h₂ _ => hc.keep hL hP h h₂ fun r hr => by
    obtain ⟨b, k, hb, rfl⟩ := hs r hr
    exact scD hL (.inr (by omega_arith)) h₂ (by unfold scrBytes; omega_arith),
   fun _ _ hd => hc.slotKeep hL hP h (fun r hr => by
    obtain ⟨b, k, hb, rfl⟩ := hs r hr
    exact scSub (by unfold scrBytes; omega_arith)) hd⟩

/-- The streaming state at `scratch + a` represents what it did, if a call
missed it. -/
theorem Post.repr (hL : L.Ok) (hP : 16 ≤ L.P) {t t' : State} (hc : Post L g vv m₀ R EM t) {ws : List Region}
    (h : After t ws t') {a : Nat} (ha : a + 96 ≤ scrBytes)
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨scA L a, 96⟩ r) {msg : List Byte}
    (hr : (OK v).SH.Repr t.mem (scA L a) msg) : (OK v).SH.Repr t'.mem (scA L a) msg :=
  (OK v).stream.repr _ _ _ _ _ (fun i hi => h.frame.bytes (R := ⟨scA L a, 96⟩) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hd r hr
    · rw [List.mem_singleton.mp hr]; exact (hc.stk hL hP ha).symm) (Nat.le_of_ble_eq_true rfl)
    (Nat.lt_of_lt_of_le hi (Nat.le_of_ble_eq_true rfl))) hr

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega_arith
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega_arith

/-! ## The arguments -/

theorem macInitArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) (key : Nat) (hk : key < 4096) :
    WP isa (.block (macInitArgs key)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oScr + BitVec.ofNat 64 sOuter ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 key ∧
      u.gpr .x3 = BitVec.ofNat 64 32 ∧ u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [macInitArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, sSt, sOuter, sWork, hk, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem scA_toNat (hL : L.Ok) {a : Nat} (ha : a ≤ scrBytes) : (scA L a).toNat = L.scr.toNat + a := by
  have := hL.bS; have := hL.s8192
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by unfold scrBytes at ha; omega_arith),
    Nat.mod_eq_of_lt (by unfold scrBytes at ha; omega_arith)]

/-! ## HMAC's `init` -/

/-- After HMAC's `init` with the key `k0` (padded), from `t`. -/
structure MacInit (v : Compress) (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (R : BitVec 64) (EM : List Byte) (k0 : List Byte) (t u : State) : Prop where
  post : Post L g vv m₀ R EM u
  inner : (OK v).SH.Repr u.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad)
  outer : (OK v).SH.Repr u.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)
  keep : Keep L 0 0 t.mem u.mem

theorem mac_init (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {key : Nat}
    (hk1 : 1024 ≤ key) (hk2 : key + 32 ≤ scrBytes) {rest : Prog isa} {Q' : State → Prop}
    (hrest : ∀ u, MacInit v L g vv m₀ R EM
      (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt t.mem (scA L key) 32)) t u → WP isa rest u Q') :
    WP isa (.seq (.block (macInitArgs key)) (.seq (.call (HH v).hmacInitN (HH v).hmacInit) rest)) t Q' := by
  have hs := hL.s8192
  refine WP.seq (WP.mono (macInitArgs_ok hc.ctx.sp hc.slots key (by unfold scrBytes at hk2; omega_arith))
    fun t₁ ⟨S₁, x0, x1, x2, x3, x4⟩ => ?_)
  have hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr] at x0 x1 x2 x4
  refine WP.seq (Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call (OK v) (hI v) (hId v) (kl := 32)
    { x0 := x0, x1 := x1, x2 := x2, x3 := by rw [x3]; rfl, x4 := x4
      klB := Nat.le_of_ble_eq_true rfl
      cr := Covers.right (scCov hL hc₁.ctx (by omega_arith))
      cw := (scCov hL hc₁.ctx (a := sSt) (n := 96) (by decide)).cons
        ((scCov hL hc₁.ctx (a := sOuter) (n := 96) (by decide)).cons
          ((scCov hL hc₁.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
      i_o := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
      i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      o_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      k_i := scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega_arith)) hk2 (by decide)
      k_o := scD hL (b := sOuter) (m := 96) (.inr (by unfold sOuter; omega_arith)) hk2 (by decide)
      k_s := scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) hk2 (by decide)
      sp16 := hc₁.sp16 hL hP
      stk_i := hc₁.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_o := hc₁.stk hL hP (a := sOuter) (m := 96) (by decide)
      stk_k := hc₁.stk hL hP hk2
      stk_s := hc₁.stk hL hP (a := sWork) (m := 832) (by decide)
      scnw := by
        show (scA L sWork).toNat + 832 ≤ 2 ^ 64
        rw [scA_toNat hL (by decide)]; have := hL.bS; unfold sWork; omega_arith }
    fun t₂ a₂ hi₂ ho₂ => hrest t₂ ⟨hc₁.after hL hP a₂ fun r hr => ?_, ?_, ?_, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := sOuter) (n := 96) (by decide)
    · exact scSub (a := sWork) (n := 832) (by decide)
  · rw [S₁.mem] at hi₂; exact hi₂
  · rw [S₁.mem] at ho₂; exact ho₂
  · refine (Keep.of_eq S₁.mem).trans (hc₁.keepLow hL hP a₂ (fun r hr => ?_) 0 0)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sSt, 96, by decide, rfl⟩
    · exact ⟨sOuter, 96, by decide, rfl⟩
    · exact ⟨sWork, 832, by decide, rfl⟩

/-! ## `update` -/

theorem mac_upd (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {d : Addr} {n : Nat}
    (hx0 : t.gpr .x0 = scA L sSt) (hx1 : t.gpr .x1 = BitVec.ofNat 64 64) (hx2 : t.gpr .x2 = d)
    (hx3 : (t.gpr .x3).toNat = n) (hx4 : t.gpr .x4 = scA L sWork) (hcd : Covers [⟨d, n⟩] (t.rd ++ t.wr))
    (hds : ∀ a l, a + l ≤ 1024 → Region.Disjoint ⟨d, n⟩ ⟨scA L a, l⟩) (hdk : (below L.Q 16).Disjoint ⟨d, n⟩)
    {k0 : List Byte} (hk0 : k0.length = 64)
    (hi : (OK v).SH.Repr t.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad))
    (ho : (OK v).SH.Repr t.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    WP isa (.call (HH v).updN (HH v).updC) t fun u => Post L g vv m₀ R EM u ∧
      (OK v).SH.Repr u.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ Spec.Rsa.bytesAt t.mem d n) ∧
      (OK v).SH.Repr u.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) ∧ Keep L 0 0 t.mem u.mem := by
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call (OK v).stream (len := n)
    { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4
      cd := hcd
      cw := Covers.pair (scCov hL hc.ctx (a := sSt) (n := 96) (by decide))
        (scCov hL hc.ctx (a := sWork) (n := 160) (by decide))
      st_sc := scD hL (a := sSt) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
      d_st := hds sSt 96 (by decide)
      d_sc := hds sWork 160 (by decide)
      sp16 := hc.sp16 hL hP
      stk_st := hc.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_d := by rw [hc.ctx.sp]; exact hdk
      stk_sc := hc.stk hL hP (a := sWork) (m := 160) (by decide) } fun u a hu => ⟨hc.after hL hP a fun r hr => ?_,
      hu _ hi (by rw [hx1, Spec.Hmac.xorPad, List.length_map, hk0]), hc.repr hL hP a (by decide) (fun r hr => ?_) ho,
      hc.keepLow hL hP a (fun r hr => ?_) 0 0⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := sWork) (n := 160) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scD hL (a := sOuter) (n := 96) (b := sSt) (m := 96) (.inr (by decide)) (by decide) (by decide)
    · exact scD hL (a := sOuter) (n := 96) (b := sWork) (m := 160) (.inl (by decide)) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sSt, 96, by decide, rfl⟩
    · exact ⟨sWork, 160, by decide, rfl⟩

/-! ## HMAC's `finalize` -/

theorem mac_fin (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (hc : Post L g vv m₀ R EM t) {o : Nat}
    (ho1 : 1024 ≤ o) (ho2 : o + 32 ≤ scrBytes) {k0 text : List Byte} (hk0 : k0.length = 64)
    (htl : text.length < 2 ^ 32)
    (hx0 : t.gpr .x0 = scA L sSt) (hx1 : t.gpr .x1 = scA L sOuter)
    (hx2 : t.gpr .x2 = BitVec.ofNat 64 (64 + text.length)) (hx3 : t.gpr .x3 = scA L o)
    (hx4 : t.gpr .x4 = scA L sWork)
    (hi : (OK v).SH.Repr t.mem (scA L sSt) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text))
    (ho : (OK v).SH.Repr t.mem (scA L sOuter) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    WP isa (.call (HH v).hmacFinN (HH v).hmacFin) t fun u => Post L g vv m₀ R EM u ∧
      Spec.Rsa.bytesAt u.mem (scA L o) 32 = Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 text ∧
      Keep L o 32 t.mem u.mem := by
  have hs := hL.s8192
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call (OK v) (hF v) (hFd v) (cnt := t.gpr .x2)
    { x0 := hx0, x1 := hx1, x2 := rfl, x3 := hx3, x4 := hx4
      cr := Covers.right (scCov hL hc.ctx (a := sOuter) (n := 96) (by decide))
      cw := (scCov hL hc.ctx (a := sSt) (n := 96) (by decide)).cons
        ((scCov hL hc.ctx (a := o) (n := 32) ho2).cons
          ((scCov hL hc.ctx (a := sWork) (n := 832) (by decide)).cons Covers.nil))
      i_u := scD hL (a := sSt) (n := 96) (b := sOuter) (m := 96) (.inl (by decide)) (by decide) (by decide)
      i_o := scD hL (a := sSt) (n := 96) (b := o) (m := 32) (.inl (by unfold sSt; omega_arith)) (by decide) ho2
      i_s := scD hL (a := sSt) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      u_o := scD hL (a := sOuter) (n := 96) (b := o) (m := 32) (.inl (by unfold sOuter; omega_arith)) (by decide) ho2
      u_s := scD hL (a := sOuter) (n := 96) (b := sWork) (m := 832) (.inl (by decide)) (by decide) (by decide)
      o_s := scD hL (a := o) (n := 32) (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) ho2 (by decide)
      sp16 := hc.sp16 hL hP
      stk_i := hc.stk hL hP (a := sSt) (m := 96) (by decide)
      stk_u := hc.stk hL hP (a := sOuter) (m := 96) (by decide)
      stk_o := hc.stk hL hP (a := o) (m := 32) ho2
      stk_s := hc.stk hL hP (a := sWork) (m := 832) (by decide)
      scnw := by
        show (scA L sWork).toNat + 832 ≤ 2 ^ 64
        rw [scA_toNat hL (by decide)]; have := hL.bS; unfold sWork; omega_arith }
    fun u a hf => ⟨hc.after hL hP a fun r hr => ?_, ?_, ⟨fun b l h₁ h₂ h₃ => hc.keep hL hP a h₂ fun r hr => ?_,
      fun _ _ hd => hc.slotKeep hL hP a (fun r hr => ?_) hd⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := o) (n := 32) ho2
    · exact scSub (a := sWork) (n := 832) (by decide)
  · exact hf k0 text hk0 (by rw [hk0]; omega_arith) hi (by rw [hx2]; rfl) ho
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scD hL (b := sSt) (m := 96) (.inr (by unfold sSt; omega_arith)) h₂ (by decide)
    · exact scD hL (b := o) (m := 32) h₃ h₂ ho2
    · exact scD hL (b := sWork) (m := 832) (.inr (by unfold sWork; omega_arith)) h₂ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scSub (a := sSt) (n := 96) (by decide)
    · exact scSub (a := o) (n := 32) ho2
    · exact scSub (a := sWork) (n := 832) (by decide)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
