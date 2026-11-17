module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Narrow
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM-SIV in registers on x86-64: constant time

Untrusted: everything here is checked by Lean. As for the first
implementation, both runs have the same public arguments in the slots of `W`,
so the taint analysis starts from the registers that agree and those slots,
public (`sivT`, `both_agree`). This code calls nothing: the taint analysis
checks each piece whole.
-/

-- separate module: evaluates the taint analysis on the code

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc word_byte)


/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[200, 248)` public. -/
def sivT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 744], bases := [(.r15, 1, 0)],
    slots := [(1, 200, 48)] }

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D al n s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 744⟩]

/-- Two runs with the same public arguments, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  o₁ : One K W SP R N A D al n s₁
  o₂ : One K W SP R N A D al n s₂
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D al n rs s₁ s₂) : X86_64.Taint.Agree (sivT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 744⟩] → X86_64.Taint.Wf (sivT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 744 ≤ 2 ^ 64; decide
    · simp only [sivT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.o₁.wr, h.o₂.wr], wf h.o₁.env h.o₁.wr,
    wf h.o₂.env h.o₂.wr, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.o₁.env.r13, h.o₂.env.r13]
      · rw [h.o₁.env.r15, h.o₂.env.r15]
      · rw [h.o₁.env.rsp, h.o₂.env.rsp]
  · simp only [sivT, List.mem_singleton] at hsl; subst hsl; simp [sivT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 744⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
      fun s hw => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [add_ofNat_assoc, ← e]
    simp only [sivT, List.mem_singleton] at hsl; subst hsl
    rw [hb s₁ h.o₁.wr, hb s₂ h.o₂.wr]
    simp only at hk₁ hk₂
    have S₁ := h.o₁.sl
    have S₂ := h.o₂.sl
    have key : ∀ d, d ∈ [200, 208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
        s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
      rw [hw d (by omega_arith)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact word_byte S₁.rounds S₂.rounds (by omega_arith)
      · exact word_byte S₁.nonce S₂.nonce (by omega_arith)
      · exact word_byte S₁.aad S₂.aad (by omega_arith)
      · exact word_byte S₁.alen S₂.alen (by omega_arith)
      · exact word_byte S₁.data S₂.data (by omega_arith)
      · exact word_byte S₁.len S₂.len (by omega_arith)
    have hq : (k - 200) / 8 = 0 ∨ (k - 200) / 8 = 1 ∨ (k - 200) / 8 = 2 ∨ (k - 200) / 8 = 3 ∨
        (k - 200) / 8 = 4 ∨ (k - 200) / 8 = 5 := by omega_arith
    exact key (200 + 8 * ((k - 200) / 8)) (by
      rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide) (by omega_arith) (by omega_arith)

/-- Code the taint analysis checks from `sivT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, (taint.check (sivT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (sivT rs) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc


/-!
## The tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The code around each call of
`vg_aes_ctr32` passes the taint analysis from the public slots and the
registers both runs agree on (`rel_taintC`); each call has the same
arguments in both runs, by correctness.
-/

/-! ## The pieces, checked -/

open VG.Impl.AesGcmSiv.X86_64Reg

theorem derive_check : ∃ hc, (taint.check (sivT []) derive hc).isSome = true := ⟨_, by taint_decide⟩

theorem expand_check : ∃ hc, (taint.check (sivT []) expand hc).isSome = true := ⟨_, by taint_decide⟩

open VG.Impl.AesGcm.X86_64 (at_ imm ptr) in
open VG.Impl.AesGcmSiv.X86_64 (aadO alenO dataO lenO) in
theorem polyA_check : ∃ hc, (taint.check (sivT []) (.block (hkey ++
    ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absorb_check (four : Bool) : ∃ hc, (taint.check (sivT [.r12, .rbp]) (absorb four) hc).isSome = true := by
  cases four <;> exact ⟨_, by taint_decide⟩

open VG.Impl.AesGcm.X86_64 (at_ imm ptr) in
open VG.Impl.AesGcmSiv.X86_64 (aadO alenO dataO lenO) in
theorem polyD_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem lens_check : ∃ hc, (taint.check (sivT []) (.block lens) hc).isSome = true := ⟨_, by taint_decide⟩

theorem tag_check (o : Nat) (ho : o = 0 ∨ o = 128) : ∃ hc, (taint.check (sivT []) (tag o) hc).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem crypt_check : ∃ hc, (taint.check (sivT []) crypt hc).isSome = true := ⟨_, by taint_decide⟩

/-! ## A run between the pieces -/

open VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Impl.AesGcmSiv.X86_64 (entry recv tagOut restore mask okO bO tagO aadO alenO dataO lenO)
open VG.Proof.AesGcm.X86_64 (in_off)
open VG.Proof.AesGcmSiv.X86_64 (rel_taintR)

/-- A run with the public arguments and the buffers of the additional data
and the data. -/
structure Bufs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  aad : Buf K W SP t A al
  data : Buf K W SP t D n

/-- The address of the tag `T`, at `SP + 16`, where the run may read it,
apart from what the pieces write, and the tag, which it may read. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  w : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 744⟩
  d : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩
  tb : TagBuf W SP D n T
  trd : Covers [⟨T, 16⟩] (s.rd ++ s.wr)

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : ArgT W SP D n T s)
    (hf : Frame (mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgT W SP D n T s' :=
  ⟨by rw [argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d, h.tb, by rw [hrd, hwr]; exact h.trd⟩

/-- A run between the pieces: the public arguments, the buffers and the
tag's address. -/
structure St (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop where
  bufs : Bufs K W SP R N A D al n t
  nonce : Buf K W SP t N 12
  argT : ArgT W SP D n T t

theorem St.frame {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t t' : State}
    (h : St K W SP R N A D al n T t) (E : Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) (hm : Frame (mutR W SP D n) t.mem t'.mem)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    St K W SP R N A D al n T t' :=
  ⟨⟨⟨E, h.bufs.one.sl.of_frame hf hd, hwr.trans h.bufs.one.wr⟩, h.bufs.aad.of_eq hrd hwr, h.bufs.data.of_eq hrd hwr⟩,
    h.nonce.of_eq hrd hwr, h.argT.mut hm hrd hwr⟩


/-! ## The pieces keep `St` -/

section
variable {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat}

theorem St.dw {t : State} (h : St K W SP R N A D al n T t) : Covers [⟨D, n⟩] t.wr := by
  rw [h.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)

theorem derive_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa derive t (St K W SP R N A D al n T) :=
  WP.mono (derive_ok L hR h.bufs.one.env h.bufs.one.sl h.nonce) fun _ Dv =>
    h.frame Dv.env Dv.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (frA (d := 16) (k := 48) (by decide) Dv.frame) Dv.rd Dv.wr

theorem expand_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩) {t : State}
    (h : St K W SP R N A D al n T t) : WP isa expand t (St K W SP R N A D al n T) :=
  WP.mono (expand_ok hR hret h.bufs.one.env h.bufs.one.sl) fun _ X =>
    h.frame X.env X.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (frC X.frame) X.rd X.wr

theorem keys_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩) {t : State}
    (h : St K W SP R N A D al n T t) : WP isa keys t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (derive_st L hR h) fun _ h => expand_st L hR hret h)

theorem tag_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {o : Nat} (ho : o = 0 ∨ o = 128) {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (tag o) t (St K W SP R N A D al n T) :=
  WP.mono (tag_ok L hR h.bufs.one.env h.bufs.one.sl h.nonce ho) fun _ Tg =>
    h.frame Tg.env Tg.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho]))
      (frA (d := o) (k := 16) (by omega_using [ho]) Tg.frame) Tg.rd Tg.wr

theorem crypt_st (L : Lay K W SP) (hR : R = 10 ∨ R = 14) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa crypt t (St K W SP R N A D al n T) :=
  WP.mono (crypt_ok L hR h.bufs.one.env h.bufs.one.sl h.bufs.data h.dw) fun _ Cr =>
    h.frame Cr.env Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact (h.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      (Cr.frame.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩) Cr.rd Cr.wr

variable {F : MulFacts}

/-- `St`, with GHASH's registers for some key. -/
def PG (F : MulFacts) (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧ ∃ H, GReg F H t

/-- `PG`, with an input and its length in `r12` and `rbp`. -/
def PR (F : MulFacts) (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (Q : Addr) (k : Nat) (t : State) : Prop :=
  PG F K W SP R N A D al n T t ∧ t.gpr .r12 = Q ∧ t.gpr .rbp = BitVec.ofNat 64 k

/-- A pointer and a length loaded from their slots. -/
theorem ld_ok {u : State} (Eu : Env K W SP u) {o : Nat} {P : Addr} {k : Nat} (h₁ : 200 ≤ o) (h₂ : o + 16 ≤ 248)
    (hP : u.mem.readW (W + BitVec.ofNat 64 o) 64 = P)
    (hk : u.mem.readW (W + BitVec.ofNat 64 (o + 8)) 64 = BitVec.ofNat 64 k) :
    ∃ u' : State, runBlock isa [.mov .r12 (.mem (at_ .r15 o)), .mov .rbp (.mem (at_ .r15 (o + 8)))] u = some u' ∧
      u'.gpr .r12 = P ∧ u'.gpr .rbp = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → u'.gpr r = u.gpr r) ∧
      u'.xmm = u.xmm ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have h15 := Eu.r15
  obtain r₁ := Eu.perm.wR (show o + 8 ≤ 744 by omega_arith)
  obtain r₂ := Eu.perm.wR (show o + 8 + 8 ≤ 744 by omega_arith)
  refine ⟨_, by srun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, hP]
  · simp only [gpr_setReg, mem_setReg, ite_true, ite_false, reduceCtorEq, h15, hk]
  · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
  all_goals rfl

/-- `St` after code that keeps the memory, the permissions and `r13`, `r15`, `rsp`. -/
theorem St.same {t t' : State} (h : St K W SP R N A D al n T t) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    St K W SP R N A D al n T t' :=
  h.frame (rs := []) (h.bufs.one.env.keep hg hrd hwr) (by rw [hm]; exact Frame.refl _ _) (fun _ h => nomatch h)
    (by rw [hm]; exact Frame.refl _ _) hrd hwr

theorem polyA_wp {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (.block (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr))) t
      (PR F K W SP R N A D al n T A al) := by
  rw [show (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)) =
    hkey ++ ([.mov .r12 (.mem (at_ .r15 216)), .mov .rbp (.mem (at_ .r15 (216 + 8)))] : List Instr) from rfl,
    WP.block_append_iff]
  refine WP.mono (hkey_ok (F := F) h.bufs.one.env) fun t₁ ⟨g₁, _, m₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP t₁ := h.bufs.one.env.of_saved sv₁ rd₁ wr₁
  obtain ⟨t₂, run₂, r12₂, rbp₂, g₂, x₂, m₂, rd₂, wr₂⟩ := ld_ok E₁ (o := 216) (P := A) (k := al) (by decide)
    (by decide) (m₁ ▸ h.bufs.one.sl.aad) (m₁ ▸ h.bufs.one.sl.alen)
  refine WP.of_runBlock ⟨t₂, run₂, ⟨h.same (m₂.trans m₁) (fun r hr => ?_) (rd₂.trans rd₁) (wr₂.trans wr₁),
    _, by rw [x₂]; exact g₁.c, by rw [x₂]; exact g₁.h⟩, r12₂, rbp₂⟩
  have hne : r ≠ .r12 ∧ r ≠ .rbp ∧ r ∈ calleeSaved := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
  rw [g₂ r hne.1 hne.2.1, sv₁ r hne.2.2]

theorem polyD_wp {t : State} (h : PG F K W SP R N A D al n T t) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) t
      (PR F K W SP R N A D al n T D n) := by
  obtain ⟨hs, H, g⟩ := h
  obtain ⟨t₂, run₂, r12₂, rbp₂, g₂, x₂, m₂, rd₂, wr₂⟩ := ld_ok hs.bufs.one.env (o := 232) (P := D) (k := n) (by decide)
    (by decide) hs.bufs.one.sl.data hs.bufs.one.sl.len
  refine WP.of_runBlock ⟨t₂, run₂, ⟨hs.same m₂ (fun r hr => g₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂,
    H, by rw [x₂]; exact g.c, by rw [x₂]; exact g.h⟩, r12₂, rbp₂⟩

theorem absorb_st (four : Bool) (L : Lay K W SP) {Q : Addr} {k : Nat} {t : State} (hQ : Buf K W SP t Q k)
    (h : PR F K W SP R N A D al n T Q k t) : WP isa (absorb four) t (PG F K W SP R N A D al n T) := by
  obtain ⟨⟨hs, H, g⟩, r12, rbp⟩ := h
  refine WP.mono (absorb_ok four L hs.bufs.one.env g hQ r12 rbp) fun _ P => ?_
  exact ⟨hs.frame P.env P.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (frA (d := 128) (k := 16) (by decide) P.frame) P.rd P.wr, H, P.g⟩

theorem lens_st {t : State} (h : PG F K W SP R N A D al n T t) :
    WP isa (.block lens) t (St K W SP R N A D al n T) := by
  obtain ⟨hs, H, g⟩ := h
  refine WP.mono (lens_ok hs.bufs.one.env g hs.bufs.one.sl.alen hs.bufs.one.sl.len hs.bufs.aad.lt hs.bufs.data.lt)
    fun _ ⟨_, m, rd, wr, hg⟩ => hs.same m hg rd wr

theorem polyval_st (F : MulFacts) (L : Lay K W SP) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa polyval t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (polyA_wp (F := F) h) fun _ h₁ => WP.seq (WP.mono (absorb_st false L h₁.1.1.bufs.aad h₁)
    fun _ h₂ => WP.seq (WP.mono (polyD_wp h₂) fun _ h₃ => WP.seq (WP.mono (absorb_st true L h₃.1.1.bufs.data h₃)
      fun _ h₄ => lens_st h₄))))

/-! ## The pieces, in two runs -/

variable (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64)
include hDW hn

/-- A piece the taint analysis checks from `sivT []`, which keeps `St`. -/
theorem piece_rel {c : Prog isa} (hc : ∃ hc, (taint.check (sivT []) c hc).isSome = true)
    (hst : ∀ t, St K W SP R N A D al n T t → WP isa c t (St K W SP R N A D al n T)) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P c fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ :=
  (rel_taintC [] hDW hn (fun _ _ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one, fun _ h => nomatch h⟩) hc).wp
    fun _ _ h => ⟨hst _ (hP _ _ h).1, hst _ (hP _ _ h).2⟩

theorem keys_rel (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P keys fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ :=
  RelCT.seq (piece_rel hDW hn derive_check (fun _ h => derive_st L hR h) hP)
    (piece_rel hDW hn expand_check (fun _ h => expand_st L hR hret h) fun _ _ h => h.2)

theorem polyval_rel (F : MulFacts) (L : Lay K W SP) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P polyval fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one,
      fun _ h => nomatch h⟩) polyA_check).wp
    (F₁ := PR F K W SP R N A D al n T A al) (F₂ := PR F K W SP R N A D al n T A al)
    fun t₁ t₂ h => ⟨polyA_wp (hP _ _ h).1, polyA_wp (hP _ _ h).2⟩
  have r₂ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧ PR F K W SP R N A D al n T A al t₁ ∧
      PR F K W SP R N A D al n T A al t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check false)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st false L h.2.1.1.1.bufs.aad h.2.1, absorb_st false L h.2.2.1.1.bufs.aad h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧ PG F K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) polyD_check).wp
    (F₁ := PR F K W SP R N A D al n T D n) (F₂ := PR F K W SP R N A D al n T D n)
    fun t₁ t₂ h => ⟨polyD_wp h.2.1, polyD_wp h.2.2⟩
  have r₄ := (rel_taintC [.r12, .rbp] (P := fun t₁ t₂ => True ∧ PR F K W SP R N A D al n T D n t₁ ∧
      PR F K W SP R N A D al n T D n t₂) hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.1.bufs.one, h.2.2.1.1.bufs.one, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.2.1.2.1, h.2.2.2.1]
        · rw [h.2.1.2.2, h.2.2.2.2]⟩) (absorb_check true)).wp
    (F₁ := PG F K W SP R N A D al n T) (F₂ := PG F K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨absorb_st true L h.2.1.1.1.bufs.data h.2.1, absorb_st true L h.2.2.1.1.bufs.data h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ PG F K W SP R N A D al n T t₁ ∧ PG F K W SP R N A D al n T t₂)
      hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) lens_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨lens_st h.2.1, lens_st h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ r₅)))

end

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by srun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 24))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 16`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s fun s₁ => Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
      InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ?_, by rw [rd₁, wr₁]; exact hTr⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R al n : Nat} (Ar : Args s K W SP N A D R al n)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-! ## The tag's address -/

/-- What the copies of the tag need of a run: `r15` and `rsp` hold `W` and
`SP`, and the address of the tag `T` is at `SP + 16`, where the run may read
it. -/
def TagIn (W SP T : Addr) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

theorem St.tagIn {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {σ s : State}
    (h : St K W SP R N A D al n T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : TagIn W SP T s :=
  ⟨by rw [← hg]; exact h.bufs.one.env.r15, by rw [← hg]; exact h.bufs.one.env.rsp, by rw [← hm]; exact h.argT.val,
    hc _ _ h.argT.rd⟩

/-- `mov rcx, [rsp + 16]`: the tag's address in `rcx`. -/
theorem loadT_ok {W SP T : Addr} {s : State} (h : TagIn W SP T s) :
    WP isa (.block [.mov .rcx (.mem (at_ .rsp 16))]) s fun s' =>
      s'.gpr .rcx = T ∧ s'.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r := by
  obtain ⟨h15, hsp, hT, hr⟩ := h
  refine WP.of_runBlock ⟨_, by srun [hsp, hr], ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hT]
  · simp only [gpr_setReg, ite_false, reduceCtorEq, h15]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem loadT_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (at_ .rsp 16))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `mov rcx, [rsp + 16]` and then `c`, which the taint analysis checks with
`rcx` and `r15` public, in two runs with the same `W`, `SP` and tag
address. -/
theorem rel_loadT {W SP T : Addr} {P : State → State → Prop} {l : List Instr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → TagIn W SP T s₁ ∧ TagIn W SP T s₂)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block l) hc).isSome = true) :
    RelCT isa P (.block (([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ l)) fun _ _ => True := by
  have a := (rel_taintR (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨-, a₁, -⟩, ⟨-, a₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) loadT_check).wp
    (F₁ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    (F₂ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    fun _ _ h => ⟨WP.mono (loadT_ok (hP _ _ h).1) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩,
      WP.mono (loadT_ok (hP _ _ h).2) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩⟩
  exact RelCT.block_append (M := isa) (RelCT.seq a (rel_taintR [.rcx, .r15] (fun _ _ h r hr => by
    obtain ⟨-, ⟨c₁, w₁, -⟩, ⟨c₂, w₂, -⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [c₁, c₂]
    · rw [w₁, w₂]) hc))

/-! ## `seal` -/

/-- `s` with the tag read only, and the data and `W` its writable regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, 16⟩]) [⟨D, n⟩, ⟨W, 744⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 744⟩] ∧ St K W SP R N A D al n T (narrowT D n T W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hwr : s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 744⟩])
    (h : Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧ InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8) :
    SealIn K W SP R N A D al n T s₁ := by
  obtain ⟨E, S, rd, wr, hT, hTr⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 744⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((narrowT D n T W s₁).rd ++ (narrowT D n T W s₁).wr) := by
    rw [hwr₁]; exact covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → Buf K W SP (narrowT D n T W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.aad, hb Ar.data⟩, hb Ar.nonce,
    ⟨hT, hc _ _ hTr, Ar.argsW, Ar.argsD, Tb, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩⟩

theorem entry_seal {s : State} (hp : sealPre s) :
    WP isa (.block entry) s (SealIn (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  WP.mono (entry_post (args_of_seal hp).1.1 rfl (ofNat_toNat64 _).symm rfl rfl rfl
      (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl)
    fun _ h => sealIn_of (args_of_seal hp).1.1 (args_of_seal hp).1.2 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_seal hp'


section
variable {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat}

/-- `seal` after its entry, up to the copy of the tag. -/
abbrev sealFront : Prog isa := .seq (.seq (.seq keys polyval) (tag tagO)) crypt

theorem sealFront_st (F : MulFacts) (L : Lay K W SP) (hR : R = 10 ∨ R = 14) (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩)
    {t : State} (h : St K W SP R N A D al n T t) : WP isa sealFront t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (keys_st L hR hret h) fun _ h => polyval_st F L h))
    fun _ h => tag_st L hR (.inl rfl) h)) fun _ h => crypt_st L hR h)

theorem sealFront_rel (F : MulFacts) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64) (L : Lay K W SP)
    (hR : R = 10 ∨ R = 14) (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P sealFront fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ :=
  RelCT.seq (RelCT.seq (RelCT.seq (keys_rel hDW hn L hR hret hP) (polyval_rel hDW hn F L fun _ _ h => h.2))
    (piece_rel hDW hn (tag_check 0 (.inl rfl)) (fun _ h => tag_st L hR (.inl rfl) h) fun _ _ h => h.2))
    (piece_rel hDW hn crypt_check (fun _ h => crypt_st L hR h) fun _ _ h => h.2)

end

theorem tagOut_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block (tagOut.tail ++ restore)) hc).isSome =
    true := ⟨_, by taint_decide⟩


/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem seal_rel (F : MulFacts) {s₀ s₀' : State} (hp : sealPre s₀) (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') Impl.AesGcmSiv.X86_64Reg.seal fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  refine RelCT.assoc (RelCT.assoc (RelCT.assoc ?_))
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₂)
    [⟨arg s₀ 1, 16⟩] [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 744⟩]
    (sealFront_rel F Ar.data.w hn L Ar.rounds Ar.retW
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 1, 16⟩, ⟨arg s₀ 2, 744⟩] →
          Covers ([⟨arg s₀ 1, 16⟩] ++ [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 744⟩]) s.wr ∧
          Covers [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 744⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealFront_st F L Ar.rounds Ar.retW p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealFront_st F L Ar.rounds Ar.retW p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (rel_loadT (l := tagOut.tail ++ restore) (fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.tagIn g₁ h₁ c₁, m₂.tagIn g₂ h₂ c₂⟩) tagOut_check)

/-! ## `open` -/

theorem entry_st {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hwr : s.wr = [⟨D, n⟩, ⟨W, 744⟩]) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s (St K W SP R N A D al n T) :=
  WP.mono (entry_post Ar hsp hn hT hW hdi hsi hdx hcx hr8 hr9) fun _ ⟨E₁, S₁, rd₁, wr₁, hT₁, hTa₁⟩ =>
    ⟨⟨⟨E₁, S₁, wr₁.trans hwr⟩, Ar.aad.of_eq rd₁ wr₁, Ar.data.of_eq rd₁ wr₁⟩, Ar.nonce.of_eq rd₁ wr₁,
      ⟨hT₁, hTa₁, Ar.argsW, Ar.argsD, Tb, by rw [rd₁, wr₁]; exact hTr⟩⟩

theorem entry_open {s : State} (hp : openPre s) :
    WP isa (.block entry) s (St (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  entry_st (args_of_open hp).1.1 (args_of_open hp).1.2 (args_of_open hp).2 hp.2.1 rfl (ofNat_toNat64 _).symm rfl rfl
    rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (St (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_open hp'

theorem recv_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block recv) t (St K W SP R N A D al n T) := by
  obtain ⟨t', run', fR, -, hg', hrd', hwr'⟩ := recv_ok h.bufs.one.env h.argT.val h.argT.rd
    (h.argT.tb.buf h.argT.trd)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fR (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using L.w_w (a := 200) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide))
    (fR.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by mem_lit, Region.sub_prefix (by decide)⟩)
    hrd' hwr'⟩

theorem recv_split : recv = ([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ recv.tail := rfl

theorem recv_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block recv.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (taint.check (sivT []) (.block Impl.AesGcmSiv.X86_64.cmp) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ hc, (taint.check (sivT []) mask hc).isSome = true := ⟨_, by taint_decide⟩

theorem fin_check : ∃ hc, (taint.check (sivT [])
    (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `St`, with `ok` at `W + 192` either 1 or 0. -/
def StO (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧
    (t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 ∨ t.mem.readW (W + BitVec.ofNat 64 192) 64 = 0#64)

theorem cmp_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block Impl.AesGcmSiv.X86_64.cmp) t (StO K W SP R N A D al n T) := by
  obtain ⟨t', run', hm', hg', hrd', hwr'⟩ := cmp_ok h.bufs.one.env
  have fO : Frame [wO W] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩) hrd' hwr', ?_⟩
  rw [hm', Mem.readW_writeW_self64]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem mask_st {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StO K W SP R N A D al n T t) : WP isa mask t (St K W SP R N A D al n T) := by
  have hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 then 1#64 else 0#64 := by
    rcases h.2 with h' | h' <;> rw [h'] <;> decide
  refine WP.mono (mask_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)) hok) fun _ Mk =>
    h.1.frame Mk.env Mk.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact (h.1.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
      Mk.rd Mk.wr


/-- `open` after its entry, in two runs. -/
theorem openBody_rel (F : MulFacts) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 744⟩) (hn : n ≤ 2 ^ 64)
    (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (.seq (.block recv) (.seq keys (.seq crypt (.seq polyval
      (.seq (tag bO) (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))
      fun _ _ => True := by
  have r₀ := (rel_loadT (l := recv.tail) (fun t₁ t₂ h =>
      ⟨(hP _ _ h).1.tagIn rfl rfl (Covers.refl _), (hP _ _ h).2.tagIn rfl rfl (Covers.refl _)⟩) recv_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨by rw [← recv_split]; exact recv_st L (hP _ _ h).1, by rw [← recv_split]; exact recv_st L (hP _ _ h).2⟩
  have r₁ := keys_rel hDW hn L hR hret (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun _ _ h => h.2
  have r₂ := piece_rel hDW hn crypt_check (fun _ h => crypt_st L hR h) (P := fun t₁ t₂ => True ∧
      St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) fun _ _ h => h.2
  have r₃ := polyval_rel hDW hn F L (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun _ _ h => h.2
  have r₄ := piece_rel hDW hn (tag_check 128 (.inr rfl)) (fun _ h => tag_st L hR (.inr rfl) h)
    (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) fun _ _ h => h.2
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) cmp_check).wp
    (F₁ := StO K W SP R N A D al n T) (F₂ := StO K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨cmp_st L h.2.1, cmp_st L h.2.2⟩
  have r₆ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StO K W SP R N A D al n T t₁ ∧ StO K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) mask_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨mask_st h.2.1, mask_st h.2.2⟩
  have r₇ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) fin_check
  rw [recv_split]
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇))))))

/-- `vg_aes_gcm_siv_open`, in two runs with the same public arguments. -/
theorem open_rel (F : MulFacts) {s₀ s₀' : State} (hp : openPre s₀) (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') Impl.AesGcmSiv.X86_64Reg.open fun _ _ => True := by
  have Ar := (args_of_open hp).1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel F Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.retW fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSivReg.X86_64
