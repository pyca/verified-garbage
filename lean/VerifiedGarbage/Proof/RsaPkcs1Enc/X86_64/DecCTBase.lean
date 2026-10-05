import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecArgs
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: two runs

Two runs from entry states that agree on the public data (`decK.pub`: the
pointers and lengths, `n` and `e`) are related piece by piece: each point of
the code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`). The registers a piece's addresses and branches depend on are
functions of the public data (`pins`); each call's public arguments are too
(`init_two`, `upd_two`, …).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := decK.pre s ∧ decK.pub a s

theorem pub_refl (s : State) : decK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 17) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : Sib a s) : nB s = nB a := h.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib a s) : eB s = eB a := h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.scr {a s : State} (h : Sib a s) : Dec.sc s = Dec.sc a := h.arg (by decide)

theorem Sib.scr' {a s : State} (h : Sib a s) (d : Nat) : Dec.scA s d = Dec.scA a d := by
  show off (Dec.sc s) d = off (Dec.sc a) d; rw [h.scr]

theorem Sib.k {a s : State} (h : Sib a s) : kOf s = kOf a := by
  show (s.gpr .r8).toNat = _; rw [h.gpr (r := .r8) (by decide)]

theorem Sib.p {a s : State} (h : Sib a s) : DPre s := dPre_of h.1

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- Registers `J` gives as functions of the public data, at once. -/
theorem pins {J : State → State → Prop} (rs : List (Reg × (State → BitVec 64)))
    (hf : ∀ p ∈ rs, ∀ s t, J s t → t.gpr p.1 = p.2 s) (hs : ∀ p ∈ rs, ∀ a s, Sib a s → p.2 s = p.2 a) :
    Pins (At J) (rs.map (·.1)) := fun a t₁ t₂ h₁ h₂ r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact pin p.2 (hf p hp) (hs p hp) h₁ h₂

theorem fb_pin : ∀ a s, Sib a s → fb s = fb a := fun _ _ h => h.fb
theorem sc_pin : ∀ a s, Sib a s → sc s = sc a := fun _ _ h => h.scr
theorem scA_pin (d : Nat) : ∀ a s, Sib a s → scA s d = scA a d := fun _ _ h => h.scr' d
theorem const_pin (v : BitVec 64) : ∀ a s, Sib a s → (fun _ : State => v) s = (fun _ : State => v) a :=
  fun _ _ _ => rfl
theorem gpr_pin {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    ∀ a s, Sib a s → s.gpr r = a.gpr r := fun _ _ h => h.gpr hr
theorem arg_pin {i : Nat} (hi : i < 17) : ∀ a s, Sib a s → stackArg s i = stackArg a i := fun _ _ h => h.arg hi

/-- `Ctx` for some result and `EM`. -/
def Cx (s t : State) : Prop := ∃ R EM, Ctx s R EM t

theorem Cx.rsp {s t : State} (h : Cx s t) : t.gpr .rsp = fb s := let ⟨_, _, hc⟩ := h; hc.rsp

/-- `rsp` in a state with `Cx`. -/
theorem rsp_pin {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t) : Pins (At J) [.rsp] :=
  pins (J := J) [(.rsp, fb)] (by simp only [List.mem_singleton]; rintro p rfl s t h; exact (hJ s t h).rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)

/-! ## The calls -/

variable {v : Compress}


/-- The registers a callee sees, but `rsp`. -/
theorem ce_eq {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) (h : t₁.gpr r = t₂.gpr r) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ hr, State.callEntry_gpr _ hr, h]

theorem ce_rsp {t₁ t₂ : State} (h : t₁.gpr .rsp = t₂.gpr .rsp) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, h]

/-- Two runs at a call, each with `Ctx`, the same `rsp` and its arguments. -/
theorem two_ctx {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t) {a t₁ t₂ : State} (h₁ : At J a t₁)
    (h₂ : At J a t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  rsp_pin hJ a t₁ t₂ h₁ h₂ .rsp (List.mem_singleton_self _)

theorem init_two {J : State → State → Prop} (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0) :
    RelCT isa (Two (At J)) (.call (HH v).initN (HH v).initC) fun _ _ => True := by
  obtain ⟨-, -, -, -, hS, -, -, -⟩ := sizes v
  refine RelCT.callEx (OK v).stream.init.1 (OK v).stream.init.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂⟩ := hJ _ _ j₂
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Ctx s R EM t → t.gpr .rdi = scA s 0 →
      (VG.Proof.Pbkdf2.Md.X86_64.Calls.initK (HH v).stream.S (OK v).stream.SH.Repr).pre (t.callEntry.withRegions [] [⟨scA s 0, (HH v).stream.S⟩]) :=
    fun {s t R EM} hp hc hd => by
      refine ⟨rfl, by simp [State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hd], ?_⟩
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hd]
      rw [hS]
      exact (by rw [below_rsp hc]; exact stkD hp (by decide) (by decide) :
        (below (t.gpr .rsp) 16).Disjoint ⟨scA s 0, 96⟩).sub_left (Proof.Pbkdf2.Md.X86_64.Calls.ret_sub t)
  have cv : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Ctx s R EM t →
      Covers [⟨scA s 0, (HH v).stream.S⟩] t.wr := fun hp hc => by rw [hS]; exact scCov hp hc (by decide)
  refine ⟨_, _, _, _, pre S₁.p c₁ d₁, pre S₂.p c₂ d₂, ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr (cv S₁.p c₁), cv S₁.p c₁, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr (cv S₂.p c₂), cv S₂.p c₂, sp⟩


theorem upd_two {J : State → State → Prop} {da : State → Addr} {L : State → Nat} {si : State → BitVec 64}
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = si s ∧ t.gpr .rdx = da s ∧
      (t.gpr .rcx).toNat = L s ∧ t.gpr .r8 = scA s sWork)
    (hd : ∀ s, DPre s → DataOk s (da s) (L s)) (hda : ∀ a s, Sib a s → da s = da a)
    (hL : ∀ a s, Sib a s → L s = L a) (hsi : ∀ a s, Sib a s → si s = si a) :
    RelCT isa (Two (At J)) (.call (HH v).updN (HH v).updC) fun _ _ => True := by
  refine RelCT.callEx (OK v).stream.upd.1 (OK v).stream.upd.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := updArgsOf (v := v) S₁.p c₁ (hd _ S₁.p) d₁ x₁ k₁ r₁
  have A₂ := updArgsOf (v := v) S₂.p c₂ (hd _ S₂.p) d₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v).stream, A₂.pre (OK v).stream, ?_, A₁.covers (OK v).stream, A₁.cw,
    A₂.covers (OK v).stream, A₂.cw, sp⟩
  have cx : t₁.gpr .rcx = t₂.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [k₁, k₂, hL _ _ S₁, hL _ _ S₂])
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, hsi _ _ S₁, hsi _ _ S₂]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, hda _ _ S₁, hda _ _ S₂]) _ _ _ _, ce_eq (by decide) cx _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem fin_two {J : State → State → Prop}
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = s.gpr .r8 ∧ t.gpr .rdx = scA s sDH ∧
      t.gpr .rcx = scA s sWork) :
    RelCT isa (Two (At J)) (.call (HH v).finN (HH v).finC) fun _ _ => True := by
  refine RelCT.callEx (OK v).stream.fin.1 (OK v).stream.fin.2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂⟩ := hJ _ _ j₂
  have A₁ := finArgsOf (v := v) S₁.p c₁ d₁ x₁ k₁
  have A₂ := finArgsOf (v := v) S₂.p c₂ d₂ x₂ k₂
  refine ⟨_, _, _, _, A₁.pre (OK v).stream, A₂.pre (OK v).stream, ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr A₁.cw, A₁.cw, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr A₂.cw, A₂.cw,
    sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.gpr (r := .r8) (by decide), S₂.gpr (r := .r8) (by decide)]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, S₁.scr' sDH, S₂.scr' sDH]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem hinit_two {J : State → State → Prop} {kOff : Nat} (hk1 : sMsg ≤ kOff) (hk2 : kOff + 32 ≤ scrBytes)
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧ t.gpr .rdx = scA s kOff ∧
      t.gpr .rcx = BitVec.ofNat 64 32 ∧ t.gpr .r8 = scA s sWork) :
    RelCT isa (Two (At J)) (.call (HH v).hmacInitN (HH v).hmacInit) fun _ _ => True := by
  refine RelCT.callEx (hI v).1 (hI v).2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := hinitArgsOf (v := v) S₁.p c₁ hk1 hk2 d₁ i₁ x₁ k₁ r₁
  have A₂ := hinitArgsOf (v := v) S₂.p c₂ hk1 hk2 d₂ i₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v), A₂.pre (OK v), ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw, sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.scr' sOuter, S₂.scr' sOuter]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, S₁.scr' kOff, S₂.scr' kOff]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂]) _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩

theorem hfin_two {J : State → State → Prop} {dOff : State → Nat} {cnt : State → Addr}
    (hd1 : ∀ s, sMsg ≤ dOff s) (hd2 : ∀ s, dOff s + 32 ≤ scrBytes)
    (hJ : ∀ s t, J s t → Cx s t ∧ t.gpr .rdi = scA s 0 ∧ t.gpr .rsi = scA s sOuter ∧ t.gpr .rdx = cnt s ∧
      t.gpr .rcx = scA s (dOff s) ∧ t.gpr .r8 = scA s sWork)
    (hdO : ∀ a s, Sib a s → dOff s = dOff a) (hcnt : ∀ a s, Sib a s → cnt s = cnt a) :
    RelCT isa (Two (At J)) (.call (HH v).hmacFinN (HH v).hmacFin) fun _ _ => True := by
  refine RelCT.callEx (hF v).1 (hF v).2.1 fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_
  have sp := two_ctx (fun s t h => (hJ s t h).1) h₁ h₂
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  obtain ⟨⟨_, _, c₁⟩, d₁, i₁, x₁, k₁, r₁⟩ := hJ _ _ j₁
  obtain ⟨⟨_, _, c₂⟩, d₂, i₂, x₂, k₂, r₂⟩ := hJ _ _ j₂
  have A₁ := hfinArgsOf (v := v) S₁.p c₁ (hd1 s₁) (hd2 s₁) d₁ i₁ x₁ k₁ r₁
  have A₂ := hfinArgsOf (v := v) S₂.p c₂ (hd1 s₂) (hd2 s₂) d₂ i₂ x₂ k₂ r₂
  refine ⟨_, _, _, _, A₁.pre (OK v), A₂.pre (OK v), ?_,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw, sp⟩
  exact ⟨ce_eq (by decide) (by rw [d₁, d₂, S₁.scr' 0, S₂.scr' 0]) _ _ _ _,
    ce_eq (by decide) (by rw [i₁, i₂, S₁.scr' sOuter, S₂.scr' sOuter]) _ _ _ _,
    ce_eq (by decide) (by rw [x₁, x₂, hcnt _ _ S₁, hcnt _ _ S₂]) _ _ _ _,
    ce_eq (by decide) (by rw [k₁, k₂, hdO _ _ S₁, hdO _ _ S₂, S₁.scr', S₂.scr']) _ _ _ _,
    ce_eq (by decide) (by rw [r₁, r₂, S₁.scr' sWork, S₂.scr' sWork]) _ _ _ _, ce_rsp sp _ _ _ _⟩


/-! ## Pieces -/

/-- A piece the taint analysis checks from registers `J` fixes, with what
correctness gives after it. -/
theorem two_blk {J J' : State → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins (At J) rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s t, DPre s → J s t → WP isa c t (J' s)) : RelCT isa (Two (At J)) c (Two (At J')) :=
  two_piece rs hpin h fun _ _ ⟨s, S, j⟩ => WP.mono (hw _ _ S.p j) fun _ j' => ⟨s, S, j'⟩

/-- A piece related in two runs, with what correctness gives after it. -/
theorem two_then {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (At J)) c fun _ _ => True)
    (hw : ∀ s t, DPre s → J s t → WP isa c t (J' s)) : RelCT isa (Two (At J)) c (Two (At J')) :=
  two_post hct fun _ _ ⟨s, S, j⟩ => WP.mono (hw _ _ S.p j) fun _ j' => ⟨s, S, j'⟩

/-- Weakening what is known. -/
theorem two_weak {J J' : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ s t, J s t → J' s t) (hct : RelCT isa (Two (At J')) c Q) : RelCT isa (Two (At J)) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ⟨a, ⟨s₁, S₁, h _ _ j₁⟩, ⟨s₂, S₂, h _ _ j₂⟩⟩) fun _ _ q => q

/-- Relations that are unions. -/
theorem relCT_union {β : Type} {P : β → State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ b, RelCT isa (P b) c Q) : RelCT isa (fun s₁ s₂ => ∃ b, P b s₁ s₂) c Q :=
  fun _ _ _ _ _ _ ⟨b, hp⟩ e₁ e₂ => h b _ _ _ _ _ _ hp e₁ e₂

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
