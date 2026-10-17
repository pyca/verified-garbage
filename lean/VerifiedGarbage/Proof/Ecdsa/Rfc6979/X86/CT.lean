module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.X25519.X86.Column
meta import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): constant time, up to the number of candidates

Two runs whose public data agree (the pointers, `digest_len` and `hash`)
have the same layout, run the same hash function, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the save of our caller's registers and the frame's
release they are related by `Two` (`Two0` before the hash function's sizes
are stored): both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs). The blocks address only the stack and the buffers, from
registers that agree (the taint analysis); each dispatch on `hash` takes the
same case in both runs (`calls_ct`, by `Dispatch.chain_relCT`); each call, in
a frame of its arguments, is of constant-time code whose public data agree
(`hi_rel`, `upd_rel`, `hf_rel`, `callWithR_ct`); and the loops' branches
agree: the candidate's on the count of its `V`s, the same in both runs, and
the candidates' since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`). The frame's allocation and
release access no memory (`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Whole.X86 (hi_rel hf_rel)
open VG.Proof.Pbkdf2.Stream.X86 (upd_rel)

/-! ## Frames -/

/-- Two runs of a frame allocated on the stack leak the same trace when the
runs of its body, from the states after the allocation, do: the allocation
and the release access no memory. -/
theorem alloc_ct {n : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState n s₁ ∧ b = allocState n s₂) body R) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocState n s := by
    intro s a h
    simp only [isa, push] at h
    split at h <;> [cases h; cases h]
    rfl
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨by simp only [addrs], trivial⟩

/-- `RelCT.callWith`, for a frame popped into any register `r`. -/
theorem callWithR_ct {rs : List Reg} {r : Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {Pr : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, Pr s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa Pr (.frame (.push rs) (.call n c) (.pop r rs.length)) fun _ _ => True := by
  refine VG.X86.RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (VG.X86.RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

/-! ## Two runs -/

/-- What each of two runs has, between the save of our caller's registers
and the frame's release. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.I.hashLen → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the layout and saved registers of `e`, that stop at the
same candidate, each satisfying `Ctx` and `Φ`. -/
def TwoAt (P : RfcHash) (Φ : Pred P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ Fits P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pred P) (a b : State) : Prop := ∃ e, TwoAt P Φ e a b

/-- `TwoAt`, before the hash function's sizes are stored (`Ctx0`). -/
def TwoAt0 (P : RfcHash) (Φ : Pred P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ Fits P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx0 e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx0 e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.1 e.2.2.2.2 b

def Two0 (P : RfcHash) (Φ : Pred P) (a b : State) : Prop := ∃ e, TwoAt0 P Φ e a b

variable {P : RfcHash}

theorem two_exists {Φ : Pred P} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ e, RelCT isa (TwoAt P Φ e) c Q) : RelCT isa (Two P Φ) c Q :=
  VG.RelCT.exists_ h

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g m₀ t, Φ L g m₀ t → Ψ L g m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ _ f₁, h _ _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → Fits P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL hq c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL hq c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem esp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx0 L g₁ m₁ t₁) (c₂ : Ctx0 L g₂ m₂ t₂) : t₁.gpr .esp = t₂.gpr .esp :=
  c₁.esp.trans c₂.esp.symm

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr rs) (.block is) hc).isSome = true

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem espOnly {Φ : Pred P} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ [Reg.esp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact esp_two c₁.toCtx0 c₂.toCtx0

/-- Code that leaves `Φ` with other flags: the dispatch's tests. -/
def FlagStable (Φ : Pred P) : Prop :=
  ∀ L g m₀ t t', Proof.Dispatch.X86.FlagsOnly t t' → Φ L g m₀ t → Φ L g m₀ t'

/-- The dispatch on `hash` in `ebx`: both runs take the run's hash function's case. -/
theorem calls_ct {mk : Impl.Pbkdf2.Whole.X86.Fns → Prog isa} {Φ : Pred P} {Q : State → State → Prop}
    (hbx : ∀ L g m₀ t, Φ L g m₀ t → t.gpr .ebx = L.hs) (hst : FlagStable Φ)
    (h : RelCT isa (Two P Φ) (mk P.F) Q) : RelCT isa (Two P Φ) ((cfgOf P).calls mk) Q := by
  show RelCT isa (Two P Φ) (Impl.Dispatch.X86.chain .ebx (P.fns.map fun p => (p.1, mk p.2))) Q
  have hkeys : Proof.Dispatch.keys (P.fns.map fun p => (p.1, mk p.2)) = P.fns.map (·.1) := by
    simp only [Proof.Dispatch.keys, List.map_map]; rfl
  have hm : (P.k, mk P.F) ∈ P.fns.map fun p => (p.1, mk p.2) := List.mem_map.mpr ⟨_, P.mem, rfl⟩
  have hnd : (Proof.Dispatch.keys (P.fns.map fun p => (p.1, mk p.2))).Nodup := by rw [hkeys]; exact P.nodup
  have hsel : ∀ s₁ s₂, Two P Φ s₁ s₂ → Proof.Dispatch.X86.sel .ebx s₁ = P.k ∧ Proof.Dispatch.X86.sel .ebx s₂ = P.k :=
    fun _ _ ⟨_, _, hk, _, _, _, f₁, f₂⟩ => ⟨by simp only [Proof.Dispatch.X86.sel]; rw [hbx _ _ _ _ f₁, hk.hs],
      by simp only [Proof.Dispatch.X86.sel]; rw [hbx _ _ _ _ f₂, hk.hs]⟩
  refine Proof.Dispatch.chain_relCT (Proof.Dispatch.X86.tests .ebx) (fun k hk' => ?_) hnd
    (fun s₁ s₂ hp => ⟨(hsel _ _ hp).1.trans (hsel _ _ hp).2.symm, by
      rw [(hsel _ _ hp).1, hkeys]; exact List.mem_map.mpr ⟨_, P.mem, rfl⟩⟩) fun k c hc => ?_
  · rw [hkeys] at hk'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk'
    exact P.keys_lt p hp
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hrel e₁ e₂
    obtain ⟨a₁, a₂, hp, hk₁, r₁, r₂, -, -⟩ := hrel
    rw [(hsel _ _ hp).1] at hk₁
    subst hk₁
    rw [Proof.Dispatch.case_unique hnd hc hm] at e₁ e₂
    obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := hp
    exact h _ _ _ _ _ _ ⟨e, hL, hq, hx, c₁.flags hL r₁, c₂.flags hL r₂, hst _ _ _ _ _ r₁ f₁, hst _ _ _ _ _ r₂ f₂⟩ e₁ e₂

/-! ## The blocks that set the calls' arguments -/

theorem init_blk : TaintOk [.esp] hmacArgs₁ := ⟨_, by native_taint_decide⟩
theorem vUpd_blk : TaintOk [.esp] (hmacArgs₂ (fr .edx fV) pD) := ⟨_, by native_taint_decide⟩
theorem vFin_blk : TaintOk [.esp] (hmacArgs₃ pF0 fV) := ⟨_, by native_taint_decide⟩
theorem kUpd₁_blk : TaintOk [.esp] (hmacArgs₂ (scr .edx sMsg) pL1) := ⟨_, by native_taint_decide⟩
theorem kFin₁_blk : TaintOk [.esp] (hmacArgs₃ pF1 fK) := ⟨_, by native_taint_decide⟩
theorem kUpdF_blk : TaintOk [.esp] (hmacArgs₂ (scr .edx sMsg) pLF) := ⟨_, by native_taint_decide⟩
theorem kFinF_blk : TaintOk [.esp] (hmacArgs₃ pFF fK) := ⟨_, by native_taint_decide⟩

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`, and `hash` in `ebx`. -/
def IA (P : RfcHash) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧
    u.gpr .edx = L.F + BitVec.ofNat 32 0 ∧ u.gpr .ecx = L.pv 0 ∧
    u.gpr .ebp = L.a3 + BitVec.ofNat 32 384 ∧ u.gpr .ebx = L.hs

/-- The arguments of the streaming `update`, for the data at `dv L` of `len`
bytes (the size `il`), and `hash` in `ebx`. -/
def UA (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (il : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32)
    (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.pv 1 ∧ u.gpr .eax = 0 ∧
    u.gpr .edx = dv L ∧ u.gpr .ecx = L.pv il ∧ u.gpr .ebp = L.a3 + BitVec.ofNat 32 384 ∧ u.gpr .ebx = L.hs

/-- The arguments of HMAC's `finalize`, for the size `it` of the inner state
and the MAC to `dst`, and `hash` in `ebx`. -/
def FA (P : RfcHash) (it dst : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edx = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧
    u.gpr .eax = L.pv it ∧ u.gpr .ecx = 0 ∧ u.gpr .edi = L.F + BitVec.ofNat 32 dst ∧
    u.gpr .ebp = L.a3 + BitVec.ofNat 32 384 ∧ u.gpr .ebx = L.hs

theorem flagStable_regs {Φ : Pred P} (h : ∀ L g m₀ (t t' : State), (∀ r, t'.gpr r = t.gpr r) → Φ L g m₀ t → Φ L g m₀ t') :
    FlagStable Φ := fun L g m₀ t t' hr hp => h L g m₀ t t' hr.gpr hp

theorem hinit_ct :
    RelCT isa (Two P (IA P)) ((cfgOf P).calls hiCall) fun _ _ => True :=
  calls_ct (fun _ _ _ _ h => h.2.2.2.2.2)
    (flagStable_regs fun _ _ _ _ _ hr ⟨a, b, c, d, e, f⟩ => ⟨by rw [hr]; exact a, by rw [hr]; exact b, by rw [hr]; exact c,
      by rw [hr]; exact d, by rw [hr]; exact e, by rw [hr]; exact f⟩)
    (two_exists fun e => hi_rel P.ok.hi (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
      ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2.1,
        initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2.1, c₁.esp, c₂.esp⟩)

theorem hupd_ct {dv : Lay P.I.hashLen → BitVec 32} {len il : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256)
    (hpl : ∀ L : Lay P.I.hashLen, Fits P L → L.pv il = BitVec.ofNat 32 len) :
    RelCT isa (Two P (UA P dv il)) ((cfgOf P).calls updCall) fun _ _ => True :=
  calls_ct (fun _ _ _ _ h => h.2.2.2.2.2.2)
    (flagStable_regs fun _ _ _ _ _ hr ⟨a, b, c, d, e, f, k⟩ => ⟨by rw [hr]; exact a, by rw [hr]; exact b,
      by rw [hr]; exact c, by rw [hr]; exact d, by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact k⟩)
    (two_exists fun e => upd_rel P.ok.hH (sp := e.1.F) fun _ _ ⟨hL, hk, _, c₁, c₂, a₁, a₂⟩ =>
      ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 (by rw [a₁.2.1]; show BitVec.ofNat 32 e.1.Bk = _; rw [hk.bk])
          a₁.2.2.1 a₁.2.2.2.1 (by rw [a₁.2.2.2.2.1, hpl _ hk]) a₁.2.2.2.2.2.1,
        updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 (by rw [a₂.2.1]; show BitVec.ofNat 32 e.1.Bk = _; rw [hk.bk])
          a₂.2.2.1 a₂.2.2.2.1 (by rw [a₂.2.2.2.2.1, hpl _ hk]) a₂.2.2.2.2.2.1, c₁.esp, c₂.esp⟩)

theorem hfin_ct {len it dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (hpt : ∀ L : Lay P.I.hashLen, Fits P L → L.pv it = BitVec.ofNat 32 (P.F.H.B + len)) :
    RelCT isa (Two P (FA P it dst)) ((cfgOf P).calls hfCall) fun _ _ => True :=
  calls_ct (fun _ _ _ _ h => h.2.2.2.2.2.2)
    (flagStable_regs fun _ _ _ _ _ hr ⟨a, b, c, d, e, f, k⟩ => ⟨by rw [hr]; exact a, by rw [hr]; exact b,
      by rw [hr]; exact c, by rw [hr]; exact d, by rw [hr]; exact e, by rw [hr]; exact f, by rw [hr]; exact k⟩)
    (two_exists fun e => hf_rel P.ok.hf (sp := e.1.F) fun _ _ ⟨hL, hk, _, c₁, c₂, a₁, a₂⟩ =>
      ⟨finA (P := P) hL c₁ (len := len) hdst a₁.1 a₁.2.1 (by rw [a₁.2.2.1, hpt _ hk]) a₁.2.2.2.1 a₁.2.2.2.2.1
          a₁.2.2.2.2.2.1,
        finA (P := P) hL c₂ (len := len) hdst a₂.1 a₂.2.1 (by rw [a₂.2.2.1, hpt _ hk]) a₂.2.2.2.1 a₂.2.2.2.2.1
          a₂.2.2.2.2.2.1, c₁.esp, c₂.esp⟩)

/-! ## One HMAC -/

/-- After HMAC's `init` and `update`: the states, for the state before. -/
def Ini (P : RfcHash) : Pred P := fun L g m₀ u => ∃ t, Inited P L g m₀ t u
def Upt (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P :=
  fun L g m₀ u => ∃ t, Updated P L g m₀ t (dv L) len u

theorem initS_ct {Φ : Pred P} :
    RelCT isa (Two P Φ) (.seq (.block hmacArgs₁) ((cfgOf P).calls hiCall)) (Two P (Ini P)) :=
  two_wp ((two_wp (Ψ := IA P) (two_blk [.esp] espOnly init_blk) fun _ _ _ _ hL _ hc _ =>
      WP.mono (initArgs_ok hL hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq hinit_ct)
    fun _ _ _ t hL hk hc _ => WP.mono (init_step hL hk hc) fun _ h => ⟨h.ctx, t, h⟩

theorem updS_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len il lenS : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → Fits P L → Ctx L g m₀ u →
      WP isa (.block dataA) u (Upd L g m₀ u .edx (dv L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) (hil : il < 8)
    (hlS : lenS = 128 + 4 * il) (hpl : ∀ L : Lay P.I.hashLen, Fits P L → L.pv il = BitVec.ofNat 32 len)
    (t₂ : TaintOk [.esp] (hmacArgs₂ dataA lenS)) :
    RelCT isa (Two P (Ini P)) (.seq (.block (hmacArgs₂ dataA lenS)) ((cfgOf P).calls updCall))
      (Two P (Upt P dv len)) :=
  two_wp ((two_wp (Ψ := UA P dv il) (two_blk [.esp] espOnly t₂) fun L g m₀ _ hL hk hc _ =>
      WP.mono (updArgs_ok hL hc (fun u hu => hdA L g m₀ u hL hk hu) hil hlS) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq
      (hupd_ct hd hlen hpl))
    fun L g m₀ _ hL hk _ ⟨t, hi⟩ =>
      WP.mono (upd_step hL hk hi (fun u hu => hdA L g m₀ u hL hk hu) (hd L hL) hlen hil hlS (hpl L hk))
        fun _ h => ⟨h.ctx, t, h⟩

theorem finS_ct {dv : Lay P.I.hashLen → BitVec 32} {len dst it totS : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (hit : it < 8) (htS : totS = 128 + 4 * it)
    (hpt : ∀ L : Lay P.I.hashLen, Fits P L → L.pv it = BitVec.ofNat 32 (P.F.H.B + len))
    (t₃ : TaintOk [.esp] (hmacArgs₃ totS dst)) :
    RelCT isa (Two P (Upt P dv len)) (.seq (.block (hmacArgs₃ totS dst)) ((cfgOf P).calls hfCall))
      fun _ _ => True :=
  (two_wp (Ψ := FA P it dst) (two_blk [.esp] espOnly t₃) fun _ _ _ _ hL _ hc _ =>
    WP.mono (finArgs_ok hL hc hit htS dst) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq (hfin_ct hdst hpt)

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from
`esp`, and its calls are of the run's hash function, constant time with
arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len dst il it lenS totS : Nat}
    {Φ : Pred P}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → Fits P L → Ctx L g m₀ u →
      WP isa (.block dataA) u (Upd L g m₀ u .edx (dv L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 128)
    (hil : il < 8) (hit : it < 8) (hlS : lenS = 128 + 4 * il) (htS : totS = 128 + 4 * it)
    (hpl : ∀ L : Lay P.I.hashLen, Fits P L → L.pv il = BitVec.ofNat 32 len)
    (hpt : ∀ L : Lay P.I.hashLen, Fits P L → L.pv it = BitVec.ofNat 32 (P.F.H.B + len))
    (t₂ : TaintOk [.esp] (hmacArgs₂ dataA lenS)) (t₃ : TaintOk [.esp] (hmacArgs₃ totS dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA lenS totS dst) fun _ _ => True :=
  RelCT.assoc (initS_ct.seq (RelCT.assoc ((updS_ct hdA hd hlen hil hlS hpl t₂).seq (finS_ct hdst hit htS hpt t₃))))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dv := fun L => L.F + BitVec.ofNat 32 64) (len := P.F.H.D) (dst := 64) (il := 0) (it := 4)
    (fun _ _ _ _ hL _ hu => fr_ok hL hu (d := .edx) (by decide) 64)
    (fun _ _ => .inl ⟨64, rfl, by nums⟩) (by nums) (by nums) (by decide) (by decide) rfl rfl
    (fun _ hk => (pv_eq hk).1) (fun _ hk => (pv_eq hk).2.2.2.1) vUpd_blk vFin_blk

/-- `K = HMAC_K(m)`, for the message of the size `il` at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Pred P} {len il it lenS totS : Nat} (hlen : len ≤ 256) (hil : il < 8) (hit : it < 8)
    (hlS : lenS = 128 + 4 * il) (htS : totS = 128 + 4 * it)
    (hpl : ∀ L : Lay P.I.hashLen, Fits P L → L.pv il = BitVec.ofNat 32 len)
    (hpt : ∀ L : Lay P.I.hashLen, Fits P L → L.pv it = BitVec.ofNat 32 (P.F.H.B + len))
    (t₂ : TaintOk [.esp] (hmacArgs₂ (scr .edx sMsg) lenS)) (t₃ : TaintOk [.esp] (hmacArgs₃ totS fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (scr .edx sMsg) lenS totS fK) fun _ _ => True :=
  hmac_ct (dv := fun L => L.a3 + BitVec.ofNat 32 2256) (dst := 0)
    (fun _ _ _ _ hL _ hu => scr_ok hL hu (d := .edx) (by decide) 2256)
    (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) hlen (by nums) hil hit hlS htS hpl hpt t₂ t₃

/-- The message's pointers. -/
theorem msgPtrs_blk : TaintOk [.esp] msgPtrs := ⟨_, by native_taint_decide⟩
theorem msgV_blk : TaintOk [.esp, .edi] msgV := ⟨_, by native_taint_decide⟩

/-- The message's tail, for each length of the scalars. -/
theorem msgTail_blk {Q : Nat} (hQ : Q = 24 ∨ Q = 28 ∨ Q = 32 ∨ Q = 48 ∨ Q = 64 ∨ Q = 66) :
    TaintOk [.esp, .edi, .esi] (msgTail Q 0 true) ∧ TaintOk [.esp, .edi, .esi] (msgTail Q 1 true) ∧
      TaintOk [.esp, .edi, .esi] (msgTail Q 0 false) := by
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem lengths (P : RfcHash) : P.Q = 24 ∨ P.Q = 28 ∨ P.Q = 32 ∨ P.Q = 48 ∨ P.Q = 64 ∨ P.Q = 66 := by
  cases hW : P.R.wide
  · rcases P.lengthsA hW with h | h | h | h | h <;> simp [h]
  · simp [(P.sizesW hW).2.1]

/-- `scratch` in `edi`, `d` in `esi`. -/
def PtrsIn {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 ∧ u.gpr .esi = L.a1

/-- `scratch + D` in `edi`, `d` in `esi`. -/
def TailIn {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 + BitVec.ofNat 32 dn ∧ u.gpr .esi = L.a1

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} {full : Bool} {il it lenS totS : Nat}
    (hil : il < 8) (hit : it < 8) (hlS : lenS = 128 + 4 * il) (htS : totS = 128 + 4 * it)
    (hpl : ∀ L : Lay P.I.hashLen, Fits P L →
      L.pv il = BitVec.ofNat 32 (if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1))
    (hpt : ∀ L : Lay P.I.hashLen, Fits P L →
      L.pv it = BitVec.ofNat 32 (P.F.H.B + (if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1)))
    (t₁ : TaintOk [.esp, .edi, .esi] (msgTail P.Q b full))
    (t₂ : TaintOk [.esp] (hmacArgs₂ (scr .edx sMsg) lenS)) (t₃ : TaintOk [.esp] (hmacArgs₃ totS fK)) :
    RelCT isa (Two P Φ) (.seq (.block msgPtrs) (.seq (.block msgV) (.seq (.block (msgTail P.Q b full))
      (.seq ((cfgOf P).hmac (scr .edx sMsg) lenS totS fK) (cfgOf P).hmacV)))) fun _ _ => True := by
  have hlen' : (if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1) ≤ 256 := by
    cases full <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> nums
  refine (two_wp (Ψ := PtrsIn) (two_blk [.esp] espOnly msgPtrs_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, a, b'⟩ => ⟨c, a, b'⟩).seq ?_
  refine (two_wp (Ψ := TailIn) (two_blk [.esp, .edi] (fun L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact esp_two c₁.toCtx0 c₂.toCtx0
      · exact f₁.1.trans f₂.1.symm) msgV_blk) fun _ _ _ _ hL _ hc hp =>
    WP.mono (msgV_ok hL hc hp.1) fun _ ⟨c, hg, hdi, _⟩ => ⟨c, hdi, by rw [hg _ (by decide) (by decide), hp.2]⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ _ => True) (two_blk [.esp, .edi, .esi] (fun L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact esp_two c₁.toCtx0 c₂.toCtx0
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) t₁) fun _ _ _ _ hL hk hc hp =>
    WP.mono (msgTail_ok hL hc hp.1 hp.2 b full (by nums) (by nums) (by nums) (by rw [hk.q]))
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ _ => True) (hmacK_ct hlen' hil hit hlS htS hpl hpt t₂ t₃) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok (P := P) hL hk hc hlen' hil hit hlS htS (hpl _ hk) (hpt _ hk)) fun _ h => ⟨h.1, trivial⟩).seq
    hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  have ht := msgTail_blk (lengths P)
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (full := true) (il := 3) (it := 6) (by decide) (by decide) rfl rfl
      (fun _ hk => (pv_eq hk).2.2.1) (fun _ hk => (pv_eq hk).2.2.2.2.2) ht.1 kUpdF_blk kFinF_blk
  · exact rekey_gen_ct (full := true) (il := 3) (it := 6) (by decide) (by decide) rfl rfl
      (fun _ hk => (pv_eq hk).2.2.1) (fun _ hk => (pv_eq hk).2.2.2.2.2) ht.2.1 kUpdF_blk kFinF_blk

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) (il := 2) (it := 5) (by decide) (by decide) rfl rfl
    (fun _ hk => (pv_eq hk).2.1) (fun _ hk => (pv_eq hk).2.2.2.2.1) (msgTail_blk (lengths P)).2.2 kUpd₁_blk kFin₁_blk

/-! ## The candidate -/

theorem candInit_blk : TaintOk [.esp] candInit := ⟨_, by native_taint_decide⟩
theorem candAt_blk : TaintOk [.esp] Impl.Ecdsa.Rfc6979.X86.candAt := ⟨_, by native_taint_decide⟩
theorem candStep_blk : TaintOk [.esp, .edi] candStep := ⟨_, by native_taint_decide⟩
theorem scrPtr_blk : TaintOk [.esp] scrPtr := ⟨_, by native_taint_decide⟩

/-- The offset and count of the candidate's `V`s, after `i` of them. -/
def CI (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 (i * P.F.H.D) ∧
    u.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 (P.nb - i) ∧ i < P.nb

/-- `CI`, and where the next `V` goes in `edi`. -/
def CIe (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop :=
  CI P i L g m₀ u ∧ u.gpr .edi = L.F + BitVec.ofNat 32 (332 + i * P.F.H.D)

/-- `scratch` in `edi`. -/
def ScrIn {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop := u.gpr .edi = L.a3

/-- One of the candidate's `V`s: both runs go on, or both stop. -/
theorem candIter_ct {i : Nat} :
    RelCT isa (Two P (CI P i)) (.seq (cfgOf P).hmacV (.seq (.block Impl.Ecdsa.Rfc6979.X86.candAt) (.block candStep)))
      (Two P fun L g m u => (i + 1 < P.nb → CI P (i + 1) L g m u) ∧ isa.eval .ne u = some (decide (i + 1 < P.nb))) := by
  have hnb := P.nb_facts
  refine (two_wp (Ψ := CI P i) hmacV_ct fun L _ _ _ hL hk hc hi => WP.mono (hmacV_ok hL hk hc)
      fun _ ⟨c, hf, _, _⟩ => ⟨c, ?_⟩).seq ?_
  · have kvw : ∀ o, 236 ≤ o → o + 4 ≤ 244 → ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, 4⟩ r :=
      fun o h₁ h₂ r hr => by
        have nB := hL.nB
        simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_SCR (by omega)
        · exact Offset.disjoint_base _ (by omega) (by omega)
    exact ⟨(hf.readW (Region.contains_self _ _) (kvw 236 (by omega) (by omega)) (by decide)).trans hi.1,
      (hf.readW (Region.contains_self _ _) (kvw 240 (by omega) (by omega)) (by decide)).trans hi.2.1, hi.2.2⟩
  refine (two_wp (Ψ := CIe P i) (two_blk [.esp] espOnly candAt_blk) fun _ _ _ _ hL _ hc hi =>
    WP.mono (candAt_ok hL hc hi.1) fun _ h => ⟨h.ctx, ⟨by rw [h.mem]; exact hi.1, by rw [h.mem]; exact hi.2.1,
      hi.2.2⟩, h.val⟩).seq ?_
  refine (two_wp (Ψ := fun L g m u => (i + 1 < P.nb → CI P (i + 1) L g m u) ∧
      isa.eval .ne u = some (decide (i + 1 < P.nb)))
    (two_blk [.esp, .edi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact esp_two c₁.toCtx0 c₂.toCtx0
      · exact f₁.2.trans f₂.2.symm) candStep_blk) fun L _ _ _ hL hk hc hi => ?_)
  · have hiD : i * P.F.H.D ≤ 64 :=
      Nat.le_trans (Nat.mul_le_mul_right _ (show i ≤ P.nb - 1 by have := hi.1.2.2; omega)) hnb.2.2.1
    refine WP.mono (candStep_ok hL hc hiD hi.2 hi.1.1 hi.1.2.1) fun u ⟨c, _, _, ho, hn, hz⟩ => ⟨c, fun hlt =>
      ⟨by rw [ho, show L.pv 0 = BitVec.ofNat 32 P.F.H.D from rfl, BitVec.ofNat_add_ofNat, Nat.succ_mul],
        by rw [hn, cnt_sub hi.1.2.2], hlt⟩, ?_⟩
    show u.zf.map (!·) = _
    rw [hz, cnt_sub hi.1.2.2]
    have := cnt_ne (T := P.nb) (i := i) (by omega)
    by_cases hc' : i + 1 < P.nb
    · have h1 := this.mpr hc'
      simp only [hc', decide_true, Option.map_some, beq_eq_false_iff_ne.mpr h1, Bool.not_false]
    · have h0 : BitVec.ofNat 32 (P.nb - (i + 1)) = 0 := Classical.not_not.mp (mt this.mp hc')
      simp only [hc', decide_false, Option.map_some, h0, beq_self_eq_true, Bool.not_true]

/-- The candidate's `V`s. -/
theorem candLoop_ct :
    RelCT isa (Two P (CI P 0)) (.loop (.seq (cfgOf P).hmacV (.seq (.block Impl.Ecdsa.Rfc6979.X86.candAt)
      (.block candStep))) .ne) (Two P fun _ _ _ _ => True) := by
  have hnb := P.nb_facts
  have h := VG.RelCT.loop (M := isa) (Q := Two P fun _ _ _ _ => True) (c := .ne)
    (body := .seq (cfgOf P).hmacV (.seq (.block Impl.Ecdsa.Rfc6979.X86.candAt) (.block candStep)))
    (fun n s₁ s₂ => 1 ≤ n ∧ n ≤ P.nb ∧ Two P (CI P (P.nb - n)) s₁ s₂) (fun n => ?_) P.nb
  · exact h.mono (fun s₁ s₂ h' => ⟨hnb.1, Nat.le_refl _, by rw [Nat.sub_self]; exact h'⟩) fun _ _ h => h
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂
    obtain ⟨ht, e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := candIter_ct (P := P) (i := P.nb - n) _ _ _ _ _ _ hp e₁ e₂
    refine ⟨ht, f₁.2.trans f₂.2.symm, fun _ => ⟨e, hL, hk, hx, c₁, c₂, trivial, trivial⟩, fun hc => ?_⟩
    have hlt : P.nb - n + 1 < P.nb := by
      have := f₁.2; rw [hc] at this; exact of_decide_eq_true (Option.some.inj this).symm
    refine ⟨n - 1, by omega, by omega, by omega, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩
    · rw [show P.nb - (n - 1) = P.nb - n + 1 by omega]; exact f₁.1 hlt
    · rw [show P.nb - (n - 1) = P.nb - n + 1 by omega]; exact f₂.1 hlt

/-- The conversions of P-521's candidate and digest. -/
theorem conv_blks (hW : P.R.wide = true) :
    TaintOk [.esp, .edi] ((cfgOf P).conv fC (cfgOf P).sh) ∧
      TaintOk [.esp, .edi] ((cfgOf P).conv fX (8 - (cfgOf P).sh) ++ initKV) := by
  have hQ : (cfgOf P).len = 66 := (P.sizesW hW).2.1
  have h7 : (cfgOf P).sh = 7 := (P.sizesW hW).2.2
  simp only [Cfg.conv, hQ, h7]
  exact ⟨⟨_, by native_taint_decide⟩, ⟨_, by native_taint_decide⟩⟩

theorem scrIn_regs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
    ScrIn L g₁ m₁ t₁ → ScrIn L g₂ m₂ t₂ → ∀ r ∈ [Reg.esp, .edi], t₁.gpr r = t₂.gpr r := by
  intro _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_two c₁.toCtx0 c₂.toCtx0
  · exact f₁.trans f₂.symm

theorem scrPtr_two {Φ : Pred P} : RelCT isa (Two P Φ) (.block scrPtr) (Two P ScrIn) :=
  two_wp (two_blk [.esp] espOnly scrPtr_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 4) (by decide)) fun _ h => ⟨h.ctx, h.val⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  refine (two_wp (Ψ := CI P 0) (two_blk [.esp] espOnly candInit_blk) fun _ _ _ _ hL hk hc _ =>
    WP.mono (candInit_ok hL hk hc) fun _ h => ⟨h.ctx, by simpa using h.off, h.cnt2, P.nb_facts.1⟩).seq ?_
  refine candLoop_ct.seq ?_
  cases hW : P.R.wide
  · simp only [show (cfgOf P).sh = 0 from P.sh0 hW, ite_true]
    exact two_blk [] (fun _ _ _ _ _ _ _ _ _ _ _ r hr => absurd hr (List.not_mem_nil)) ⟨_, by native_taint_decide⟩
  · have hs : (cfgOf P).sh ≠ 0 := by rw [show (cfgOf P).sh = 7 from (P.sizesW hW).2.2]; decide
    simp only [hs, ite_false]
    exact scrPtr_two.seq (two_blk [.esp, .edi] scrIn_regs (conv_blks hW).1)

/-! ## One candidate -/

/-- `core`, in a frame of its arguments, which agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u)
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call P.R.coreN P.R.coreC) (.pop .ecx 5))
      fun _ _ => True :=
  two_exists fun e => callWithR_ct (rs := core5) P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun _ _ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      obtain ⟨v₀, v₁, v₂, v₃, v₄⟩ := core_argv hL c₁ a₁ (rd := coreRd P e.1) (wr := coreWr P e.1)
      obtain ⟨w₀, w₁, w₂, w₃, w₄⟩ := core_argv hL c₂ a₂ (rd := coreRd P e.1) (wr := coreWr P e.1)
      refine ⟨core_callPre hL hk c₁ a₁, core_callPre hL hk c₂ a₂, esp_two c₁.toCtx0 c₂.toCtx0,
        by rw [State.withRegions_gpr, State.withRegions_gpr, core_esp c₁, core_esp c₂],
        by rw [v₀, w₀], by rw [v₁, w₁], by rw [v₂, w₂], by rw [v₃, w₃], by rw [v₄, w₄], ?_⟩
      intro c hc
      rw [← hk.cs] at hc
      rw [core_syms c₁ hc, core_syms c₂ hc]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem coreArgs_blk : TaintOk [.esp] coreArgs := ⟨_, by native_taint_decide⟩
theorem goOn_blk : TaintOk [.esp] goOn := ⟨_, by native_taint_decide⟩
theorem again_blk : TaintOk [.esp] again := ⟨_, by native_taint_decide⟩
theorem stop_blk : TaintOk [.esp] stop := ⟨_, by native_taint_decide⟩
theorem wipe_blk : TaintOk [.esp] wipe := ⟨_, by native_taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u)
    (two_blk [.esp] espOnly coreArgs_blk) fun _ _ _ _ hL _ hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk [.esp] espOnly goOn_blk)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ _ => True) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL hk hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [.esp] espOnly again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.esp] espOnly stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (fun L _ m₀ t => Exit P L m₀ i t) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (fun L _ m₀ t => LoopInv P L m₀ (i + 1) t) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega)), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {T n : Nat} (h : T - n + 1 < T) : T - (T - n + 1) < n ∧ T - (T - (T - n + 1)) = T - n + 1 :=
  ⟨by omega, by omega⟩

theorem loop_ct :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

/-- One count's initial store, from which every count's follows. -/
abbrev initCnt₀ : List Instr := (cfgC
    { n := 4, C := Spec.P256.curve, SP := Spec.Weierstrass.Mont.p256p, SN := Spec.Weierstrass.Mont.p256n }).initCnt

/-- The analysis' hint for `initCnt₀`. -/
abbrev initCntHint : VG.Taint.Hint taint.T := taint.hintOfSize Taint.chunk (τr [.esp]) (.block initCnt₀)

theorem initCnt_blk₀ : (VG.Taint.check taint (τr [.esp]) (.block initCnt₀) initCntHint).isSome = true := by
  decide +kernel

/-- The count's initial store, for any count: the analysis does not read
immediates (`check_erase`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk [.esp] c.initCnt := by
  refine ⟨initCntHint, ?_⟩
  have hn : Taint.noBases (τr [.esp]) = true := by decide +kernel
  have hh : Taint.hintNoBases initCntHint = true := by decide +kernel
  rw [← Taint.check_erase (.block c.initCnt) _ _ hn hh,
    show Code.erase (.block c.initCnt) = Code.erase (.block initCnt₀) from rfl,
    Taint.check_erase (.block initCnt₀) _ _ hn hh]
  exact initCnt_blk₀

/-- `h = X mod n`, or P-521's shift of `X`, and `K` and `V`. -/
theorem prep_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).prep fun _ _ => True := by
  cases hW : P.R.wide
  · simp only [Cfg.prep, show (cfgOf P).sh = 0 from P.sh0 hW, ite_true]
    exact two_blk [.esp] espOnly (P.R.reduceT hW)
  · have hs : (cfgOf P).sh ≠ 0 := by rw [show (cfgOf P).sh = 7 from (P.sizesW hW).2.2]; decide
    simp only [Cfg.prep, hs, ite_false]
    exact scrPtr_two.seq (two_blk [.esp, .edi] scrIn_regs (conv_blks hW).2)

/-- The body after the hash function's sizes and `X`. -/
theorem rest_ct :
    RelCT isa (Two P fun L _ m₀ t => XOk P L m₀ t.mem) (.seq (cfgOf P).prep
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block wipe)))))) fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QB P L m₀ t) prep_ct fun _ _ _ _ hL _ hc h =>
    stageB_ok (P := P) hL hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk [.esp] espOnly (initCnt_blk _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  exact loop_ct.seq (two_blk [.esp] espOnly wipe_blk)

end VG.Proof.Ecdsa.Rfc6979.X86
