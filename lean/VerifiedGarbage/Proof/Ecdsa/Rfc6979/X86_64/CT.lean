module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: constant time, up to the number of candidates

Two runs whose public data agree call the same hash function (the
precondition fixes `hash`), have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frame's push and pop they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis; the blocks that depend on the curve are checked for it,
`CurveBlks`, and those whose immediates depend on the hash function are
checked once for any immediates, `taintOk_erase`); each dispatch on the hash
function runs the same case in both runs (`two_dispatch`); each call is of
constant-time code whose public data agree (`RelCT.callEx`); and the loops'
branches agree: the candidate's, since in both runs its offset is the same
after the same number of `V`s, and the candidates', since in both runs it
goes on after candidate `i` iff `i` is before the candidate it stops at
(`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL hq c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL hq c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem Two.mono {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

theorem rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rspOnly {Φ : Lay P.I.hashLen → Mem → State → Prop} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-- The taint check of a block passes if it does of a block that differs only
in displacements and immediates: the analysis does not read them
(`taint_eraseInv`). -/
theorem taintOk_erase {rs : List Reg} {is is' : List Instr}
    (he : Code.mapBlocks Instr.erase (.block is : Prog isa) = Code.mapBlocks Instr.erase (.block is' : Prog isa))
    (h : TaintOk rs is') :
    TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨hc, ?_⟩
  rw [← (taint_eraseInv.check (.block is) (Taint.ofRegs rs) hc rfl).1, he,
    (taint_eraseInv.check (.block is') (Taint.ofRegs rs) hc rfl).1]
  exact hs

/-! ## The dispatches on the hash function -/

/-- `Φ` does not depend on the flags. -/
def NoFlags (Φ : Lay P.I.hashLen → Mem → State → Prop) : Prop :=
  ∀ L m₀ t t', Φ L m₀ t → Proof.Dispatch.X86_64.FlagsOnly t t' → Φ L m₀ t'

/-- A dispatch on the hash function, `hash` in `rax`: both runs run the case
of `P`'s, from states of other flags. -/
theorem two_dispatch {f : Impl.Pbkdf2.Md.X86_64.Hash → Prog isa} {Φ : Lay P.I.hashLen → Mem → State → Prop}
    {Q : State → State → Prop} (hax : ∀ L m₀ t, Φ L m₀ t → t.gpr .rax = BitVec.ofNat 64 P.k) (hΦ : NoFlags Φ)
    (h : RelCT isa (Two P Φ) (f P.H) Q) :
    RelCT isa (Two P Φ) (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, f p.2))) Q := by
  have hk := P.hk
  have hk8 : P.k < 8 := by
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hsel : ∀ L m₀ t, Φ L m₀ t → Proof.Dispatch.X86_64.sel t = P.k := fun L m₀ t h => by
    rw [Proof.Dispatch.X86_64.sel, hax L m₀ t h, BitVec.toNat_ofNat]; omega
  have hkeys := keys_cases P f
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests ?_ ?_ ?_ ?_
  · intro i hi
    rw [Proof.Dispatch.keys, hkeys] at hi
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · rw [Proof.Dispatch.keys, hkeys]; decide
  · rintro s₁ s₂ ⟨_, _, _, _, _, _, f₁, f₂⟩
    rw [hsel _ _ _ f₁, hsel _ _ _ f₂, Proof.Dispatch.keys, hkeys]; exact ⟨rfl, hk⟩
  · intro k c hc s₁ s₂ t₁ t₂ s₁' s₂' ⟨a₁, a₂, ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩, hs, r₁, r₂, _, _⟩ e₁ e₂
    rw [hsel _ _ _ f₁] at hs
    subst hs
    rw [case_eq P f hc] at e₁ e₂
    exact h _ _ _ _ _ _ ⟨e, hL, hq, hx, c₁.flags hL r₁, c₂.flags hL r₂, hΦ _ _ _ _ f₁ r₁, hΦ _ _ _ _ f₂ r₂⟩ e₁ e₂

/-- The call of a function of the hash function, by a dispatch. -/
theorem two_callH {f : Impl.Pbkdf2.Md.X86_64.Hash → String × Prog isa} {Φ : Lay P.I.hashLen → Mem → State → Prop}
    {Q : State → State → Prop} (hax : ∀ L m₀ t, Φ L m₀ t → t.gpr .rax = BitVec.ofNat 64 P.k) (hΦ : NoFlags Φ)
    (h : RelCT isa (Two P Φ) (.call (f P.H).1 (f P.H).2) Q) :
    RelCT isa (Two P Φ) ((cfgOf P).callH f) Q :=
  two_dispatch (f := fun H => .call (f H).1 (f H).2) hax hΦ h

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`, and `hash`. -/
def IA (P : RfcHash) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 256 ∧
    u.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧ u.gpr .rax = BitVec.ofNat 64 P.k

/-- The arguments of the streaming `update`, for the data at `da L` of `len`
bytes, and `hash`. -/
def UA (P : RfcHash) (da : Lay P.I.hashLen → Addr) (len : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = BitVec.ofNat 64 P.H.P.B ∧ u.gpr .rdx = da L ∧
    u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧ u.gpr .rax = BitVec.ofNat 64 P.k

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC
to `dst`, and `hash`. -/
def FA (P : RfcHash) (len dst : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 256 ∧
    u.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + len) ∧ u.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 512 ∧ u.gpr .rax = BitVec.ofNat 64 P.k

theorem ia_nf : NoFlags (IA P) := fun _ _ _ _ h hf => by simp only [IA, hf.gpr]; exact h
theorem ua_nf {da : Lay P.I.hashLen → Addr} {len : Nat} : NoFlags (UA P da len) := fun _ _ _ _ h hf => by
  simp only [UA, hf.gpr]; exact h
theorem fa_nf {len dst : Nat} : NoFlags (FA P len dst) := fun _ _ _ _ h hf => by simp only [FA, hf.gpr]; exact h

theorem ce_rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, rsp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

theorem hinit_ct : RelCT isa (Two P (IA P)) (.call P.H.hmacInitN P.H.hmacInit) fun _ _ => True :=
  RelCT.callEx P.hI.1 P.hI.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have A₁ := initA (P := P) hL c₁ d₁ s₁ x₁ k₁ r₁
    have A₂ := initA (P := P) hL c₂ d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.X86_64.Pbk.InitArgs.pre P.ok A₁, Pbkdf2.Md.X86_64.Pbk.InitArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_rsp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw,
      rsp_two c₁ c₂⟩

theorem hupd_ct {da : Lay P.I.hashLen → Addr} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P da len)) (.call P.H.updN P.H.updC) fun _ _ => True :=
  RelCT.callEx P.ok.stream.upd.1 P.ok.stream.upd.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have A₁ := updA (P := P) hL c₁ (hd L hL) hlen d₁ x₁ k₁ r₁
    have A₂ := updA (P := P) hL c₂ (hd L hL) hlen d₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.X86_64.Calls.UpdArgs.pre P.ok.stream A₁,
      Pbkdf2.Md.X86_64.Calls.UpdArgs.pre P.ok.stream A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_rsp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.X86_64.Calls.UpdArgs.covers P.ok.stream A₁, A₁.cw,
      Pbkdf2.Md.X86_64.Calls.UpdArgs.covers P.ok.stream A₂, A₂.cw, rsp_two c₁ c₂⟩

theorem hfin_ct {len dst : Nat} (hdst : dst + P.H.D ≤ 168) :
    RelCT isa (Two P (FA P len dst)) (.call P.H.hmacFinN P.H.hmacFin) fun _ _ => True :=
  RelCT.callEx P.hF.1 P.hF.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have A₁ := finA (P := P) hL c₁ hdst d₁ s₁ x₁ k₁ r₁
    have A₂ := finA (P := P) hL c₂ hdst d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.X86_64.Pbk.FinArgs.pre P.ok A₁, Pbkdf2.Md.X86_64.Pbk.FinArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_rsp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw,
      rsp_two c₁ c₂⟩

/-! ## The calls keep `Ctx` -/

variable {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_sub {dn : Nat} {L : Lay dn} {r : Region} (h : Region.Sub r ⟨L.scr, 2560⟩) : Safe L r :=
  .inr (.inl (h.trans (Region.sub_prefix (by omega))))

theorem initCall_ctx (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (ha : IA P L m₀ u) :
    WP isa ((cfgOf P).callH fun H => (H.hmacInitN, H.hmacInit)) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, s, x, k, r, hax⟩ := ha
  refine callH_ok P hax fun w hf => ?_
  have hcw := hc.flags hL hf
  refine WP.of_syms (Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId
    (initA hL hcw ((hf.gpr _).trans d) ((hf.gpr _).trans s) ((hf.gpr _).trans x) ((hf.gpr _).trans k)
      ((hf.gpr _).trans r))
    fun u' hrd hwr hcs hf' _ _ hsy => ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf'
      (safe_call hcw (fun r hr => scr_sub ?_) (Nat.le_refl _)) hsy, trivial⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scr_work (by nums)

theorem updCall_ctx {da : Lay P.I.hashLen → Addr} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (hlen : len ≤ 256) (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (ha : UA P da len L m₀ u) :
    WP isa ((cfgOf P).callH fun H => (H.updN, H.updC)) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, _, x, k, r, hax⟩ := ha
  refine callH_ok P hax fun w hf => ?_
  have hcw := hc.flags hL hf
  refine WP.of_syms (Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream
    (updA hL hcw (hd L hL) hlen ((hf.gpr _).trans d) ((hf.gpr _).trans x) ((hf.gpr _).trans k) ((hf.gpr _).trans r))
    (by omega) fun u' af _ hsy => ⟨hcw.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr)
      af.frame (safe_call hcw (fun r hr => scr_sub ?_) (by omega)) hsy, trivial⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact scr_work (by nums)

theorem finCall_ctx {len dst : Nat} (hdst : dst + P.H.D ≤ 168) (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u)
    (ha : FA P len dst L m₀ u) :
    WP isa ((cfgOf P).callH fun H => (H.hmacFinN, H.hmacFin)) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, s, x, k, r, hax⟩ := ha
  refine callH_ok P hax fun w hf => ?_
  have hcw := hc.flags hL hf
  refine WP.of_syms (Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd
    (finA hL hcw hdst ((hf.gpr _).trans d) ((hf.gpr _).trans s) ((hf.gpr _).trans x) ((hf.gpr _).trans k)
      ((hf.gpr _).trans r))
    fun u' hrd hwr hcs hf' _ hsy => ⟨hcw.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf'
      (safe_call hcw (fun r hr => ?_) (Nat.le_refl _)) hsy, trivial⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact scr_sub (scr_work (by nums))
  · exact safe_low L (by nums)
  · exact scr_sub (scr_work (by nums))

/-! ## One HMAC -/

theorem args₁_blk : TaintOk [.rsp] Cfg.hmacArgs₁ := ⟨_, by taint_decide⟩

theorem args₂V_blk (e : Nat) : TaintOk [.rsp] (Cfg.hmacArgs₂ (Cfg.fr .rdx fV) e) :=
  taintOk_erase (is' := Cfg.hmacArgs₂ (Cfg.fr .rdx fV) 0) rfl ⟨_, by taint_decide⟩

theorem args₂M_blk (e : Nat) : TaintOk [.rsp] (Cfg.hmacArgs₂ (Cfg.scr .rdx sMsg) e) :=
  taintOk_erase (is' := Cfg.hmacArgs₂ (Cfg.scr .rdx sMsg) 0) rfl ⟨_, by taint_decide⟩

theorem args₃_blk (e dst : Nat) : TaintOk [.rsp] (Cfg.hmacArgs₃ e dst) :=
  taintOk_erase (is' := Cfg.hmacArgs₃ 0 0) rfl ⟨_, by taint_decide⟩

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from
`rsp`, and its calls, each by a dispatch, are constant time with arguments
that agree. -/
theorem hmac_ct {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {e dst : Nat}
    {Φ : Lay P.I.hashLen → Mem → State → Prop}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx (da L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) (P.H.D + e)) (hlen : P.H.D + e ≤ 256)
    (hdst : dst + P.H.D ≤ 168) (t₂ : TaintOk [.rsp] (Cfg.hmacArgs₂ dataA e)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA e dst) fun _ _ => True := by
  refine (two_wp (Ψ := IA P) (two_blk [.rsp] rspOnly args₁_blk) fun L _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2.1 hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_callH (fun _ _ _ h => h.2.2.2.2.2) ia_nf hinit_ct)
    fun _ _ _ _ hL _ hc ha => initCall_ctx hL hc ha).seq ?_
  refine (two_wp (Ψ := UA P da (P.H.D + e)) (two_blk [.rsp] rspOnly t₂) fun L g m₀ _ hL hk hc _ =>
    WP.mono (updArgs_ok hL hk.2.1 hc (fun u hu => hdA L g m₀ u hL hu) (e := e) (by omega))
      fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_callH (fun _ _ _ h => h.2.2.2.2.2) ua_nf (hupd_ct hd hlen))
    fun _ _ _ _ hL _ hc ha => updCall_ctx hd hlen hL hc ha).seq ?_
  exact (two_wp (Ψ := FA P (P.H.D + e) dst) (two_blk [.rsp] rspOnly (args₃_blk e dst)) fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.2.1 hc (e := e) (dst := dst) (by omega) (by omega)) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq
    (two_callH (fun _ _ _ h => h.2.2.2.2.2) fa_nf (hfin_ct hdst))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (da := fun L => L.B + BitVec.ofNat 64 (24 + 64)) (e := 0) (dst := 64)
    (fun _ _ _ _ hL hu => fr_ok hL hu (d := .rdx) (by decide) (o := 64) (by decide))
    (fun _ _ => .inl ⟨88, rfl, by omega, by nums⟩) (by nums) (by nums) (args₂V_blk 0)

/-- `K = HMAC_K(m)`, for the message of `D + e` bytes at `scratch + 2560`. -/
theorem hmacK_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {e : Nat} (hlen : P.H.D + e ≤ 256) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (Cfg.scr .rdx sMsg) e fK) fun _ _ => True :=
  hmac_ct (da := fun L => L.scr + BitVec.ofNat 64 2560) (dst := 0)
    (fun _ _ _ _ hL hu => scr_ok hL hu (d := .rdx) (by decide) (a := 2560) (by decide))
    (fun _ _ => .inr ⟨2560, rfl, by omega, by omega⟩) hlen (by nums) (args₂M_blk e)

/-- `scratch` in `rdi`, `d` in `rsi`, and `D` in `rdx`. -/
def PtrsIn (P : RfcHash) {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr ∧ u.gpr .rsi = L.d ∧ u.gpr .rdx = BitVec.ofNat 64 P.H.D

theorem msgPtrs_blk : TaintOk [.rsp] Cfg.msgPtrs := ⟨_, by taint_decide⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {b : Nat} {full : Bool} {e : Nat}
    (he : e = if full then 2 * P.Q + 1 else 1) (t₁ : TaintOk [.rsp, .rdi, .rsi, .rdx] (Cfg.msg P.Q b full)) :
    RelCT isa (Two P Φ) (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg P.Q b full))
      (.seq ((cfgOf P).hmac (Cfg.scr .rdx sMsg) e fK) (cfgOf P).hmacV))) fun _ _ => True := by
  have hlen : P.H.D + e ≤ 256 := by
    cases full <;> simp only [he, Bool.false_eq_true, ite_true, ite_false] <;> nums
  refine (two_wp (Ψ := PtrsIn P) (two_blk [.rsp] rspOnly msgPtrs_blk) fun _ _ _ _ hL hk hc _ =>
    WP.mono (ptrs_ok hL hk.2.1 hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_blk [.rsp, .rdi, .rsi, .rdx]
    (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.1.trans f₂.2.1.symm
      · exact f₁.2.2.trans f₂.2.2.symm) t₁) fun _ _ _ _ hL hk hc hp =>
    WP.mono (msg_ok hL hc hp.1 hp.2.1 hp.2.2 b full (Q := P.Q) (by nums) (by nums) (by nums) (Nat.le_of_eq hk.1.symm))
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ => True) (hmacK_ct hlen) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok (P := P) hL hk.2.1 hc hlen) fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (full := true) rfl P.R.blks.msg₀f
  · exact rekey_gen_ct (full := true) rfl P.R.blks.msg₁f

theorem rekey_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) rfl P.R.blks.msg₀

/-! ## One candidate -/

/-- `V = HMAC_K(V)` keeps the candidate's offset. -/
theorem hmacV_off (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ offOf L t'.mem = offOf L t.mem :=
  WP.mono (hmacV_ok hL hq hc) fun _ ⟨hc', hf, _, _⟩ => ⟨hc', hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by have := L.he; omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)⟩

/-- `n` `V`s before the candidate is complete: the offset after `nb - n`. -/
def LoopAt (P : RfcHash) (n : Nat) {dn : Nat} (L : Lay dn) (_ : Mem) (t : State) : Prop :=
  n ≤ P.nb ∧ offOf L t.mem = BitVec.ofNat 64 ((P.nb - n) * P.H.D) ∧ (P.nb - n) * P.H.D < P.Q

/-- The offset, loaded. -/
def OffIn (P : RfcHash) (n : Nat) {dn : Nat} (_ : Lay dn) (_ : Mem) (t : State) : Prop :=
  t.gpr .rdx = BitVec.ofNat 64 ((P.nb - n) * P.H.D)

theorem offLd_blk : TaintOk [.rsp] Cfg.offLd := ⟨_, by taint_decide⟩

theorem candStep_trace {n : Nat} : RelCT isa (Two P (LoopAt P n)) (cfgOf P).candStep fun _ _ => True := by
  refine (two_wp (Ψ := LoopAt P n) hmacV_ct fun _ _ _ _ hL hk hc ho =>
    WP.mono (hmacV_off hL hk.2.1 hc) fun _ ⟨hc', he⟩ => ⟨hc', ho.1, he.trans ho.2.1, ho.2.2⟩).seq ?_
  refine (two_wp (Ψ := OffIn P n) (two_blk [.rsp] rspOnly offLd_blk) fun _ _ _ _ hL _ hc ho =>
    WP.mono (ld_ok hL hc (d := .rdx) (by decide) (o := fOff) (by decide)) fun _ h =>
      ⟨h.ctx, h.val.trans ho.2.1⟩).seq ?_
  exact two_blk [.rsp, .rdx] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rsp_two c₁ c₂
    · exact f₁.trans f₂.symm) P.R.blks.appendV

/-- One `V`: the runs' offsets, and so whether to go on, agree. -/
theorem candStep_ct (n : Nat) :
    RelCT isa (Two P (LoopAt P n)) (cfgOf P).candStep fun s₁ s₂ =>
      isa.eval .b s₁ = isa.eval .b s₂ ∧ (isa.eval .b s₁ = some false → Two P (fun _ _ _ => True) s₁ s₂) ∧
        (isa.eval .b s₁ = some true → ∃ m < n, Two P (LoopAt P m) s₁ s₂) := by
  have hnb := (nb_len (P := P)).1
  refine (two_wp (Ψ := fun L _ t => n ≤ P.nb ∧ (P.nb - n) * P.H.D < P.Q ∧
      offOf L t.mem = BitVec.ofNat 64 ((P.nb - n) * P.H.D + P.H.D) ∧
      t.cf = some (decide ((P.nb - n) * P.H.D + P.H.D < P.Q))) candStep_trace
    fun _ _ _ _ hL hk hc ho => WP.mono (candStepOff_ok hL hk.2.1 hc (by have := ho.2.2; nums) ho.2.1)
      fun _ ⟨hc', h₁, h₂⟩ => ⟨hc', ho.1, ho.2.2, h₁, h₂⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨e, hL, hk, hx, c₁, c₂, ⟨hn, hlt, o₁, f₁⟩, ⟨-, -, o₂, f₂⟩⟩
  have hb₁ : isa.eval .b s₁ = some (decide ((P.nb - n) * P.H.D + P.H.D < P.Q)) := f₁
  have hb₂ : isa.eval .b s₂ = some (decide ((P.nb - n) * P.H.D + P.H.D < P.Q)) := f₂
  refine ⟨hb₁.trans hb₂.symm, fun _ => ⟨e, hL, hk, hx, c₁, c₂, trivial, trivial⟩, fun ht => ?_⟩
  rw [hb₁, Option.some.injEq, decide_eq_true_iff] at ht
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [Nat.sub_zero] at hlt; omega
    · exact h
  have e₁ : P.nb - (n - 1) = P.nb - n + 1 := by omega
  have e₂ : (P.nb - (n - 1)) * P.H.D = (P.nb - n) * P.H.D + P.H.D := by rw [e₁, Nat.succ_mul]
  exact ⟨n - 1, by omega, e, hL, hk, hx, c₁, c₂, ⟨by omega, by rw [e₂]; exact o₁, by rw [e₂]; exact ht⟩,
    ⟨by omega, by rw [e₂]; exact o₂, by rw [e₂]; exact ht⟩⟩

theorem loopC_ct :
    RelCT isa (Two P (LoopAt P P.nb)) (.loop (cfgOf P).candStep .b) (Two P fun _ _ _ => True) :=
  VG.RelCT.loop (M := isa) (fun n => Two P (LoopAt P n)) candStep_ct P.nb

/-- `scratch` in `rdi`. -/
def ScrIn {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop := u.gpr .rdi = L.scr

theorem offInit_blk : TaintOk [.rsp] Cfg.offInit := ⟨_, by taint_decide⟩
theorem scrPtr_blk : TaintOk [.rsp] Cfg.scrPtr := ⟨_, by taint_decide⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  have hnb := (nb_len (P := P)).1
  rw [Cfg.cand]
  refine (two_wp (Ψ := LoopAt P P.nb) (two_blk [.rsp] rspOnly offInit_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (offInit_ok hL hc) fun _ ⟨hc', _, ho⟩ => ⟨hc', Nat.le_refl _,
      by rw [ho, Nat.sub_self, Nat.zero_mul]; rfl, by rw [Nat.sub_self, Nat.zero_mul]; nums⟩).seq ?_
  have hsh := P.R.sh_wide
  cases hw : P.R.wide
  · have e : (cfgOf P).sh = 0 := by show P.R.sh = 0; rw [hsh, hw]; rfl
    simp only [e, ↓reduceIte]
    exact loopC_ct.mono (fun _ _ h => h) fun _ _ _ => trivial
  · have e : (cfgOf P).sh ≠ 0 := by show P.R.sh ≠ 0; rw [hsh, hw]; decide
    simp only [e, ↓reduceIte]
    refine loopC_ct.seq ((two_wp (Ψ := ScrIn) (two_blk [.rsp] rspOnly scrPtr_blk) fun _ _ _ _ hL _ hc _ =>
      WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2⟩).seq ?_)
    exact two_blk [.rsp, .rdi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.trans f₂.symm) P.R.blks.conv

/-! ## One try -/

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  RelCT.callEx (k := (coreK P.R.E).clear) (fun s h => P.R.coreX s h.1 h.2)
    (fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => P.R.coreCT s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1)
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L,
      ⟨core_pre hL hk c₁ a₁.rdi a₁.rsi a₁.rdx a₁.rcx a₁.r8, core_clear hL hk c₁⟩,
      ⟨core_pre hL hk c₂ a₂.rdi a₂.rsi a₂.rdx a₂.rcx a₂.r8, core_clear hL hk c₂⟩,
      ⟨ce_rsp_two c₁ c₂ _ _ _ _, ce_two (by decide) a₁.rdi a₂.rdi _ _ _ _, ce_two (by decide) a₁.rsi a₂.rsi _ _ _ _,
        ce_two (by decide) a₁.rdx a₂.rdx _ _ _ _, ce_two (by decide) a₁.rcx a₂.rcx _ _ _ _,
        ce_two (by decide) a₁.r8 a₂.r8 _ _ _ _, fun c hc => by
          have hc' : c ∈ L.cs := by rw [hk.2.2]; exact hc
          exact (c₁.sy c hc').trans (c₂.sy c hc').symm⟩,
      core_covers hk hL c₁, core_coversW hk.1 c₁, core_covers hk hL c₂, core_coversW hk.1 c₂, rsp_two c₁ c₂⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem coreArgs_blk : TaintOk [.rsp] Cfg.coreArgs := ⟨_, by taint_decide⟩
theorem goOn_blk : TaintOk [.rsp] Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk [.rsp] Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk [.rsp] Cfg.stop := ⟨_, by taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [.rsp] rspOnly coreArgs_blk)
    fun _ _ _ _ hL _ hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [.rsp] rspOnly goOn_blk)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ => True) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL (hok_of hk) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [.rsp] rspOnly again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.rsp] rspOnly stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega)), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hk, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hk, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {T n : Nat} (h : T - n + 1 < T) : T - (T - n + 1) < n ∧ T - (T - (T - n + 1)) = T - n + 1 :=
  ⟨by omega, by omega⟩

theorem loop_ct :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## `h` and `core`'s digest -/

/-- `digest` in `rsi`, `scratch` in `rdi`. -/
def DgIn {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop := u.gpr .rsi = L.dg ∧ u.gpr .rdi = L.scr

/-- And `hash` in `rax`, and `core`'s digest (and, if `wide`, `h`) cleared. -/
def Zeroed (P : RfcHash) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rsi = L.dg ∧ u.gpr .rdi = L.scr ∧ u.gpr .rax = BitVec.ofNat 64 P.k ∧
    Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 240) (8 * nz P) = List.replicate (8 * nz P) 0

theorem zeroed_nf : NoFlags (Zeroed P) := fun _ _ _ _ h hf => by
  simp only [Zeroed, hf.gpr, hf.mem]; exact h

theorem prepZero_blk (c : Cfg) : TaintOk [.rsp] c.prepZero := by
  cases h : c.wide
  · simp only [Cfg.prepZero, h, Bool.false_eq_true, ite_false]; exact ⟨_, by taint_decide⟩
  · simp only [Cfg.prepZero, h, ite_true]; exact ⟨_, by taint_decide⟩

/-- The digest's copies for `P`'s output length, by a dispatch: `scratch`
stays in `rdi`. -/
theorem prepCase_scr (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hz : Zeroed P L m₀ t) :
    WP isa (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, .block ((cfgOf P).prepCase p.2.D)))) t
      fun u => Ctx L g m₀ u ∧ ScrIn L m₀ u := by
  refine dispatch_ok P (f := fun H => .block ((cfgOf P).prepCase H.D)) hz.2.2.1 fun u hf => ?_
  have hcu := hc.flags hL hf
  have hsi : u.gpr .rsi = L.dg := (hf.gpr _).trans hz.1
  have hdi : u.gpr .rdi = L.scr := (hf.gpr _).trans hz.2.1
  have hm : u.mem = t.mem := hf.mem
  have hdn : P.H.D ≤ P.I.hashLen := Nat.le_refl _
  cases hw : P.R.wide
  · have hz' : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 240) 72 = List.replicate 72 0 := by
      rw [hm]; simpa [nz, hw] using hz.2.2.2
    exact WP.mono (prepCaseA_ok hL hw hcu hdn hsi hz') fun _ ⟨c, _, hg, _⟩ => ⟨c, (hg _ (by decide)).trans hdi⟩
  · have hz' : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 240) 144 = List.replicate 144 0 := by
      rw [hm]; simpa [nz, hw] using hz.2.2.2
    exact WP.mono (prepCaseW_ok hL hw hcu hdn hsi hz') fun _ ⟨c, _, hg, _, _⟩ => ⟨c, (hg _ (by decide)).trans hdi⟩

theorem dims_mem (P : RfcHash) : P.H.D ∈ [20, 28, 32, 48, 64] := by
  rcases P.dims with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide

theorem prep_trace : RelCT isa (Two P DgIn) (cfgOf P).prep fun _ _ => True := by
  refine (two_wp (Ψ := Zeroed P) (two_blk [.rsp] rspOnly (prepZero_blk _)) fun _ _ _ _ hL hk hc hd =>
    WP.mono (prepZero_ok hL hk.2.1 hc) fun _ ⟨hc', hg, hax, _, hz⟩ =>
      ⟨hc', ⟨(hg _ (by decide) (by decide)).trans hd.1, (hg _ (by decide) (by decide)).trans hd.2, hax, hz⟩⟩).seq ?_
  refine (two_wp (Ψ := ScrIn) (two_dispatch (f := fun H => .block ((cfgOf P).prepCase H.D))
      (fun _ _ _ h => h.2.2.1) zeroed_nf (two_blk [.rsp, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact rsp_two c₁ c₂
        · exact f₁.1.trans f₂.1.symm) (P.R.blks.prepCase P.H.D (dims_mem P))))
    fun _ _ _ _ hL _ hc hz => prepCase_scr hL hc hz).seq ?_
  exact two_blk [.rsp, .rdi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rsp_two c₁ c₂
    · exact f₁.trans f₂.symm) P.R.blks.post

/-! ## The frame's body -/

theorem digestPtr_blk : TaintOk [.rsp] Cfg.digestPtr := ⟨_, by taint_decide⟩
theorem initKV_blk : TaintOk [.rsp] Cfg.initKV := ⟨_, by taint_decide⟩
theorem wipe_blk : TaintOk [.rsp] Cfg.wipe := ⟨_, by taint_decide⟩

/-- The count's initial store, for any count. -/
theorem initCnt_blk (c : Cfg) : TaintOk [.rsp] c.initCnt :=
  taintOk_erase (is' := [.mov32 .rax (.imm 0), .store (stk fCnt) .rax]) rfl ⟨_, by taint_decide⟩

theorem body_ct :
    RelCT isa (Two P fun _ _ _ => True) (cfgOf P).body (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := DgIn) (two_blk [.rsp] rspOnly digestPtr_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (digestPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := Prepped P) prep_trace fun _ _ _ _ hL hk hc h => prep_ok hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := QB P) (two_blk [.rsp] rspOnly initKV_blk) fun _ _ _ _ hL _ hc h =>
    stageB_ok (P := P) hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.rsp] rspOnly (initCnt_blk _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [.rsp] rspOnly wipe_blk) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Two calls' states whose public data agree. -/
abbrev Calls (P : RfcHash) (s₁ s₂ : State) : Prop :=
  (rfcX86_64 P.R.E.combConsts P.I P.k 544).pre s₁ ∧ (rfcX86_64 P.R.E.combConsts P.I P.k 544).pre s₂ ∧
    (rfcX86_64 P.R.E.combConsts P.I P.k 544).pub s₁ s₂

/-- A block that addresses no memory: its taint check from no public register. -/
theorem noMem_ct {is : List Instr} {R : State → State → Prop} (h : TaintOk [] is) :
    RelCT isa R (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ hr => absurd hr (by simp)) h

theorem entry_blk : TaintOk [] Cfg.entry := ⟨_, by taint_decide⟩

theorem sizes_blk (D B : Nat) : TaintOk [] (Cfg.sizes D B) :=
  taintOk_erase (is' := Cfg.sizes 0 0) rfl ⟨_, by taint_decide⟩

/-- The entry and the dispatch on `hash` that sets `D` and `B`: both runs
take the same case. -/
theorem entered_ct : RelCT isa (Calls P) (.seq (.block Cfg.entry)
    (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, .block (Cfg.sizes p.2.D p.2.P.B)))))
    fun _ _ => True := by
  have hk := P.hk
  have hk8 : P.k < 8 := by
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hkeys := keys_cases P fun H => (Code.block (Cfg.sizes H.D H.P.B) : Prog isa)
  refine (RelCT.wpDep (noMem_ct entry_blk) fun s₁ s₂ h => ⟨entryBlk_ok h.1, entryBlk_ok h.2.1⟩).seq ?_
  have hsel : ∀ σ s, EntryBlk P.k σ s → Proof.Dispatch.X86_64.sel s = P.k := fun σ s h => by
    rw [Proof.Dispatch.X86_64.sel, h.2.2.2.2.1, BitVec.toNat_ofNat]; omega
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests ?_ ?_ ?_ ?_
  · intro i hi
    rw [Proof.Dispatch.keys, hkeys] at hi
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · rw [Proof.Dispatch.keys, hkeys]; decide
  · rintro s₁ s₂ ⟨-, σ₁, σ₂, -, e₁, e₂⟩
    rw [hsel _ _ e₁, hsel _ _ e₂, Proof.Dispatch.keys, hkeys]; exact ⟨rfl, hk⟩
  · intro k c hc
    obtain ⟨p, -, he⟩ := List.mem_map.mp hc
    cases he
    exact noMem_ct (sizes_blk _ _)

theorem sign_ct : ConstantTime isa (rfcX86_64 P.R.E.combConsts P.I P.k 544).pre
    (rfcX86_64 P.R.E.combConsts P.I P.k 544).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  rw [Cfg.sign]
  refine RelCT.assoc ((RelCT.wpDep entered_ct fun s₁ s₂ h => ⟨entered_ok h.1, entered_ok h.2.1⟩).seq ?_)
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, e₁, e₂⟩ =>
    e₁.rsp.trans (hp.1.trans e₂.rsp.symm)) ?_
  refine body_ct.mono (fun a b ⟨s₁, s₂, ⟨_, σ₁, σ₂, ⟨p₁, p₂, hsp, hdi, hsi, hdx, h8, hres, hsy⟩, e₁, e₂⟩, ea, eb⟩ => ?_)
    fun _ _ _ => trivial
  subst ea eb
  have hsy' : (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then σ₁.syms n else 0) =
      fun n => if n ∈ P.R.E.combConsts.map Prod.fst then σ₂.syms n else 0 := funext fun n => by
    split
    · next h => obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact hsy c hc
    · rfl
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts σ₁ =
      lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts σ₂ := by
    unfold lay; rw [hsp, hdi, hsi, hdx, h8, hsy']
  have hr : (result P.I σ₁.mem (σ₁.gpr .rsi) (σ₁.gpr .rdx)).2 =
      (result P.I σ₂.mem (σ₁.gpr .rsi) (σ₁.gpr .rdx)).2 := by
    rw [hres, hsi, hdx]
  refine ⟨⟨lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts σ₁, σ₁.gpr, σ₂.gpr, σ₁.mem,
    σ₂.mem⟩, lay_ok P.k P.H.D P.H.P.B p₁, coreOk_lay P σ₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, push_ctx p₁ e₁,
    by rw [hl]; exact push_ctx p₂ e₂, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
