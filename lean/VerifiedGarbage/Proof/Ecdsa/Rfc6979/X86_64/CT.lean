import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Impl.Sha256.X86_64.Stream

/-!
# Deterministic ECDSA on x86-64: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frame's push and pop they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis, of the blocks for each size of hash function: `Blks`);
each call is of constant-time code whose public data agree (`RelCT.callEx`);
and the loop's branch agrees, since in both runs it goes on after candidate
`i` iff `i` is before the candidate it stops at (`go_iff`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hx, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hx, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rspOnly {Φ : Lay P.I.hashLen → Mem → State → Prop} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-! ## The blocks, for each size of hash function -/

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- The blocks that depend on the hash function's output size `D` and block
size `B`, each of which addresses memory only from `rsp` (and the message's
from the pointers it is given). -/
structure Blks (D B : Nat) : Prop where
  init : TaintOk [.rsp] (Cfg.hmacArgs₁ D)
  vUpd : TaintOk [.rsp] (Cfg.hmacArgs₂ B (Cfg.fr .rdx fV) D)
  vFin : TaintOk [.rsp] (Cfg.hmacArgs₃ B D fV)
  kUpd₁ : TaintOk [.rsp] (Cfg.hmacArgs₂ B (Cfg.scr .rdx sMsg) (D + 1))
  kFin₁ : TaintOk [.rsp] (Cfg.hmacArgs₃ B (D + 1) fK)
  kUpd₆₅ : TaintOk [.rsp] (Cfg.hmacArgs₂ B (Cfg.scr .rdx sMsg) (D + 65))
  kFin₆₅ : TaintOk [.rsp] (Cfg.hmacArgs₃ B (D + 65) fK)
  msg₀ : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg D 0 false)
  msg₀f : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg D 0 true)
  msg₁f : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg D 1 true)

theorem blks (P : RfcHash) : Blks P.H.D P.H.P.B := by
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The code's blocks that depend on neither the hash function nor the
compression function. -/
def cfgC : Cfg where
  H := ⟨Impl.Sha256.X86_64.Stream.params, 32, 104, "", .block [], "", .block [], "", "", "", "", ""⟩
  n := Spec.P256.n
  tries := 8
  coreN := ""
  coreC := .block []

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 384

/-- The arguments of the streaming `update`, for the data at `dA L` of `len` bytes. -/
def UA (P : RfcHash) (dA : Lay P.I.hashLen → Addr) (len : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = BitVec.ofNat 64 P.H.P.B ∧ u.gpr .rdx = dA L ∧
    u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .r8 = L.scr + BitVec.ofNat 64 384

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC to `dst`. -/
def FA (P : RfcHash) (len dst : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .rdx = BitVec.ofNat 64 (P.H.P.B + len) ∧ u.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 384

theorem ce_rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, rsp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

theorem hinit_ct : RelCT isa (Two P (IA P)) (.call P.H.hmacInitN P.H.hmacInit) fun _ _ => True :=
  RelCT.callEx P.hI.1 P.hI.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := initA (P := P) hL c₁ d₁ s₁ x₁ k₁ r₁
    have A₂ := initA (P := P) hL c₂ d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.X86_64.Pbk.InitArgs.pre P.ok A₁, Pbkdf2.Md.X86_64.Pbk.InitArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_rsp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw,
      rsp_two c₁ c₂⟩

theorem hupd_ct {dA : Lay P.I.hashLen → Addr} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dA L) len)
    (hlen : len ≤ 192) :
    RelCT isa (Two P (UA P dA len)) (.call P.H.updN P.H.updC) fun _ _ => True :=
  RelCT.callEx P.ok.stream.upd.1 P.ok.stream.upd.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
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
  RelCT.callEx P.hF.1 P.hF.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := finA (P := P) hL c₁ hdst d₁ s₁ x₁ k₁ r₁
    have A₂ := finA (P := P) hL c₂ hdst d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.X86_64.Pbk.FinArgs.pre P.ok A₁, Pbkdf2.Md.X86_64.Pbk.FinArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_rsp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.X86_64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.X86_64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw,
      rsp_two c₁ c₂⟩

/-! ## The calls keep `Ctx` -/

variable {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_sub {dn : Nat} {L : Lay dn} {r : Region} (h : Region.Sub r ⟨L.scr, 2256⟩) : Safe L r :=
  .inr (.inl (h.trans (Region.sub_prefix (by omega))))

theorem init_ctx (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (ha : IA P L m₀ u) :
    WP isa (.call P.H.hmacInitN P.H.hmacInit) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, s, x, k, r⟩ := ha
  refine Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId (initA (P := P) hL hc d s x k r)
    fun u' hrd hwr hcs hf _ _ => ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
      (safe_call hc (fun r hr => scr_sub ?_) (Nat.le_refl _)), trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scr_work (by nums)

theorem upd_ctx {dA : Lay P.I.hashLen → Addr} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dA L) len)
    (hlen : len ≤ 192) (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (ha : UA P dA len L m₀ u) :
    WP isa (.call P.H.updN P.H.updC) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, _, x, k, r⟩ := ha
  refine Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream (updA (P := P) hL hc (hd L hL) hlen d x k r) (by omega)
    fun u' af _ => ⟨hc.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
      (safe_call hc (fun r hr => scr_sub ?_) (by omega)), trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact scr_work (by nums)

theorem fin_ctx {len dst : Nat} (hdst : dst + P.H.D ≤ 168) (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u)
    (ha : FA P len dst L m₀ u) :
    WP isa (.call P.H.hmacFinN P.H.hmacFin) u fun u' => Ctx L g m₀ u' ∧ True := by
  obtain ⟨d, s, x, k, r⟩ := ha
  refine Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd (finA (P := P) hL hc hdst d s x k r)
    fun u' hrd hwr hcs hf _ => ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
      (safe_call hc (fun r hr => ?_) (Nat.le_refl _)), trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact scr_sub (scr_work (by nums))
  · exact safe_low L (by nums)
  · exact scr_sub (scr_work (by nums))

/-! ## One HMAC -/

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from `rsp`
(the taint checks of the blocks that depend on the data, `t₂` and `t₃`), and
its calls are constant time with arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {dA : Lay P.I.hashLen → Addr} {len dst : Nat}
    {Φ : Lay P.I.hashLen → Mem → State → Prop}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx (dA L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dA L) len) (hlen : len ≤ 192) (hdst : dst + P.H.D ≤ 168)
    (t₂ : TaintOk [.rsp] (Cfg.hmacArgs₂ P.H.P.B dataA len)) (t₃ : TaintOk [.rsp] (Cfg.hmacArgs₃ P.H.P.B len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA len dst) fun _ _ => True := by
  refine (two_wp (Ψ := IA P) (two_blk [.rsp] rspOnly (blks P).init) fun L _ _ _ hL hc _ =>
    WP.mono (initArgs_ok hL hc P.H.D (by nums)) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (hinit_ct (P := P)) fun _ _ _ _ hL hc ha => init_ctx hL hc ha).seq ?_
  refine (two_wp (Ψ := UA P dA len) (two_blk [.rsp] rspOnly t₂) fun L g m₀ _ hL hc _ =>
    WP.mono (updArgs_ok hL hc (fun u hu => hdA L g m₀ u hL hu) (B := P.H.P.B) (by nums) (by omega))
      fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (hupd_ct (P := P) hd hlen) fun _ _ _ _ hL hc ha => upd_ctx hd hlen hL hc ha).seq ?_
  exact (two_wp (Ψ := FA P len dst) (two_blk [.rsp] rspOnly t₃) fun _ _ _ _ hL hc _ =>
    WP.mono (finArgs_ok hL hc (B := P.H.P.B) (len := len) (by nums) (by omega)) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq
    (hfin_ct hdst)

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dA := fun L => L.B + BitVec.ofNat 64 (24 + 64)) (len := P.H.D) (dst := 64)
    (fun _ _ _ _ hL hu => fr_ok hL hu (d := .rdx) (by decide) (o := 64) (by decide))
    (fun _ _ => .inl ⟨88, rfl, by omega, by nums⟩) (by nums) (by nums) (blks P).vUpd (blks P).vFin

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {len : Nat} (hlen : len ≤ 192)
    (t₂ : TaintOk [.rsp] (Cfg.hmacArgs₂ P.H.P.B (Cfg.scr .rdx sMsg) len))
    (t₃ : TaintOk [.rsp] (Cfg.hmacArgs₃ P.H.P.B len fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) fun _ _ => True :=
  hmac_ct (dA := fun L => L.scr + BitVec.ofNat 64 2256) (dst := 0)
    (fun _ _ _ _ hL hu => scr_ok hL hu (d := .rdx) (by decide) (a := 2256) (by decide))
    (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) hlen (by nums) t₂ t₃

/-- `scratch` in `rdi`, `d` in `rsi`. -/
def PtrsIn {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop := u.gpr .rdi = L.scr ∧ u.gpr .rsi = L.d

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {b : Nat} {full : Bool} {len : Nat}
    (hlen : len = if full then P.H.D + 65 else P.H.D + 1)
    (t₁ : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg P.H.D b full))
    (t₂ : TaintOk [.rsp] (Cfg.hmacArgs₂ P.H.P.B (Cfg.scr .rdx sMsg) len))
    (t₃ : TaintOk [.rsp] (Cfg.hmacArgs₃ P.H.P.B len fK)) :
    RelCT isa (Two P Φ) (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg P.H.D b full))
      (.seq ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) (cfgOf P).hmacV))) fun _ _ => True := by
  have hlen' : len ≤ 192 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> nums
  refine (two_wp (Ψ := PtrsIn) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_blk [.rsp, .rdi, .rsi] (fun L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) t₁) fun _ _ _ _ hL hc hp =>
    WP.mono (msg_ok hL hc hp.1 hp.2 b full (D := P.H.D) (by nums) (by nums)) fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ => True) (hmacK_ct hlen' t₂ t₃) fun _ _ _ _ hL hc _ =>
    WP.mono (hmacK_ok (P := P) hL hc hlen') fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (len := P.H.D + 65) rfl (blks P).msg₀f (blks P).kUpd₆₅ (blks P).kFin₆₅
  · exact rekey_gen_ct (len := P.H.D + 65) rfl (blks P).msg₁f (blks P).kUpd₆₅ (blks P).kFin₆₅

theorem rekey_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) (len := P.H.D + 1) rfl (blks P).msg₀ (blks P).kUpd₁ (blks P).kFin₁

/-! ## One candidate -/

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  RelCT.callEx P.coreX P.coreCT
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd L, coreWr L, coreRd L, coreWr L, core_pre hL P.len32 c₁ a₁.rdi a₁.rsi a₁.rdx a₁.rcx a₁.r8,
      core_pre hL P.len32 c₂ a₂.rdi a₂.rsi a₂.rdx a₂.rcx a₂.r8,
      ⟨ce_rsp_two c₁ c₂ _ _ _ _, ce_two (by decide) a₁.rdi a₂.rdi _ _ _ _, ce_two (by decide) a₁.rsi a₂.rsi _ _ _ _,
        ce_two (by decide) a₁.rdx a₂.rdx _ _ _ _, ce_two (by decide) a₁.rcx a₂.rcx _ _ _ _,
        ce_two (by decide) a₁.r8 a₂.r8 _ _ _ _⟩,
      core_covers P.len32 c₁, core_coversW c₁, core_covers P.len32 c₂, core_coversW c₂, rsp_two c₁ c₂⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) hmacV_ct fun _ _ _ _ hL hc hi =>
    try₁_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args L u) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hc hi =>
    try₃_ok hL hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hc hi => try₄_ok hL hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ => True) rekey_ct fun _ _ _ _ hL hc _ =>
      WP.mono (rekey_ok hL hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hc hi => tryOne_ok hL hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < 8 := ⟨hI.fails i (by omega), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega)), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {n : Nat} (h : 8 - n + 1 < 8) : 8 - (8 - n + 1) < n ∧ 8 - (8 - (8 - n + 1)) = 8 - n + 1 :=
  ⟨by omega, by omega⟩

theorem loop_ct :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) :=
  VG.RelCT.loop (M := isa) (fun n => Two P fun L m₀ t => LoopInv P L m₀ (8 - n) t)
    (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
      ⟨he, fun h => (hf h).mono fun _ _ _ hx => ⟨_, hx⟩, fun h => by
        obtain ⟨e, hL, hx, c₁, c₂, f₁, f₂⟩ := ht h
        have hn := next_n f₁.lt
        refine ⟨8 - (8 - n + 1), hn.1, e, hL, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩) 8

/-! ## The frame's body -/

theorem reduce_blk : TaintOk [.rsp, .rsi] (cfgC.reduce ++ Cfg.initKV) := ⟨_, by taint_decide⟩

theorem initCnt_blk : TaintOk [.rsp] cfgC.initCnt := ⟨_, by taint_decide⟩

/-- `digest` in `rsi`. -/
def DgIn {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop := u.gpr .rsi = L.dg

theorem body_ct :
    RelCT isa (Two P fun _ _ _ => True) (cfgOf P).body (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := DgIn) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hc _ =>
    WP.mono (digestPtr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩).seq ?_
  refine (two_wp (Ψ := QB P) (two_blk [.rsp, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.trans f₂.symm) reduce_blk) fun _ _ _ _ hL hc h => stageB_ok (P := P) hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hc h => stageC_ok (P := P) hL hc h).seq ?_
  refine (two_wp (Ψ := QD P) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hc h => stageD_ok (P := P) hL hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.rsp] rspOnly initCnt_blk)
    fun _ _ _ _ hL hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Runs whose public data agree have the same layout, and stop at the same candidate. -/
theorem sign_ct : ConstantTime isa (rfcX86_64 P.I).pre (rfcX86_64 P.I).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_)
  refine body_ct.mono (fun a b ⟨s₁, s₂, ⟨p₁, p₂, hsp, hdi, hsi, hdx, hcx, hres⟩, ea, eb⟩ => ?_) fun _ _ _ => trivial
  subst ea eb
  have hl : lay P.I.hashLen s₁ = lay P.I.hashLen s₂ := by simp only [lay, hsp, hdi, hsi, hdx, hcx]
  have hr : (result P.I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result P.I s₂.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 := by
    rw [hres, hsi, hdx]
  refine ⟨⟨lay P.I.hashLen s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁,
    congrArg (fun x => if x = 0 then 7 else x - 1) hr, push_ctx p₁, by rw [hl]; exact push_ctx p₂, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
