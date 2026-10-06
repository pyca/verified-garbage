import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Deterministic ECDSA on x86 (32-bit): constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the save of our caller's registers and the frame's release they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs). The blocks address only the stack and the buffers, from
registers that agree (the taint analysis, of the blocks for each size of hash
function: `Blks`); each call, in a frame of its arguments, is of
constant-time code whose public data agree (`hi_rel`, `upd_rel`, `hf_rel`,
`callWithR_ct`); and the loop's branch agrees, since in both runs it goes on
after candidate `i` iff `i` is before the candidate it stops at (`go_iff`).
The frame's allocation and release access no memory (`alloc_ct`).
-/

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
  e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pred P) (a b : State) : Prop := ∃ e, TwoAt P Φ e a b

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
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
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
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .esp = t₂.gpr .esp :=
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
  exact esp_two c₁ c₂

/-! ## The blocks, for each size of hash function -/

/-- The registers the message's block addresses memory from. -/
abbrev msgRegs (wide : Bool) : List Reg := [.esp, .edi, .esi] ++ (if wide then [.edx] else [])

/-- The blocks that depend on the hash function's output size `D` and block
size `B`, and on the scalars' `Q` bytes, each of which addresses memory only
from `esp` (and the message's from the pointers it is given). -/
structure Blks (Q D B : Nat) (wide : Bool) : Prop where
  init : TaintOk [.esp] (Cfg.hmacArgs₁ wide D)
  vUpd : TaintOk [.esp] (Cfg.hmacArgs₂ wide B (Cfg.fr .edx fV) D)
  vFin : TaintOk [.esp] (Cfg.hmacArgs₃ wide B D fV)
  kUpd₁ : TaintOk [.esp] (Cfg.hmacArgs₂ wide B (Cfg.scr wide .edx sMsg) (D + 1))
  kFin₁ : TaintOk [.esp] (Cfg.hmacArgs₃ wide B (D + 1) fK)
  kUpdF : TaintOk [.esp] (Cfg.hmacArgs₂ wide B (Cfg.scr wide .edx sMsg) (D + 2 * Q + 1))
  kFinF : TaintOk [.esp] (Cfg.hmacArgs₃ wide B (D + 2 * Q + 1) fK)
  msg₀ : TaintOk [.esp, .edi, .esi] (Cfg.msg Q D 0 false false)
  msg₀f : TaintOk (msgRegs wide) (Cfg.msg Q D 0 true wide)
  msg₁f : TaintOk (msgRegs wide) (Cfg.msg Q D 1 true wide)

theorem blks (P : RfcHash) : Blks P.Q P.F.H.D P.F.H.B P.R.wide := by
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hQ : P.Q = 8 * P.w := hQ8
    rw [hQ]
    rcases (P.R.sizesA hw).1 with hn | hn <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      rw [show P.w = P.R.E.n from rfl, hn, h, h'] <;>
      first
      | (exfalso; rw [hQ, show P.w = P.R.E.n from rfl, hn, h] at hQD; omega)
      | exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
          ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
          ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  · obtain ⟨-, hQ66, hD64, hB⟩ := P.sizesW hw
    rw [hQ66, hD64, hB]
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-! The blocks that depend on whether two `V`s make a candidate. -/

theorem coreArgs_blk (wide : Bool) : TaintOk [.esp] (Cfg.coreArgs wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem wipe_blk (wide : Bool) : TaintOk [.esp] (Cfg.wipe wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem msgPtrs_blk (wide full : Bool) : TaintOk [.esp] (Cfg.msgPtrs wide full) := by
  cases wide <;> cases full
  all_goals exact ⟨_, by taint_decide⟩

/-- If two `V`s make a candidate: the digest for `core` and `V = 0x01…`,
`K = 0x00…` (from `esp`, `digest` and `scratch`), `V` kept, and the
candidate (from `esp` and `scratch`). -/
structure WideBlks (P : RfcHash) : Prop where
  prep : TaintOk [.esp, .esi, .edi] ((cfgOf P).coreDigest ++ Cfg.initKV)
  keep : TaintOk [.esp] (cfgOf P).keepV
  top : TaintOk [.esp, .edi] (cfgOf P).candTop

theorem wideBlks (hw : P.R.wide = true) : WideBlks P := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
  have hsh := sh7 hw
  have e₁ : (cfgOf P).len = 66 := hQ66
  have e₂ : (cfgOf P).w = 18 := by show 2 * P.R.E.n = 18; simp only [RfcHash.w] at hw9; omega
  have e₃ : (cfgOf P).F.H.D = 64 := hD64
  have e₄ : (cfgOf P).sh = 7 := hsh
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Cfg.coreDigest, Cfg.keepV, Cfg.candTop, Cfg.conv, e₁, e₂, e₃, e₄] <;>
    exact ⟨_, by taint_decide⟩

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧
    u.gpr .edx = L.F + BitVec.ofNat 32 0 ∧ u.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .ebp = L.a3 + BitVec.ofNat 32 384

/-- The arguments of the streaming `update`, for the data at `dv L` of `len` bytes. -/
def UA (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32)
    (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = BitVec.ofNat 32 P.F.H.B ∧ u.gpr .eax = 0 ∧
    u.gpr .edx = dv L ∧ u.gpr .ecx = BitVec.ofNat 32 len ∧ u.gpr .ebp = L.a3 + BitVec.ofNat 32 384

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC to `dst`. -/
def FA (P : RfcHash) (len dst : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edx = L.a3 + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.a3 + BitVec.ofNat 32 192 ∧
    u.gpr .eax = BitVec.ofNat 32 (P.F.H.B + len) ∧ u.gpr .ecx = 0 ∧ u.gpr .edi = L.F + BitVec.ofNat 32 dst ∧
    u.gpr .ebp = L.a3 + BitVec.ofNat 32 384

theorem hinit_ct :
    RelCT isa (Two P (IA P)) (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call P.F.hiN P.F.hiC) (.pop .eax 5))
      fun _ _ => True :=
  two_exists fun e => hi_rel P.ok.hi (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.esp, c₂.esp⟩

theorem hupd_ct {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len)
    (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P dv len))
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call P.F.H.updN P.F.H.updC) (.pop .eax 6))
      fun _ _ => True :=
  two_exists fun e => upd_rel P.ok.hH (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2, c₁.esp, c₂.esp⟩

theorem hfin_ct {len dst : Nat} (hdst : dst + P.F.H.D ≤ 180) :
    RelCT isa (Two P (FA P len dst))
      (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call P.F.hfN P.F.hfC) (.pop .eax 6)) fun _ _ => True :=
  two_exists fun e => hf_rel P.ok.hf (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2, c₁.esp, c₂.esp⟩

/-! ## One HMAC -/

/-- After HMAC's `init` and `update`: the states, for the state before. -/
def Ini (P : RfcHash) : Pred P := fun L g m₀ u => ∃ t, Inited P L g m₀ t u
def Upt (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P :=
  fun L g m₀ u => ∃ t, Updated P L g m₀ t (dv L) len u

theorem initS_ct {Φ : Pred P} :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.hmacArgs₁ P.R.wide P.F.H.D))
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call P.F.hiN P.F.hiC) (.pop .eax 5))) (Two P (Ini P)) :=
  two_wp ((two_wp (Ψ := IA P) (two_blk [.esp] espOnly (blks P).init) fun _ _ _ _ hL hk hc _ => by
      rw [← hk.2.2]; exact WP.mono (initArgs_ok hL hc _) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq hinit_ct)
    fun _ _ _ t hL hk hc _ => WP.mono (init_step hL hk.2.2 hc) fun _ h => ⟨h.ctx, t, h⟩

theorem updS_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → CoreOk P L → Ctx L g m₀ u →
      WP isa (.block dataA) u (Upd L g m₀ u .edx (dv L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256)
    (t₂ : TaintOk [.esp] (Cfg.hmacArgs₂ P.R.wide P.F.H.B dataA len)) :
    RelCT isa (Two P (Ini P)) (.seq (.block (Cfg.hmacArgs₂ P.R.wide P.F.H.B dataA len))
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call P.F.H.updN P.F.H.updC) (.pop .eax 6)))
      (Two P (Upt P dv len)) :=
  two_wp ((two_wp (Ψ := UA P dv len) (two_blk [.esp] espOnly t₂) fun L g m₀ _ hL hk hc _ => by
      rw [← hk.2.2]
      exact WP.mono (updArgs_ok hL hc (fun u hu => hdA L g m₀ u hL hk hu) (len := len) P.F.H.B)
        fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq (hupd_ct hd hlen))
    fun L g m₀ _ hL hk _ ⟨t, hi⟩ =>
      WP.mono (upd_step hL hk.2.2 hi (fun u hu => hdA L g m₀ u hL hk hu) (hd L hL) hlen) fun _ h => ⟨h.ctx, t, h⟩

theorem finS_ct {dv : Lay P.I.hashLen → BitVec 32} {len dst : Nat} (hdst : dst + P.F.H.D ≤ 180)
    (t₃ : TaintOk [.esp] (Cfg.hmacArgs₃ P.R.wide P.F.H.B len dst)) :
    RelCT isa (Two P (Upt P dv len)) (.seq (.block (Cfg.hmacArgs₃ P.R.wide P.F.H.B len dst))
      (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call P.F.hfN P.F.hfC) (.pop .eax 6)))
      fun _ _ => True :=
  (two_wp (Ψ := FA P len dst) (two_blk [.esp] espOnly t₃) fun _ _ _ _ hL hk hc _ => by
    rw [← hk.2.2]; exact WP.mono (finArgs_ok hL hc _ len dst) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq (hfin_ct hdst)

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from
`esp` (the taint checks of the blocks that depend on the data, `t₂` and
`t₃`), and its calls are constant time with arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len dst : Nat} {Φ : Pred P}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → CoreOk P L → Ctx L g m₀ u →
      WP isa (.block dataA) u (Upd L g m₀ u .edx (dv L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 180)
    (t₂ : TaintOk [.esp] (Cfg.hmacArgs₂ P.R.wide P.F.H.B dataA len))
    (t₃ : TaintOk [.esp] (Cfg.hmacArgs₃ P.R.wide P.F.H.B len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA len dst) fun _ _ => True :=
  RelCT.assoc (initS_ct.seq (RelCT.assoc ((updS_ct hdA hd hlen t₂).seq (finS_ct hdst t₃))))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dv := fun L => L.F + BitVec.ofNat 32 64) (len := P.F.H.D) (dst := 64)
    (fun _ _ _ _ hL _ hu => fr_ok hL hu (d := .edx) (by decide) 64)
    (fun _ _ => .inl ⟨64, rfl, by nums⟩) (by nums) (by nums) (blks P).vUpd (blks P).vFin

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256)
    (t₂ : TaintOk [.esp] (Cfg.hmacArgs₂ P.R.wide P.F.H.B (Cfg.scr P.R.wide .edx sMsg) len))
    (t₃ : TaintOk [.esp] (Cfg.hmacArgs₃ P.R.wide P.F.H.B len fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (Cfg.scr P.R.wide .edx sMsg) len fK) fun _ _ => True :=
  hmac_ct (dv := fun L => L.a3 + BitVec.ofNat 32 2256) (dst := 0)
    (fun _ _ _ _ hL hk hu => by rw [← hk.2.2]; exact scr_ok hL hu (d := .edx) (by decide) 2256)
    (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) hlen (by nums) t₂ t₃

/-- `scratch` in `edi`, `d` in `esi`, and, if `wd`, `digest` in `edx`. -/
def PtrsIn (wd : Bool) {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .edi = L.a3 ∧ u.gpr .esi = L.a1 ∧ (wd = true → u.gpr .edx = L.a2)

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} {full wd : Bool} (hwd : wd = (full && P.R.wide)) {len : Nat}
    (hlen : len = if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1)
    (t₁ : TaintOk (msgRegs wd) (Cfg.msg P.Q P.F.H.D b full wd))
    (t₂ : TaintOk [.esp] (Cfg.hmacArgs₂ P.R.wide P.F.H.B (Cfg.scr P.R.wide .edx sMsg) len))
    (t₃ : TaintOk [.esp] (Cfg.hmacArgs₃ P.R.wide P.F.H.B len fK)) :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.msgPtrs P.R.wide full)) (.seq (.block (Cfg.msg P.Q P.F.H.D b full wd))
      (.seq ((cfgOf P).hmac (Cfg.scr P.R.wide .edx sMsg) len fK) (cfgOf P).hmacV))) fun _ _ => True := by
  have hlen' : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> nums
  refine (two_wp (Ψ := PtrsIn wd) (two_blk [.esp] espOnly (msgPtrs_blk _ _)) fun _ _ _ _ hL hk hc _ => by
    rw [← hk.2.2]
    exact WP.mono (ptrs_ok hL hc full) fun _ ⟨c, _, a, b', d⟩ => ⟨c, a, b', fun h => d (by
      rw [hk.2.2]; rw [hwd] at h; exact ((Bool.and_eq_true _ _).mp h).2) (by
      rw [hwd] at h; exact ((Bool.and_eq_true _ _).mp h).1)⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ _ => True) (two_blk (msgRegs wd) (fun L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      cases wd
      · simp only [msgRegs, Bool.false_eq_true, ite_false, List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact esp_two c₁ c₂
        · exact f₁.1.trans f₂.1.symm
        · exact f₁.2.1.trans f₂.2.1.symm
      · simp only [msgRegs, ite_true, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact esp_two c₁ c₂
        · exact f₁.1.trans f₂.1.symm
        · exact f₁.2.1.trans f₂.2.1.symm
        · exact (f₁.2.2 rfl).trans (f₂.2.2 rfl).symm) t₁) fun _ _ _ _ hL hk hc hp =>
    WP.mono (msg_ok hL hc hp.1 hp.2.1 b full wd (fun h _ => hp.2.2 h) (D := P.F.H.D) (Q := P.Q) (by nums)
      (by nums) (by nums) (by nums) (by rw [hk.1])
      (fun hf hwf => by
        have := P.sizesA (by rw [hwd, hf] at hwf; exact hwf); exact ⟨by rw [this.1]; omega, by omega⟩)
      (fun hf hwt => by
        have hW : P.R.wide = true := by rw [hwd, hf] at hwt; exact hwt
        have := P.sizesW hW; exact ⟨by omega, by omega, by rw [P.len]⟩))
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ _ => True) (hmacK_ct hlen' t₂ t₃) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok (P := P) hL hk.2.2 hc hlen') fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (full := true) rfl (len := P.F.H.D + 2 * P.Q + 1) rfl (blks P).msg₀f (blks P).kUpdF
      (blks P).kFinF
  · exact rekey_gen_ct (full := true) rfl (len := P.F.H.D + 2 * P.Q + 1) rfl (blks P).msg₁f (blks P).kUpdF
      (blks P).kFinF

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) (wd := false) rfl (len := P.F.H.D + 1) rfl (blks P).msg₀ (blks P).kUpd₁
    (blks P).kFin₁

/-- `scratch` in `edi`. -/
def ScrIn {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop := u.gpr .edi = L.a3

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  cases hw : P.R.wide
  · have e : (cfgOf P).cand = (cfgOf P).hmacV := by simp only [Cfg.cand, cfgOf, hw]; rfl
    rw [e]; exact hmacV_ct
  · have e : (cfgOf P).wide = true := hw
    have W := wideBlks hw
    simp only [Cfg.cand, e, ite_true]
    refine (two_wp (Ψ := fun _ _ _ _ => True) hmacV_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (hmacV_ok hL hk.2.2 hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := fun _ _ _ _ => True) (two_blk [.esp] espOnly W.keep) fun L _ _ _ hL hk hc _ => ?_).seq ?_
    · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
      have he := e36 hk.2.2 hw
      have e₃ : (cfgOf P).F.H.D = 64 := hD64
      simp only [Cfg.keepV, e₃]
      exact WP.mono (copyF_ok hL hc (src := .esp) (S := L.F) (SA := L.B + BitVec.ofNat 64 140) hc.esp
        (by decide) (so := 64) (d := 268) (K := 64 / 4) (by omega) (by omega) (fun j hj => fr_addr hL (by omega))
        (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega) (by omega) hL)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) fun _ h => ⟨h.1, trivial⟩
    refine (two_wp (Ψ := fun _ _ _ _ => True) hmacV_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (hmacV_ok hL hk.2.2 hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := ScrIn) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hk hc _ => by
      have ha := arg_ok hL hc (d := .edi) (by decide) (i := 3) (by omega)
      rw [hk.2.2, hw] at ha
      exact WP.mono ha fun _ h => ⟨h.ctx, h.val⟩).seq ?_
    exact two_blk [.esp, .edi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.trans f₂.symm) W.top

/-! ## One candidate -/

/-- `core`, in a frame of its arguments, which agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u)
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5))
      fun _ _ => True :=
  two_exists fun e => callWithR_ct (rs := core5) P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun _ _ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      obtain ⟨v₀, v₁, v₂, v₃, v₄⟩ := core_argv hL c₁ a₁ (rd := coreRd P e.1) (wr := coreWr P e.1)
      obtain ⟨w₀, w₁, w₂, w₃, w₄⟩ := core_argv hL c₂ a₂ (rd := coreRd P e.1) (wr := coreWr P e.1)
      exact ⟨core_callPre hL hk c₁ a₁, core_callPre hL hk c₂ a₂, esp_two c₁ c₂,
        by rw [State.withRegions_gpr, State.withRegions_gpr, core_esp c₁, core_esp c₂],
        by rw [v₀, w₀], by rw [v₁, w₁], by rw [v₂, w₂], by rw [v₃, w₃], by rw [v₄, w₄]⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u)
    (two_blk [.esp] espOnly (coreArgs_blk _)) fun _ _ _ _ hL hk hc hi => try₂_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ _ => True) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL (hok_of hk) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.esp] espOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

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
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < 8 := ⟨hI.fails i (by omega), hI.lt⟩
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

theorem next_n {n : Nat} (h : 8 - n + 1 < 8) : 8 - (8 - n + 1) < n ∧ 8 - (8 - (8 - n + 1)) = 8 - n + 1 :=
  ⟨by omega, by omega⟩

theorem loop_ct :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) :=
  VG.RelCT.loop (M := isa) (fun n => Two P fun L _ m₀ t => LoopInv P L m₀ (8 - n) t)
    (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
      ⟨he, fun h => (hf h).mono fun _ _ _ _ hx => ⟨_, hx⟩, fun h => by
        obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
        have hn := next_n f₁.lt
        refine ⟨8 - (8 - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩) 8

/-! ## The frame's body -/

theorem initCnt_blk : TaintOk [.esp] (cfgC ⟨4, Spec.P256.curve⟩).initCnt := ⟨_, by taint_decide⟩

/-- `digest` in `esi`, and, if two `V`s make a candidate, `scratch` in `edi`. -/
def DgIn (P : RfcHash) {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .esi = L.a2 ∧ (P.R.wide = true → u.gpr .edi = L.a3)

theorem prep_ct : RelCT isa (Two P (DgIn P))
    (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV)) fun _ _ => True := by
  cases hw : P.R.wide
  · have e : (cfgOf P).wide = false := hw
    simp only [e, Bool.false_eq_true, ite_false]
    exact two_blk [.esp, .esi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm) (P.R.reduceT hw)
  · have e : (cfgOf P).wide = true := hw
    simp only [e, ite_true]
    exact two_blk [.esp, .esi, .edi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact (f₁.2 hw).trans (f₂.2 hw).symm) (wideBlks hw).prep

/-- The body after our caller's registers are saved and `esi` (and `edi`) set. -/
theorem rest_ct :
    RelCT isa (Two P (DgIn P)) (.seq (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++
      Cfg.initKV)) (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block (Cfg.wipe P.R.wide))))))) fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QB P L m₀ t) prep_ct fun _ _ _ _ hL hk hc h =>
    stageB_ok (P := P) hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk [.esp] espOnly initCnt_blk)
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  exact loop_ct.seq (two_blk [.esp] espOnly (wipe_blk _))

/-! ## The whole function -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcX86 P.I (272 + 4 * P.e)).pre s₁ ∧ (rfcX86 P.I (272 + 4 * P.e)).pre s₂ ∧
    (rfcX86 P.I (272 + 4 * P.e)).pub s₁ s₂) ∧ a = allocState (196 + 4 * P.e) s₁ ∧ b = allocState (196 + 4 * P.e) s₂

theorem start_tk (wide : Bool) : TaintOk [.esp] (Cfg.save ++ Cfg.digestPtr wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem start_blk : RelCT isa (Entered P) (.block (Cfg.save ++ Cfg.digestPtr P.R.wide)) fun _ _ => True :=
  let ⟨_, h⟩ := start_tk P.R.wide
  VG.RelCT.taint (A := taint) (τr [.esp]) (fun _ _ ⟨s₁, s₂, ⟨_, _, hsp, _⟩, ea, eb⟩ => agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr ea eb
    rw [allocState_esp, allocState_esp, hsp]) h

/-- Our caller's registers saved, and `digest` in `esi` (and `scratch` in
`edi`): the runs are related by `Two`, with the layout of the arguments,
which agree, and the same number of candidates. -/
theorem start_ct : RelCT isa (Entered P) (.block (Cfg.save ++ Cfg.digestPtr P.R.wide)) (Two P (DgIn P)) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨p₁, p₂, hsp, hdi, hsi, hdx, hcx, hres⟩, rfl, rfl⟩ := hp
  have hw : ∀ s, (rfcX86 P.I (272 + 4 * P.e)).pre s → WP isa (.block (Cfg.save ++ Cfg.digestPtr P.R.wide))
      (allocState (196 + 4 * P.e) s)
      fun u => Ctx (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) s.gpr s.mem u ∧
        DgIn P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) s.gpr s.mem u := fun s h =>
    save_ok h fun _ hc _ => WP.mono (digestPtr_ok (lay_ok h) hc) fun _ ⟨c, a, d⟩ => ⟨c, a, d⟩
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ p₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ p₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₂ = lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁ := by
    simp only [lay, hsp, hdi, hsi, hdx, hcx]
  have hr : (result P.I s₁.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).d
        (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).dg).2 =
      (result P.I s₂.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).d
        (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).dg).2 := by
    show (result P.I s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
      (result P.I s₂.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2
    rw [hres, hsi, hdx]
  rw [hl] at y₂
  exact ⟨ht, ⟨lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁,
    coreOk_lay P s₁, congrArg (fun x => if x = 0 then 7 else x - 1) hr, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- Runs whose public data agree have the same layout, and stop at the same candidate. -/
theorem sign_ct : ConstantTime isa (rfcX86 P.I (272 + 4 * P.e)).pre (rfcX86 P.I (272 + 4 * P.e)).pub
    (cfgOf P).sign :=
  VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (start_ct.seq rest_ct |>.mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h))

end VG.Proof.Ecdsa.Rfc6979.X86
