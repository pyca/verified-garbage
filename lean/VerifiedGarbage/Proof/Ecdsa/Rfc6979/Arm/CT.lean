import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Deterministic ECDSA on 32-bit ARM: constant time, up to the number of candidates

As on x86 (`Proof/Ecdsa/Rfc6979/X86/CT.lean`): two runs whose public data
agree have the same layout, and stop at the same candidate (`exitAt`, from
the contract's leakage: the number of candidates RFC 6979 tries). Between
the prologue and the frame's release they are related by `Two`: both satisfy
`Ctx` with that layout (and `Φ`, what the next piece needs). The blocks
address only the frame and the buffers, from the registers that hold the
pointers, which agree (the taint analysis, of the blocks for each size of
hash function: `Blks`); each call, in its frame, is of constant-time code
whose public data agree (`hi_rel`, `upd_rel`, `hf_rel`, `frame2_rel`); and
the loop's branch agrees, since in both runs it goes on after candidate `i`
iff `i` is before the candidate it stops at (`go_iff`). The prologue's first
instruction reads `sp`, which agrees (`start_blk`), and the frame's
allocation and release access no memory (`alloc_ct`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (hi_rel hf_rel frame2_rel)

/-! ## Frames and single instructions -/

/-- Allocating and freeing a buffer leaks no addresses. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- An instruction that leaks the same in two runs, then a block. -/
theorem block_cons_ct {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by rw [he], hq⟩

/-! ## The taint of the registers that hold pointers -/

theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (τr rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

/-! ## Two runs -/

/-- What each of two runs has, between the prologue and the frame's release. -/
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

theorem sp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- The registers that hold the pointers agree. -/
theorem ptr_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : ∀ r ∈ ptrRegs, t₁.gpr r = t₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r4, c₂.r4]
  · rw [c₁.r5, c₂.r5]
  · rw [c₁.r6, c₂.r6]
  · rw [c₁.r8, c₂.r8]
  · rw [c₁.r11, c₂.r11]

/-- The taint check of a block whose addresses depend only on the registers that hold pointers. -/
abbrev TaintOk (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (τr ptrRegs) (.block is) hc).isSome = true

/-- Such a block. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr ptrRegs) (fun _ _ ⟨_, _, _, _, c₁, c₂, _, _⟩ => agree_regs (ptr_two c₁ c₂)) h

/-! ## The blocks, for each size of hash function -/

/-- The blocks that depend on the hash function's output size `D` and block
size `B`, and on the scalars' `k` words and `Q` bytes, each of which
addresses memory only from the registers that hold pointers. -/
structure Blks (k Q D B : Nat) (wide : Bool) : Prop where
  init : TaintOk (Cfg.hmacArgs₁ D)
  vUpd : TaintOk (Cfg.hmacArgs₂ B [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] D)
  vFin : TaintOk (Cfg.hmacArgs₃ B D fV)
  kUpd₁ : TaintOk (Cfg.hmacArgs₂ B (scrAt .r1 sMsg) (D + 1))
  kFin₁ : TaintOk (Cfg.hmacArgs₃ B (D + 1) fK)
  kUpdF : TaintOk (Cfg.hmacArgs₂ B (scrAt .r1 sMsg) (D + 2 * Q + 1))
  kFinF : TaintOk (Cfg.hmacArgs₃ B (D + 2 * Q + 1) fK)
  msg₀ : TaintOk (Cfg.msg k Q D 0 false false)
  msg₀f : TaintOk (Cfg.msg k Q D 0 true wide)
  msg₁f : TaintOk (Cfg.msg k Q D 1 true wide)

theorem blks (P : RfcHash) : Blks P.k P.Q P.F.H.D P.F.H.B P.R.wide := by
  have hk : P.k = 2 * P.R.E.n := rfl
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hQ : P.Q = 8 * P.R.E.n := hQ8
    rw [hQ, hk]
    rcases (P.R.sizesA hw).1 with hn | hn | hn <;> rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      rw [hn, h, h'] <;>
      first
      | (exfalso; rw [hQ, hn, h] at hQD; omega)
      | exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
          ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
          ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  · obtain ⟨hw9, hQ66, hD64, hB⟩ := P.sizesW hw
    rw [hQ66, hD64, hB, hk, show P.R.E.n = 9 from hw9]
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-! The blocks that depend on whether two `V`s make a candidate. -/

theorem coreArgs_blk (wide : Bool) : TaintOk (Cfg.coreArgs wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem wipe_blk (wide : Bool) : TaintOk (Cfg.wipe wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- If two `V`s make a candidate: the digest for `core` and `V = 0x01…`,
`K = 0x00…`, `V` kept, and the candidate. -/
structure WideBlks (P : RfcHash) : Prop where
  prep : TaintOk ((cfgOf P).coreDigest ++ Cfg.initKV)
  keep : TaintOk (cfgOf P).keepV
  top : TaintOk (cfgOf P).candTop

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
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

/-- The arguments of the streaming `update`, for the data at `dv L` of `len` bytes. -/
def UA (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32)
    (_ : Mem) (u : State) : Prop :=
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = dv L ∧ u.gpr .r2 = BitVec.ofNat 32 P.F.H.B ∧
    u.gpr .r3 = 0 ∧ u.gpr .r7 = BitVec.ofNat 32 len ∧ u.gpr .r10 = L.scr + BitVec.ofNat 32 384

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC to `dst`. -/
def FA (P : RfcHash) (len dst : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + len) ∧ u.gpr .r3 = 0 ∧ u.gpr .r10 = L.fp + BitVec.ofNat 32 dst ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

theorem hinit_ct :
    RelCT isa (Two P (IA P)) (.frame (.push [.r12, .lr]) (.call P.F.hiN P.F.hiC) (.pop .r12 8))
      fun _ _ => True :=
  two_exists fun e => hi_rel P.ok.hi (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.sp, c₂.sp⟩

theorem hupd_ct {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len)
    (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P dv len))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call P.F.H.updN P.F.H.updC) (.pop .r1 16)) fun _ _ => True :=
  two_exists fun e => Proof.Pbkdf2.Whole.Arm.upd_rel P.ok.hH (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [Pbkdf2.Stream.Arm.count, Pbkdf2.Stream.Arm.count, a₁.2.2.1, a₁.2.2.2.1, a₂.2.2.1, a₂.2.2.2.1],
      c₁.sp, c₂.sp⟩

theorem hfin_ct {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    RelCT isa (Two P (FA P len dst))
      (.frame (.push [.r10, .r12]) (.call P.F.hfN P.F.hfC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => hf_rel P.ok.hf (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [a₁.2.2.1, a₂.2.2.1], by rw [a₁.2.2.2.1, a₂.2.2.2.1], c₁.sp, c₂.sp⟩

/-! ## One HMAC -/

/-- After HMAC's `init` and `update`: the states, for the state before. -/
def Ini (P : RfcHash) : Pred P := fun L g m₀ u => ∃ t, Inited P L g m₀ t u
def Upt (P : RfcHash) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P :=
  fun L g m₀ u => ∃ t, Updated P L g m₀ t (dv L) len u

theorem initS_ct {Φ : Pred P} :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.hmacArgs₁ P.F.H.D))
      (.frame (.push [.r12, .lr]) (.call P.F.hiN P.F.hiC) (.pop .r12 8))) (Two P (Ini P)) :=
  two_wp ((two_wp (Ψ := IA P) (two_blk (blks P).init) fun _ _ _ _ _ _ hc _ =>
      WP.mono (initArgs_ok hc (by anums)) fun _ ⟨c, _, a⟩ => ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1⟩).seq
      hinit_ct)
    fun _ _ _ t hL _ hc _ => WP.mono (init_step hL hc) fun _ h => ⟨h.ctx, t, h⟩

theorem updS_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀, L.Ok → DataA L g m₀ dataA (dv L))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256)
    (t₂ : TaintOk (Cfg.hmacArgs₂ P.F.H.B dataA len)) :
    RelCT isa (Two P (Ini P)) (.seq (.block (Cfg.hmacArgs₂ P.F.H.B dataA len))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call P.F.H.updN P.F.H.updC) (.pop .r1 16)))
      (Two P (Upt P dv len)) :=
  two_wp ((two_wp (Ψ := UA P dv len) (two_blk t₂) fun L g m₀ _ hL _ hc _ =>
      WP.mono (updArgs_ok hc (hdA L g m₀ hL) (B := P.F.H.B) (by anums) (len := len) (by omega))
        fun _ ⟨c, _, a⟩ => ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1⟩).seq (hupd_ct hd hlen))
    fun L g m₀ _ hL _ _ ⟨t, hi⟩ => WP.mono (upd_step hL hi (hdA L g m₀ hL) (hd L hL) hlen)
      fun _ h => ⟨h.ctx, t, h⟩

theorem finS_ct {dv : Lay P.I.hashLen → BitVec 32} {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (he : encodable (BitVec.ofNat 32 dst) = true) (t₃ : TaintOk (Cfg.hmacArgs₃ P.F.H.B len dst)) (hlen : len ≤ 256) :
    RelCT isa (Two P (Upt P dv len)) (.seq (.block (Cfg.hmacArgs₃ P.F.H.B len dst))
      (.frame (.push [.r10, .r12]) (.call P.F.hfN P.F.hfC) (.pop .r12 8)))
      fun _ _ => True :=
  (two_wp (Ψ := FA P len dst) (two_blk t₃) fun _ _ _ _ _ _ hc _ =>
    WP.mono (finArgs_ok hc (B := P.F.H.B) (len := len) (by anums) he) fun _ ⟨c, _, a⟩ =>
      ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1⟩).seq (hfin_ct hdst)

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, and its
calls are constant time with arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len dst : Nat} {Φ : Pred P}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀, L.Ok → DataA L g m₀ dataA (dv L))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 128)
    (he : encodable (BitVec.ofNat 32 dst) = true)
    (t₂ : TaintOk (Cfg.hmacArgs₂ P.F.H.B dataA len)) (t₃ : TaintOk (Cfg.hmacArgs₃ P.F.H.B len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA len dst) fun _ _ => True :=
  RelCT.assoc (initS_ct.seq (RelCT.assoc ((updS_ct hdA hd hlen t₂).seq (finS_ct hdst he t₃ hlen))))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dv := fun L => L.fp + BitVec.ofNat 32 64) (len := P.F.H.D) (dst := 64)
    (fun _ _ _ _ => dataV) (fun _ _ => .inl ⟨64, rfl, by anums⟩) (by anums) (by anums) (by decide)
    (blks P).vUpd (blks P).vFin

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256)
    (t₂ : TaintOk (Cfg.hmacArgs₂ P.F.H.B (scrAt .r1 sMsg) len)) (t₃ : TaintOk (Cfg.hmacArgs₃ P.F.H.B len fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) fun _ _ => True :=
  hmac_ct (dv := fun L => L.scr + BitVec.ofNat 32 2256) (dst := 0) (fun _ _ _ _ => dataM)
    (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) hlen (by anums) (by decide) t₂ t₃

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} (hb : b < 2) {full wd : Bool} (hwd : wd = (full && P.R.wide))
    {len : Nat} (hlen : len = if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1)
    (t₁ : TaintOk (Cfg.msg P.k P.Q P.F.H.D b full wd))
    (t₂ : TaintOk (Cfg.hmacArgs₂ P.F.H.B (scrAt .r1 sMsg) len)) (t₃ : TaintOk (Cfg.hmacArgs₃ P.F.H.B len fK)) :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.msg P.k P.Q P.F.H.D b full wd))
      (.seq ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) (cfgOf P).hmacV)) fun _ _ => True := by
  have hlen' : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  refine (two_wp (Ψ := fun _ _ _ _ => True) (two_blk t₁) fun _ _ _ _ hL hk hc _ =>
    WP.mono (msg_ok hL hc hb full wd (D := P.F.H.D) (k := P.k) (Q := P.Q) (by anums) (by anums) (by anums)
      (by anums) (by rw [hk.1])
      (fun hf hwf => by
        have := P.sizesA (by rw [hwd, hf] at hwf; exact hwf)
        simp only [RfcHash.k, RfcHash.w] at this ⊢; exact ⟨by omega, by omega⟩)
      (fun hf hwt => by
        have hW : P.R.wide = true := by rw [hwd, hf] at hwt; exact hwt
        have := P.sizesW hW; exact ⟨by omega, by omega, by rw [P.len]⟩))
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ _ => True) (hmacK_ct hlen' t₂ t₃) fun _ _ _ _ hL _ hc _ =>
    WP.mono (hmacK_ok (P := P) hL hc hlen') fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (full := true) hb rfl (len := P.F.H.D + 2 * P.Q + 1) rfl (blks P).msg₀f (blks P).kUpdF
      (blks P).kFinF
  · exact rekey_gen_ct (full := true) hb rfl (len := P.F.H.D + 2 * P.Q + 1) rfl (blks P).msg₁f (blks P).kUpdF
      (blks P).kFinF

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (by decide) (full := false) (wd := false) rfl (len := P.F.H.D + 1) rfl (blks P).msg₀
    (blks P).kUpd₁ (blks P).kFin₁

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  cases hw : P.R.wide
  · have e : (cfgOf P).cand = (cfgOf P).hmacV := by simp only [Cfg.cand, cfgOf, hw]; rfl
    rw [e]; exact hmacV_ct
  · have e : (cfgOf P).wide = true := hw
    have W := wideBlks hw
    simp only [Cfg.cand, e, ite_true]
    refine (two_wp (Ψ := fun _ _ _ _ => True) hmacV_ct fun _ _ _ _ hL _ hc _ =>
      WP.mono (hmacV_ok hL hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := fun _ _ _ _ => True) (two_blk W.keep) fun L _ _ _ hL hk hc _ => ?_).seq ?_
    · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
      have he := e36 hk.2.2 hw
      have e₃ : (cfgOf P).F.H.D = 64 := hD64
      have hfp := fp_toNat' hL
      have := L.sp.isLt
      have nB := hL.nB
      simp only [Cfg.keepV, e₃]
      exact WP.mono (copyF_ok hL hc (src := .r8) (S := L.fp) hc.r8 (by decide) (so := 64) (d := 288)
        (K := 64 / 4) (by omega) (by omega) (by omega) (by omega)
        (fun j hj => by rw [fpd hL]; exact hc.inFr (by omega) (by omega))
        (by rw [fpd hL]; exact Offset.disjoint _ (by omega) (by omega) (by omega))) fun _ h => ⟨h.1, trivial⟩
    refine (two_wp (Ψ := fun _ _ _ _ => True) hmacV_ct fun _ _ _ _ hL _ hc _ =>
      WP.mono (hmacV_ok hL hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    exact two_blk W.top

/-! ## One candidate -/

/-- `core`, in its frame, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u)
      (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => frame2_rel rfl P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun s₁ s₂ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      have h₁ := c₁.sp24 hL
      have h₂ := c₂.sp24 hL
      refine ⟨sp_two c₁ c₂, core_pre hL hk c₁ a₁, core_pre hL hk c₂ a₂, ?_,
        core_cov hL hk c₁, core_covW hk.1 c₁, core_cov hL hk c₂, core_covW hk.1 c₂⟩
      simp only [coreK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        Pbkdf2.Stream.Arm.ce0, Pbkdf2.Stream.Arm.ce1, Pbkdf2.Stream.Arm.ce2, Pbkdf2.Stream.Arm.ce3, pushed_gpr,
        pushed_sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₁) (by omega), Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₂) (by omega),
        a₁.r12, a₂.r12, sp_two c₁ c₂, and_self]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem goOn_blk : TaintOk Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk Cfg.stop := ⟨_, by taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u) (two_blk (coreArgs_blk _))
    fun _ _ _ _ _ hk hc hi => try₂_ok hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
    fun _ _ _ _ _ _ hc hi => try₄_ok hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ _ => True) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL (hok_of hk) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → Two P (fun L _ m₀ t => Exit P L m₀ i t) s₁ s₂) ∧
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

theorem reduce_eq : (cfgOf P).reduce ++ Cfg.initKV = (cfgC P.R.E).reduce ++ Cfg.initKV := rfl
theorem initCnt_eq : (cfgOf P).initCnt = [.movw .r9 (BitVec.ofNat 16 8)] := rfl

theorem initCnt_blk : TaintOk [.movw .r9 (BitVec.ofNat 16 8)] := ⟨_, by taint_decide⟩

/-- The body after the prologue, `h`, `V` and `K`. -/
theorem rest_ct :
    RelCT isa (Two P fun L _ m₀ t => QB P L m₀ t) (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne) (.block (Cfg.wipe (cfgOf P).wide))))))
      fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (by rw [initCnt_eq]; exact two_blk initCnt_blk)
    fun _ _ _ _ _ _ hc h => stageE_ok (P := P) hc h).seq ?_
  exact loop_ct.seq (two_blk (wipe_blk _))

theorem prep_ct : RelCT isa (Two P fun _ _ _ _ => True)
    (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV))
      fun _ _ => True := by
  cases hw : P.R.wide
  · have e : (cfgOf P).wide = false := hw
    simp only [e, Bool.false_eq_true, ite_false]
    rw [reduce_eq]; exact two_blk (P.R.reduceT hw)
  · have e : (cfgOf P).wide = true := hw
    simp only [e, ite_true]
    exact two_blk (wideBlks hw).prep

/-- `h`, `V` and `K`, after the prologue. -/
theorem stageB_ct :
    RelCT isa (Two P fun _ _ _ _ => True)
      (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV))
      (Two P fun L _ m₀ t => QB P L m₀ t) :=
  two_wp prep_ct fun _ _ _ _ hL hk hc _ => stageB_ok (P := P) hL hk hc

/-! ## The prologue -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcArm P.I (240 + 4 * P.e)).pre s₁ ∧ (rfcArm P.I (240 + 4 * P.e)).pre s₂ ∧
    (rfcArm P.I (240 + 4 * P.e)).pub s₁ s₂) ∧
    a = allocated (frameBytes P.R.wide) s₁ ∧ b = allocated (frameBytes P.R.wide) s₂

theorem prologue_tail : ∃ hc, (VG.Taint.check taint (τr [.r0, .r1, .r2, .r3, .r12])
    (.block (Impl.Ecdsa.Rfc6979.Arm.saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r11 (.reg .r3),
        .mov .r8 (.reg .r12)] : List Instr)))
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- The prologue reads `sp`, which agrees, and then addresses the frame through `r12`. -/
theorem start_blk : RelCT isa (Entered P) (.block Cfg.prologue) fun _ _ => True := by
  rw [Cfg.prologue, List.cons_append]
  refine block_cons_ct (R := fun a b => ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r12], a.gpr r = b.gpr r)
    (fun a b a' b' ⟨s₁, s₂, ⟨_, _, hsp, h0, h1, h2, h3, _⟩, ea, eb⟩ ha hb => ?_) ?_
  · subst ea eb
    simp only [exec, show (0 : Nat) < 256 by decide, ↓reduceIte, Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [State.setReg, reduceCtorEq, ↓reduceIte, allocated, h0, h1, h2, h3, hsp]
  · let ⟨_, h⟩ := prologue_tail
    exact VG.RelCT.taint (A := taint) _ (fun _ _ h => agree_regs h) h

/-- After the prologue, the runs are related by `Two`, with the layout of the
arguments, which agree, and the same number of candidates. -/
theorem start_ct : RelCT isa (Entered P) (.block Cfg.prologue) (Two P fun _ _ _ _ => True) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨p₁, p₂, hsp, h0, h1, h2, h3, hres⟩, rfl, rfl⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok (P := P) p₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok (P := P) p₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₂ = lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁ := by simp only [lay, hsp, h0, h1, h2, h3]
  have hr : (result P.I s₁.mem (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).d) (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).dg)).2 =
      (result P.I s₂.mem (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).d) (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁).dg)).2 := by
    show (result P.I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result P.I s₂.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2
    rw [hres, h1, h2]
  rw [hl] at y₂
  exact ⟨ht, ⟨lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁,
    coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then 7 else x - 1) hr, y₁, y₂, trivial, trivial⟩

/-- Runs whose public data agree have the same layout, and stop at the same candidate. -/
theorem sign_ct : ConstantTime isa (rfcArm P.I (240 + 4 * P.e)).pre (rfcArm P.I (240 + 4 * P.e)).pub
    (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (R := fun _ _ => True) ?_)
  rw [Cfg.body, show Cfg.prologue ++ (if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++
    Cfg.initKV = Cfg.prologue ++ ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++
      Cfg.initKV) from List.append_assoc _ _ _]
  refine (RelCT.block_append (start_ct.seq stageB_ct)).seq rest_ct |>.mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.Arm
