module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Attempt
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The seeds in turn: the refillable-tape controller

`search_ok`: the seeds, one at a time from the cursor `fC`, with `fSeedLeft`
seeds left, until one gives a domain (`fStatus` := 1, p‖q‖g at `sPk`),
`rand` runs out (2) or the seeds do (3), as `Spec.Dsa.parameterSearch` tries
them (`Proof/Dsa/Generation/RefillSearch.lean`): the end it reaches is
`sOut`, and its result as the spec states it `cRes`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Proof.Dsa.Generation

theorem Env.Valid.qLen_eq {E : Env} (v : E.Valid) : E.qLen = Spec.Dsa.generationQLen E.pLen := by
  rcases v.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [Spec.Dsa.generationQLen, h, h']

/-! ## The controller's spec -/

/-- The seed at the cursor `c`, as the code runs it. -/
abbrev sR (E : Env) (c : Nat) : Option (Option Spec.Dsa.Params × Spec.RsaKeyGen.Rand) :=
  refillAttempt E.pLen E.qLen ((E.witT.drop c).take E.qLen) (E.witT.drop (c + E.qLen))

/-- How the controller ends. -/
inductive COut where
  | found (a : Spec.Dsa.Params) (u : Nat)
  | noSeeds (c : Nat)
  | ranOut (j c : Nat)

/-- The next seed's state after the one at the cursor `c`, with `j` seeds
left, if the controller goes on. -/
def sStep (E : Env) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | j + 1, c => if E.witLen - c < E.qLen then none else
    match sR E c with
    | some (none, rest) => some (j, E.witLen - rest.length)
    | _ => none

/-- The controller's end from `j` seeds left and the cursor `c`. -/
def sOut (E : Env) : Nat → Nat → COut
  | 0, c => .noSeeds c
  | j + 1, c => if E.witLen - c < E.qLen then .ranOut (j + 1) c else
    match sR E c with
    | some (none, rest) => sOut E j (E.witLen - rest.length)
    | some (some a, rest) => .found a (E.witLen - rest.length)
    | none => .ranOut (j + 1) c

/-- Its result, as the spec states it. -/
def cRes (E : Env) : COut → Spec.Dsa.ParameterSearchResult
  | .found a u => ⟨.accepted a, u, []⟩
  | .noSeeds c => ⟨.exhausted, c, []⟩
  | .ranOut j c => ranOutResult E.pLen j (E.witLen - c) c

/-- The controller's end in memory `m`. -/
def SRes (E : Env) (g : Geo) (m : Mem) : COut → Prop
  | .found a u => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 1 ∧
      Spec.Rsa.bytesAt m (off E.base sPk) (2 * g.pLen + g.qLen) = Spec.Dsa.encodeParams g.pLen g.qLen a ∧
      m.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u ∧ u ≤ E.witLen
  | .noSeeds c => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 3 ∧
      m.readW (off E.base fC) 32 = BitVec.ofNat 32 c ∧ c ≤ E.witLen
  | .ranOut j c => m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 2 ∧
      m.readW (off E.base fC) 32 = BitVec.ofNat 32 c ∧ m.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 j ∧
      c ≤ E.witLen ∧ j ≤ Spec.Dsa.parameterSeeds

/-! ## What the controller keeps -/

/-- The ranges the search changes. -/
def sRanges (g : Geo) : List (Nat × Nat) := atRanges g ++ [(fSeed, 4), (fSeedLeft, 4), (fC, 4)]

theorem sRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) :
    E.Apart (sRanges g) := by
  have sz := v.size_ge
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact atRanges_apart G v hp o h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [fSeed, fSeedLeft, fC, fOut, fUsedP, fWitLen, hdr] <;> omega

/-- What the search keeps. -/
structure SKeep (E : Env) (g : Geo) (s t : State) : Prop where
  base : Base E t
  chg : E.Chg (sRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem SKeep.mem {E : Env} {g : Geo} {s t t' : State} (K : SKeep E g s t) (hm : t'.mem = t.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : SKeep E g s t' :=
  ⟨K.base.regs hm edi sp rd wr sy, by rw [hm]; exact K.chg, by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

theorem SKeep.store {E : Env} {g : Geo} {s t t' : State} (K : SKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {d : Nat} (hd : (d, 4) ∈ sRanges g) (x : BitVec 32)
    (hm : t'.mem = t.mem.writeW (off E.base d) x) (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp)
    (rd : t'.rd = t.rd) (wr : t'.wr = t.wr) (sy : t'.syms = t.syms) : SKeep E g s t' := by
  have C : E.Chg [(d, 4)] t.mem t'.mem := by
    rw [hm]; exact (Env.Chg.refl _ _).store (List.mem_singleton_self _) (by decide) x
  exact ⟨K.base.keep v C (fun o ho => sRanges_apart G v hp o
      (by simp only [List.mem_singleton] at ho; rw [ho]; exact hd)) edi sp rd wr sy,
    K.chg.trans (C.widen fun o ho => ⟨o, by simp only [List.mem_singleton] at ho; rw [ho]; exact hd,
      Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd], by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- Stores into ranges of the search. -/
theorem SKeep.chgs {E : Env} {g : Geo} {s t t' : State} (K : SKeep E g s t) (G : GeoOk g) (v : E.Valid)
    (hp : E.pLen = g.pLen) {os : List (Nat × Nat)} (hos : ∀ o ∈ os, o ∈ sRanges g) (C : E.Chg os t.mem t'.mem)
    (edi : t'.gpr .edi = t.gpr .edi) (sp : t'.gpr .esp = t.gpr .esp) (rd : t'.rd = t.rd) (wr : t'.wr = t.wr)
    (sy : t'.syms = t.syms) : SKeep E g s t' :=
  ⟨K.base.keep v C (fun o ho => sRanges_apart G v hp o (hos o ho)) edi sp rd wr sy,
    K.chg.trans (C.widen fun o ho => ⟨o, hos o ho, Nat.le_refl _, Nat.le_refl _⟩), by rw [rd, K.rd],
    by rw [wr, K.wr], by rw [sy, K.syms]⟩

/-- At the loop's head, with `j` seeds left and the cursor at `c`. -/
structure SLoop (E : Env) (g : Geo) (s : State) (j c : Nat) (t : State) : Prop where
  keep : SKeep E g s t
  left : t.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 j
  cur : t.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c
  status : t.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0
  hc : c ≤ E.witLen
  hj : j ≤ Spec.Dsa.parameterSeeds
  spec : (Spec.Dsa.parameterSearch E.pLen j (E.witT.drop c)).consume c [] =
    Spec.Dsa.parameterSearch E.pLen E.k0 E.witT
  out : sOut E j c = sOut E E.k0 0

/-! ## The controller's blocks -/

section
variable {is : List Instr} {Q : State → Prop}

/-- The octets of `rand` after the cursor, compared with `w`. -/
theorem availCmp_ok {E : Env} (v : E.Valid) {s : State} (B : Base E s) {c : Nat}
    (hC : s.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c) (hc : c ≤ E.witLen) {w : Nat} (hw : w < 2 ^ 32)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → s'.gpr .eax = BitVec.ofNat 32 (E.witLen - c) →
      isa.eval .b s' = some (decide (E.witLen - c < w)) → WP isa (.block is) s' Q) :
    WP isa (.block (Geo.avail ++ .alu .cmp .eax (.imm (BitVec.ofNat 32 w)) :: is)) s Q := by
  have sz := v.size_ge
  have wl := v.witLen32
  simp only [Geo.avail, List.cons_append, List.nil_append]
  refine ld_ok B.scr (d := fWitLen) (by simp only [fWitLen, hdr]; omega) fun s₁ u₁ =>
    ld_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fC)
      (by simp only [fC, hdr]; omega) fun s₂ u₂ => wp_sub fun s₃ u₃ _ => wp_cmpi fun s₄ f₄ c₄ _ => ?_
  have eax : s₄.gpr .eax = BitVec.ofNat 32 (E.witLen - c) := by
    rw [f₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, B.witLenW, hC, sub_ofNat hc]
  refine k s₄ (fun r h₁ h₂ => by rw [f₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁])
    (by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [f₄.syms, u₃.syms, u₂.syms, u₁.syms]) eax ?_
  show s₄.cf = _
  rw [c₄, show s₃.gpr .eax = BitVec.ofNat 32 (E.witLen - c) by rw [← eax, f₄.gpr], toNat_ofNat_lt (by omega),
    toNat_ofNat_lt hw]

/-- The seed at the cursor `c`: `fSeed` := `rand + c`, its witnesses from `c + q_len`. -/
theorem seedStart_ok {g : Geo} {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) {s : State} (B : Base E s) {c : Nat}
    (hC : s.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c) :
    WP isa (.block g.seedStart) s fun t => t.mem = (s.mem.writeW (off E.base fSeed)
      ((E.wit + BitVec.ofNat 64 c).setWidth 32)).writeW (off E.base fUsed) (BitVec.ofNat 32 (c + E.qLen)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  unfold Geo.seedStart
  refine ld_ok B.scr (d := fC) (by simp only [fC, hdr]; omega) fun s₁ u₁ =>
    ld_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fWit)
      (by simp only [fWit, hdr]; omega) fun s₂ u₂ => wp_add fun s₃ u₃ _ => ?_
  have hs₃ : Scr s₃ E.base E.size := Scr.of_eq B.scr (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  refine st_ok hs₃ (d := fSeed) (by simp only [fSeed, hdr]; omega) fun s₄ M₄ => wp_addi fun s₅ u₅ =>
    st_ok (Scr.of_eq hs₃ (by rw [u₅.other _ (by decide), M₄.gpr]) (by rw [u₅.other _ (by decide), M₄.gpr])
      (by rw [u₅.wr, M₄.wr])) (d := fUsed) (by simp only [fUsed, hdr]; omega) fun s₆ M₆ => WP.block_nil ?_
  have ecx₃ : s₃.gpr .ecx = BitVec.ofNat 32 c := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hC]
  refine ⟨?_, fun r h₁ h₂ => by
      rw [M₆.gpr, u₅.other _ h₂, M₄.gpr, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₂],
    by rw [M₆.rd, u₅.rd, M₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [M₆.wr, u₅.wr, M₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [M₆.syms, u₅.syms, M₄.syms, u₃.syms, u₂.syms, u₁.syms]⟩
  rw [M₆.mem, u₅.mem, M₄.mem, u₅.gpr, M₄.gpr, ecx₃, u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide), u₂.mem,
    u₁.gpr, u₁.mem, B.witW, hC, ptr_add, hq, ← BitVec.ofNat_add]

/-- A rejected seed: the cursor past it, one seed fewer left. -/
theorem rejected_ok {E : Env} (v : E.Valid) {s : State} (B : Base E s) {u j : Nat}
    (hU : s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u)
    (hL : s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 (j + 1)) (hj : j + 1 < 2 ^ 32) :
    WP isa (.block Geo.rejected) s fun t => t.mem = (s.mem.writeW (off E.base fC) (BitVec.ofNat 32 u)).writeW
      (off E.base fSeedLeft) (BitVec.ofNat 32 j) ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have sz := v.size_ge
  unfold Geo.rejected
  refine ld_ok B.scr (d := fUsed) (by simp only [fUsed, hdr]; omega) fun s₁ u₁ =>
    st_ok (Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr) (d := fC)
      (by simp only [fC, hdr]; omega) fun s₂ M₂ => ?_
  have hs₂ : Scr s₂ E.base E.size := Scr.of_eq B.scr (by rw [M₂.gpr, u₁.other _ (by decide)])
    (by rw [M₂.gpr, u₁.other _ (by decide)]) (by rw [M₂.wr, u₁.wr])
  refine ld_ok hs₂ (d := fSeedLeft) (by simp only [fSeedLeft, hdr]; omega) fun s₃ u₃ => wp_subi fun s₄ u₄ _ _ =>
    st_ok (Scr.of_eq hs₂ (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])) (d := fSeedLeft)
      (by simp only [fSeedLeft, hdr]; omega) fun s₅ M₅ => WP.block_nil ⟨?_, fun r h => by
        rw [M₅.gpr, u₄.other _ h, u₃.other _ h, M₂.gpr, u₁.other _ h], by rw [M₅.rd, u₄.rd, u₃.rd, M₂.rd, u₁.rd],
        by rw [M₅.wr, u₄.wr, u₃.wr, M₂.wr, u₁.wr], by rw [M₅.syms, u₄.syms, u₃.syms, M₂.syms, u₁.syms]⟩
  rw [M₅.mem, u₄.mem, u₃.mem, u₄.gpr, u₃.gpr, M₂.mem, u₁.gpr, u₁.mem, hU, word_store_other v _
    (by simp only [fSeedLeft, hdr]; omega) (by simp only [fC, hdr]; omega) (by simp only [fC, fSeedLeft, hdr]; omega),
    hL, ofNat_pred (by omega)]
  rfl

end

/-! ## The loop -/

/-- The cursor after a seed, from the witnesses its attempt left. -/
theorem cursor_of {E : Env} (hl : E.witT.length = E.witLen) {u : Nat} (hu : u ≤ E.witLen) :
    E.witLen - (E.witT.drop u).length = u := by
  rw [List.length_drop, hl]; omega

/-- One seed: the loop exits with the search's end, or goes on to the next. -/
theorem sBody_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} {j c : Nat} {t : State} (L : SLoop E g s j c t) :
    WP isa (seqs [.block (cmpF fSeedLeft 0),
      .ite .e (.block (stImm fStatus 3))
        (seqs [.block (Geo.avail ++ ([.alu .cmp .eax (.imm (BitVec.ofNat 32 g.qLen))] : List Instr)),
          .ite .b (.block (stImm fStatus 2))
            (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
              .ite .e (.block Geo.rejected) (.block [])])]),
      .block (cmpF fStatus 0)]) t fun t' => t'.zf = some (sStep E j c).isSome ∧
      (sStep E j c = none → SKeep E g s t' ∧ SRes E g t'.mem (sOut E j c) ∧
        cRes E (sOut E j c) = Spec.Dsa.parameterSearch E.pLen E.k0 E.witT) ∧
      (∀ j' c', sStep E j c = some (j', c') → j' < j ∧ SLoop E g s j' c' t') := by
  have sz := v.size_ge
  have bd := G.bounds
  have wl := v.witLen32
  have hl : E.witT.length = E.witLen := by rw [← L.keep.base.wit, VG.Proof.Bignum.bytesAt_length]
  have qE := v.qLen_eq
  have pp : 0 < E.pLen := by omega
  have ws : ∀ (m : Mem) {d e : Nat}, d + 4 ≤ sState → e + 4 ≤ sState → (d + 4 ≤ e ∨ e + 4 ≤ d) → ∀ y,
      (m.writeW (off E.base e) y).readW (off E.base d) 32 = m.readW (off E.base d) 32 :=
    fun m d e h₁ h₂ h y => word_store_other v m (by simp only [sState] at h₁; omega) (by simp only [sState] at h₂; omega)
      h y
  simp only [seqs]
  refine WP.seq (cmpF_end L.keep.base.scr (o := fSeedLeft) (v := 0) (by simp only [fSeedLeft, hdr]; omega) L.left
    (by have := L.hj; simp only [Spec.Dsa.parameterSeeds] at this; omega) (by decide)
    fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  have K₁ := L.keep.mem m₁ (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ sy₁
  rcases j with _ | j
  · -- No seeds left: `fStatus` := 3.
    refine WP.seq (WP.ite _ z₁ (fun _ => stImm_end K₁.base.scr (o := fStatus) (v := 3)
      (by simp only [fStatus, hdr]; omega) fun t₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_) (fun h => by simp at h))
    have K₂ := K₁.store G v hp (d := fStatus) (by simp [sRanges, atRanges]) _ m₂ (g₂ _ (by decide))
      (g₂ _ (by decide)) rd₂ wr₂ sy₂
    refine cmpF_end K₂.base.scr (o := fStatus) (v := 0) (w := 3) (by simp only [fStatus, hdr]; omega)
      (by rw [m₂, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ z₃ => ?_
    refine ⟨z₃, fun _ => ⟨K₂.mem m₃ (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ sy₃, ?_, ?_⟩,
      fun _ _ h => by simp [sStep] at h⟩
    · refine ⟨by rw [m₃, m₂, Mem.readW_writeW_self32], ?_, L.hc⟩
      rw [m₃, m₂, ws _ (by simp only [fC, sState, hdr]; omega) (by simp only [fStatus, sState, hdr]; omega)
        (by simp only [fC, fStatus, hdr]; omega), m₁, L.cur]
    · rw [← L.spec]; exact (search_zero _ _ _).symm
  have j1 : j + 1 < 2 ^ 32 := by have := L.hj; simp only [Spec.Dsa.parameterSeeds] at this; omega
  refine WP.seq (WP.ite _ z₁ (fun h => by simp only [decide_eq_true_eq] at h; omega) (fun _ => ?_))
  refine WP.seq (availCmp_ok v K₁.base (c := c) (by rw [m₁]; exact L.cur) L.hc (w := g.qLen) (by omega)
    fun t₂ g₂ m₂ rd₂ wr₂ sy₂ _ c₂ => WP.block_nil ?_)
  have K₂ := K₁.mem m₂ (g₂ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)) rd₂ wr₂ sy₂
  have mem₂ : t₂.mem = t.mem := by rw [m₂, m₁]
  have hpL : 0 < E.pLen := pp
  by_cases short : E.witLen - c < E.qLen
  · -- Too few octets for a seed: `fStatus` := 2.
    refine WP.ite _ c₂ (fun _ => stImm_end K₂.base.scr (o := fStatus) (v := 2)
      (by simp only [fStatus, hdr]; omega) fun t₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_) (fun h => by simp [hq ▸ short] at h)
    have K₃ := K₂.store G v hp (d := fStatus) (by simp [sRanges, atRanges]) _ m₃ (g₃ _ (by decide))
      (g₃ _ (by decide)) rd₃ wr₃ sy₃
    have hS : sStep E (j + 1) c = none := by simp [sStep, short]
    refine cmpF_end K₃.base.scr (o := fStatus) (v := 0) (w := 2) (by simp only [fStatus, hdr]; omega)
      (by rw [m₃, Mem.readW_writeW_self32]) (by decide) (by decide) fun t₄ g₄ m₄ rd₄ wr₄ sy₄ z₄ => ?_
    refine ⟨by rw [show t₄.zf = _ from z₄, hS]; rfl, fun _ => ⟨K₃.mem m₄ (g₄ _ (by decide)) (g₄ _ (by decide)) rd₄
      wr₄ sy₄, ?_, ?_⟩, fun _ _ h => by rw [hS] at h; cases h⟩
    · simp only [sOut, short, ↓reduceIte, SRes]
      refine ⟨by rw [m₄, m₃, Mem.readW_writeW_self32], ?_, ?_, L.hc, L.hj⟩
      · rw [m₄, m₃, ws _ (by simp only [fC, sState, hdr]; omega) (by simp only [fStatus, sState, hdr]; omega)
          (by simp only [fC, fStatus, hdr]; omega), mem₂, L.cur]
      · rw [m₄, m₃, ws _ (by simp only [fSeedLeft, sState, hdr]; omega) (by simp only [fStatus, sState, hdr]; omega)
          (by simp only [fSeedLeft, fStatus, hdr]; omega), mem₂, L.left]
    · simp only [sOut, short, ↓reduceIte, cRes]
      rw [← L.spec, search_short (by rw [hl, ← qE]; exact short), hl]
  -- A seed.
  have hcq : c + E.qLen ≤ E.witLen := by omega
  refine WP.ite _ c₂ (fun h => by simp only [decide_eq_true_eq] at h; omega) (fun _ => ?_)
  refine WP.seq (WP.mono (seedStart_ok v hq K₂.base (c := c) (by rw [mem₂]; exact L.cur))
    fun t₃ ⟨m₃, g₃, rd₃, wr₃, sy₃⟩ => ?_)
  have edi₃ : t₃.gpr .edi = t₂.gpr .edi := g₃ _ (by decide) (by decide)
  have esp₃ : t₃.gpr .esp = t₂.gpr .esp := g₃ _ (by decide) (by decide)
  have C₃ : E.Chg [(fSeed, 4), (fUsed, 4)] t₂.mem t₃.mem := by
    rw [m₃]
    exact ((Env.Chg.refl _ _).store (d := fSeed) (n := 4) (by simp) (by decide) _).store (d := fUsed)
      (n := 4) (by simp) (by decide) _
  have K₃ : SKeep E g s t₃ := K₂.chgs G v hp (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp [sRanges, atRanges, qRanges]) C₃ edi₃ esp₃ rd₃ wr₃ sy₃
  have w₃ : ∀ d, d + 4 ≤ sState → (d + 4 ≤ fSeed ∨ fSeed + 4 ≤ d) → (d + 4 ≤ fUsed ∨ fUsed + 4 ≤ d) →
      t₃.mem.readW (off E.base d) 32 = t.mem.readW (off E.base d) 32 := fun d h₀ h₁ h₂ => by
    rw [m₃, ws _ h₀ (by simp only [fUsed, sState, hdr]; omega) h₂, ws _ h₀ (by simp only [fSeed, sState, hdr]; omega) h₁,
      mem₂]
  have v' := v.atSeed hcq
  have hS : t₃.mem.readW (off E.base fSeed) 32 =
      ((E.atSeed c).seeds + BitVec.ofNat 64 (0 * (E.atSeed c).qLen)).setWidth 32 := by
    rw [m₃, ws _ (by simp only [fSeed, sState, hdr]; omega) (by simp only [fUsed, sState, hdr]; omega)
      (by simp only [fSeed, fUsed, hdr]; omega), Mem.readW_writeW_self32, Nat.zero_mul, BitVec.add_zero]
    rfl
  have hU : t₃.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 (c + E.qLen) := by
    rw [m₃, Mem.readW_writeW_self32]
  have st₃ : t₃.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
    rw [w₃ fStatus (by simp only [fStatus, sState, hdr]; omega) (.inr (by simp only [fSeed, fStatus, hdr]; omega))
      (.inr (by simp only [fUsed, fStatus, hdr]; omega)), L.status]
  refine WP.seq (WP.mono (attempt_ok G v' hp hq (K₃.base.toSeed c) (k := 0)
    (by simp only [Env.atSeed]; omega) hS hU hcq st₃) fun t₄ ⟨AK, AR⟩ => ?_)
  have eR : refillAttempt g.pLen g.qLen (chunk (E.atSeed c) 0) ((E.atSeed c).witT.drop (c + E.qLen)) = sR E c := by
    simp only [chunk, Env.seedT, Env.atSeed, sR, hp, hq, Nat.zero_mul, List.drop_zero, List.take_take, Nat.min_self]
  rw [eR] at AR
  have K₄ : SKeep E g s t₄ := ⟨AK.base.ofSeed, K₃.chg.trans ((AK.chg : E.Chg _ _ _).widen fun o ho =>
    ⟨o, List.mem_append_left _ ho, Nat.le_refl _, Nat.le_refl _⟩), by rw [AK.rd, K₃.rd], by rw [AK.wr, K₃.wr],
    by rw [AK.syms, K₃.syms]⟩
  have left₄ : t₄.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 (j + 1) := by
    rw [show t₄.mem.readW (off E.base fSeedLeft) 32 = t₃.mem.readW (off E.base fSeedLeft) 32 from
      AK.word G v' hp (by simp only [fSeedLeft]; omega) (by simp only [fSeedLeft, fUsed, hdr]; omega),
      w₃ fSeedLeft (by simp only [fSeedLeft, sState, hdr]; omega) (.inr (by simp only [fSeed, fSeedLeft, hdr]; omega))
        (.inl (by simp only [fUsed, fSeedLeft, hdr]; omega)), L.left]
  have cur₄ : t₄.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 c := by
    rw [show t₄.mem.readW (off E.base fC) 32 = t₃.mem.readW (off E.base fC) 32 from AK.cur G v' hp,
      w₃ fC (by simp only [fC, sState, hdr]; omega) (.inr (by simp only [fSeed, fC, hdr]; omega))
        (.inr (by simp only [fUsed, fC, hdr]; omega)), L.cur]
  have hRc : (E.witT.drop c).take (Spec.Dsa.generationQLen E.pLen) = (E.witT.drop c).take E.qLen := by rw [qE]
  have hcq' : c + Spec.Dsa.generationQLen E.pLen ≤ E.witT.length := by rw [hl, ← qE]; exact hcq
  have sOutE : ∀ x, sR E c = x → sOut E (j + 1) c = match x with
      | some (none, rest) => sOut E j (E.witLen - rest.length)
      | some (some a, rest) => .found a (E.witLen - rest.length)
      | none => .ranOut (j + 1) c := fun x hx => by
    simp only [sOut, short, ↓reduceIte, hx]
  rcases hR : sR E c with _ | ⟨_ | a, rest⟩ <;> rw [hR] at AR
  · -- `rand` ran out inside the seed.
    have hS' : sStep E (j + 1) c = none := by simp [sStep, short, hR]
    have st₄ : t₄.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 2 := AR
    refine WP.seq (cmpF_end K₄.base.scr (o := fStatus) (v := 0) (w := 2) (by simp only [fStatus, hdr]; omega) st₄
      (by decide) (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => WP.block_nil ?_)
    refine cmpF_end K₅.base.scr (o := fStatus) (v := 0) (w := 2) (by simp only [fStatus, hdr]; omega)
      (by rw [m₅]; exact st₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_
    refine ⟨by rw [show t₆.zf = _ from z₆, hS']; rfl, fun _ => ⟨K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆
      wr₆ sy₆, ?_, ?_⟩, fun _ _ h => by rw [hS'] at h; cases h⟩
    · rw [sOutE _ hR]
      exact ⟨by rw [m₆, m₅]; exact st₄, by rw [m₆, m₅]; exact cur₄, by rw [m₆, m₅]; exact left₄, L.hc, L.hj⟩
    · rw [sOutE _ hR, cRes, ← L.spec, search_attemptNone hpL hcq' (by rw [hRc, ← qE]; exact hR), hl]
  · -- Rejected: the next seed.
    obtain ⟨st₄, u, hu, fu₄, du⟩ := AR
    replace st₄ : t₄.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := st₄
    replace fu₄ : t₄.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u := fu₄
    have uc : E.witLen - rest.length = u := by rw [← du]; exact cursor_of hl hu
    have hS' : sStep E (j + 1) c = some (j, u) := by simp [sStep, short, hR, uc]
    refine WP.seq (cmpF_end K₄.base.scr (o := fStatus) (v := 0) (w := 0) (by simp only [fStatus, hdr]; omega) st₄
      (by decide) (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun _ => WP.mono (rejected_ok v K₅.base (u := u) (j := j) (by rw [m₅]; exact fu₄)
      (by rw [m₅]; exact left₄) j1) fun t₆ ⟨m₆, g₆, rd₆, wr₆, sy₆⟩ => ?_) (fun h => by simp at h)
    have C₆ : E.Chg [(fC, 4), (fSeedLeft, 4)] t₅.mem t₆.mem := by
      rw [m₆]
      exact ((Env.Chg.refl _ _).store (d := fC) (n := 4) (by simp) (by decide) _).store (d := fSeedLeft)
        (n := 4) (by simp) (by decide) _
    have K₆ : SKeep E g s t₆ := K₅.chgs G v hp (fun o ho => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp [sRanges]) C₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆ wr₆ sy₆
    have st₆ : t₆.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0 := by
      rw [m₆, ws _ (by simp only [fStatus, sState, hdr]; omega) (by simp only [fSeedLeft, sState, hdr]; omega)
        (by simp only [fSeedLeft, fStatus, hdr]; omega), ws _ (by simp only [fStatus, sState, hdr]; omega)
        (by simp only [fC, sState, hdr]; omega) (by simp only [fC, fStatus, hdr]; omega), m₅, st₄]
    refine cmpF_end K₆.base.scr (o := fStatus) (v := 0) (w := 0) (by simp only [fStatus, hdr]; omega) st₆
      (by decide) (by decide) fun t₇ g₇ m₇ rd₇ wr₇ sy₇ z₇ => ?_
    refine ⟨by rw [show t₇.zf = _ from z₇, hS']; rfl, (fun h => by rw [hS'] at h; cases h), fun j' c' h => ?_⟩
    rw [hS'] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨by omega, K₆.mem m₇ (g₇ _ (by decide)) (g₇ _ (by decide)) rd₇ wr₇ sy₇, ?_, ?_, by rw [m₇]; exact st₆, hu,
      by have := L.hj; omega, ?_, ?_⟩
    · rw [m₇, m₆, Mem.readW_writeW_self32]
    · rw [m₇, m₆, ws _ (by simp only [fC, sState, hdr]; omega) (by simp only [fSeedLeft, sState, hdr]; omega)
        (by simp only [fSeedLeft, fC, hdr]; omega), Mem.readW_writeW_self32]
    · have du' : E.witT.drop u = rest := du
      rw [← L.spec, search_rejected (u := u) hpL hcq' (by omega) (by rw [hRc, ← qE, du']; exact hR)]
    · rw [← L.out, sOutE _ hR]
      dsimp only
      rw [uc]
  · -- Parameters.
    obtain ⟨st₄, pk₄, u, hu, fu₄, du⟩ := AR
    replace st₄ : t₄.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 1 := st₄
    replace fu₄ : t₄.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 u := fu₄
    replace pk₄ : Spec.Rsa.bytesAt t₄.mem (off E.base sPk) (2 * g.pLen + g.qLen) =
      Spec.Dsa.encodeParams g.pLen g.qLen a := pk₄
    have uc : E.witLen - rest.length = u := by rw [← du]; exact cursor_of hl hu
    have hS' : sStep E (j + 1) c = none := by simp [sStep, short, hR]
    refine WP.seq (cmpF_end K₄.base.scr (o := fStatus) (v := 0) (w := 1) (by simp only [fStatus, hdr]; omega) st₄
      (by decide) (by decide) fun t₅ g₅ m₅ rd₅ wr₅ sy₅ z₅ => ?_)
    have K₅ := K₄.mem m₅ (g₅ _ (by decide)) (g₅ _ (by decide)) rd₅ wr₅ sy₅
    refine WP.ite _ z₅ (fun h => by simp at h) (fun _ => WP.block_nil ?_)
    refine cmpF_end K₅.base.scr (o := fStatus) (v := 0) (w := 1) (by simp only [fStatus, hdr]; omega)
      (by rw [m₅]; exact st₄) (by decide) (by decide) fun t₆ g₆ m₆ rd₆ wr₆ sy₆ z₆ => ?_
    refine ⟨by rw [show t₆.zf = _ from z₆, hS']; rfl, fun _ => ⟨K₅.mem m₆ (g₆ _ (by decide)) (g₆ _ (by decide)) rd₆
      wr₆ sy₆, ?_, ?_⟩, fun _ _ h => by rw [hS'] at h; cases h⟩
    · rw [sOutE _ hR]
      dsimp only
      rw [uc]
      exact ⟨by rw [m₆, m₅]; exact st₄, by rw [m₆, m₅]; exact pk₄, by rw [m₆, m₅]; exact fu₄, hu⟩
    · have du' : E.witT.drop u = rest := du
      rw [sOutE _ hR]
      dsimp only
      rw [uc, cRes, ← L.spec, search_accepted (u := u) hpL hcq' (by omega) (by rw [hRc, ← qE, du']; exact hR)]

/-- The seeds from the cursor 0, with `state[0]` seeds left. -/
theorem search_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s)
    (hL : s.mem.readW (off E.base fSeedLeft) 32 = BitVec.ofNat 32 E.k0)
    (hC : s.mem.readW (off E.base fC) 32 = BitVec.ofNat 32 0)
    (hst : s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 0) :
    WP isa g.search s fun t => SKeep E g s t ∧ SRes E g t.mem (sOut E E.k0 0) ∧
      cRes E (sOut E E.k0 0) = Spec.Dsa.parameterSearch E.pLen E.k0 E.witT := by
  have L₀ : SLoop E g s E.k0 0 s := ⟨⟨B, Env.Chg.refl _ _, rfl, rfl, rfl⟩, hL, hC, hst, Nat.zero_le _, v.k0le,
    by simp [Spec.Entropy.Result.consume], rfl⟩
  unfold Geo.search
  refine WP.loop (M := isa) (fun m t => ∃ j c, j < m ∧ SLoop E g s j c t)
    (fun m t ⟨j, c, hm, L⟩ => WP.mono (sBody_ok G v hp hq L) fun t' ⟨z, hn, hs⟩ => ?_) (E.k0 + 1) s
    ⟨E.k0, 0, by omega, L₀⟩
  rcases h : sStep E j c with _ | ⟨j', c'⟩
  · rw [h] at z
    obtain ⟨K, R, e⟩ := hn h
    rw [L.out] at R e
    exact .inl ⟨z, K, R, e⟩
  · rw [h] at z
    obtain ⟨hj, L'⟩ := hs j' c' h
    exact .inr ⟨z, m - 1, by omega, j', c', by omega, L'⟩

end VG.Proof.Dsa.X86.Generation
