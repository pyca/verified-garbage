module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT1
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
public import VerifiedGarbage.Proof.Rsa.AArch64.RdStages
public import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT1
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the first pieces
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- No facts. -/
abbrev XT : Pub → State → Prop := fun _ _ => True

/-- `x15` a mask. -/
def XM (_ : Pub) (s : State) : Prop := ∃ c, s.gpr .x15 = mask c

theorem deMinus_ct : CTW (GC vk XT) (GC Wk XT) deMinus := by
  unfold deMinus oneA
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  refine CTW.cons (by simp) (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  exact CTW.one (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial))

/-! ## Masks and `x`'s top word -/

/-- Register `r` a mask. -/
def MR (r : Reg) (s : State) : Prop := ∃ c, s.gpr r = mask c

theorem MR.keep {r : Reg} {rs : List Reg} {s t : State} (h : MR r s) (k : Keep rs s t) (hr : r ∉ rs) : MR r t := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, (k.gpr r hr).trans hc⟩

/-- The top word of narrow `x` zero. -/
def zX (P : DP) (s : State) : Prop := word s.mem P.B (slot (vk P.k) nXn + 8 * vk P.k) = 0

theorem zX_out {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s) {d n : Nat}
    (o : Outside a.1.B d n s.mem t.mem)
    (hd : slot (vk a.1.k) nXn + 8 * vk a.1.k + 8 ≤ d ∨ d + n ≤ slot (vk a.1.k) nXn + 8 * vk a.1.k)
    (z : zX a.1 s) : zX a.1 t := by
  rcases a with ⟨P, i⟩
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  subst e
  have o' : Outside I.B d n s.mem t.mem := o
  have hd' : slot (vk I.k) nXn + 8 * vk I.k + 8 ≤ d ∨ d + n ≤ slot (vk I.k) nXn + 8 * vk I.k := hd
  have z' : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := z
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega_using [])
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [o'.word hd' (by omega_using [this])]; exact z'

theorem zX_frm {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s)
    (f : Frm a.1.B hdrW s.mem t.mem) (z : zX a.1 s) : zX a.1 t := by
  rcases a with ⟨P, i⟩
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  subst e
  have f' : Frm I.B hdrW s.mem t.mem := f
  have z' : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := z
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega_using [])
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [Frm.hdrW_word f' (by have := slot_ge (vk I.k) nXn; omega_using [this]) (by omega_using [this])]; exact z'

/-! ## The shifts' stages -/

/-- The count in header slot `sl`: `T`, below `bnd`. -/
def XS (sl : Nat) (bnd : DP → Nat) (a : Pub) (s : State) : Prop :=
  ∃ T, word s.mem a.1.B (8 * sl) = BitVec.ofNat 64 T ∧ T < bnd a.1 ∧ T < 2 ^ 64

open VG.Proof.MlKem.AArch64 (eval_zero eval_nonzero)
open VG.Proof.Bignum.ShiftStages (tz)

/-- Registers `rs` at `f a`, after a block: what the rest of a piece's taint check starts from. -/
theorem rel_pin {Φ Ψ : Pub → State → Prop} {l : List Instr} {rest : Prog isa} (rs : List Reg)
    (f : Pub → Reg → BitVec 64) (h0 : Pins Φ [.x0]) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block l) s fun t => Ψ a t ∧ ∀ r ∈ rs, t.gpr r = f a r)
    (h2 : RelCT isa (Two fun a t => Ψ a t ∧ ∀ r ∈ rs, t.gpr r = f a r) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq (.block l) rest) fun _ _ => True :=
  RelCT.seq (two_post (two_taint [.x0] h0 h1) hw) h2

theorem pins_of {Ψ : Pub → State → Prop} {rs : List Reg} {f : Pub → Reg → BitVec 64} :
    Pins (fun a t => Ψ a t ∧ ∀ r ∈ rs, t.gpr r = f a r) rs :=
  fun _ _ _ h₁ h₂ r hr => (h₁.2 r hr).trans (h₂.2 r hr).symm

/-- The pins after a word stage's guard: `x3 = ⌊(N - 1) / 2^k⌋`. -/
def fG (wide : Bool) (k : Nat) (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else BitVec.ofNat 64 ((nw a.1.k wide - 1) / 2 ^ k)

/-- The pins of a word stage's moves. -/
def fW (wide up : Bool) (j k : Nat) (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x13 then BitVec.ofNat 64 (nw a.1.k wide - 2 ^ k)
  else if r = .x16 then (if up then off a.1.B (slot (nw a.1.k wide) j + 8 * nw a.1.k wide - 8)
    else off a.1.B (slot (nw a.1.k wide) j))
  else if up then off a.1.B (slot (nw a.1.k wide) j + 8 * nw a.1.k wide - 8 - 8 * 2 ^ k)
  else off a.1.B (slot (nw a.1.k wide) j + 8 * 2 ^ k)

theorem pins_GC' {w : Nat → Nat} {X : Pub → State → Prop} {Φ : Pub → State → Prop}
    (h : ∀ a s, Φ a s → GC w X a s) : Pins Φ [.x0] := fun a s₁ s₂ h₁ h₂ => pins_GC a s₁ s₂ (h _ _ h₁) (h _ _ h₂)

/-- A word stage's guard block. -/
abbrev wGuard (wide : Bool) (k : Nat) : List Instr :=
  setNar ++ ctxOf wide ++ [.subImm .x .x3 .x12 1, .lsr .x .x3 .x3 k]

/-- A word stage's guard: its taint check, and the pins after it. -/
theorem wGuard_rel {w : Nat → Nat} {sl : Nat} {bnd : DP → Nat} {Φ : Pub → State → Prop}
    (hΦ : ∀ a s, Φ a s → GC w (XS sl bnd) a s) (wide : Bool) (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride)
    {k : Nat} (hk : k < 9) {rest : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block (wGuard wide k)) hc).isSome = true)
    (h2 : RelCT isa (Two fun a t => GC (fun k => nw k wide) (XS sl bnd) a t ∧ ∀ r ∈ [Reg.x0, .x3],
      t.gpr r = fG wide k a r) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq (.block (wGuard wide k)) rest) fun _ _ => True := by
  refine rel_pin (Ψ := GC (fun k => nw k wide) (XS sl bnd)) [.x0, .x3] (fG wide k) (pins_GC' hΦ) h1
    (fun ⟨P, i⟩ s h => (hΦ _ s h).elim fun I m₀ c e g L ⟨T, hT, hTb, hT'⟩ => ?_) h2
  subst e
  have hk1 := L.1.k1
  have hk2 := L.1.k2
  unfold wGuard
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (g.setNar_ok L.1) fun t₀ ⟨g₀, f₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ctx_ok g₀ L.1 wide (fun _ => rfl) rfl) fun t₁ ⟨⟨g₁, f₁, h12, _⟩, k₁⟩ => ?_
  refine WP.mono (guardT_ok (k := k) h12 (by cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [])
    (by cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]) (by omega_using [hk])) fun t₂ ⟨⟨h3, m₂⟩, k₂⟩ => ?_
  refine ⟨⟨I, m₀, c, rfl, g₁.same m₂ k₂ (by decide), L, T, ?_, hTb, hT'⟩, fun r hr => ?_⟩
  · show word t₂.mem I.B (8 * sl) = _
    rw [m₂, hdrW_word (f₀.trans f₁) hsl hsl' hslS]; exact hT
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [k₂.get .x0, k₁.get .x0, k₀.get .x0, g.ws.x0]; rfl
    · rw [h3]; rfl

/-- A word stage's moves' head, up. -/
abbrev wHeadU (wide : Bool) (j sl : Nat) (words : Bool) (k : Nat) : List Instr :=
  ctxOf wide ++ base j .x8 ++ stageMask sl words k ++
    [.lsl .x .x3 .x12 3, .add .x .x16 .x8 .x3, .subImm .x .x16 .x16 8, .subImm .x .x17 .x16 (8 * 2 ^ k),
      .subImm .x .x13 .x12 (2 ^ k)]

/-- A word stage's moves' head, down. -/
abbrev wHeadD (wide : Bool) (j sl : Nat) (words : Bool) (k : Nat) : List Instr :=
  ctxOf wide ++ base j .x16 ++ stageMask sl words k ++ [.addImm .x .x17 .x16 (8 * 2 ^ k), .subImm .x .x13 .x12 (2 ^ k)]

/-- A word stage's moves after the head. -/
abbrev wRest (up : Bool) (k : Nat) : Prog isa :=
  seqs [countLoop .x13 (wMove up), .block [movi .x13 (2 ^ k)], countLoop .x13 (wClear up), .block setNar]

theorem wstage_eq (j : Nat) (wide up : Bool) (sl : Nat) (words : Bool) (k : Nat) :
    wstage j wide up sl words k = .seq (.block (wGuard wide k)) (.ite (.zero .x .x3) (.block setNar)
      (.seq (.block (if up then wHeadU wide j sl words k else wHeadD wide j sl words k)) (wRest up k))) := by
  cases up <;> simp [wstage, seqs, List.append_assoc]

theorem wstage_rel {w : Nat → Nat} {sl : Nat} {bnd : DP → Nat} {Φ : Pub → State → Prop}
    (hΦ : ∀ a s, Φ a s → GC w (XS sl bnd) a s) (wide up : Bool) {j : Nat} (hsl : 16 ≤ sl)
    (hsl' : sl < 32) (hslS : sl ≠ sStride) (words : Bool) {k : Nat} (hk : k < 9)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block (wGuard wide k)) hc₁).isSome = true)
    (h2 : (taint.check (Taint.ofRegs [.x0])
      (.block (if up then wHeadU wide j sl words k else wHeadD wide j sl words k)) hc₂).isSome = true)
    (h3 : (taint.check (Taint.ofRegs [.x0, .x13, .x16, .x17]) (wRest up k) hc₃).isSome = true) :
    RelCT isa (Two Φ) (wstage j wide up sl words k) fun _ _ => True := by
  rw [wstage_eq]
  refine wGuard_rel hΦ wide hsl hsl' hslS hk h1 (two_ite (fun a s₁ s₂ h₁ h₂ => by
    rw [eval_zero, eval_zero, h₁.2 .x3 (by simp), h₂.2 .x3 (by simp)]) ?_ ?_)
  · exact two_taint [.x0] (fun a s₁ s₂ h₁ h₂ => pins_GC a s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)
  refine rel_pin (Ψ := fun _ _ => True) [.x0, .x13, .x16, .x17] (fW wide up j k)
    (fun a s₁ s₂ h₁ h₂ => pins_GC a s₁ s₂ h₁.1.1 h₂.1.1) h2 (fun ⟨P, i⟩ s ⟨⟨h, hp⟩, hz⟩ => h.elim
      fun I m₀ c e g L ⟨T, hT, hTb, hT'⟩ => ?_) (two_taint _ pins_of h3)
  subst e
  have hk1 := L.1.k1
  have hk2 := L.1.k2
  have hN2 : 2 ≤ nw I.k wide := by cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
  have hNl : nw I.k wide < 512 := by
    cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]
  have hd : 2 ^ k < nw I.k wide := by
    have h3 : s.gpr .x3 = BitVec.ofNat 64 ((nw I.k wide - 1) / 2 ^ k) := hp .x3 (by simp)
    rw [eval_zero, h3, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNl]))] at hz
    have := of_decide_eq_false (Option.some.inj hz)
    rw [Nat.div_eq_zero_iff] at this
    omega_using [this]
  have x0 : s.gpr .x0 = I.B := g.ws.x0
  cases up
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (pre_ok g L.1 wide (fun hw => by rw [hw]; rfl) .x16 (.inr rfl) hsl hsl' hslS hT hT' words
      (by omega_using [hk]) rfl) fun t₃ ⟨⟨g₃, f₃, h12₃, h16₃, _, _⟩, k₃⟩ => ?_
    refine WP.mono (tailWD_ok h12₃ h16₃ hd (by omega_using [hNl]) hk) fun t₄ ⟨⟨h17₄, h13₄, _⟩, k₄⟩ => ⟨trivial, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₄.get .x0, k₃.get .x0, x0]; rfl
    · rw [h13₄]; rfl
    · rw [k₄.get .x16, h16₃]; rfl
    · rw [h17₄]; rfl
  · simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (pre_ok g L.1 wide (fun hw => by rw [hw]; rfl) .x8 (.inl rfl) hsl hsl' hslS hT hT' words
      (by omega_using [hk]) rfl) fun t₃ ⟨⟨g₃, f₃, h12₃, h8₃, _, _⟩, k₃⟩ => ?_
    refine WP.mono (tailWU_ok h12₃ h8₃ hd (by omega_using [hNl]) hk) fun t₄ ⟨⟨h16₄, h17₄, h13₄, _⟩, k₄⟩ =>
      ⟨trivial, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₄.get .x0, k₃.get .x0, x0]; rfl
    · rw [h13₄]; rfl
    · rw [h16₄]; rfl
    · rw [h17₄]; rfl

/-- What the stages keep: facts kept by a change to the header and array `j` at the width `N`. -/
def Stable (N : DP → Nat) (j : Nat) (E : Pub → State → Prop) : Prop :=
  ∀ a s t (w : Nat → Nat) (X : Pub → State → Prop), GC w X a s →
    Frm a.1.B (hdrW ++ [(slot (N a.1) j, 8 * N a.1)]) s.mem t.mem → E a s → E a t

/-- A word stage, between `GC`s that keep its count and `E`. -/
theorem wstage_ct {w : Nat → Nat} {sl : Nat} {bnd : DP → Nat} {E : Pub → State → Prop} (wide up : Bool) {j : Nat}
    (hE : Stable (fun P => nw P.k wide) j E) (hj : j < 16)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride) (words : Bool) {k : Nat} (hk : k < 9)
    (hw : ∀ P T, T < bnd P → (if words then T / 64 else T) < nw P.k wide)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block (wGuard wide k)) hc₁).isSome = true)
    (h2 : (taint.check (Taint.ofRegs [.x0])
      (.block (if up then wHeadU wide j sl words k else wHeadD wide j sl words k)) hc₂).isSome = true)
    (h3 : (taint.check (Taint.ofRegs [.x0, .x13, .x16, .x17]) (wRest up k) hc₃).isSome = true) :
    CTW (GC w fun a s => XS sl bnd a s ∧ E a s) (GC vk fun a s => XS sl bnd a s ∧ E a s)
      (wstage j wide up sl words k) :=
  ⟨wstage_rel (fun a s h => h.elim fun I m₀ c e g L x => ⟨I, m₀, c, e, g, L, x.1⟩) wide up hsl hsl' hslS words hk
    h1 h2 h3, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨⟨T, hT, hTb, hT'⟩, he⟩ => by
      subst e
      exact WP.mono (wstage_ok g L.1 wide up hj hsl hsl' hslS hT hT' words hk rfl (hw _ T hTb))
        fun t ⟨g', f, _, _⟩ => ⟨I, m₀, c, rfl, g', L, ⟨T, (stage_word f hsl hsl' hslS).trans hT, hTb, hT'⟩,
          hE _ s t _ _ h f he⟩⟩

/-- The pins of a bit stage's pass. -/
def fB (wide up : Bool) (j : Nat) (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x14 then BitVec.ofNat 64 (nw a.1.k wide)
  else if up then off a.1.B (slot (nw a.1.k wide) j) else off a.1.B (slot (nw a.1.k wide) j + 8 * nw a.1.k wide - 8)

/-- A bit stage's head. -/
abbrev bHead (wide up : Bool) (j sl k : Nat) : List Instr :=
  ctxOf wide ++ base j .x16 ++ stageMask sl false k ++
    (if up then [mov .x14 .x12, movi .x2 0]
      else [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, mov .x14 .x12, movi .x2 0])

/-- A bit stage after its head. -/
abbrev bRest (up : Bool) (k : Nat) : Prog isa := seqs [countLoop .x14 (bWord up k), .block setNar]

theorem bstage_eq (j : Nat) (wide up : Bool) (sl k : Nat) :
    bstage j wide up sl k = .seq (.block (bHead wide up j sl k)) (bRest up k) := by
  cases up <;> simp [bstage, seqs, List.append_assoc]

theorem bstage_ct {sl : Nat} {bnd : DP → Nat} {E : Pub → State → Prop} (wide up : Bool) {j : Nat}
    (hE : Stable (fun P => nw P.k wide) j E) (hj : j < 16)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride) {k : Nat} (hk : k < 6)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block (bHead wide up j sl k)) hc₁).isSome = true)
    (h2 : (taint.check (Taint.ofRegs [.x0, .x14, .x16]) (bRest up k) hc₂).isSome = true) :
    CTW (GC vk fun a s => XS sl bnd a s ∧ E a s) (GC vk fun a s => XS sl bnd a s ∧ E a s) (bstage j wide up sl k) := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨⟨T, hT, hTb, hT'⟩, he⟩ => ?_⟩
  · rw [bstage_eq]
    refine rel_pin (Ψ := fun _ _ => True) [.x0, .x14, .x16] (fB wide up j) pins_GC h1
      (fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L ⟨⟨T, hT, hTb, hT'⟩, _⟩ => ?_) (two_taint _ pins_of h2)
    subst e
    have hk1 := L.1.k1
    have hk2 := L.1.k2
    have hN2 : 2 ≤ nw I.k wide := by
      cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
    have hNl : nw I.k wide < 512 := by
      cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]
    have x0 : s.gpr .x0 = I.B := g.ws.x0
    rw [bHead, WP.block_append_iff]
    refine WP.mono (pre_ok g L.1 wide (fun _ => rfl) .x16 (.inr rfl) hsl hsl' hslS hT hT' false (by omega_using [hk]) rfl)
      fun t₃ ⟨⟨_, _, h12₃, h16₃, _, _⟩, k₃⟩ => ?_
    cases up
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.mono (tailBD_ok h12₃ h16₃ (by omega_using [hN2]) (by omega_using [hNl])) fun t₄ ⟨⟨h16₄, h14₄, _, _⟩, k₄⟩ =>
        ⟨trivial, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [k₄.get .x0, k₃.get .x0, x0]; rfl
      · rw [h14₄]; rfl
      · rw [h16₄]; rfl
    · simp only [↓reduceIte]
      refine WP.mono (tailBU_ok h12₃) fun t₄ ⟨⟨h14₄, _, _⟩, k₄⟩ => ⟨trivial, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [k₄.get .x0, k₃.get .x0, x0]; rfl
      · rw [h14₄]; rfl
      · rw [k₄.get .x16, h16₃]; rfl
  · subst e
    exact WP.mono (bstage_ok g L.1 wide up hj hsl hsl' hslS hT hT' hk rfl)
      fun t ⟨g', f, _, _⟩ => ⟨I, m₀, c, rfl, g', L, ⟨T, (stage_word f hsl hsl' hslS).trans hT, hTb, hT'⟩,
        hE _ s t _ _ h f he⟩

/-- A list of pieces, the first from `Φ` to `Ψ`, the rest keeping `Ψ`. -/
theorem CTW.range {f : Nat → Prog isa} {Φ Ψ : Pub → State → Prop} :
    ∀ {M : Nat}, 1 ≤ M → CTW Φ Ψ (f 0) → (∀ m, 1 ≤ m → m < M → CTW Ψ Ψ (f m)) →
      CTW Φ Ψ (seqs ((List.range M).map f))
  | 0, h, _, _ => absurd h (by decide)
  | 1, _, h0, _ => by simpa using CTW.one h0
  | M + 2, _, h0, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact CTW.app (by simp) (by simp) (CTW.range (M := M + 1) (by omega_using []) h0 fun m h1 h2 => hs m h1 (by omega_using [h2]))
      (CTW.one (hs (M + 1) (by omega_using []) (by omega_using [])))

/-- A shift by the count in slot `sl`. -/
theorem shiftBy_ct {w : Nat → Nat} {sl : Nat} {bnd : DP → Nat} {E : Pub → State → Prop} (wide up : Bool) {j : Nat}
    (hE : Stable (fun P => nw P.k wide) j E) (hj : j < 16)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride)
    (hw : ∀ P T, T < bnd P → T / 64 < nw P.k wide)
    (hG : ∀ k < 9, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (wGuard wide k)) hc).isSome = true)
    (hH : ∀ k < 9, ∃ hc, (taint.check (Taint.ofRegs [.x0])
      (.block (if up then wHeadU wide j sl true k else wHeadD wide j sl true k)) hc).isSome = true)
    (hR : ∀ k < 9, ∃ hc, (taint.check (Taint.ofRegs [.x0, .x13, .x16, .x17]) (wRest up k) hc).isSome = true)
    (hBH : ∀ k < 6, ∃ hc, (taint.check (Taint.ofRegs [.x0]) (.block (bHead wide up j sl k)) hc).isSome = true)
    (hBR : ∀ k < 6, ∃ hc, (taint.check (Taint.ofRegs [.x0, .x14, .x16]) (bRest up k) hc).isSome = true) :
    CTW (GC w fun a s => XS sl bnd a s ∧ E a s) (GC vk fun a s => XS sl bnd a s ∧ E a s)
      (seqs (shiftBy j wide up sl)) := by
  have W : ∀ {w' : Nat → Nat} k, k < 9 → CTW (GC w' fun a s => XS sl bnd a s ∧ E a s)
      (GC vk fun a s => XS sl bnd a s ∧ E a s) (wstage j wide up sl true k) :=
    fun k hk => by
      obtain ⟨_, h1⟩ := hG k hk
      obtain ⟨_, h2⟩ := hH k hk
      obtain ⟨_, h3⟩ := hR k hk
      exact wstage_ct wide up hE hj hsl hsl' hslS true hk (fun P T h => by simpa using hw P T h) h1 h2 h3
  unfold shiftBy
  refine CTW.app (by simp) (by simp) (CTW.range (by decide) (W 0 (by decide)) fun m _ hm => W m hm) ?_
  refine CTW.range (by decide) ?_ fun m _ hm => ?_
  · obtain ⟨_, h1⟩ := hBH 0 (by decide)
    obtain ⟨_, h2⟩ := hBR 0 (by decide)
    exact bstage_ct wide up hE hj hsl hsl' hslS (by decide) h1 h2
  · obtain ⟨_, h1⟩ := hBH m hm
    obtain ⟨_, h2⟩ := hBR m hm
    exact bstage_ct wide up hE hj hsl hsl' hslS hm h1 h2

/-- The taint checks of every stage `k < 9`. -/
macro "taints9" : tactic => `(tactic| (intro k hk; rcases k with _|_|_|_|_|_|_|_|_|k <;>
  first | exact absurd hk (by omega) | exact ⟨_, by taint_decide⟩))

/-- The taint checks of every stage `k < 6`. -/
macro "taints6" : tactic => `(tactic| (intro k hk; rcases k with _|_|_|_|_|_|k <;>
  first | exact absurd hk (by omega) | exact ⟨_, by taint_decide⟩))

/-- A slot of the stages' own, kept by the stages of another slot. -/
theorem stable_XS {sl : Nat} {bnd : DP → Nat} {N : DP → Nat} {j : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32)
    (hslS : sl ≠ sStride) : Stable N j (XS sl bnd) := fun _ _ _ _ _ _ f ⟨T, hT, hb, hT'⟩ =>
  ⟨T, (stage_word f hsl hsl' hslS).trans hT, hb, hT'⟩

/-- `x`'s top word, kept by the stages of the arrays apart from it. -/
theorem stable_zX {N : DP → Nat} {j : Nat} (hsep : ∀ P : DP, 2 ≤ P.k →
    slot (N P) j + 8 * N P ≤ slot (vk P.k) nXn + 8 * vk P.k ∨ slot (vk P.k) nXn + 8 * vk P.k + 8 ≤ slot (N P) j) :
    Stable N j (fun a s => zX a.1 s) := fun ⟨P, i⟩ s t w X h f z => h.elim fun I m₀ c e g L _ => by
  subst e
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega_using [])
  have hk : slot (N (dpub I)) j + 8 * N (dpub I) ≤ slot (vk I.k) nXn + 8 * vk I.k ∨
      slot (vk I.k) nXn + 8 * vk I.k + 8 ≤ slot (N (dpub I)) j := hsep (dpub I) (by have := L.1.k1; show 2 ≤ I.k; omega_using [this])
  have f' : Frm I.B (hdrW ++ [(slot (N (dpub I)) j, 8 * N (dpub I))]) s.mem t.mem := f
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [f'.word_eq (fun r hr => by
    simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h256 := hdr_lt_slot (vk I.k) nXn (i := 31) (by decide)
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact .inr (by simp only [sW]; omega_using [h256])
    · exact .inr (by simp only [sArr]; omega_using [h256])
    · exact .inr (by simp only [sStride, sFn]; omega_using [h256])
    · exact hk.symm) (by omega_using [this])]
  exact z

theorem stable_and {N : DP → Nat} {j : Nat} {E F : Pub → State → Prop} (hE : Stable N j E) (hF : Stable N j F) :
    Stable N j fun a s => E a s ∧ F a s := fun a s t w X g f h => ⟨hE a s t w X g f h.1, hF a s t w X g f h.2⟩

theorem stable_true {N : DP → Nat} {j : Nat} : Stable N j fun _ _ => True := fun _ _ _ _ _ _ _ _ => trivial


/-! ## The halvings -/

theorem tz_zero : tz 0 = 0 := by unfold tz; simp

/-- The pins of `ctzOr`'s scan. -/
def fZ (A Bj : Nat) (a : Pub) (r : Reg) : BitVec 64 :=
  if r = .x0 then a.1.B else if r = .x14 then BitVec.ofNat 64 (vk a.1.k)
  else if r = .x16 then off a.1.B (slot (vk a.1.k) A) else off a.1.B (slot (vk a.1.k) Bj)

/-- `ctzOr`'s head. -/
abbrev czHead (A Bj : Nat) : List Instr :=
  setNar ++ ws ++ base A .x16 ++ base Bj .x17 ++
    [movi .x7 0, .subImm .x .x15 .x7 1, movi .x5 0, movi .x6 0, movi .x8 0, mov .x14 .x12]

theorem ctzOr_ct {w : Nat → Nat} {sl : Nat} (hsl : Own sl) {A Bj : Nat} (hA : A < 16) (hB : Bj < 16)
    {E : Pub → State → Prop}
    (hE : ∀ a s t (w : Nat → Nat) (X : Pub → State → Prop), GC w X a s →
      Frm a.1.B (hdrW ++ [(8 * sl, 8)]) s.mem t.mem → E a s → E a t)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (h1 : (taint.check (Taint.ofRegs [.x0]) (.block (czHead A Bj)) hc₁).isSome = true)
    (h2 : (taint.check (Taint.ofRegs [.x0, .x14, .x16, .x17])
      (.seq (countLoop .x14 ctzScan) (.block [sth .x5 sl])) hc₂).isSome = true) :
    CTW (GC w E) (GC vk fun a s => XS sl (fun P => 64 * vk P.k) a s ∧ E a s) (ctzOr A Bj sl) := by
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => ?_⟩
  · show RelCT isa _ (.seq (.block (czHead A Bj)) (.seq (countLoop .x14 ctzScan) (.block [sth .x5 sl]))) _
    refine rel_pin (Ψ := fun _ _ => True) [.x0, .x14, .x16, .x17] (fZ A Bj) pins_GC h1
      (fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => ?_) (two_taint _ pins_of h2)
    subst e
    rw [czHead, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (g.setNar_ok L.1) fun t₀ ⟨g₀, _, k₀⟩ => ?_
    refine WP.mono (ws_ok g₀.ws.scr g₀.ws.x0 g₀.ws.h256 g₀.ws.hw g₀.ws.hS) fun t₁ ⟨⟨h12, h11, _, _⟩, k₁⟩ => ?_
    have x0₁ : t₁.gpr .x0 = I.B := (k₁.gpr .x0 (by decide)).trans g₀.ws.x0
    refine WP.mono (base_ok A .x16 x0₁ h11) fun t₂ ⟨⟨h16, _, _⟩, k₂⟩ => ?_
    refine WP.mono (base_ok Bj .x17 ((k₂.gpr .x0 (by decide)).trans x0₁) ((k₂.gpr .x11 (by decide)).trans h11))
      fun t₃ ⟨⟨h17, _, _⟩, k₃⟩ => ?_
    have h12₃ : t₃.gpr .x12 = BitVec.ofNat 64 (vk I.k) := by
      rw [k₃.gpr .x12 (by decide), k₂.gpr .x12 (by decide), h12]
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x14, .x15] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (vk I.k))
      (by brun [h12₃, mov, movi]) (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨h14, k₄⟩ =>
        ⟨trivial, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₄.get .x0, k₃.get .x0, k₂.get .x0, x0₁]; rfl
    · rw [h14]; rfl
    · rw [k₄.get .x16, k₃.get .x16, h16]; rfl
    · rw [k₄.get .x17, h17]; rfl
  · subst e
    have hk1 := L.1.k1
    refine WP.mono (ctzOr_ok g L.1 hA hB hsl) fun t ⟨g', f, hw, _⟩ => ⟨I, m₀, c, rfl, g', L, ⟨_, hw, ?_, ?_⟩,
      hE _ s t _ _ h f x⟩
    · generalize hV : wv s.mem I.B (slot (vk I.k) A) (vk I.k) ||| wv s.mem I.B (slot (vk I.k) Bj) (vk I.k) = V
      have hVl : V < 2 ^ (64 * vk I.k) := by rw [← hV]; exact Nat.or_lt_two_pow (wv_lt _ _ _ _) (wv_lt _ _ _ _)
      show tz V < 64 * vk I.k
      rcases Nat.eq_zero_or_pos V with h0 | h0
      · rw [h0, tz_zero]; have : 1 ≤ vk I.k := by simp only [vk]; omega_using []
        omega_using [this]
      · exact VG.Proof.Bignum.ShiftStages.tz_lt h0 hVl
    · generalize hV : wv s.mem I.B (slot (vk I.k) A) (vk I.k) ||| wv s.mem I.B (slot (vk I.k) Bj) (vk I.k) = V
      have hVl : V < 2 ^ (64 * vk I.k) := by rw [← hV]; exact Nat.or_lt_two_pow (wv_lt _ _ _ _) (wv_lt _ _ _ _)
      have : tz V < 64 * vk I.k + 1 := by
        rcases Nat.eq_zero_or_pos V with h0 | h0
        · rw [h0, tz_zero]; omega_using []
        · have := VG.Proof.Bignum.ShiftStages.tz_lt h0 hVl; omega_using [this]
      have := L.1.k2
      have : vk I.k < 200 := by simp only [vk]; omega_using [this]
      omega_arith

/-- A store to a header slot keeps `x`'s top word. -/
theorem zX_hdr {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s) {sl : Nat}
    (hsl : sl < 32) (f : Frm a.1.B (hdrW ++ [(8 * sl, 8)]) s.mem t.mem) (z : zX a.1 s) : zX a.1 t := by
  rcases a with ⟨P, i⟩
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  subst e
  have f' : Frm I.B (hdrW ++ [(8 * sl, 8)]) s.mem t.mem := f
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega_using [])
  have h256 := hdr_lt_slot (vk I.k) nXn (i := 31) (by decide)
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [f'.word_eq (fun r hr => by
    simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact .inr (by simp only [sW]; omega_using [h256])
    · exact .inr (by simp only [sArr]; omega_using [h256])
    · exact .inr (by simp only [sStride, sFn]; omega_using [h256])
    · exact .inr (by dsimp only; omega_using [hsl, h256])) (by omega_using [this])]
  exact z

theorem twos_eq : twos = seqs ((([.block setNar] : List (Prog isa)) ++ oneA nOne ++ [zeroA nU, subA nU Public.aN nOne, zeroA nXn,
    copyA nXn (2 * wX), ctzOr nU nXn sT1, ctzOr nU nU sT2]) ++ (shiftBy nU false false sT2 ++
    (shiftBy nXn false false sT1 ++ (shiftBy wX true true sT1 ++ ([.block setNar] : List (Prog isa)))))) := by
  simp only [twos, List.append_assoc]

theorem GC.map {w : Nat → Nat} {X X' : Pub → State → Prop} {a : Pub} {s : State} (h : GC w X a s)
    (hX : X a s → X' a s) : GC w X' a s :=
  h.elim fun I m₀ c e g L x => ⟨I, m₀, c, e, g, L, hX x⟩

/-- The halvings' counts' bound. -/
abbrev bT (P : DP) : Nat := 64 * vk P.k

theorem twos_ct : CTW (GC Wk XT) (GC vk fun a s => zX a.1 s) twos := by
  rw [twos_eq]
  refine CTW.app (Ψ := GC vk fun a s => XS sT2 bT a s ∧ (XS sT1 bT a s ∧ zX a.1 s)) (by simp) (by simp [shiftBy])
    ?_ ?_
  · simp only [oneA, List.cons_append, List.nil_append]
    refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intros; trivial) (by taint_decide)) ?_
    refine CTW.cons (by simp) (zeroA_w (Y := fun a s => zX a.1 s) (by decide) (fun ⟨P, i⟩ s t h _ _ z => by
      obtain ⟨I, m₀, c, e, g, L, -⟩ := h
      subst e
      exact (wv_eq_zero_iff _ _ _ _).mp (show wv t.mem I.B (slot (vk I.k) nXn) (vk I.k + 2) = 0 from z) (vk I.k)
        (by omega_using [])) (by taint_decide)) ?_
    refine CTW.cons (by simp) (copyA_w (Y := fun a s => zX a.1 s) (by decide) (by decide) (by decide)
      (fun _ _ _ h o _ => zX_out h o (.inr (by omega_using [])) h.x) (by taint_decide)) ?_
    refine CTW.cons (by simp) (ctzOr_ct (sl := sT1) ⟨by decide, by decide, by decide⟩ (by decide) (by decide)
      (fun _ _ _ _ _ h f z => zX_hdr h (by decide) f z) (by taint_decide) (by taint_decide)) ?_
    exact CTW.one (ctzOr_ct (sl := sT2) ⟨by decide, by decide, by decide⟩ (by decide) (by decide)
      (fun _ _ _ _ _ h f x => ⟨let ⟨T, hT, hb, hT'⟩ := x.1; ⟨T, (own_word f ⟨by decide, by decide, by decide⟩
        (by decide)).trans hT, hb, hT'⟩, zX_hdr h (by decide) f x.2⟩) (by taint_decide) (by taint_decide))
  refine CTW.app (by simp [shiftBy]) (by simp [shiftBy]) (shiftBy_ct (sl := sT2) (bnd := bT) false false (j := nU)
    (E := fun a s => XS sT1 bT a s ∧ zX a.1 s) (stable_and (stable_XS (by decide) (by decide) (by decide))
      (stable_zX fun P _ => .inl (by simp only [nw, slot, hdrBytes, nU, nXn, Bool.false_eq_true, ↓reduceIte]; omega_using [])))
    (by decide) (by decide) (by decide) (by decide) (fun P T h => by simp only [bT] at h; simp only [nw, Bool.false_eq_true, ↓reduceIte]; omega_using [h])
    (by taints9) (by taints9) (by taints9) (by taints6) (by taints6)) ?_
  refine CTW.app (by simp [shiftBy]) (by simp) ((shiftBy_ct (sl := sT1) (bnd := bT) false false (j := nXn)
    (E := fun a s => zX a.1 s) (stable_zX fun P _ => .inl (by simp only [nw, Bool.false_eq_true, ↓reduceIte]; omega_using []))
    (by decide) (by decide) (by decide) (by decide) (fun P T h => by simp only [bT] at h; simp only [nw, Bool.false_eq_true, ↓reduceIte]; omega_using [h])
    (by taints9) (by taints9) (by taints9) (by taints6) (by taints6)).mono (fun a s h => h.map fun x => x.2)
    fun _ _ h => h) ?_
  refine CTW.app (by simp [shiftBy]) (by simp) (shiftBy_ct (sl := sT1) (bnd := bT) true true (j := wX)
    (E := fun a s => zX a.1 s) (stable_zX fun P _ => .inr (by simp only [nw, Wk, slot, hdrBytes, wX, nXn, ↓reduceIte]; omega_using []))
    (by decide) (by decide) (by decide) (by decide) (fun P T h => by simp only [bT] at h; simp only [nw, Wk, ↓reduceIte]; omega_using [h])
    (by taints9) (by taints9) (by taints9) (by taints6) (by taints6)) ?_
  exact CTW.one (setNar_w (Y := fun a s => zX a.1 s) fun _ _ _ h f _ => zX_frm h f h.x.2)

end VG.Proof.Rsa.AArch64.Rd
