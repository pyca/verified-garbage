import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Ctx
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-!
# An RSA key from its primes on AArch64: constant time, the relation

Two runs agree on the public data (`KP`: the working space, the pointers
and lengths, `e` and the status). Between the pieces of the code, each run
is in a state `KS` describes for its own inputs, with the facts `F` the next
piece needs (`KG F`). The taint analysis tracks registers only, and every
load gives a secret: a piece reloads `w` and the stride from the header
(`ws`) and computes the arrays' bases from them, so `x0`, `x12` and `x11`
are pinned after `ws` by correctness (`kg_ws`, from `ws_ct`), and the rest
of the piece is checked by the taint analysis.

Two ways to go from one piece to the next: `kg_ws` and `kg_ct` give the
facts after a piece from its correctness (as x86-64's `CTBase.lean`, with
`Stab` for the facts that survive it); `kg_ws0` checks a piece with no
postcondition, and `kg_then` and `kg_split` take the facts in between from
the correctness of the first part and the facts after both from that of
the whole, for code whose parts have no correctness proof of their own.
`kg_blk_ws0` checks a block that reloads `w` and the stride in its middle,
and `kg_ite` a branch on a register both runs agree on (`kg_zero_eq`,
`kg_nonzero_eq`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The public data -/

/-- The public part of the inputs: the working space, the primes' length,
the outputs, `e`'s pointer, length and octets, and the writable regions. -/
structure KQ where
  B : Addr
  Z : Nat
  pl : Nat
  pN : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pE : Addr
  el : Nat
  eb : List Byte
  Wr : List Region

/-- The public data: the public inputs and the status. -/
structure KP where
  q : KQ
  st : Nat

/-- The words of `n`, from the public data (`KIn.W`). -/
abbrev KQ.W (q : KQ) : Nat := 2 * q.pl / 8

/-- The public part of the inputs. -/
def KIn.pub (I : KIn) : KQ := ⟨I.B, I.Z, I.pl, I.pN, I.pD, I.pP, I.pQ, I.pDp, I.pDq, I.pQi, I.pE, I.el, I.eb, I.Wr⟩

/-- The status of the inputs (`keyLeak`'s last entry). -/
abbrev KIn.st (I : KIn) : Nat := Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb)

theorem KIn.pub_W {I : KIn} {q : KQ} (h : I.pub = q) : I.W = q.W := by rw [← h]; rfl

theorem KIn.pub_B {I : KIn} {q : KQ} (h : I.pub = q) : I.B = q.B := by rw [← h]; rfl

theorem KIn.pub_eb {I : KIn} {q : KQ} (h : I.pub = q) : I.eb = q.eb := by rw [← h]; rfl

/-- `e`'s value is public. -/
theorem KIn.pub_E {I : KIn} {q : KQ} (h : I.pub = q) : I.E = Spec.Rsa.os2ip q.eb := by rw [← h]; rfl

/-! ## The relation between the pieces -/

/-- Between the pieces: the state of some inputs with the public data `p`,
with the facts `F`. -/
def KG (F : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I s₀, I.pub = p.q ∧ I.st = p.st ∧ KS I s₀ s ∧ KLens I ∧ KOuts I ∧ F I s

/-- No facts. -/
abbrev NF : KIn → State → Prop := fun _ _ => True

theorem KG.ws {F : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) : Ws s p.q.B p.q.Z p.q.W := by
  obtain ⟨I, s₀, he, -, hk, -⟩ := h
  rw [← he]; exact hk.ws

theorem pins_kg (F : KIn → State → Prop) : Pins (KG F) [.x0] :=
  pins_ws (fun p : KP => p.q.B) (fun p => p.q.Z) (fun p => p.q.W) fun _ _ h => h.ws

/-- `KG` with other facts. -/
theorem KG.imp {F G : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) (hFG : ∀ I, F I s → G I s) :
    KG G p s := by
  obtain ⟨I, s₀, he, hst, hk, L, O, hF⟩ := h
  exact ⟨I, s₀, he, hst, hk, L, O, hFG I hF⟩

/-- `KG` with other facts, which may use `KS` and the lengths. -/
theorem KG.imp' {F G : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s)
    (hFG : ∀ I s₀, KS I s₀ s → KLens I → F I s → G I s) : KG G p s := by
  obtain ⟨I, s₀, he, hst, hk, L, O, hF⟩ := h
  exact ⟨I, s₀, he, hst, hk, L, O, hFG I s₀ hk L hF⟩

/-- Two runs related with some facts, related with others. -/
theorem two_kg {F G : KIn → State → Prop} (hFG : ∀ I s, F I s → G I s) {s₁ s₂ : State}
    (h : Two (KG F) s₁ s₂) : Two (KG G) s₁ s₂ :=
  two_mono (fun _ _ h => h.imp fun I => hFG I _) h

/-- A piece from `KG F` to `KG G`, by what correctness gives from `KS`. -/
theorem kg_post {F G : KIn → State → Prop} {c : Prog isa}
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c s fun t => KS I s₀ t ∧ G I t) :
    ∀ p s, KG F p s → WP isa c s (KG G p) := fun _ _ ⟨I, s₀, he, hst, hk, L, O, hF⟩ =>
  WP.mono (hw I s₀ _ hk L hF) fun _ ⟨hk', hG⟩ => ⟨I, s₀, he, hst, hk', L, O, hG⟩

/-- A piece that leaks the same, with what its correctness gives after it. -/
theorem kg_ct {F G : KIn → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (KG F)) c fun _ _ => True)
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c s fun t => KS I s₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) c (Two (KG G)) :=
  two_post hct (kg_post hw)

/-- Two pieces that leak the same, the facts between them from the first's
correctness. -/
theorem kg_then {F G : KIn → State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Two (KG F)) c₁ fun _ _ => True)
    (hw₁ : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c₁ s fun t => KS I s₀ t ∧ G I t)
    (h₂ : RelCT isa (Two (KG G)) c₂ fun _ _ => True) :
    RelCT isa (Two (KG F)) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (kg_ct h₁ hw₁) h₂

/-- `kg_then`, with the facts after both from the correctness of the whole. -/
theorem kg_split {F G H : KIn → State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (Two (KG F)) c₁ fun _ _ => True)
    (hw₁ : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c₁ s fun t => KS I s₀ t ∧ G I t)
    (h₂ : RelCT isa (Two (KG G)) c₂ fun _ _ => True)
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa (.seq c₁ c₂) s fun t => KS I s₀ t ∧ H I t) :
    RelCT isa (Two (KG F)) (.seq c₁ c₂) (Two (KG H)) :=
  kg_ct (kg_then h₁ hw₁ h₂) hw

/-- `kg_then` for a sequence in two parts. -/
theorem kg_app0 {F G : KIn → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h₁ : RelCT isa (Two (KG F)) (seqs a) fun _ _ => True)
    (hw₁ : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa (seqs a) s fun t => KS I s₀ t ∧ G I t)
    (h₂ : RelCT isa (Two (KG G)) (seqs b) fun _ _ => True) :
    RelCT isa (Two (KG F)) (seqs (a ++ b)) fun _ _ => True :=
  RelCT.seqs_append ha hb (kg_then h₁ hw₁ h₂)

/-- No postcondition. -/
theorem RelCT.drop {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P c fun _ _ => True :=
  h.mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## Pinning `ws`' registers -/

/-- `pin_seq`, with no postcondition. -/
theorem kpin_seq0 {α : Type} {Φ : α → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg)
    (f : α → Reg → BitVec 64) (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs) c₂ hc₂).isSome = true) :
    RelCT isa (Two Φ) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (two_post (Ψ := fun a t => ∀ r ∈ rs, t.gpr r = f a r) h₁ hp)
    (two_taint rs (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht₂)

/-- `ws` and then code checked by the taint analysis from `x0`, `x12` and
`x11`, with no postcondition. -/
theorem kg_ws0 {F : KIn → State → Prop} {rest : List Instr} {body : Prog isa}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (.block (ws ++ rest)) body) fun _ _ => True :=
  RelCT.block_seq (kpin_seq0 [.x0, .x12, .x11] (fun p : KP => wsVal p.q.B p.q.W)
    (two_taint [.x0] (pins_kg F) (by taint_decide)) (fun _ _ h => ws_pin h.ws) ht)

/-- `kg_ws0` for a block. -/
theorem kg_wsb0 {F : KIn → State → Prop} {rest : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true) :
    RelCT isa (Two (KG F)) (.block (ws ++ rest)) fun _ _ => True :=
  RelCT.block_append (kpin_seq0 [.x0, .x12, .x11] (fun p : KP => wsVal p.q.B p.q.W)
    (two_taint [.x0] (pins_kg F) (by taint_decide)) (fun _ _ h => ws_pin h.ws) ht)

/-- A block that starts with code checked from `x0` (which leaves `KS`, with
the facts `G`, by its correctness) and goes on from `ws`: the taint analysis
cannot see `w` and the stride reloaded in the middle of a block. -/
theorem kg_blk_ws0 {F G : KIn → State → Prop} {l₁ rest : List Instr} {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block l₁) hc₁).isSome = true)
    (hw₁ : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa (.block l₁) s fun t => KS I s₀ t ∧ G I t)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.block (l₁ ++ (ws ++ rest))) fun _ _ => True :=
  RelCT.block_append (kg_then (two_taint [.x0] (pins_kg F) ht₁) hw₁ (kg_wsb0 ht₂))

/-- `kg_blk_ws0`, for a block followed by code. -/
theorem kg_blk_ws_seq0 {F G : KIn → State → Prop} {l₁ rest : List Instr} {body : Prog isa}
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block l₁) hc₁).isSome = true)
    (hw₁ : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa (.block l₁) s fun t => KS I s₀ t ∧ G I t)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (.block (l₁ ++ (ws ++ rest))) body) fun _ _ => True :=
  RelCT.block_seq (kg_then (two_taint [.x0] (pins_kg F) ht₁) hw₁ (kg_ws0 ht₂))

/-- `ws` and then code the taint analysis checks from `x0`, `x12` and `x11`,
with what correctness gives after it. -/
theorem kg_ws {F G : KIn → State → Prop} {rest : List Instr} {body : Prog isa}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s →
      WP isa (.seq (.block (ws ++ rest)) body) s fun t => KS I s₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.seq (.block (ws ++ rest)) body) (Two (KG G)) :=
  kg_ct (kg_ws0 ht) hw

/-- `kg_ws` for a block. -/
theorem kg_wsb {F G : KIn → State → Prop} {rest : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true)
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa (.block (ws ++ rest)) s fun t => KS I s₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block (ws ++ rest)) (Two (KG G)) :=
  kg_ct (kg_wsb0 ht) hw

/-- Code the taint analysis checks from `x0` alone. -/
theorem kg_x0 {F G : KIn → State → Prop} {c : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) c hc).isSome = true)
    (hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c s fun t => KS I s₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) c (Two (KG G)) :=
  two_piece [.x0] (pins_kg F) ht (kg_post hw)

/-- A sequence in two parts, each constant time. -/
theorem rs_app {P R Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h₁ : RelCT isa P (seqs a) R) (h₂ : RelCT isa R (seqs b) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  RelCT.seqs_append ha hb (RelCT.seq h₁ h₂)

/-! ## Branches on public registers -/

/-- A register both runs agree on: a function of the public data. -/
theorem KG.gpr_eq {F : KIn → State → Prop} {r : Reg} {g : KP → BitVec 64}
    (hg : ∀ I t, F I t → t.gpr r = g ⟨I.pub, I.st⟩) {p : KP} {s₁ s₂ : State} (h₁ : KG F p s₁) (h₂ : KG F p s₂) :
    s₁.gpr r = s₂.gpr r := by
  obtain ⟨I₁, _, e₁, t₁, _, _, _, f₁⟩ := h₁
  obtain ⟨I₂, _, e₂, t₂, _, _, _, f₂⟩ := h₂
  rw [hg _ _ f₁, hg _ _ f₂, e₁, e₂, t₁, t₂]

theorem kg_zero_eq {F : KIn → State → Prop} {r : Reg} {g : KP → BitVec 64}
    (hg : ∀ I t, F I t → t.gpr r = g ⟨I.pub, I.st⟩) :
    ∀ p s₁ s₂, KG F p s₁ → KG F p s₂ → isa.eval (.zero .x r) s₁ = isa.eval (.zero .x r) s₂ := fun _ _ _ h₁ h₂ => by
  rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, KG.gpr_eq hg h₁ h₂]

theorem kg_nonzero_eq {F : KIn → State → Prop} {r : Reg} {g : KP → BitVec 64}
    (hg : ∀ I t, F I t → t.gpr r = g ⟨I.pub, I.st⟩) :
    ∀ p s₁ s₂, KG F p s₁ → KG F p s₂ → isa.eval (.nonzero .x r) s₁ = isa.eval (.nonzero .x r) s₂ :=
  fun _ _ _ h₁ h₂ => by
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.eval_nonzero, KG.gpr_eq hg h₁ h₂]

/-- A branch whose condition both runs agree on (`kg_zero_eq`,
`kg_nonzero_eq`), each side from `KG` with the condition's value. -/
theorem kg_ite {F : KIn → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ p s₁ s₂, KG F p s₁ → KG F p s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two (KG fun I t => F I t ∧ isa.eval cond t = some true)) th Q)
    (he : RelCT isa (Two (KG fun I t => F I t ∧ isa.eval cond t = some false)) el Q) :
    RelCT isa (Two (KG F)) (.ite cond th el) Q :=
  two_ite hc (ht.mono (fun _ _ h => two_mono (fun _ _ ⟨h, hb⟩ => h.imp fun _ f => ⟨f, hb⟩) h) fun _ _ h => h)
    (he.mono (fun _ _ h => two_mono (fun _ _ ⟨h, hb⟩ => h.imp fun _ f => ⟨f, hb⟩) h) fun _ _ h => h)

/-! ## Facts that survive a piece -/

/-- Facts that survive a piece which changes the parts `cs` and keeps the
registers outside `rs`. -/
def Stab (F : KIn → State → Prop) (cs : List Rc) (rs : List Reg) : Prop :=
  ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → KF I.B I.W cs s.mem t.mem → Keep rs s t → F I t

theorem kf_eq {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (hm : m' = m) : KF B W cs m m' := KF.of_eq hm

theorem stab_nf (cs : List Rc) (rs : List Reg) : Stab NF cs rs := fun _ _ _ _ _ _ _ => trivial

theorem Stab.mono {F : KIn → State → Prop} {cs cs' : List Rc} {rs rs' : List Reg} (h : Stab F cs rs)
    (hc : ∀ c ∈ cs', c ∈ cs) (hr : ∀ r ∈ rs', r ∈ rs) : Stab F cs' rs' :=
  fun I s t hZ hF hf k => h I s t hZ hF (hf.mono hc) (k.mono hr)

theorem stab_and {F G : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (hF : Stab F cs rs)
    (hG : Stab G cs rs) : Stab (fun I t => F I t ∧ G I t) cs rs :=
  fun I s t hZ ⟨a, b⟩ hf k => ⟨hF I s t hZ a hf k, hG I s t hZ b hf k⟩

/-- The registers a piece may change: `mmRegs` (`x1` to `x17`). -/
abbrev allR : List Reg := mmRegs

theorem Stab.sub {F : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (h : Stab F cs allR)
    (hr : ∀ r ∈ rs, r ∈ allR := by decide) : Stab F cs rs :=
  h.mono (fun _ h => h) hr

/-- `e`'s value in its header slot. -/
abbrev EvOK : KIn → State → Prop := fun I t => word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E

theorem stab_ev {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kEv ∉ cs) :
    Stab EvOK cs rs := fun _ _ _ _ hF hf _ => (hf.word hok (by decide) hn).trans hF

/-- A mask in `kOk`. -/
abbrev KokM : KIn → State → Prop := fun I t => ∃ c, word t.mem I.B (8 * kOk) = mask c

theorem stab_kok {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kOk ∉ cs) :
    Stab KokM cs rs := fun _ _ _ _ ⟨c, h⟩ f _ => ⟨c, (f.word hok (by decide) hn).trans h⟩

/-- A mask in `x15`. -/
abbrev X15M : KIn → State → Prop := fun _ t => ∃ c, t.gpr .x15 = mask c

theorem stab_x15 {cs : List Rc} {rs : List Reg} (h : .x15 ∉ rs) : Stab X15M cs rs :=
  fun _ _ _ _ ⟨c, hc⟩ _ k => ⟨c, (k.gpr .x15 h).trans hc⟩

/-- Array `j` zero (`W + 2` words). -/
abbrev Zero (j : Nat) : KIn → State → Prop := fun I t => wv t.mem I.B (slot I.W j) (I.W + 2) = 0

/-- Word `W` of array `j` zero. -/
abbrev TopZ (j : Nat) : KIn → State → Prop := fun I t => atop I t.mem j = 0

theorem stab_top {j : Nat} {cs : List Rc} (rs : List Reg) (hj : j < 16) (hok : cs.all Rc.ok = true)
    (hn : .arr j ∉ cs) : Stab (TopZ j) cs rs := fun _ _ _ hZ h f _ => (f.top hok hj hn hZ).trans h

/-- Array `j`'s value. -/
abbrev AvIs (j v : Nat) : KIn → State → Prop := fun I t => av I t.mem j = v

theorem stab_av {j v : Nat} {cs : List Rc} (rs : List Reg) (hj : j < 16) (hok : cs.all Rc.ok = true)
    (hn : .arr j ∉ cs) : Stab (AvIs j v) cs rs := fun _ _ _ hZ h f _ => (f.av hok hj hn hZ).trans h

/-- Arrays `a` and `b` equal. -/
abbrev AvEq (a b : Nat) : KIn → State → Prop := fun I t => av I t.mem a = av I t.mem b

theorem stab_aveq {a b : Nat} {cs : List Rc} (rs : List Reg) (ha : a < 16) (hb : b < 16) (hok : cs.all Rc.ok = true)
    (hna : .arr a ∉ cs) (hnb : .arr b ∉ cs) : Stab (AvEq a b) cs rs := fun _ _ _ hZ h f _ => by
  dsimp only [AvEq] at h ⊢; rw [f.av hok ha hna hZ, f.av hok hb hnb hZ]; exact h

/-! ## After the front -/

/-- After the front: `KPrimes` but for `KS`, and words `W` of `p − 1` and
`q − 1` zero. -/
def PF (I : KIn) (t : State) : Prop :=
  av I t.mem aPa = I.P ∧ av I t.mem aQa = I.Q ∧ av I t.mem aPm = I.P - 1 ∧ av I t.mem aQm = I.Q - 1 ∧
    EvOK I t ∧ TopZ aPm I t ∧ TopZ aQm I t

theorem PF.primes {I : KIn} {s₀ t : State} (h : KS I s₀ t) (hf : PF I t) : KPrimes I s₀ t :=
  ⟨h, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩

/-- `PF` across a change of none of its parts. -/
theorem PF.frame {cs : List Rc} (hok : cs.all Rc.ok = true) (hPa : .arr aPa ∉ cs)
    (hQa : .arr aQa ∉ cs) (hPm : .arr aPm ∉ cs) (hQm : .arr aQm ∉ cs) (hEv : .hdr kEv ∉ cs) {I : KIn} {s t : State}
    (hZ : slot I.W 16 ≤ 2 ^ 64) (h : PF I s) (hf : KF I.B I.W cs s.mem t.mem) : PF I t :=
  let ⟨a, b, c, d, e, f, g⟩ := h
  ⟨(hf.av hok (by decide) hPa hZ).trans a, (hf.av hok (by decide) hQa hZ).trans b,
    (hf.av hok (by decide) hPm hZ).trans c, (hf.av hok (by decide) hQm hZ).trans d,
    (hf.word hok (by decide) hEv).trans e, (hf.at hok (by decide) hPm hZ).trans f,
    (hf.at hok (by decide) hQm hZ).trans g⟩

/-- `PF` survives a piece that changes none of its parts. -/
theorem stab_pf {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hPa : .arr aPa ∉ cs)
    (hQa : .arr aQa ∉ cs) (hPm : .arr aPm ∉ cs) (hQm : .arr aQm ∉ cs) (hEv : .hdr kEv ∉ cs) : Stab PF cs rs :=
  fun _ _ _ hZ h hf _ => PF.frame hok hPa hQa hPm hQm hEv hZ h hf

/-- A block that changes the registers alone, checked by the taint analysis
from `x0`. -/
theorem kg_regs {F G : KIn → State → Prop} {l : List Instr} {rs : List Reg} (hr : ∀ r ∈ rs, r ∈ mmRegs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (ht : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true)
    (hw : ∀ I s, slot I.W 16 ≤ 2 ^ 64 → F I s → WP isa (.block l) s fun t => t.mem = s.mem ∧ Keep rs s t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block l) (Two (KG G)) :=
  kg_x0 ht fun I _ s h _ hf => WP.mono (hw I s h.hZ hf) fun _ ⟨hm, k, hg⟩ => ⟨h.regs hm k hr, hg⟩

end VG.Proof.RsaKeyGen.AArch64.Key
