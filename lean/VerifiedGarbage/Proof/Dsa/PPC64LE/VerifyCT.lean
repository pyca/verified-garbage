module

import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.DomainShape
meta import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
meta import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! ### `Dsa.PPC64LE.CT.Key`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.CT.Sizes`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.CT.Base`, which this module and modules that import it used -/

section

/-!
# DSA on PPC64LE: the relation of two runs, for constant time

The taint analysis treats memory as secret, so values computed from the key's
public part, which the code loads from memory, are secret to it, although
both runs share them. Two runs are related by `Two` (`MontCT.lean`) for the
same public data `VD`: the layout, the pointers, the digest's length and the
key's public bytes (`Base`). The checks of the key branch on values computed
from those bytes; at each such branch both runs satisfy the same predicate,
which fixes the branch's condition (`rel_ite_zero`), and between branches the
taint analysis checks the code from the registers each predicate fixes
(`pins_ph`).

Signing shares the checks: its public data also name the key's whole length
(with x), the nonce's and `out`, which the header's word `hOut` keeps
(`VD.out`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- A call's public data. -/
structure VD where
  L : Lay
  key : Addr
  sig : Addr
  dig : Addr
  dl : Nat
  kb : List Byte
  /-- The key's octets the call may read (x's too, when signing). -/
  kl : Nat
  /-- The signature's octets, or the nonce's when signing. -/
  sl : Nat
  /-- When signing, `out`, which the header's word `hOut` keeps. -/
  out : Option Addr
  /-- The key's public octets, `kb`'s: p||q||g, and y for a key. -/
  kn : Nat

/-- The digest's length the code uses: at most 64 octets. -/
abbrev VD.d (v : VD) : Nat := min v.dl 64

/-- What every state from the entry on satisfies, for the public data `v`. -/
structure Base (v : VD) (s : State) : Prop where
  ok : v.L.Ok
  regs : Regs s v.L v.key v.sig v.dig
  scr : ScrL s v.L
  hk : Src s v.L v.key v.kn
  hsg : Src s v.L v.sig v.sl
  hdg : Src s v.L v.dig v.d
  kb : Spec.Rsa.bytesAt s.mem v.key v.kn = v.kb
  hx : Src s v.L v.key v.kl
  hdr : ∀ o ∈ v.out, word s.mem v.L.S Impl.Dsa.PPC64LE.Sign.hOut = o
  sgn : v.out.isSome → v.kl = 3 * v.L.pl + 2 * v.L.ql ∧ v.sl = v.L.ql ∧ v.kn = 3 * v.L.pl + v.L.ql
  /-- The public octets hold at least the domain. -/
  kn : 2 * v.L.pl + v.L.ql ≤ v.kn

/-- A change past the header keeps its word `hOut`. -/
theorem Base.hdr_body {v : VD} {s t : State} (h : Base v s) (ho : Body v.L s.mem t.mem) :
    ∀ o ∈ v.out, word t.mem v.L.S Impl.Dsa.PPC64LE.Sign.hOut = o := fun o hm =>
  (Outside.word ho (Or.inl (by simp only [Impl.Dsa.PPC64LE.Sign.hOut]; omega_using []))
    (by simp only [Impl.Dsa.PPC64LE.Sign.hOut]; omega_using [])).trans (h.hdr o hm)

theorem Base.step {v : VD} {s t : State} {rs : List Reg} (h : Base v s) (k : Keep rs s t)
    (ho : Body v.L s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Base v t :=
  ⟨h.ok, h.regs.keep k hr, h.scr.congr k.wr, h.hk.keep k.rd k.wr, h.hsg.keep k.rd k.wr,
    h.hdg.keep k.rd k.wr, (h.hk.kept (ho.mono (Nat.zero_le _) (by have := h.ok.z256; omega_using [this]))).trans h.kb,
    h.hx.keep k.rd k.wr, h.hdr_body ho, h.sgn, h.kn⟩

/-- The key's octets from `o`, `k` of them. -/
def VD.at (v : VD) (o k : Nat) : List Byte := (v.kb.drop o).take k

theorem Base.bytes {v : VD} {s : State} (h : Base v s) {o k : Nat} (hk : o + k ≤ v.kn) :
    Spec.Rsa.bytesAt s.mem (off v.key o) k = v.at o k := by
  rw [VD.at, ← h.kb, VG.Proof.Dsa.bytesAt_slice s.mem v.key hk]

theorem Base.p {v : VD} {s : State} (h : Base v s) :
    pOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at 0 v.L.pl) := by
  have := h.kn
  have := h.bytes (o := 0) (k := v.L.pl) (by omega_using [this])
  rw [off, BitVec.add_zero] at this
  rw [pOf, this]

theorem Base.q {v : VD} {s : State} (h : Base v s) :
    qOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at v.L.pl v.L.ql) := by
  have := h.kn
  rw [qOf, h.bytes (by omega_using [this])]

theorem Base.g {v : VD} {s : State} (h : Base v s) :
    gOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at (v.L.pl + v.L.ql) v.L.pl) := by
  have := h.kn
  rw [gOf, h.bytes (by omega_using [this])]

theorem Base.y {v : VD} {s : State} (h : Base v s) (h3 : 3 * v.L.pl + v.L.ql ≤ v.kn) :
    yOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at (2 * v.L.pl + v.L.ql) v.L.pl) := by
  rw [yOf, h.bytes (by omega_using [h3])]

/-- The registers every phase fixes: `r2` and those `Regs` reads. -/
def coreRegs : List Reg := [.r2, .r21, .r26, .r27, .r28]

/-- A phase: `Base`, `r2` holding the lengths with `qb v` as q's octets, and `X`. -/
def Ph (qb : VD → Nat) (X : VD → State → Prop) (v : VD) (s : State) : Prop :=
  Base v s ∧ s.gpr .r2 = pack v.L.pl v.L.ql (qb v) v.d ∧ X v s

/-- A phase fixes `coreRegs` and the registers `X` fixes. -/
theorem pins_ph {qb : VD → Nat} {X : VD → State → Prop} (rs : List Reg) (val : VD → Reg → BitVec 64)
    (hX : ∀ v s, X v s → ∀ r ∈ rs, s.gpr r = val v r) : Pins (Ph qb X) (coreRegs ++ rs) := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [coreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.1.regs.r21, h₂.1.regs.r21]
    · rw [h₁.1.regs.r26, h₂.1.regs.r26]
    · rw [h₁.1.regs.r27, h₂.1.regs.r27]
    · rw [h₁.1.regs.r28, h₂.1.regs.r28]
  · rw [hX v s₁ h₁.2.2 r hr, hX v s₂ h₂.2.2 r hr]

/-- The registers of `ps` hold their values. -/
def FixL (ps : List (Reg × BitVec 64)) (s : State) : Prop := ∀ p ∈ ps, s.gpr p.1 = p.2

/-- A phase whose `X` fixes registers by `FixL`. -/
theorem pins_fixL {qb : VD → Nat} {X : VD → State → Prop} (ps : VD → List (Reg × BitVec 64)) (rs : List Reg)
    (hrs : ∀ v, (ps v).map Prod.fst = rs) :
    Pins (Ph qb fun v s => FixL (ps v) s ∧ X v s) (coreRegs ++ rs) := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_ph (qb := qb) (X := fun v s => FixL (ps v) s ∧ X v s) [] (fun _ _ => 0)
      (fun _ _ _ _ h => absurd h List.not_mem_nil) v s₁ s₂ h₁ h₂ r (List.mem_append_left _ hr)
  · rw [← hrs v] at hr
    obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
    rw [h₁.2.2.1 p hm, h₂.2.2.1 p hm]

theorem pins_and {α : Type} {Φ E : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ E a s) rs :=
  fun a _ _ h₁ h₂ => h a _ _ h₁.1 h₂.1

/-- `Two` for a stronger predicate. -/
theorem two_mono {α : Type} {Φ Ψ : α → State → Prop} (h : ∀ a s, Φ a s → Ψ a s) {s₁ s₂ : State}
    (h₂ : Two Φ s₁ s₂) : Two Ψ s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := h₂
  ⟨a, h _ _ h₁, h _ _ h₂, hsp⟩

/-- A branch on a register both runs agree is zero or not; each branch may
assume which. -/
theorem rel_ite_zero {α : Type} {Φ : α → State → Prop} {r : Reg} {t e : Prog isa}
    {Q : State → State → Prop}
    (hz : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr r == 0) = (s₂.gpr r == 0))
    (ht : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r = 0) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r ≠ 0) e Q) :
    RelCT isa (Two Φ) (.ite (.zero .d r) t e) Q := by
  refine RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => by rw [eval_zero, eval_zero, hz a _ _ h₁ h₂]) ?_ ?_
  · refine ht.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h
    rw [eval_zero, Option.some.injEq, beq_iff_eq] at hc
    have hc₂ : (s₂.gpr r == 0) = true := by rw [← hz a _ _ h₁ h₂, hc, beq_self_eq_true]
    exact ⟨a, ⟨h₁, hc⟩, ⟨h₂, beq_iff_eq.mp hc₂⟩, hsp⟩
  · refine he.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h
    rw [eval_zero, Option.some.injEq] at hc
    have hc₂ : (s₂.gpr r == 0) = false := by rw [← hz a _ _ h₁ h₂, hc]
    exact ⟨a, ⟨h₁, fun e => by rw [e] at hc; exact absurd hc (by decide)⟩,
      ⟨h₂, fun e => by rw [e] at hc₂; exact absurd hc₂ (by decide)⟩, hsp⟩

/-- A phase step that keeps a fact `G` of the public data, which the taint
analysis and the step need not know (`G` restricts the public data a caller
relates, e.g. to signing's). -/
theorem two_postG {α : Type} {Φ Ψ : α → State → Prop} {G : α → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two fun a s => Φ a s ∧ G a) c (Two fun a s => Ψ a s ∧ G a) :=
  two_post (hct.mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h) fun a s h =>
    (hw a s h.1).mono fun _ x => ⟨x, h.2⟩

/-- `rel_ite_zero`, keeping a fact `G` of the public data. -/
theorem rel_ite_zeroG {α : Type} {Φ : α → State → Prop} {G : α → Prop} {r : Reg} {t e : Prog isa}
    {Q : State → State → Prop}
    (hz : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr r == 0) = (s₂.gpr r == 0))
    (ht : RelCT isa (Two fun a s => (Φ a s ∧ s.gpr r = 0) ∧ G a) t Q)
    (he : RelCT isa (Two fun a s => (Φ a s ∧ s.gpr r ≠ 0) ∧ G a) e Q) :
    RelCT isa (Two fun a s => Φ a s ∧ G a) (.ite (.zero .d r) t e) Q :=
  rel_ite_zero (fun a s₁ s₂ h₁ h₂ => hz a s₁ s₂ h₁.1 h₂.1)
    (ht.mono (fun _ _ => two_mono fun _ _ ⟨⟨h, g⟩, z⟩ => ⟨⟨h, z⟩, g⟩) fun _ _ h => h)
    (he.mono (fun _ _ => two_mono fun _ _ ⟨⟨h, g⟩, z⟩ => ⟨⟨h, z⟩, g⟩) fun _ _ h => h)

/-- Both runs agree whether `r` is zero when the predicate says exactly when. -/
theorem zero_iff_agree {α : Type} {Φ : α → State → Prop} {r : Reg} (C : α → Prop)
    (h : ∀ a s, Φ a s → (s.gpr r = 0 ↔ C a)) :
    ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr r == 0) = (s₂.gpr r == 0) := by
  intro a s₁ s₂ h₁ h₂
  have e₁ := h a _ h₁
  have e₂ := h a _ h₂
  by_cases hc : C a
  · rw [beq_iff_eq.mpr (e₁.mpr hc), beq_iff_eq.mpr (e₂.mpr hc)]
  · rw [show (s₁.gpr r == 0) = false from by simpa using fun e => hc (e₁.mp e),
      show (s₂.gpr r == 0) = false from by simpa using fun e => hc (e₂.mp e)]

/-- After the code: `r21` still holds `S`. -/
def End (v : VD) (s : State) : Prop := s.gpr .r21 = v.L.S

/-- Code that never writes `r21` ends where `End` holds, from a phase in
which `r21` holds `S`. -/
theorem rel_end {Φ : VD → State → Prop} {c : Prog isa} (h : RelCT isa (Two Φ) c fun _ _ => True)
    (h21 : ∀ v s, Φ v s → s.gpr .r21 = v.L.S)
    (hw : (instrs c).all (fun i => dstOf i != some .r21) = true) :
    RelCT isa (Two Φ) c (Two End) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨v, h₁, h₂, hsp⟩ := hp
  have hc : ∀ i ∈ instrs c, dstOf i ≠ some .r21 := fun i hi => by
    have := List.all_eq_true.mp hw i hi
    simpa using this
  exact ⟨ht, v, (Exec.gpr hc e₁ (.inr (by decide))).trans (h21 v _ h₁), (Exec.gpr hc e₂ (.inr (by decide))).trans (h21 v _ h₂),
    by rw [Exec.sp e₁, Exec.sp e₂, hsp]⟩

theorem pins_End : Pins End [.r21] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [h₁, h₂]

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA on PPC64LE: constant time of the check of the sizes

`sizes_rel`: two runs of `sizes` for the same public data leak the same
trace. Each scan's branches depend on the key's octets, which both runs share:
the phases fix the scans' results.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)

/-- p's and q's octets. -/
def VD.pB (v : VD) : List Byte := v.at 0 v.L.pl
def VD.qB (v : VD) : List Byte := v.at v.L.pl v.L.ql

theorem Base.bytesP {v : VD} {s : State} (h : Base v s) : Spec.Rsa.bytesAt s.mem v.key v.L.pl = v.pB := by
  have := h.kn
  have := h.bytes (o := 0) (k := v.L.pl) (by omega_using [this])
  rwa [off, BitVec.add_zero] at this

theorem Base.bytesQ {v : VD} {s : State} (h : Base v s) :
    Spec.Rsa.bytesAt s.mem (off v.key v.L.pl) v.L.ql = v.qB := by
  have := h.kn
  exact h.bytes (by omega_using [this])

/-- The sizes are supported, on the public data. -/
def SzOk (v : VD) : Prop :=
  Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE v.pB)) (Spec.Dsa.bitLength (Spec.Dsa.decodeBE v.qB))

/-- q's significant octets. -/
def VD.qb (v : VD) : Nat := (significant v.qB).1

/-- p's and q's scans: significant octets, and the first one's value. -/
def VD.sP (v : VD) : Nat := (significant v.pB).1
def VD.tP (v : VD) : Nat := (significant v.pB).2.toNat
def VD.tQ (v : VD) : Nat := (significant v.qB).2.toNat

/-- On entry to the checks. -/
def S0 : VD → State → Prop := Ph (fun _ => 0) fun _ s => FixL [] s ∧ True

/-- After p's scan of its octets. -/
def S0a : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r12, v.key), (.r6, BitVec.ofNat 64 v.L.pl), (.r16, BitVec.ofNat 64 v.sP)] s ∧ True

/-- After p's `bytesBits`. -/
def S1 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r16, BitVec.ofNat 64 v.sP)] s ∧ (s.gpr .r0 = 0 ↔ 128 ≤ v.tP)

/-- p's octets into `r24`. -/
def S2 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP)] s ∧ 128 ≤ v.tP

/-- After q's scan of its octets. -/
def S2a : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP), (.r12, off v.key v.L.pl), (.r6, BitVec.ofNat 64 v.L.ql),
    (.r16, BitVec.ofNat 64 v.qb)] s ∧ 128 ≤ v.tP

/-- After q's `bytesBits`. -/
def S3 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP), (.r16, BitVec.ofNat 64 v.qb)] s ∧ 128 ≤ v.tP ∧
    (s.gpr .r0 = 0 ↔ 128 ≤ v.tQ)

/-- After `pairs`. -/
def S4 : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ 128 ≤ v.tP ∧ 128 ≤ v.tQ ∧ (s.gpr .r0 = 0 ↔ Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.qb))

/-- After `sizes`. -/
def S5 : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ SzOk v

theorem pins_S0 : Pins S0 (coreRegs ++ ([] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S0a : Pins S0a (coreRegs ++ ([.r12, .r6, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S1 : Pins S1 (coreRegs ++ ([.r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S2 : Pins S2 (coreRegs ++ ([.r24] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S2a : Pins S2a (coreRegs ++ ([.r24, .r12, .r6, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S3 : Pins S3 (coreRegs ++ ([.r24, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl

theorem fixL_nil (s : State) : FixL [] s := fun _ h => absurd h List.not_mem_nil

/-- A branch's assumption, dropped. -/
theorem rel_weaken {α : Type} {Φ E : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two Φ) c Q) : RelCT isa (Two fun a s => Φ a s ∧ E a s) c Q :=
  h.mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h

theorem pl_bounds {v : VD} {s : State} (h : Base v s) : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by
  rcases h.ok.pl with e | e | e <;> omega_using [e]

/-- `ptrP` and p's scan. -/
theorem w_scanP {v : VD} {s : State} (h : S0 v s) : WP isa (.seq (.block ptrP) sigLen) s (S0a v) := by
  obtain ⟨B, r2, -⟩ := h
  have hb := pl_bounds B
  have := B.kn
  refine WP.seq (WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (sigLen_ok a12 a6 (by omega_using [hb]) (by omega_using [hb]) fun i hi => B1.hk.rd i (by omega_using [this, hi]))
    fun u ⟨⟨b16, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, trivial⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r12 (by decide)).trans a12, (k2.gpr .r6 (by decide)).trans a6,
      by rw [b16, m1, B.bytesP]; rfl⟩

/-- `ptrP` and p's `bytesBits`. -/
theorem w_bitsP {v : VD} {s : State} (h : S0 v s) : WP isa (.seq (.block ptrP) bytesBits) s (S1 v) := by
  obtain ⟨B, r2, -⟩ := h
  have hb := pl_bounds B
  have := B.kn
  refine WP.seq (WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (bytesBits_ok a12 a6 (by omega_using [hb]) (by omega_using [hb]) fun i hi => B1.hk.rd i (by omega_using [this, hi]))
    fun u ⟨⟨b16, b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    rw [b16, m1, B.bytesP]; rfl
  · rw [b0, m1, B.bytesP]; rfl

theorem ite16_rel : RelCT isa (Two S0a) (.ite (.zero .d .r16) (.block [.li .r0 1]) (.block topBit))
    fun _ _ => True :=
  rel_ite_zero (fun v s₁ s₂ h₁ h₂ => by rw [pins_S0a v s₁ s₂ h₁ h₂ .r16 (by decide)])
    (rel_weaken (two_taint _ pins_S0a (by taint_decide))) (rel_weaken (two_taint _ pins_S0a (by taint_decide)))

theorem bitsP_rel {G : VD → Prop} :
    RelCT isa (Two fun v s => S0 v s ∧ G v) (.seq (.block ptrP) bytesBits) (Two fun v s => S1 v s ∧ G v) :=
  two_postG (RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_S0 (by taint_decide)) fun _ _ h => w_scanP h)
    ite16_rel)) fun _ _ h => w_bitsP h

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA on PPC64LE: constant time of the checks of the key after the sizes

`paramsTail_rel`: two runs of the checks of the domain after `sizes` (p
and q odd, `p mod q = 1`, g in the subgroup) for the same public data leak
the same trace; `oddsTail_rel`, the same with y's check after them. The taint analysis checks the code between the branches on the
checks' results (`t1`–`t8`, from the registers each phase fixes), and each
phase states the result as a fact of the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The registers `rs` hold the values `x`. -/
def FixR (rs : List Reg) (x : Reg → BitVec 64) (s : State) : Prop := ∀ r ∈ rs, s.gpr r = x r

theorem pins_fixR (rs : List Reg) : Pins (FixR rs) rs :=
  fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm

/-- Code the taint analysis checks from the registers `rs`, for any phase
that fixes them. -/
theorem rel_pins {α : Type} {Φ : α → State → Prop} {rs : List Reg} {c : Prog isa} {Q : State → State → Prop}
    (h : Pins Φ rs) (t : RelCT isa (Two (FixR rs)) c Q) : RelCT isa (Two Φ) c Q :=
  t.mono (fun s₁ _ ⟨a, h₁, h₂, hsp⟩ => ⟨s₁.gpr, fun _ _ => rfl, fun r hr => (h a _ _ h₁ h₂ r hr).symm, hsp⟩)
    fun _ _ q => q

/-- The registers of the P space's `Env`, and `r23`. -/
def envRegs' : List Reg := [.r10, .r11, .r29, .r31, .r23]

theorem t1 : RelCT isa (Two (FixR (coreRegs ++ []))) (.block (ptrP ++ odd)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t2 : RelCT isa (Two (FixR (coreRegs ++ []))) (.block (ptrQ ++ odd)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t3 : RelCT isa (Two (FixR (coreRegs ++ []))) pModQ fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t4 : RelCT isa (Two (FixR (coreRegs ++ []))) setupPre fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
/-- The registers `setupPre` leaves fixed: the P space's, and the bases of
arrays 1–3. -/
def preRegs : List Reg := envRegs' ++ [.r5, .r8, .r9]
theorem t4a : RelCT isa (Two (FixR (coreRegs ++ preRegs)))
    (.seq VG.Impl.Bignum.PPC64LE.Precompute.r2Prime (VG.Impl.MillerRabin.PPC64LE.copy 24 1)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t4b : RelCT isa (Two (FixR (coreRegs ++ preRegs)))
    (.seq VG.Impl.Bignum.PPC64LE.Precompute.r2Hi (VG.Impl.MillerRabin.PPC64LE.copy 24 1)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t5 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptrG) (loadArr 4)) elemRange)
    fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t6 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) elemOrder fun _ _ => True :=
  two_taintR _ (pins_fixR _) (by taint_decide_rel)
theorem t8 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptrY) (loadArr 4)) elemRange)
    fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)

/-! ## The key's values -/

def VD.p (v : VD) : Nat := Spec.Dsa.decodeBE v.pB
def VD.q (v : VD) : Nat := Spec.Dsa.decodeBE v.qB
/-- The number at octet `o` of the key, `p_len` octets (g or y). -/
def VD.e (v : VD) (o : Nat) : Nat := Spec.Dsa.decodeBE (v.at o v.L.pl)

/-- After the sizes, both odd. -/
def KO (v : VD) : Prop := SzOk v ∧ v.p % 2 = 1 ∧ v.q % 2 = 1
/-- And `p mod q = 1`. -/
def KM (v : VD) : Prop := KO v ∧ v.p % v.q = 1
/-- The number at octet `o` is in `(1, p)`, and in the subgroup. -/
def ERange (o : Lay → Nat) (v : VD) : Prop := 1 < v.e (o v.L) ∧ v.e (o v.L) < v.p
def EOk (o : Lay → Nat) (v : VD) : Prop := ERange o v ∧ v.e (o v.L) ^ v.q % v.p = 1

theorem KO.bounds {v : VD} (h : KO v) : 1 < v.p ∧ 255 < v.q ∧ v.q < v.p :=
  VG.Proof.Dsa.supported_bounds h.1

/-! ## The phases -/

/-- q in the Q space's array 0, its top word 0. -/
def QF (v : VD) (s : State) : Prop := arrQ s.mem v.L 0 = v.q ∧ word s.mem v.L.Q (slot 4 0 + 32) = 0

/-- After p's oddness check. -/
def O1 : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ SzOk v ∧ (s.gpr .r0 = 0 ↔ v.p % 2 = 1)
/-- After q's. -/
def O2 : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ SzOk v ∧ v.p % 2 = 1 ∧ (s.gpr .r0 = 0 ↔ v.q % 2 = 1)
/-- After `pModQ`. -/
def OM : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ (KO v ∧ QF v s) ∧ (s.gpr .r0 = 0 ↔ v.p % v.q = 1)

/-- The P space's registers. -/
def envP (v : VD) : List (Reg × BitVec 64) :=
  [(.r10, off v.L.S (slot v.L.wp 0)), (.r11, BitVec.ofNat 64 (2 * v.L.wp)),
    (.r29, BitVec.ofNat 64 (8 * (v.L.wp + 2))), (.r31, v.L.S), (.r23, v.L.S)]

/-- In the P space, with p and `R² mod p` in arrays 0 and 24. -/
def PF (v : VD) (s : State) : Prop :=
  InP s v.L ∧ arrP s.mem v.L 0 = v.p ∧ word s.mem v.L.S (slot v.L.wp 0 + 8 * v.L.wp) = 0 ∧
    arrP s.mem v.L 24 = 2 ^ (128 * v.L.wp) % v.p ∧ QF v s

/-- In the P space, the key satisfying `K`. -/
def PP (K : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s => FixL (envP v) s ∧ PF v s ∧ K v
/-- After an element's range check. -/
def PE (c : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s => FixL (envP v) s ∧ (s.gpr .r0 = 0 ↔ c v)
/-- After an element's check. -/
def CC (K c : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s =>
  FixL (envP v) s ∧ PF v s ∧ K v ∧ (s.gpr .r0 = 0 ↔ c v)
/-- Before `rest`: the key passed the checks, with p, `R² mod p` and q in
the arrays. -/
def K9 : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ PF v s ∧ (KM v ∧ EOk (fun L => L.pl + L.ql) v) ∧ EOk (fun L => 2 * L.pl + L.ql) v

theorem pins_O1 : Pins O1 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_O2 : Pins O2 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_OM : Pins OM (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_S5' : Pins S5 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_PP (K : VD → Prop) : Pins (PP K) (coreRegs ++ envRegs') := pins_fixL _ _ fun _ => rfl
theorem pins_PE (c : VD → Prop) : Pins (PE c) (coreRegs ++ envRegs') := pins_fixL _ _ fun _ => rfl

theorem envP_of {v : VD} {s : State} (h : InP s v.L) : FixL (envP v) s := by
  simp only [FixL, envP, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨h.env.h10, h.env.h11, h.env.h29, h.env.h31, h.h23⟩

theorem ql_bounds {v : VD} {s : State} (h : Base v s) : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := h.ok.ql

/-! ## The steps between the branches -/

theorem w_O1 {v : VD} {s : State} (h : S5 v s) : WP isa (.block (ptrP ++ odd)) s (O1 v) := by
  obtain ⟨B, r2, -, hsz⟩ := h
  have hb := pl_bounds B
  have := B.kn
  rw [WP.block_append_iff]
  refine WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (odd_ok a12 a6 (by omega_arith) (by omega_arith) fun i hi => B1.hk.rd i (by omega_arith))
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, fixL_nil _, hsz, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [b0, m1, B.bytesP]; rfl

theorem w_O2 {v : VD} {s : State} (h : O1 v s ∧ s.gpr .r0 = 0) : WP isa (.block (ptrQ ++ odd)) s (O2 v) := by
  obtain ⟨⟨B, r2, -, hsz, e0⟩, z⟩ := h
  have hb := ql_bounds B
  have := B.kn
  rw [WP.block_append_iff]
  refine WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (odd_ok a12 a6 (by omega_arith) (by omega_arith)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega_arith)).rd i hi)
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, fixL_nil _, hsz,
      e0.mp z, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [b0, m1, B.bytesQ]; rfl

theorem w_OM {v : VD} {s : State} (h : O2 v s ∧ s.gpr .r0 = 0) : WP isa pModQ s (OM v) := by
  obtain ⟨⟨B, r2, -, hsz, hpo, e0⟩, z⟩ := h
  have ko : KO v := ⟨hsz, hpo, e0.mp z⟩
  have bd := ko.bounds
  refine WP.mono (pModQ_ok B.ok B.scr B.regs (B.hk.take B.kn) (by rw [B.q]; exact Nat.lt_trans (by decide) bd.2.1))
    fun t ⟨⟨_, q0, qtop, r0, qb⟩, k⟩ =>
      ⟨B.step k (qb.body B.ok), ?_, fixL_nil _, ⟨ko, by rw [q0, B.q]; rfl, qtop⟩, ?_⟩
  · rw [k.gpr .r2 (by decide), r2]
  · rw [r0, B.p, B.q]; rfl

/-- `setupP`, from a state in the Q space with q in its array 0, for a key
satisfying `K`. -/
theorem w_setupP {K : VD → Prop} (hK : ∀ v, K v → KO v) {v : VD} {s : State} (B : Base v s)
    (r2 : s.gpr .r2 = pack v.L.pl v.L.ql v.qb v.d) (qf : QF v s) (kv : K v) : WP isa setupP s (PP K v) := by
  have bd := (hK v kv).bounds
  refine WP.mono (setupP_ok B.ok B.scr B.regs (B.hk.take B.kn) (by rw [B.p]; exact bd.1)
      (by rw [B.p]; exact (hK v kv).2.1))
    fun t ⟨⟨ip, p0, ptop, p8, pb⟩, k⟩ => ⟨B.step k (pb.body B.ok), ?_, envP_of ip,
      ⟨ip, ?_, ptop, ?_, (pb.arrQ B.ok 0 (by decide)).trans qf.1, (pb.qtop B.ok).trans qf.2⟩, kv⟩
  · rw [k.gpr .r2 (by decide), r2]
  · rw [p0, B.p]; rfl
  · rw [p8, B.p]; rfl

theorem w_P {v : VD} {s : State} (h : OM v s ∧ s.gpr .r0 = 0) : WP isa setupP s (PP KM v) := by
  obtain ⟨⟨B, r2, -, ⟨ko, qf⟩, e0⟩, z⟩ := h
  exact w_setupP (K := KM) (fun _ h => h.1) B r2 qf ⟨ko, e0.mp z⟩

/-- The P space's registers and the bases of arrays 1–3. -/
def envPB (v : VD) : List (Reg × BitVec 64) :=
  envP v ++ [(.r5, off v.L.S (slot v.L.wp 1)), (.r8, off v.L.S (slot v.L.wp 2)), (.r9, off v.L.S (slot v.L.wp 3))]

/-- After `setupPre`: `r3` is zero exactly when p's top word is. -/
def SPre : VD → State → Prop := Ph VD.qb fun v s =>
  FixL (envPB v) s ∧ (s.gpr .r3 = 0 ↔ v.p / 2 ^ (64 * (v.L.wp - 1)) = 0)

theorem pins_SPre : Pins SPre (coreRegs ++ preRegs) := pins_fixL _ _ fun _ => rfl

/-- p's top word is its quotient by `2^(64 (w − 1))`. -/
theorem top_div {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) :
    (word m B (d + 8 * (w - 1))).toNat = val32 m B d (2 * w) / 2 ^ (64 * (w - 1)) := by
  rw [val32_top m B d w hw]
  have hlo := val32_lt m B d (2 * (w - 1))
  rw [show 32 * (2 * (w - 1)) = 64 * (w - 1) by omega_using []] at hlo
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem w_pre0 {v : VD} {s : State} (B : Base v s) (r2 : s.gpr .r2 = pack v.L.pl v.L.ql v.qb v.d)
    (hpo : v.p % 2 = 1) : WP isa setupPre s (SPre v) := by
  have hL := B.ok
  have hw := hL.wp_ge
  have hnw := hL.nowrap
  have hqZ : v.L.qOff + 1600 ≤ v.L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have e0 := Lay.slot_eq v.L.wp 0; have e28 := Lay.slot_eq v.L.wp 28
  have hq28 : v.L.qOff = slot v.L.wp 28 := rfl
  have hp : pOf s.mem v.L v.key = v.p := by rw [B.p]; rfl
  refine WP.mono (setupPre_ok B.ok B.scr B.regs (B.hk.take B.kn) (by rw [hp]; exact hpo))
    fun t ⟨⟨hin, a5, a8, a9, _, _, v0, _, o3, a3⟩, k⟩ => ⟨B.step k (Body.ofP hL o3 (by omega_arith) (by omega_arith)), ?_, ?_, ?_⟩
  · rw [k.gpr .r2 (by decide), r2]
  · have f := envP_of hin
    simp only [FixL, envPB, envP, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
      false_imp_iff, imp_true_iff, and_true] at f ⊢
    exact ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, a5, a8, a9⟩
  · rw [a3, ← hp, ← v0, ← top_div (by omega_arith)]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)

/-- `setupP`, for phases that fix `coreRegs` and hold `Base`, `r2`'s lengths
and an odd p: its branch on p's top word is the same in both runs. -/
theorem setupP_rel {Φ : VD → State → Prop} (hpin : Pins Φ (coreRegs ++ []))
    (hΦ : ∀ v s, Φ v s → Base v s ∧ s.gpr .r2 = pack v.L.pl v.L.ql v.qb v.d ∧ v.p % 2 = 1) :
    RelCT isa (Two Φ) setupP fun _ _ => True := by
  unfold setupP
  refine RelCT.seq (two_post (rel_pins hpin t4) fun v s h =>
    have ⟨B, r2, hpo⟩ := hΦ v s h; w_pre0 B r2 hpo) ?_
  exact rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2)
    (rel_pins (pins_and pins_SPre) t4a) (rel_pins (pins_and pins_SPre) t4b)

/-! ## An element's check -/

section Elem

variable (ptr : List Instr) (o : Lay → Nat) {G : VD → Prop}
  (ho : ∀ v s, Base v s → G v → o v.L + v.L.pl ≤ v.kn)
  (hptr : ∀ {s : State} {L : Lay} {key sig dig : Addr}, Regs s L key sig dig →
    WP isa (.block ptr) s fun t =>
      (t.gpr .r12 = off key (o L) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [.r0, .r6, .r12] s t)

include ho hptr in
/-- The pointer, the load and the range check. -/
theorem w_pre {K : VD → Prop} {v : VD} {s : State} (h : PP K v s) (hg : G v) :
    WP isa (.seq (.seq (.block ptr) (loadArr 4)) elemRange) s (PE (ERange o) v) := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, -, -⟩, -⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : v.L.qOff + 1600 ≤ v.L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith
  have hq28 : v.L.qOff = slot v.L.wp 28 := rfl
  have hov := ho v s B hg
  have e0 := Lay.slot_eq v.L.wp 0; have e3 := Lay.slot_eq v.L.wp 3; have e4 := Lay.slot_eq v.L.wp 4
  have e8 := Lay.slot_eq v.L.wp 8; have e28 := Lay.slot_eq v.L.wp 28
  refine WP.seq (WP.seq (WP.mono (hptr B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_))
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  have en1 := ip.env.keep k1 (by decide)
  have he := B1.hk.sub (o := o v.L) (k := v.L.pl) hov
  refine WP.mono (loadArr_ok en1 (j := 4) (by decide) a12 a6 (by omega_arith) (by omega_arith) he.rd
    (fun i hi x hx => he.sep i hi x (by omega_arith))) fun u ⟨⟨v4, top4, o2, a10⟩, k2⟩ => ?_
  have en2 := env_keep10 en1 k2 (by decide) a10
  have B2 := B1.step k2 (o2.mono (by omega_arith) (by omega_arith))
  refine WP.mono (elemRange_ok en2 top4) fun w ⟨⟨r0, _, o3, en3⟩, k3⟩ => ?_
  have B3 := B2.step k3 (o3.mono (by omega_arith) (by omega_arith))
  have p1 : arr u.mem v.L.S v.L.wp 0 = v.p := by
    rw [arr, Outside.val32 o2 (by omega_arith) (by omega_arith), m1]; exact p0
  have x4 : arr u.mem v.L.S v.L.wp 4 = v.e (o v.L) := by
    rw [arr, v4, m1, B.bytes hov]; rfl
  refine ⟨B3, ?_, ?_, ?_⟩
  · rw [k3.gpr .r2 (by decide), k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, envP, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨en3.h10, en3.h11, en3.h29, en3.h31,
      (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans ((k1.gpr .r23 (by decide)).trans ip.h23))⟩
  · rw [r0, x4, p1]; rfl

include ho hptr in
/-- The pointer and `checkElem`. -/
theorem w_elem {K : VD → Prop} (hK : ∀ v, K v → 2 ≤ v.p ∧ v.p % 2 = 1) {v : VD} {s : State}
    (h : PP K v s) (hg : G v) : WP isa (.seq (.block ptr) checkElem) s (CC K (EOk o) v) := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, p8, qf⟩, kv⟩ := h
  have hL := B.ok
  have hov := ho v s B hg
  obtain ⟨hp, hpo⟩ := hK v kv
  refine WP.seq (WP.mono (hptr B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (checkElem_ok hL B1.regs (ip.keep k1 (by decide)) (B1.hk.take B1.kn) (B1.hk.sub (o := o v.L) (k := v.L.pl) hov)
      a12 a6 (by rw [m1]; exact p0) (by rw [m1]; exact ptop) hp hpo (by rw [m1]; exact p8))
    fun u ⟨⟨ip', p0', ptop', p8', r0, pb⟩, k2⟩ =>
      ⟨B1.step k2 (pb.body hL), ?_, envP_of ip', ⟨ip', p0', ptop', ?_,
        (pb.arrQ hL 0 (by decide)).trans (by rw [m1]; exact qf.1), (pb.qtop hL).trans (by rw [m1]; exact qf.2)⟩,
        kv, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [p8', m1]; exact p8
  · rw [r0, B1.bytes hov, B1.q, EOk, ERange, and_assoc]; rfl

include ho hptr in
theorem elem_rel
    (hT : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptr) (loadArr 4)) elemRange)
      fun _ _ => True)
    {K : VD → Prop} (hK : ∀ v, K v → 2 ≤ v.p ∧ v.p % 2 = 1) :
    RelCT isa (Two fun v s => PP K v s ∧ G v) (.seq (.block ptr) checkElem)
      (Two fun v s => CC K (EOk o) v s ∧ G v) := by
  refine two_post ?_ fun _ _ h => (w_elem ptr o ho hptr hK h.1 h.2).mono fun _ x => ⟨x, h.2⟩
  unfold checkElem andThen
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (rel_pins (pins_and (pins_PP K)) hT)
      fun _ _ h => w_pre ptr o ho hptr h.1 h.2)
    (rel_ite_zero (zero_iff_agree (ERange o) fun _ _ h => h.2.2.2) (rel_weaken (rel_pins (pins_PE _) t6))
      (rel_weaken (RelCT.block_nil fun _ _ _ => trivial)))))

end Elem

/-! ## The checks after the sizes -/

theorem KM_p {v : VD} (h : KM v) : 2 ≤ v.p ∧ v.p % 2 = 1 := ⟨h.1.bounds.1, h.1.2.1⟩

/-- After g's check: the domain passed the checks. -/
abbrev K8 : VD → State → Prop := PP fun v => KM v ∧ EOk (fun L => L.pl + L.ql) v

/-- The checks of the domain after the sizes, for public data satisfying `G`. -/
theorem paramsTail_rel {rest fail : Prog isa} {Q : State → State → Prop} {G : VD → Prop}
    (hrest : RelCT isa (Two fun v s => K8 v s ∧ G v) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s ∧ G v) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two fun v s => S5 v s ∧ G v) (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG)
      checkElem) rest fail)) fail) fail) Q := by
  have hG := elem_rel ptrG (fun L => L.pl + L.ql) (G := G) (fun _ _ B _ => by have := B.kn; omega_using [this])
    (fun h => ptrG_ok h) t5 (K := KM) (fun _ => KM_p)
  unfold odds andThen
  refine RelCT.seq (two_postG (rel_pins pins_S5' t1) fun _ _ h => w_O1 h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (rel_pins (pins_and pins_O1) t2) fun _ _ h => w_O2 h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (rel_pins (pins_and pins_O2) t3) fun _ _ h => w_OM h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (setupP_rel (pins_and pins_OM)
      fun _ _ ⟨⟨B, r2, _, ⟨ko, _⟩, _⟩, _⟩ => ⟨B, r2, ko.2.1⟩) fun _ _ h => w_P h) (RelCT.seq
    hG (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩)))
  exact hrest.mono (fun _ _ => two_mono fun _ _ ⟨⟨⟨B, r2, fx, pf, k, e⟩, z⟩, g⟩ =>
      ⟨⟨B, r2, fx, pf, k, e.mp z⟩, g⟩) fun _ _ h => h

/-- The checks of the key after the sizes, for public data satisfying `G`, which
names y among the public octets. -/
theorem oddsTail_rel {rest fail : Prog isa} {Q : State → State → Prop} {G : VD → Prop}
    (hy : ∀ v s, Base v s → G v → 3 * v.L.pl + v.L.ql ≤ v.kn)
    (hrest : RelCT isa (Two fun v s => K9 v s ∧ G v) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s ∧ G v) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two fun v s => S5 v s ∧ G v) (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG)
      checkElem) (andThen (.seq (.block ptrY) checkElem) rest fail) fail)) fail) fail) Q := by
  refine paramsTail_rel ?_ hfail
  have hY := elem_rel ptrY (fun L => 2 * L.pl + L.ql) (G := G) (fun v s B g => by have := hy v s B g; omega_using [this])
    (fun h => ptrY_ok h) t8 (K := fun v => KM v ∧ EOk (fun L => L.pl + L.ql) v) (fun _ h => KM_p h.1)
  unfold andThen
  refine RelCT.seq hY
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  exact hrest.mono (fun _ _ => two_mono fun _ _ ⟨⟨⟨B, r2, _, pf, k, e⟩, z⟩, g⟩ =>
    ⟨⟨B, r2, fixL_nil _, pf, k, e.mp z⟩, g⟩) fun _ _ h => h

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.CT.SizesRest`, which this module and modules that import it used -/

section

/-!
# DSA on PPC64LE: constant time of the check of the sizes, after p's scan

`sizes_rel`: two runs of `sizes rest fail` for the same public data leak the
same trace, when `rest` and `fail` do from the phases they start in.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)

theorem sP_le {v : VD} {s : State} (h : Base v s) : v.sP ≤ v.L.pl := by
  have := VG.Proof.Dsa.significant_fits v.pB
  rw [← h.bytesP, bytesAt_length] at this
  rw [VD.sP, ← h.bytesP]; exact this

theorem qb_le {v : VD} {s : State} (h : Base v s) : v.qb ≤ v.L.ql := by
  have := VG.Proof.Dsa.significant_fits v.qB
  rw [← h.bytesQ, bytesAt_length] at this
  rw [VD.qb, ← h.bytesQ]; exact this

/-- `Base` after `r2` gets q's octets. -/
theorem Base.step2 {v : VD} {s t : State} {rs : List Reg} {qb : Nat} (h : Base v s) (k : Keep rs s t)
    (ho : Body v.L s.mem t.mem) (h2 : t.gpr .r2 = pack v.L.pl v.L.ql qb v.d) (hqb : qb < 2 ^ 16)
    (hr : ∀ r ∈ ([.r21, .r26, .r27, .r28] : List Reg), r ∉ rs := by decide) : Base v t :=
  ⟨h.ok, Regs.of_pack h.ok ((k.gpr .r21 (hr _ (by decide))).trans h.regs.r21)
      ((k.gpr .r27 (hr _ (by decide))).trans h.regs.r27) ((k.gpr .r28 (hr _ (by decide))).trans h.regs.r28)
      ((k.gpr .r26 (hr _ (by decide))).trans h.regs.r26) h2 hqb (by simp only [VD.d]; omega_arith),
    h.scr.congr k.wr, h.hk.keep k.rd k.wr, h.hsg.keep k.rd k.wr, h.hdg.keep k.rd k.wr,
    (h.hk.kept (ho.mono (Nat.zero_le _) (by have := h.ok.z256; omega_arith))).trans h.kb, h.hx.keep k.rd k.wr,
    h.hdr_body ho, h.sgn, h.kn⟩

/-- p's octets into `r24`. -/
theorem w_a24 {v : VD} {s : State} (h : S1 v s ∧ s.gpr .r0 = 0) :
    WP isa (.block [.addi .r24 .r16 0]) s (S2 v) := by
  obtain ⟨⟨B, r2, f, h0⟩, z⟩ := h
  have f16 : s.gpr .r16 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = BitVec.ofNat 64 v.sP ∧ t.mem = s.mem)
    (by prun [f16, BitVec.add_zero]) (by decide)) fun t ⟨⟨a24, m⟩, k⟩ =>
    ⟨B.step k (by rw [m]; exact Outside.refl _ _ _ _), by rw [k.gpr .r2 (by decide), r2], ?_, h0.mp z⟩
  simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact a24

/-- `ptrQ` and q's scan. -/
theorem w_scanQ {v : VD} {s : State} (h : S2 v s) : WP isa (.seq (.block ptrQ) sigLen) s (S2a v) := by
  obtain ⟨B, r2, f, tp⟩ := h
  have f24 : s.gpr .r24 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  have hq := B.ok.ql
  have := B.kn
  refine WP.seq (WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (sigLen_ok a12 a6 (by omega_arith) (by omega_arith)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega_arith)).rd i hi)
    fun u ⟨⟨b16, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, tp⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r24 (by decide)).trans ((k1.gpr .r24 (by decide)).trans f24),
      (k2.gpr .r12 (by decide)).trans a12, (k2.gpr .r6 (by decide)).trans a6,
      by rw [b16, m1, B.bytesQ]; rfl⟩

/-- `ptrQ` and q's `bytesBits`. -/
theorem w_bitsQ {v : VD} {s : State} (h : S2 v s) : WP isa (.seq (.block ptrQ) bytesBits) s (S3 v) := by
  obtain ⟨B, r2, f, tp⟩ := h
  have f24 : s.gpr .r24 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  have hq := B.ok.ql
  have := B.kn
  refine WP.seq (WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (bytesBits_ok a12 a6 (by omega_arith) (by omega_arith)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega_arith)).rd i hi)
    fun u ⟨⟨b16, b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, tp, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r24 (by decide)).trans ((k1.gpr .r24 (by decide)).trans f24),
      by rw [b16, m1, B.bytesQ]; rfl⟩
  · rw [b0, m1, B.bytesQ]; rfl

theorem ite16q_rel : RelCT isa (Two S2a) (.ite (.zero .d .r16) (.block [.li .r0 1]) (.block topBit))
    fun _ _ => True :=
  rel_ite_zero (fun v s₁ s₂ h₁ h₂ => by rw [pins_S2a v s₁ s₂ h₁ h₂ .r16 (by decide)])
    (rel_weaken (two_taint _ pins_S2a (by taint_decide))) (rel_weaken (two_taint _ pins_S2a (by taint_decide)))

theorem bitsQ_rel {G : VD → Prop} :
    RelCT isa (Two fun v s => S2 v s ∧ G v) (.seq (.block ptrQ) bytesBits) (Two fun v s => S3 v s ∧ G v) :=
  two_postG (RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_S2 (by taint_decide)) fun _ _ h => w_scanQ h)
    ite16q_rel)) fun _ _ h => w_bitsQ h

/-- q's octets into `r25` and `r2`, and `pairs`. -/
theorem w_pairs {v : VD} {s : State} (h : S3 v s ∧ s.gpr .r0 = 0) :
    WP isa (.seq (.block [.addi .r25 .r16 0, .lsl .r0 .r16 32, .add .r2 .r2 .r0]) pairs) s (S4 v) := by
  obtain ⟨⟨B, r2, f, tp, h0⟩, z⟩ := h
  simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true] at f
  obtain ⟨f24, f16⟩ := f
  have hp := sP_le B
  have hqb := qb_le B
  have hql := B.ok.ql
  have hpl := pl_bounds B
  refine WP.seq (WP.mono (WP.keep [.r25, .r0, .r2] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 v.qb ∧
      t.gpr .r2 = pack v.L.pl v.L.ql v.qb v.d ∧ t.mem = s.mem)
    (by prun [f16, r2, BitVec.add_zero, pack_add (show v.qb < 2 ^ 16 by omega_arith)]) (by decide))
    fun t ⟨⟨a25, a2, m1⟩, k1⟩ => ?_)
  refine WP.mono (pairs_ok ((k1.gpr .r24 (by decide)).trans f24) a25 (by omega_arith) (by omega_arith))
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨(B.step2 k1 (by rw [m1]; exact Outside.refl _ _ _ _) a2 (by omega_arith)).step k2
      (by rw [m2]; exact Outside.refl _ _ _ _), by rw [k2.gpr .r2 (by decide), a2], fixL_nil u, tp, h0.mp z, b0⟩

/-- The check of the sizes, for public data satisfying `G`. -/
theorem sizes_rel {rest fail : Prog isa} {Q : State → State → Prop} {G : VD → Prop}
    (hrest : RelCT isa (Two fun v s => S5 v s ∧ G v) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s ∧ G v) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two fun v s => S0 v s ∧ G v) (sizes rest fail) Q := by
  unfold sizes andThen
  refine RelCT.seq bitsP_rel (rel_ite_zeroG (zero_iff_agree (fun (v : VD) => 128 ≤ v.tP)
    fun _ _ h => h.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (two_taint _ (pins_and pins_S1) (by taint_decide)) fun _ _ h => w_a24 h) ?_
  refine RelCT.seq bitsQ_rel (rel_ite_zeroG (zero_iff_agree (fun (v : VD) => 128 ≤ v.tQ)
    fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.assoc (RelCT.seq (two_postG (two_taint _ (pins_and pins_S3) (by taint_decide))
    fun _ _ h => w_pairs h) ?_)
  refine rel_ite_zeroG (zero_iff_agree (fun (v : VD) => Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.qb))
    fun _ _ h => h.2.2.2.2.2) (hrest.mono (fun _ _ => two_mono fun v s ⟨⟨⟨B, r2, _, tp, tq, h0⟩, z⟩, g⟩ =>
      ⟨⟨B, r2, fixL_nil s, (VG.Proof.Dsa.supported_scans v.pB v.qB).mpr ⟨tp, tq, h0.mp z⟩⟩, g⟩) fun _ _ h => h)
    (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩)

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.CT.Entry`, which this module and modules that import it used -/

section

/-!
# DSA verification on PPC64LE: constant time of the entry

`entry_rel`: from two states that satisfy the contract with the same public
data (`vdOf`), the entry leaks the same trace and leaves both in the phase
`S0`. The taint analysis treats `scratch`'s address, loaded from the stack,
as secret: the phase `L1` after `loadS` fixes it.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- A call's public data. -/
def vdOf (s : State) : VD :=
  ⟨layOf s, s.gpr .r3, s.gpr .r7, s.gpr .r9, (s.gpr .r10).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat),
    3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat, 2 * (s.gpr .r6).toNat, none,
    3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat⟩

/-- The public octets name y. -/
def KY (v : VD) : Prop := 3 * v.L.pl + v.L.ql ≤ v.kn

/-- On entry. -/
def C0 (v : VD) (s : State) : Prop := vContract.pre s ∧ vdOf s = v

/-- After `loadS`. -/
def L1 (v : VD) (s : State) : Prop :=
  s.gpr .r11 = v.L.S ∧ s.gpr .r3 = v.key ∧ s.gpr .r5 = BitVec.ofNat 64 v.L.pl ∧
    s.gpr .r6 = BitVec.ofNat 64 v.L.ql ∧ s.gpr .r7 = v.sig ∧ s.gpr .r9 = v.dig ∧
    s.gpr .r10 = BitVec.ofNat 64 v.dl

theorem C0.L1 {v : VD} {s : State} (h : C0 v s) :
    s.gpr .r3 = v.key ∧ s.gpr .r5 = BitVec.ofNat 64 v.L.pl ∧ s.gpr .r6 = BitVec.ofNat 64 v.L.ql ∧
      s.gpr .r7 = v.sig ∧ s.gpr .r9 = v.dig ∧ s.gpr .r10 = BitVec.ofNat 64 v.dl := by
  obtain ⟨-, rfl⟩ := h
  simp [vdOf, layOf]

theorem pins_C0 : Pins C0 [.r3, .r5, .r6, .r7, .r9, .r10] := by
  intro v s₁ s₂ h₁ h₂ r hr
  have a := h₁.L1
  have b := h₂.L1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a.1, b.1]
  · rw [a.2.1, b.2.1]
  · rw [a.2.2.1, b.2.2.1]
  · rw [a.2.2.2.1, b.2.2.2.1]
  · rw [a.2.2.2.2.1, b.2.2.2.2.1]
  · rw [a.2.2.2.2.2, b.2.2.2.2.2]

theorem pins_L1 : Pins L1 [.r11, .r3, .r5, .r6, .r7, .r9, .r10] := by
  intro v s₁ s₂ a b r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a.1, b.1]
  · rw [a.2.1, b.2.1]
  · rw [a.2.2.1, b.2.2.1]
  · rw [a.2.2.2.1, b.2.2.2.1]
  · rw [a.2.2.2.2.1, b.2.2.2.2.1]
  · rw [a.2.2.2.2.2.1, b.2.2.2.2.2.1]
  · rw [a.2.2.2.2.2.2, b.2.2.2.2.2.2]

theorem loadS_L1 {v : VD} {s : State} (h : C0 v s) :
    WP isa (.block [.addSp .r11 96, .load .d .r11 .r11 0]) s (L1 v) := by
  have e := h.L1
  obtain ⟨hp, rfl⟩ := h
  refine WP.mono (Pub.loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hp.2.1]; simp),
    by simp [Region.Contains]⟩) fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨a11, ?_⟩
  obtain ⟨e3, e5, e6, e7, e9, e10⟩ := e
  exact ⟨(k.gpr .r3 (by decide)).trans e3, (k.gpr .r5 (by decide)).trans e5, (k.gpr .r6 (by decide)).trans e6,
    (k.gpr .r7 (by decide)).trans e7, (k.gpr .r9 (by decide)).trans e9, (k.gpr .r10 (by decide)).trans e10⟩

/-- The contract's buffers apart from `scratch`. -/
theorem pre_src {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (layOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm, Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hn, hk, hi])⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega_using [hn]) i (by omega_using [hk, hi])⟩

theorem front_S0 {v : VD} {s : State} (h : C0 v s) :
    WP isa (.block Verify.entry) s fun t => S0 v t ∧ KY v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := layOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨-, hrd, -, dKS, dGS, dDS, -, -, -, -, -, -, hkl, hsl, -⟩ := hp
  refine WP.mono (front_ok hpre) fun t ⟨⟨hr, scr, r2, _, out⟩, k⟩ => ?_
  have hK : ∀ {u : State}, u.rd = s.rd → u.wr = s.wr → Src u (layOf s) (s.gpr .r3) (3 * (layOf s).pl + (layOf s).ql) :=
    fun hr hw => pre_src (A := s.gpr .r3) (by rw [hrd]; simp) dKS (s.gpr .r4).isLt
      (by simp only [layOf]; omega_using [hkl]) hr hw
  have Out : Outside (layOf s).S 0 (layOf s).Z s.mem t.mem := out.mono (Nat.le_refl _) (by simp only [layOf] at hZ ⊢; omega_using [hZ])
  refine ⟨⟨⟨hL, hr, scr, hK k.rd k.wr,
    pre_src (A := s.gpr .r7) (k := 2 * (layOf s).ql) (by rw [hrd]; simp) dGS (s.gpr .r8).isLt
      (by simp only [layOf]; omega_using [hsl]) k.rd k.wr,
    pre_src (A := s.gpr .r9) (k := min (s.gpr .r10).toNat 64) (by rw [hrd]; simp) dDS (s.gpr .r10).isLt
      (Nat.min_le_left _ _) k.rd k.wr,
    (hK rfl rfl).kept Out, hK k.rd k.wr, (fun _ h => nomatch h), (fun h => nomatch h),
    (by simp only [vdOf, layOf]; omega_using [])⟩, r2, fixL_nil t, trivial⟩, Nat.le_refl _⟩

theorem entry_rel : RelCT isa (Two C0) (.block Verify.entry) (Two fun v s => S0 v s ∧ KY v) := by
  refine two_post ?_ fun _ _ h => front_S0 h
  unfold Verify.entry
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA verification on PPC64LE: constant time

`verify_ct`: two runs from states that satisfy the contract and agree on its
public data (the arguments' registers, the stack's arguments, the key's
public part and the result) leak the same trace. The entry (`entry_rel`),
the checks of the key (`sizes_rel`, `oddsTail_rel`), the verification
(`body_rel`, one taint segment) and `restore` follow one another; each
branch of the checks depends only on the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

theorem fail_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) :
    RelCT isa (Two Φ) (.block [.li .r3 0]) (Two End) :=
  rel_end (two_taint [.r21] (fun v s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(h v _ h₁).regs.r21, (h v _ h₂).regs.r21])
    (by taint_decide)) (fun v s hs => (h v s hs).regs.r21) (by decide)

theorem body_rel : RelCT isa (Two K9) Verify.body (Two End) :=
  rel_end (two_taintR _ (pins_fixL _ _ fun _ => rfl) (by taint_decide_rel)) (fun _ _ h => h.1.regs.r21)
    (by rw [← Code.allInstrs_eq]; decide +kernel)

/-- The check of the key, then `rest`, or 0. -/
theorem checkKey_rel {rest : Prog isa} (hrest : RelCT isa (Two K9) rest (Two End)) :
    RelCT isa (Two fun v s => S0 v s ∧ KY v) (checkKey rest (.block [.li .r3 0])) (Two End) :=
  sizes_rel (oddsTail_rel (fun _ _ _ h => h) (hrest.mono (fun _ _ => two_mono fun _ _ h => h.1)
      fun _ _ h => h) fun _ h => fail_rel fun v s h' => (h v s h').1) fun _ h => fail_rel fun v s h' => (h v s h').1

/-- Runs that agree on the contract's public data have the same public data `vdOf`. -/
theorem vdOf_eq {s t : State} (hs : vContract.pre s) (hp : vContract.pub s t) : vdOf s = vdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, -, h9, h10, a0, a1, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega_using [hk])] at e
  simp only [vdOf, layOf, ← h3, ← h5, ← h6, ← h7, ← h9, ← h10, ← a0, ← a1, e]

end VG.Proof.Dsa.PPC64LE
