module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

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

/-- The digest's length the code uses: at most 64 octets. -/
abbrev VD.d (v : VD) : Nat := min v.dl 64

/-- What every state from the entry on satisfies, for the public data `v`. -/
structure Base (v : VD) (s : State) : Prop where
  ok : v.L.Ok
  regs : Regs s v.L v.key v.sig v.dig
  scr : ScrL s v.L
  hk : Src s v.L v.key (3 * v.L.pl + v.L.ql)
  hsg : Src s v.L v.sig (2 * v.L.ql)
  hdg : Src s v.L v.dig v.d
  kb : Spec.Rsa.bytesAt s.mem v.key (3 * v.L.pl + v.L.ql) = v.kb

theorem Base.step {v : VD} {s t : State} {rs : List Reg} (h : Base v s) (k : Keep rs s t)
    (ho : Outside v.L.S 0 v.L.Z s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Base v t :=
  ⟨h.ok, h.regs.keep k hr, h.scr.congr k.wr, h.hk.keep k.rd k.wr, h.hsg.keep k.rd k.wr,
    h.hdg.keep k.rd k.wr, (h.hk.kept ho).trans h.kb⟩

/-- The key's octets from `o`, `k` of them. -/
def VD.at (v : VD) (o k : Nat) : List Byte := (v.kb.drop o).take k

theorem Base.bytes {v : VD} {s : State} (h : Base v s) {o k : Nat} (hk : o + k ≤ 3 * v.L.pl + v.L.ql) :
    Spec.Rsa.bytesAt s.mem (off v.key o) k = v.at o k := by
  rw [VD.at, ← h.kb, VG.Proof.Dsa.bytesAt_slice s.mem v.key hk]

theorem Base.p {v : VD} {s : State} (h : Base v s) :
    pOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at 0 v.L.pl) := by
  have := h.bytes (o := 0) (k := v.L.pl) (by omega)
  rw [off, BitVec.add_zero] at this
  rw [pOf, this]

theorem Base.q {v : VD} {s : State} (h : Base v s) :
    qOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at v.L.pl v.L.ql) := by
  rw [qOf, h.bytes (by omega)]

theorem Base.g {v : VD} {s : State} (h : Base v s) :
    gOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at (v.L.pl + v.L.ql) v.L.pl) := by
  rw [gOf, h.bytes (by omega)]

theorem Base.y {v : VD} {s : State} (h : Base v s) :
    yOf s.mem v.L v.key = Spec.Dsa.decodeBE (v.at (2 * v.L.pl + v.L.ql) v.L.pl) := by
  rw [yOf, h.bytes (by omega)]

/-- The registers every phase fixes: `r2` and those `Regs` reads. -/
def coreRegs : List Reg := [.r2, .r21, .r26, .r27, .r28]

/-- A phase: `Base`, `r2` holding the lengths with `qb v` as q's octets, and `X`. -/
def Ph (qb : VD → Nat) (X : VD → State → Prop) (v : VD) (s : State) : Prop :=
  Base v s ∧ s.gpr .r2 = pack v.L.pl v.L.ql (qb v) v.d ∧ X v s

theorem Ph.base {qb : VD → Nat} {X : VD → State → Prop} {v : VD} {s : State} (h : Ph qb X v s) : Base v s :=
  h.1

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
    (hw : (instrs c).all (fun i => dstOf i != some .r21) = true) (hn : c.noCalls = true) :
    RelCT isa (Two Φ) c (Two End) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨v, h₁, h₂, hsp⟩ := hp
  have hc : ∀ i ∈ instrs c, dstOf i ≠ some .r21 := fun i hi => by
    have := List.all_eq_true.mp hw i hi
    simpa using this
  exact ⟨ht, v, (Exec.gpr hc e₁ (.inl hn)).trans (h21 v _ h₁), (Exec.gpr hc e₂ (.inl hn)).trans (h21 v _ h₂),
    by rw [Exec.sp e₁, Exec.sp e₂, hsp]⟩

end VG.Proof.Dsa.PPC64LE
