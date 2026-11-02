module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
public import VerifiedGarbage.Proof.Rsa.AArch64.RdArgs
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
public import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdArgs
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the operations

`dpub`: the public data. `GC w X`: the working space at
the width `w k` (`G`), with facts `X` about the registers or memory, for the
public data and a public count (a loop's index). `CTW Φ Ψ c`: `c` leaks the
same in two runs from `Φ` with the same public data, and runs from `Φ` to
`Ψ`; it composes in sequence. Then each operation on arrays as a `CTW`
between `GC`s: the taint analysis checks it once `ws` has pinned `x0`, `x12`
and `x11` (`ws_ct0`), and its correctness gives the `GC` after it.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data: the working space, the pointers and lengths, `n`, `e`
and the writable regions. -/
structure DP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  deriving Inhabited

/-- The public part of the inputs. -/
def dpub (I : RpIn) : DP := ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure DOuts (I : RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : Apart I.pP I.k I.pQ I.k

/-- The public data and a public count. -/
abbrev Pub : Type := DP × Nat

/-- The working space at the width `w k`, and `X`. -/
def GC (w : Nat → Nat) (X : Pub → State → Prop) (a : Pub) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (c : Bool), dpub I = a.1 ∧ G I m₀ (w I.k) c s ∧ (RpLens I ∧ DOuts I) ∧ X a s

theorem GC.ws {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s : State} (h : GC w X a s) :
    Ws s a.1.B a.1.Z (w a.1.k) := by
  obtain ⟨I, m₀, c, e, g, -⟩ := h
  rw [← e]; exact g.ws

theorem GC.x {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s : State} (h : GC w X a s) : X a s := by
  obtain ⟨_, _, _, _, _, _, x⟩ := h
  exact x

theorem pins_GC {w : Nat → Nat} {X : Pub → State → Prop} : Pins (GC w X) [.x0] :=
  pins_ws (fun a => a.1.B) (fun a => a.1.Z) (fun a => w a.1.k) fun _ _ h => h.ws

/-! ## Leaking the same, and running -/

/-- `c` leaks the same from `Φ`, and runs from `Φ a` to `Ψ a`. -/
def CTW (Φ Ψ : Pub → State → Prop) (c : Prog isa) : Prop :=
  RelCT isa (Two Φ) c (fun _ _ => True) ∧ ∀ a s, Φ a s → WP isa c s (Ψ a)

theorem CTW.ct {Φ Ψ : Pub → State → Prop} {c : Prog isa} (h : CTW Φ Ψ c) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post h.1 h.2

theorem CTW.seq {Φ Ψ Ξ : Pub → State → Prop} {c₁ c₂ : Prog isa} (h₁ : CTW Φ Ψ c₁) (h₂ : CTW Ψ Ξ c₂) :
    CTW Φ Ξ (.seq c₁ c₂) :=
  ⟨RelCT.seq h₁.ct h₂.1, fun a s h => WP.seq (WP.mono (h₁.2 a s h) fun t ht => h₂.2 a t ht)⟩

theorem CTW.mono {Φ Φ' Ψ Ψ' : Pub → State → Prop} {c : Prog isa} (h : CTW Φ Ψ c) (hΦ : ∀ a s, Φ' a s → Φ a s)
    (hΨ : ∀ a s, Ψ a s → Ψ' a s) : CTW Φ' Ψ' c :=
  ⟨h.1.mono (fun _ _ h => two_mono hΦ h) fun _ _ h => h, fun a s h' => WP.mono (h.2 a s (hΦ a s h')) (hΨ a)⟩

/-- The leaks from a stronger start, with a stronger run. -/
theorem CTW.wp {Φ Φ' Ψ Ψ' : Pub → State → Prop} {c : Prog isa} (h : CTW Φ Ψ c) (hΦ : ∀ a s, Φ' a s → Φ a s)
    (hw : ∀ a s, Φ' a s → WP isa c s (Ψ' a)) : CTW Φ' Ψ' c :=
  ⟨h.1.mono (fun _ _ h => two_mono hΦ h) fun _ _ h => h, hw⟩

theorem CTW.cons {Φ Ψ Ξ : Pub → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (he : CTW Φ Ψ e) (hr : CTW Ψ Ξ (seqs l)) : CTW Φ Ξ (seqs (e :: l)) := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact he.seq hr

theorem CTW.one {Φ Ψ : Pub → State → Prop} {e : Prog isa} (he : CTW Φ Ψ e) : CTW Φ Ψ (seqs [e]) := he

theorem CTW.app {Φ Ψ Ξ : Pub → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (hA : CTW Φ Ψ (seqs a)) (hB : CTW Ψ Ξ (seqs b)) : CTW Φ Ξ (seqs (a ++ b)) :=
  ⟨RelCT.seqs_append ha hb (RelCT.seq hA.ct hB.1), fun p s h =>
    wp_seqs_append ha hb (WP.mono (hA.2 p s h) fun t ht => hB.2 p t ht)⟩

/-- `ws`, then code the taint analysis checks from `x0`, `x12` and `x11`. -/
theorem ws_ct0 {Φ : Pub → State → Prop} (B : Pub → Addr) (Z w : Pub → Nat) {rest : List Instr} {body : Prog isa}
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) body) fun _ _ => True :=
  RelCT.block_seq (RelCT.seq (two_post (Ψ := fun a t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal (B a) (w a) r)
    (two_taint [.x0] (pins_ws B Z w hws) (by taint_decide)) fun a s h => ws_pin (hws a s h))
    (two_taint [.x0, .x12, .x11] (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht))

/-- `ws_ct0` for a block. -/
theorem ws_blk0 {Φ : Pub → State → Prop} (B : Pub → Addr) (Z w : Pub → Nat) {rest : List Instr}
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true) :
    RelCT isa (Two Φ) (.block (ws ++ rest)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_post (Ψ := fun a t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal (B a) (w a) r)
    (two_taint [.x0] (pins_ws B Z w hws) (by taint_decide)) fun a s h => ws_pin (hws a s h))
    (two_taint [.x0, .x12, .x11] (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht))

/-- An operation starting with `ws`, between `GC`s. -/
theorem wsop {w w' : Nat → Nat} {X Y : Pub → State → Prop} {op : Prog isa} {rest : List Instr} {body : Prog isa}
    (e : op = .seq (.block (ws ++ rest)) body) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ a s, GC w X a s → WP isa op s (GC w' Y a)) : CTW (GC w X) (GC w' Y) op :=
  ⟨by rw [e]; exact ws_ct0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => w a.1.k) (fun _ _ h => h.ws) ht, hw⟩

/-- A block starting with `ws`, between `GC`s. -/
theorem wsblk {w w' : Nat → Nat} {X Y : Pub → State → Prop} {l rest : List Instr} (e : l = ws ++ rest)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true)
    (hw : ∀ a s, GC w X a s → WP isa (.block l) s (GC w' Y a)) : CTW (GC w X) (GC w' Y) (.block l) :=
  ⟨by rw [e]; exact ws_blk0 (fun a => a.1.B) (fun a => a.1.Z) (fun a => w a.1.k) (fun _ _ h => h.ws) ht, hw⟩

/-- A block the taint analysis checks from `x0`, between `GC`s. -/
theorem blk {w w' : Nat → Nat} {X Y : Pub → State → Prop} {l : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true)
    (hw : ∀ a s, GC w X a s → WP isa (.block l) s (GC w' Y a)) : CTW (GC w X) (GC w' Y) (.block l) :=
  ⟨two_taint [.x0] pins_GC ht, hw⟩

/-- Unpacking a `GC`. -/
theorem GC.elim {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s : State} {P : Prop} (h : GC w X a s)
    (k : ∀ (I : RpIn) (m₀ : Mem) (c : Bool), dpub I = a.1 → G I m₀ (w I.k) c s → RpLens I ∧ DOuts I → X a s → P) : P := by
  obtain ⟨I, m₀, c, e, g, L, x⟩ := h
  exact k I m₀ c e g L x

/-- A block that starts with `ws`. -/
theorem rws_drop {l : List Instr} (h : l.take 2 = ws) : l = ws ++ l.drop 2 := by
  rw [← h, List.take_append_drop]

/-! ## The operations -/

section ops

variable {w : Nat → Nat} {X Y : Pub → State → Prop}

theorem zeroA_w {j : Nat} (hj : j < 16)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) j) (8 * (w a.1.k + 2)) s.mem t.mem →
      Keep [.x11, .x12, .x8, .x7, .x14, .x16] s t → wv t.mem a.1.B (slot (w a.1.k) j) (w a.1.k + 2) = 0 → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc).isSome = true) :
    CTW (GC w X) (GC w Y) (zeroA j) :=
  wsop (by simp only [zeroA, List.append_assoc]) ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (zeroA_ok g.ws hj) fun t ⟨z, o, _, _, _, k⟩ =>
      ⟨I, m₀, c, rfl, g.out hj (Nat.le_refl _) o k (by decide), L, hXY _ s t h o k z⟩

theorem copyA_w {o b : Nat} (ho : o < 16) (hb : b < 16) (hob : o ≠ b)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) o) (8 * w a.1.k) s.mem t.mem →
      Keep [.x11, .x12, .x3, .x14, .x16, .x17] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base b .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    CTW (GC w X) (GC w Y) (copyA o b) :=
  wsop (by simp only [copyA, List.append_assoc]) ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (copyA_ok g.ws ho hb hob) fun t ⟨_, o', _, _, k⟩ =>
      ⟨I, m₀, c, rfl, g.out ho (by omega) o' k (by decide), L, hXY _ s t h o' k⟩

theorem setOneA_w {j : Nat} (hj : j < 16)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) j) 8 s.mem t.mem →
      Keep [.x11, .x12, .x16, .x3] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block ((setOneA j).drop 2)) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (.block (setOneA j)) :=
  wsblk (rws_drop (by simp [setOneA, ws])) ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    refine WP.mono (setOneA_ok g.ws hj) fun t ⟨hm, k⟩ => ?_
    have hw := g.ws
    have o := writeW_outside s.mem I.B (1 : BitVec 64) (d := slot (w I.k) j)
      (by have := hw.sl hj; have := hw.scr.nowrap; omega)
    rw [← hm] at o
    exact ⟨I, m₀, c, rfl, g.out hj (by omega) o k (by decide), L, hXY _ s t h o k⟩

theorem eqA_w {b₁ b₂ : Nat} (h₁ : b₁ < 16) (h₂ : b₂ < 16)
    (hXY : ∀ a s t, GC w X a s → t.mem = s.mem → Keep [.x11, .x12, .x9, .x14, .x16, .x17, .x3, .x4] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base b₁ .x16 ++ base b₂ .x17)) (countLoop .x14 xorBody))) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (seqs (eqA b₁ b₂)) :=
  wsop rfl ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (eqA_ok g.ws h₁ h₂) fun t ⟨_, hm, _, _, k⟩ =>
      ⟨I, m₀, c, rfl, g.same hm k (by decide), L, hXY _ s t h hm k⟩

theorem andZero_w (hXY : ∀ a s t, GC w X a s → Keep [.x3, .x4, .x7, .x15] s t → Y a t) :
    CTW (GC w X) (GC w Y) (.block andZero) :=
  blk (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (andZero_ok (z := s.gpr .x9 = 0) g.ws g.msk Iff.rfl) fun t ⟨⟨hm, _⟩, k⟩ =>
      ⟨I, m₀, _, rfl, g.store hm k (by decide), L, hXY _ s t h k⟩

theorem andMask_w (h15 : ∀ a s, GC w X a s → ∃ c, s.gpr .x15 = mask c)
    (hXY : ∀ a s t, GC w X a s → Keep [.x3] s t → Y a t) :
    CTW (GC w X) (GC w Y) (.block andMask) :=
  blk (by taint_decide) fun ⟨P, i⟩ s h => by
    obtain ⟨c', hc'⟩ := h15 _ s h
    exact h.elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (andMask_ok g hc') fun t ⟨g', _, k⟩ => ⟨I, m₀, _, rfl, g', L, hXY _ s t h k⟩

theorem setNar_w (hXY : ∀ a s t, GC w X a s → Frm a.1.B hdrW s.mem t.mem → Keep [.x3, .x4, .x12] s t → Y a t) :
    CTW (GC w X) (GC vk Y) (.block setNar) :=
  blk (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (g.setNar_ok L.1) fun t ⟨g', f, k⟩ => ⟨I, m₀, c, rfl, g', L, hXY _ s t h f k⟩

theorem setWid_w (hXY : ∀ a s t, GC w X a s → Frm a.1.B hdrW s.mem t.mem → Keep [.x3, .x4, .x12] s t → Y a t) :
    CTW (GC w X) (GC Wk Y) (.block setWid) :=
  blk (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (g.setWid_ok L.1) fun t ⟨g', f, k⟩ => ⟨I, m₀, c, rfl, g', L, hXY _ s t h f k⟩

/-- A block of register instructions, changing no memory. -/
theorem regs_w {l : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true) {rs : List Reg} (hr : .x0 ∉ rs)
    (hl : ∀ a s, GC w X a s → WP isa (.block l) s fun t => (t.mem = s.mem ∧ Y a t) ∧ Keep rs s t) :
    CTW (GC w X) (GC w Y) (.block l) :=
  blk ht fun a s h => WP.mono (hl a s h) fun _ ⟨⟨hm, y⟩, k⟩ => h.elim fun I m₀ c e g L _ =>
    ⟨I, m₀, c, e, g.same hm k hr, L, y⟩

theorem subA_w {o b₁ b₂ : Nat} (ho : o < 16) (h₁ : b₁ < 16) (h₂ : b₂ < 16) (d₁ : o ≠ b₁) (d₂ : o ≠ b₂)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) o) (8 * w a.1.k) s.mem t.mem →
      Keep [.x3, .x4, .x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t → (∃ c, t.gpr .x15 = mask c) →
      t.gpr .x7 = 0 → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] ++ base b₁ .x16 ++ base b₂ .x17 ++ base o .x13))
      (.seq (countLoop .x14 subBody) (.block carryMask))) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (subA o b₁ b₂) :=
  wsop (by simp only [subA, seqs, List.append_assoc]) ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (subA_ok g.ws ho h₁ h₂ d₁ d₂) fun t ⟨_, h15, h7, o', k⟩ =>
      ⟨I, m₀, c, rfl, g.out ho (by omega) o' k (by decide), L, hXY _ s t h o' k ⟨_, h15⟩ h7⟩

theorem addA_w {o b₁ b₂ : Nat} (ho : o < 16) (h₁ : b₁ < 16) (h₂ : b₂ < 16) (d₁ : o ≠ b₁) (d₂ : o ≠ b₂)
    (h15 : ∀ a s, GC w X a s → ∃ c, s.gpr .x15 = mask c)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) o) (8 * w a.1.k) s.mem t.mem →
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x11, .x12, .x14] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12,
      .adds .x .x3 .x7 .x7] ++ base b₁ .x10 ++ base b₂ .x8 ++ base o .x5)) (countLoop .x14 addMBody)) hc).isSome
      = true) :
    CTW (GC w X) (GC w Y) (addA o b₁ b₂) :=
  wsop (by simp only [addA, List.append_assoc]) ht fun ⟨P, i⟩ s h => by
    obtain ⟨c', hc'⟩ := h15 _ s h
    exact h.elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (addA_ok g.ws ho h₁ h₂ d₁ d₂ hc') fun t ⟨_, _, o', k⟩ =>
        ⟨I, m₀, c, rfl, g.out ho (by omega) o' k (by decide), L, hXY _ s t h o' k⟩

/-- `halfA o a`, with nothing about its result. -/
theorem halfA_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a : Nat} (ho : o < 16) (ha : a < 16) :
    WP isa (halfA o a) s fun t =>
      Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have so := h.sl ho
  have sa := h.sl ha
  have hw1 := h.w1
  have hw2 := h.w2
  have sp : slot w o = slot w a ∨ slot w a + 8 * (w + 1) ≤ slot w o ∨ slot w o + 8 * w ≤ slot w a := by
    by_cases e : o = a
    · left; rw [e]
    · right; have := slot_sep (w := w) e; omega
  unfold halfA
  refine WP.seq (WP.mono (pairSet_ok h a o) fun t₁ ⟨⟨h16, h17, h14, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (shr_ok (h.scr.congr k₁.wr) h16 h17 h14 (by omega) (by omega) (by omega) (by omega) sp)
    fun t ⟨_, _, o₂, k₂⟩ => ⟨by rw [m₁] at o₂; exact o₂, (k₁.trans k₂).mono (by decide)⟩

theorem halfA_w {o b : Nat} (ho : o < 16) (hb : b < 16)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) o) (8 * w a.1.k) s.mem t.mem →
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([mov .x14 .x12] ++ base b .x16 ++
      base o .x17)) (countLoop .x14 shrBody)) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (halfA o b) :=
  wsop (by simp only [halfA, List.append_assoc]) ht fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (halfA_frm g.ws ho hb) fun t ⟨o', k⟩ =>
      ⟨I, m₀, c, rfl, g.out ho (by omega) o' k (by decide), L, hXY _ s t h o' k⟩

theorem selA_w {o b : Nat} (ho : o < 16) (hb : b < 16) (hob : o ≠ b)
    (h15 : ∀ a s, GC w X a s → ∃ c, s.gpr .x15 = mask c)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) o) (8 * w a.1.k) s.mem t.mem →
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([mov .x14 .x12] ++ base b .x16 ++
      base o .x17)) VG.Impl.Rsa.AArch64.Crt.selLoop) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (selA o b) :=
  wsop (by simp only [selA, List.append_assoc]) ht fun ⟨P, i⟩ s h => by
    obtain ⟨c', hc'⟩ := h15 _ s h
    exact h.elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (selA_ok g.ws ho hb hob hc') fun t ⟨_, o', k⟩ =>
        ⟨I, m₀, c, rfl, g.out ho (by omega) o' k (by decide), L, hXY _ s t h o' k⟩

/-- The carry into `dblA`: from a state `cin` sees, with `x7 = 0` and the
registers `dblA` does not write before it. -/
def CInOf (cin : List Instr) (s : State) : Prop :=
  ∃ b, ∀ t : State, t.gpr .x7 = 0 → (∀ r, r ∉ [Reg.x11, .x12, .x7, .x14, .x16] → t.gpr r = s.gpr r) → CIn cin b t

theorem cin_c0 (s : State) : CInOf c0 s := ⟨false, fun t h7 _ => c0_ok t h7⟩

theorem cin_c1 (s : State) : CInOf c1 s := ⟨true, fun t h7 _ => c1_ok t h7⟩

theorem cin_cOf {s : State} {r : Reg} (hr : r = .x1 ∨ r = .x2) {b : Bool} (hv : s.gpr r = BitVec.ofNat 64 b.toNat) :
    CInOf (cOf r) s :=
  ⟨b, fun t _ hu => cOf_ok t hr ((hu r (by rcases hr with rfl | rfl <;> decide)).trans hv)⟩

theorem cin_mask {s : State} {c : Bool} (h15 : s.gpr .x15 = mask c) : CInOf [.adds .x .x3 .x15 .x15] s :=
  ⟨c, fun t _ hu => cMask_ok t ((hu .x15 (by decide)).trans h15)⟩

theorem dblA_w {b : Nat} (hb : b < 16) {cin : List Instr} (hcin : ∀ a s, GC w X a s → CInOf cin s)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) b) (8 * w a.1.k) s.mem t.mem →
      Keep [.x3, .x4, .x7, .x11, .x12, .x14, .x16] s t → t.gpr .x7 = 0 → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12] ++
      base b .x16 ++ cin)) (.seq (countLoop .x14 shlBody) (.block []))) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (dblA b cin []) :=
  wsop (by simp only [dblA, seqs, List.append_assoc]) ht fun ⟨P, i⟩ s h => by
    obtain ⟨bc, hbc⟩ := hcin _ s h
    exact h.elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (dbl_ok g.ws hb hbc) fun t ⟨_, h7, o', k⟩ =>
        ⟨I, m₀, c, rfl, g.out hb (by omega) o' k (by decide), L, hXY _ s t h o' k h7⟩

/-- The carry out of a doubling is a bit. -/
theorem carry_bit {x n : Nat} (hx : x < 2 ^ n) (b : Bool) :
    ∃ b' : Bool, BitVec.ofNat 64 ((2 * x + b.toNat) / 2 ^ n) = BitVec.ofNat 64 b'.toNat := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hq : (2 * x + b.toNat) / 2 ^ n < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | h
  · exact ⟨false, by rw [Nat.lt_one_iff.mp h]; rfl⟩
  · exact ⟨true, by rw [h]; rfl⟩

theorem dblc_w {b : Nat} (hb : b < 16) {cin : List Instr} (hcin : ∀ a s, GC w X a s → CInOf cin s) {r : Reg}
    (hr : r = .x1 ∨ r = .x2)
    (hXY : ∀ a s t, GC w X a s → Outside a.1.B (slot (w a.1.k) b) (8 * w a.1.k) s.mem t.mem →
      Keep [r, .x3, .x4, .x7, .x11, .x12, .x14, .x16] s t → t.gpr .x7 = 0 →
      (∃ b' : Bool, t.gpr r = BitVec.ofNat 64 b'.toNat) → Y a t)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12] ++
      base b .x16 ++ cin)) (.seq (countLoop .x14 shlBody) (.block (cTo r)))) hc).isSome = true) :
    CTW (GC w X) (GC w Y) (dblA b cin (cTo r)) :=
  wsop (by simp only [dblA, seqs, List.append_assoc]) ht fun ⟨P, i⟩ s h => by
    obtain ⟨bc, hbc⟩ := hcin _ s h
    exact h.elim fun I m₀ c e g L _ => by
      subst e
      have hr0 : Reg.x0 ∉ [r, .x3, .x4, .x7, .x11, .x12, .x14, .x16] := by rcases hr with rfl | rfl <;> decide
      exact WP.mono (dblc_ok g.ws hb hbc hr) fun t ⟨_, hv, h7, o', k⟩ =>
        ⟨I, m₀, c, rfl, g.out hb (by omega) o' k hr0, L, hXY _ s t h o' k h7 (by
          rw [hv]; exact carry_bit (wv_lt _ _ _ _) bc)⟩

theorem divmod_w {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16)
    (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hXY : ∀ a s t, GC w X a s → Frm a.1.B [ar (w a.1.k) iQ, ar (w a.1.k) iR, ar (w a.1.k) iT] s.mem t.mem →
      Keep (.x11 :: .x12 :: stepRegs) s t → Y a t)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base iR .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) hc₂).isSome = true) :
    CTW (GC w X) (GC w Y) (divmod iQ iR iD iT) := by
  have e : divmod iQ iR iD iT = .seq (zeroA iR) (.seq (.block [.lsl .x .x6 .x12 6])
      (.loop (VG.Impl.Rsa.AArch64.Keys.divStep iQ iR iD iT) (.nonzero .x .x6))) := rfl
  refine ⟨?_, fun ⟨P, i⟩ s h => h.elim fun I m₀ c eI g L _ => ?_⟩
  · rw [e]
    have hz := (zeroA_w (w := w) (X := X) (Y := fun _ _ => True) hR (fun _ _ _ _ _ _ _ => trivial) ht₁)
    exact (pin_seq [.x0, .x12, .x11] (Ψ := fun _ _ => True) (fun a => wsVal a.1.B (w a.1.k)) hz.1
      (fun ⟨P, i⟩ s h => h.elim fun I m₀ c eI g L _ => by
        subst eI
        exact WP.mono (zeroA_ok g.ws hR) fun _ ⟨_, _, h12, h11, _, k⟩ =>
          wsVal_of ((k.gpr .x0 (by decide)).trans g.ws.x0) h12 h11) ht₂ fun ⟨P, i⟩ s h =>
        h.elim fun I m₀ c eI g L _ => by
          subst eI
          rw [← e]
          exact WP.mono (divmod_ok g.ws hQ hR hD hT dQR dQD dQT dRD dRT dDT) fun _ _ => trivial).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  · subst eI
    have hw := g.ws
    have hn := hw.scr.nowrap
    have hZ := hw.hZ
    refine WP.mono (divmod_ok hw hQ hR hD hT dQR dQD dQT dRD dRT dDT) fun t ⟨_, f, k, _⟩ =>
      ⟨I, m₀, c, rfl, g.step f (fun r hr => ?_) (fun r hr => ?_) k (by decide), L, hXY _ s t h f k⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (simp only [slot, hdrBytes]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := hw.sl hQ; exact this
      · have := hw.sl hR; exact this
      · have := hw.sl hT; exact this

end ops

/-! ## Loops -/

theorem GC.imp {w : Nat → Nat} {X Y : Pub → State → Prop} {a b : Pub} {s : State} (h : GC w X a s)
    (hab : a.1 = b.1) (hx : X a s → Y b s) : GC w Y b s := by
  obtain ⟨I, m₀, c, e, g, L, x⟩ := h
  exact ⟨I, m₀, c, e.trans hab, g, L, hx x⟩

theorem cnt_sub {N i : Nat} (_hN : N < 2 ^ 64) (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The loop's count in `x6`, from `N` down. -/
def XL (N : DP → Nat) (X : DP → State → Prop) (a : Pub) (s : State) : Prop :=
  s.gpr .x6 = BitVec.ofNat 64 (N a.1 - a.2) ∧ X a.1 s

/-- After a step: the count less one. -/
def XL' (N : DP → Nat) (X : DP → State → Prop) (a : Pub) (s : State) : Prop :=
  s.gpr .x6 = BitVec.ofNat 64 (N a.1 - a.2) - BitVec.ofNat 64 1 ∧ X a.1 s

/-- A loop of `N` steps counted down in `x6`, its body a `CTW`. -/
theorem GC.nb {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s : State} (h : GC w X a s) {N : DP → Nat}
    (hN : ∀ I : RpIn, RpLens I → 0 < N (dpub I) ∧ N (dpub I) < 2 ^ 64) : 0 < N a.1 ∧ N a.1 < 2 ^ 64 := by
  obtain ⟨I, m₀, c, e, g, L, x⟩ := h
  rw [← e]; exact hN I L.1

theorem loop_w {w : Nat → Nat} {X : DP → State → Prop} (N : DP → Nat)
    (hN : ∀ I : RpIn, RpLens I → 0 < N (dpub I) ∧ N (dpub I) < 2 ^ 64)
    {body : Prog isa} (hb : CTW (GC w (XL N X)) (GC w (XL' N X)) body) :
    CTW (GC w fun a s => s.gpr .x6 = BitVec.ofNat 64 (N a.1) ∧ X a.1 s) (GC w fun a s => X a.1 s)
      (.loop body (.nonzero .x .x6)) := by
  refine ⟨?_, fun a s h => ?_⟩
  · have hl := two_loop (α := Pub) (Φ := fun a j s => GC w (XL N X) (a.1, j) s) (Ψ := GC w fun a s => X a.1 s)
      (fun a => N a.1) (body := body) (cond := .nonzero .x .x6)
      (two_map (fun p => (p.1.1, p.2)) (fun p s h => h.2) hb.1) fun a j s hj h => WP.mono (hb.2 _ s h)
        fun t ht => by
          obtain ⟨hN0, hN1⟩ : 0 < N a.1 ∧ N a.1 < 2 ^ 64 := h.nb hN
          have h6 : t.gpr .x6 = BitVec.ofNat 64 (N a.1 - (j + 1)) := by
            have := (GC.x ht).1; rw [this]; exact cnt_sub hN1 hj
          refine ⟨?_, fun hl => ht.imp rfl fun x => ⟨h6, x.2⟩, fun _ => ht.imp rfl fun x => x.2⟩
          rw [VG.Proof.MlKem.AArch64.eval_nonzero, h6]
          congr 1
          by_cases hc : j + 1 < N a.1
          · rw [decide_eq_true hc]
            simp only [bne_iff_ne, ne_eq]
            intro h0
            have := congrArg BitVec.toNat h0
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
            simp at this; omega
          · rw [decide_eq_false hc, show N a.1 - (j + 1) = 0 by omega]; rfl
    exact hl.mono (fun _ _ h => two_mono (fun a s h => ⟨(h.nb hN).1, h.imp rfl fun x => ⟨by rw [x.1]; rfl, x.2⟩⟩) h)
      fun _ _ _ => trivial
  · obtain ⟨hN0, hN1⟩ := h.nb hN
    refine WP.mono (wp_countdown (cnt := .x6) hN1 hN0 (fun i s => GC w (XL N X) (a.1, i) s)
      (fun i hi s hs h6 => WP.mono (hb.2 _ s hs) fun t ht => ⟨ht.imp rfl fun x => ⟨by rw [x.1]; exact cnt_sub hN1 hi, x.2⟩,
        by rw [(GC.x ht).1, h6]⟩) (h.imp rfl fun x => ⟨by rw [x.1]; rfl, x.2⟩) (GC.x h).1)
      fun t ht => ht.imp rfl fun x => x.2

end VG.Proof.Rsa.AArch64.Rd
