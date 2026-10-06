import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# Multiword arithmetic on AArch64: constant time

Two runs are related by `Two Φ` when both satisfy `Φ a` for the same public
data `a` (whatever their secrets), with the same stack pointer, which the
taint analysis's agreement includes. The pieces of code whose addresses and
branches depend only on registers that `Φ a` fixes are checked by the taint
analysis (`two_taint`); what each run satisfies afterwards follows from
correctness (`two_post`). Branches and loops whose conditions come from
public data the taint analysis cannot track (it is loaded from memory)
agree since `Φ a` fixes them (`two_ite`, `two_loop`).

`Mont` is what RSA's proofs need of an implementation of Montgomery
multiplication in the working space of `Impl/Bignum/Layout.lean`;
`Mont.base` is `montMul`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The working space at `B`, its base in `x0`, and the header. -/
structure Good (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  hdr : Hdr t.mem B w minv

/-! ## Relating two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (RegSet.mem_ofList.mp hr)⟩) h

/-- A piece checked by the taint analysis, with what correctness gives after it. -/
theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s₁ s₂ : State}
    (hp : Two Φ s₁ s₂) : Two Φ' s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := hp; ⟨a, h a _ h₁, h a _ h₂, hsp⟩

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

/-- A loop of `N a` iterations, its `j`-th from a state satisfying `Φ a j`,
whose condition after iteration `j` is whether `j + 1 < N a`. -/
theorem two_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop} (N : α → Nat)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two fun (p : α × Nat) s => p.2 < N p.1 ∧ Φ p.1 p.2 s) body fun _ _ => True)
    (hw : ∀ a j s, j < N a → Φ a j s → WP isa body s fun s' =>
      isa.eval cond s' = some (decide (j + 1 < N a)) ∧ (j + 1 < N a → Φ a (j + 1) s') ∧
      (j + 1 = N a → Ψ a s')) :
    RelCT isa (Two fun a s => 0 < N a ∧ Φ a 0 s) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a j, n = N a - j ∧ j < N a ∧ Φ a j s₁ ∧ Φ a j s₂ ∧ s₁.sp = s₂.sp) (fun n => by
      have hp := two_post (Φ := fun (p : α × Nat) s => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ Φ p.1 p.2 s)
        (Ψ := fun p s' => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ isa.eval cond s' = some (decide (p.2 + 1 < N p.1)) ∧
          (p.2 + 1 < N p.1 → Φ p.1 (p.2 + 1) s') ∧ (p.2 + 1 = N p.1 → Ψ p.1 s'))
        (two_map id (fun p s h => ⟨h.1, h.2.2⟩) hct)
        fun p s h => WP.mono (hw p.1 p.2 s h.1 h.2.2) fun s' h' => ⟨h.1, h.2.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, j, hn, hj, h₁, h₂, hsp⟩ => ⟨(a, j), ⟨hj, hn, h₁⟩, ⟨hj, hn, h₂⟩, hsp⟩) ?_
      rintro s₁ s₂ ⟨⟨a, j⟩, ⟨hj, hn, e₁, f₁, g₁⟩, ⟨-, -, e₂, f₂, g₂⟩, hsp⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have : ¬ j + 1 < N a := by rw [e₁] at h; simpa using h
        have hjN : j + 1 = N a := by simp only at hj this; omega
        exact ⟨a, g₁ hjN, g₂ hjN, hsp⟩
      · have hlt : j + 1 < N a := by rw [e₁] at h; simpa using h
        exact ⟨N a - (j + 1), by simp only at hn; omega, a, j + 1, rfl, hlt, f₁ hlt, f₂ hlt, hsp⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, ⟨h0, h₁⟩, ⟨-, h₂⟩, hsp⟩ := hp
  exact key (N a - 0) _ _ _ _ _ _ ⟨a, 0, rfl, h0, h₁, h₂, hsp⟩ e₁ e₂

/-! ## Montgomery multiplication -/

/-- The working space, its header and its size: the public data of
`montMul`. -/
structure Lay where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64

/-- The working space and its header, for `montMul`. -/
def GoodL (L : Lay) (s : State) : Prop := Good s L.B L.Z L.w L.minv ∧ slot L.w 8 ≤ L.Z

/-- The working space and its size, without `-m⁻¹`: what `montMul`'s
timing depends on, so that runs with different (secret) moduli agree. -/
structure Ws where
  B : Addr
  Z : Nat
  w : Nat

/-- The working space and its header, for some `-m⁻¹`. -/
def GoodW (L : Ws) (s : State) : Prop := ∃ minv, Good s L.B L.Z L.w minv ∧ slot L.w 8 ≤ L.Z

/-- The working space of a layout. -/
abbrev Lay.ws (L : Lay) : Ws := ⟨L.B, L.Z, L.w⟩

theorem GoodL.goodW {L : Lay} {s : State} (h : GoodL L s) : GoodW L.ws s := ⟨L.minv, h⟩

/-- A multiplication constant time for any `-m⁻¹` is for a fixed one. -/
theorem RelCT.ofW {c : Prog isa} (h : RelCT isa (Two GoodW) c fun _ _ => True) :
    RelCT isa (Two GoodL) c fun _ _ => True :=
  two_map Lay.ws (fun _ _ h => h.goodW) h

/-- After `bases`: the bases and `w` in registers, and `x7 = 0`. -/
def BasesL (mo acc tmp o a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .x8 = off L.B (slot L.w acc) ∧ t.gpr .x9 = off L.B (slot L.w b) ∧
  t.gpr .x10 = off L.B (slot L.w mo) ∧ t.gpr .x11 = off L.B (slot L.w a) ∧
  t.gpr .x5 = off L.B (slot L.w o) ∧ t.gpr .x6 = off L.B (slot L.w tmp) ∧
  t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0

theorem pins_bases (mo acc tmp o a b : Nat) :
    Pins (BasesL mo acc tmp o a b) [.x8, .x9, .x10, .x11, .x5, .x6, .x12, .x7] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]
  · rw [i₁, i₂]

theorem pins_good : Pins GoodL [.x0] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.1.x0, h₂.1.x0]

theorem pins_goodW : Pins GoodW [.x0] := by
  intro L s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.x0, h₂.x0]

/-- What `montMul` does after its bases, checked by the taint analysis. -/
theorem mmTail_ct (mo acc tmp o a b : Nat) :
    RelCT isa (Two (BasesL mo acc tmp o a b)) (.seq zeroAcc (.seq rounds (.seq subMod selectAcc)))
      fun _ _ => True :=
  two_taint _ (pins_bases mo acc tmp o a b) (by taint_decide)

/-- `montMul` is constant time, given that the taint analysis checks its
`bases` from `x0`. -/
theorem montMul_ctW {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (bases o a b mo acc tmp)) hc).isSome = true) :
    RelCT isa (Two GoodW) (montMul mo acc tmp o a b) fun _ _ => True := by
  unfold montMul
  refine RelCT.seq (two_piece (Ψ := BasesL mo acc tmp o a b) _ pins_goodW h fun L s ⟨_, hs, hZ⟩ => ?_)
    (mmTail_ct mo acc tmp o a b)
  exact WP.mono (bases_ok hs.scr hs.x0 hs.hdr hZ ho ha hb hmo hacc htmp)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7, _, h9, _⟩, _⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩

/-! ## Implementations of Montgomery multiplication -/

open VG.Impl.Bignum.Public

/-- The multiplications RSA makes, `[o] = [a] [b] R⁻¹ mod m`: those of the
public-key operation, then the others of the private-key operation (whose
prime workspaces name arrays 1, 4 and 5 differently: its chunk, `x` and
`T`; the last builds the exponentiation's table, `T := T x`), as on x86-64. -/
def MmUse (o a b : Nat) : Prop :=
  (o = aR2 ∧ a = aR2 ∧ b = aR2) ∨ (o = aY ∧ a = aY ∧ b = aY) ∨ (o = aY ∧ a = aY ∧ b = aXm) ∨
  (o = aY ∧ a = aR2 ∧ b = aOne) ∨ (o = aXm ∧ a = aX ∧ b = aR2) ∨ (o = aY ∧ a = aY ∧ b = aOne) ∨
  (o = aR2 ∧ a = aR2 ∧ b = aOne) ∨ (o = aXm ∧ a = aX ∧ b = aOne) ∨ (o = aXm ∧ a = aY ∧ b = aR2) ∨
  (o = aY ∧ a = aXm ∧ b = aY) ∨ (o = aX ∧ a = aX ∧ b = aR2) ∨ (o = aX ∧ a = aX ∧ b = aY) ∨
  (o = aY ∧ a = aXm ∧ b = aX) ∨ (o = aXm ∧ a = aXm ∧ b = aR2)

/-- An implementation `mm o a b` of Montgomery multiplication in the working
space of the public-key operation (with `m` in array `aN` and working arrays
`aAcc` and `aTmp`), what RSA's proofs need of it: `[o] = [a] [b] R⁻¹ mod m`
changing only `aAcc`, `aTmp` and `o` and the registers `mmRegs`, and
constant time for each multiplication RSA makes, whatever the modulus. The
baseline `montMul` (`Mont.base`), or one for other CPU features. -/
structure Mont where
  mm : Nat → Nat → Nat → Prog isa
  ok : ∀ {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}, Good t B Z w minv → slot w 8 ≤ Z → 2 ≤ w →
    w < 2 ^ 31 → ∀ {o a b : Nat}, o < 8 → a < 8 → b < 8 → o ≠ aAcc → o ≠ aTmp → a ≠ aAcc → a ≠ aTmp →
    b ≠ aAcc → b ≠ aTmp → ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
    wv t.mem B (slot w b) w < wv t.mem B (slot w aN) w →
    WP isa (mm o a b) t fun t' =>
      Good t' B Z w minv ∧ wv t'.mem B (slot w o) w < wv t.mem B (slot w aN) w ∧
      wv t'.mem B (slot w o) w * 2 ^ (64 * w) % wv t.mem B (slot w aN) w =
        wv t.mem B (slot w a) w * wv t.mem B (slot w b) w % wv t.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ Keep mmRegs t t'
  ct : ∀ {o a b : Nat}, MmUse o a b → RelCT isa (Two GoodW) (mm o a b) fun _ _ => True

/-- `M.mm o a b` is constant time for a fixed modulus. -/
theorem Mont.ctL (M : Mont) {o a b : Nat} (h : MmUse o a b) :
    RelCT isa (Two GoodL) (M.mm o a b) fun _ _ => True :=
  RelCT.ofW (M.ct h)

/-- `M.mm o a b`, for arrays that are not `aAcc` or `aTmp`. -/
theorem Mont.mm_ok (M : Mont) {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc)
    (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem B (slot w b) w < wv t.mem B (slot w aN) w) (d5 : a ≠ aTmp := by decide)
    (d6 : b ≠ aTmp := by decide) :
    WP isa (M.mm o a b) t fun t' =>
      Good t' B Z w minv ∧ wv t'.mem B (slot w o) w < wv t.mem B (slot w aN) w ∧
      wv t'.mem B (slot w o) w * 2 ^ (64 * w) % wv t.mem B (slot w aN) w =
        wv t.mem B (slot w a) w * wv t.mem B (slot w b) w % wv t.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ Keep mmRegs t t' :=
  M.ok hg hZ hw hw' ho ha hb d1 d2 d3 d5 d4 d6 hinv hB

theorem mm_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x0]) (.block (bases o a b aN aAcc aTmp)) hc).isSome = true) :
    RelCT isa (Two GoodW) (Public.mm o a b) fun _ _ => True :=
  montMul_ctW (by decide) (by decide) (by decide) ho ha hb h

/-- The baseline: `montMul` with `m`, the accumulator and the temporary of
the public-key operation (`mm`). -/
def Mont.base : Mont where
  mm := Public.mm
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 _ d4 _ hinv hB :=
    WP.mono (montMul_ok hg.scr hg.x0 hg.hdr hZ hw hw' (by decide) (by decide) (by decide) ho ha hb (by decide)
      (by decide) (Ne.symm d1) (Ne.symm d3) (Ne.symm d4) (by decide) (Ne.symm d2) hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mm_ct (by decide) (by decide) (by decide) (by taint_decide)

end VG.Proof.Bignum.AArch64
