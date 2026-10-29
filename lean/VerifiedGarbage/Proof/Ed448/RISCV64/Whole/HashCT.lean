module

public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Hash
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT

/-!
# Ed448's whole functions on RISC-V: the hash in constant time

As on PPC64LE (`Proof/Ed448/PPC64LE/Whole/HashCT.lean`): two runs of
`hash` from states that agree on the registers it reads (`hashRegs`) and on
the stack pointer leak the same trace (`hash_ct`). The sponge functions save
and restore registers in their working space, which a taint analysis would
take to be secret afterwards, so their calls are related through their own
constant-time proofs (`Proof/Sha3/RISCV64/Stream/CallsCT.lean`), on the same
arguments in both runs (the positions being those of the same lengths); the
blocks that set their arguments access no memory, and the Keccak state is
zeroed through `sc` (the taint analysis).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64.Whole
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call
  absorbCall_ct padCall_ct squeezeCall_ct)

theorem absorbArgs_noMem (sc : Reg) (first : Bool) (p : Piece) : (absorbArgs sc first p).all noMem = true := by
  obtain ⟨b, o, l⟩ := p
  cases first <;> cases l <;> rfl

/-! ## What the hash keeps, and where it may run -/

/-- The permissions, the stack pointer and the callee-saved registers of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem Rg.refl (s : State) : Rg s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Rg.of {s₀ s s' : State} (hg : Rg s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Rg s₀ s' :=
  ⟨hrd.trans hg.rd, hwr.trans hg.wr, hsp.trans hg.sp, fun r hr => (hcs r hr).trans (hg.cs r hr)⟩

theorem Rg.only {s₀ s s' : State} (hg : Rg s₀ s) (h : Only s s') : Rg s₀ s' := hg.of h.rd h.wr h.sp h.cs

/-- The registers a piece reads. -/
def _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.regs (p : Piece) : List Reg :=
  p.base :: match p.len with
    | .imm _ => []
    | .reg r => [r]

/-- The registers `hash` reads. -/
def hashRegs (sc f : Reg) (ps : List Piece) : List Reg := sc :: f :: ps.flatMap Piece.regs

/-- A state `hash sc ps f o` may run from. -/
structure HashOk (sc f : Reg) (o : Nat) (ps : List Piece) (s : State) : Prop where
  psc : sc ∈ preserved
  pf : f ∈ preserved
  po : o < 2048
  ne : ps ≠ []
  env : KEnv (s.gpr sc) s
  ins : ∀ p ∈ ps, PieceOk (s.gpr sc) s p
  w : Covers [⟨s.gpr f + BitVec.ofNat 64 o, 114⟩] s.wr
  dsc : Region.Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, 114⟩ ⟨s.gpr sc, 8192⟩
  dsp : (below s.sp 1168).Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, 114⟩

/-- A piece of two states that agree on its registers. -/
theorem _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.agree {g₁ g₂ : Reg → BitVec 64} {p : Piece}
    (h : ∀ r ∈ p.regs, g₁ r = g₂ r) : p.addr g₁ = p.addr g₂ ∧ p.len.val g₁ = p.len.val g₂ := by
  obtain ⟨b, o, l⟩ := p
  refine ⟨by simp only [Piece.addr, h b (by simp [Piece.regs])], ?_⟩
  cases l with
  | imm n => rfl
  | reg r => exact congrArg BitVec.toNat (h r (by simp [Piece.regs]))

/-! ## The absorbs -/

/-- After the arguments of an `absorb` of piece `p` from position `X`. -/
structure KA (sc : Reg) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  a0 : s.gpr .a0 = s₀.gpr sc
  a1 : s.gpr .a1 = BitVec.ofNat 64 136
  a2 : s.gpr .a2 = BitVec.ofNat 64 X
  a3 : s.gpr .a3 = p.addr s₀.gpr
  a4 : s.gpr .a4 = BitVec.ofNat 64 (p.len.val s₀.gpr)

theorem ka_ok {sc : Reg} (hsc : sc ∈ preserved) {s₀ s : State} {first : Bool} {X : Nat} {p : Piece}
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) (hX : Pos first s = X) :
    WP isa (.block (absorbArgs sc first p)) s (KA sc p X s₀) :=
  WP.mono (absorbArgs_ok hsc first hp.base hp.off hp.len) fun s₁ ⟨o₁, g0, g1, g2, g3, g4⟩ =>
    ⟨hg.only o₁, by rw [g0, hg.cs _ hsc], g1, by
      rw [g2, ← hX]; cases first
      · show s.gpr .a0 = BitVec.ofNat 64 (s.gpr .a0).toNat; rw [ofNat_toNat]
      · rfl,
      by rw [g3, Piece.addr_eq hp.base hg.cs], by rw [g4, Len.val_eq hp.len hg.cs]⟩

theorem ka_args {sc : Reg} {s₀ s : State} {p : Piece} {X : Nat} (he : KEnv (s₀.gpr sc) s₀)
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hX : X < 136) (h : KA sc p X s₀ s) :
    AbsorbArgs s (s₀.gpr sc) (p.addr s₀.gpr) 136 X (p.len.val s₀.gpr) :=
  ⟨h.a0, h.a1, h.a2, h.a3, h.a4, rate136, hX, Len.val_lt _ hp.len, by rw [h.rg.sp]; exact he.spal,
    by rw [h.rg.sp]; exact he.sp, hp.dsc.sub_right (st_sub _), by rw [h.rg.sp]; exact he.d.sub_right (st_sub _),
    by rw [h.rg.sp]; exact hp.dsp⟩

theorem ka_covers {sc : Reg} {s₀ s : State} {p : Piece} (he : KEnv (s₀.gpr sc) s₀)
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) :
    Covers ([⟨p.addr s₀.gpr, p.len.val s₀.gpr⟩] ++ [⟨s₀.gpr sc, 200⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨s₀.gpr sc, 200⟩] s.wr := by
  have cw : Covers [⟨s₀.gpr sc, 200⟩] s.wr := by rw [hg.wr]; exact cov_st he.w
  exact ⟨cov_app (by rw [hg.rd, hg.wr]; exact hp.cov) (cov_right cw), cw⟩

theorem absorbs_ct {sc : Reg} (hsc : sc ∈ preserved) {s₀₁ s₀₂ : State} (he₁ : KEnv (s₀₁.gpr sc) s₀₁)
    (he₂ : KEnv (s₀₂.gpr sc) s₀₂) (hsp : s₀₁.sp = s₀₂.sp) (hsc' : s₀₁.gpr sc = s₀₂.gpr sc) :
    ∀ (ps : List Piece) (first : Bool) (X : Nat),
      (∀ p ∈ ps, PieceOk (s₀₁.gpr sc) s₀₁ p ∧ PieceOk (s₀₂.gpr sc) s₀₂ p) →
      (∀ p ∈ ps, ∀ r ∈ p.regs, s₀₁.gpr r = s₀₂.gpr r) → X < 136 →
      RelCT isa (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos first a = X ∧ Pos first b = X) (absorbs sc first ps)
        (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < 136 ∧ Pos (first && ps.isEmpty) a = Y ∧
          Pos (first && ps.isEmpty) b = Y)
  | [], first, X, _, _, hX =>
    RelCT.mono relct_nil (fun _ _ h => h) fun _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, X, hX, by simpa using h3, by simpa using h4⟩
  | p :: ps, first, X, hps, hrs, hX => by
    obtain ⟨hp₁, hp₂⟩ := hps p List.mem_cons_self
    obtain ⟨ea, el⟩ := Piece.agree (hrs p List.mem_cons_self)
    refine RelCT.seq (R := fun a b => KA sc p X s₀₁ a ∧ KA sc p X s₀₂ b)
      (relct_wp (relct_noMem (absorbArgs_noMem _ _ _)) fun a b hab =>
        ⟨ka_ok hsc hp₁ hab.1 hab.2.2.1, ka_ok hsc hp₂ hab.2.1 hab.2.2.2⟩) ?_
    refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = (X + p.len.val s₀₁.gpr) % 136 ∧
      Pos false b = (X + p.len.val s₀₁.gpr) % 136) ?_ ?_
    · refine RelCT.mono (relct_wp
        (F₁ := fun s' => Rg s₀₁ s' ∧ (s'.gpr .a0).toNat = (X + p.len.val s₀₁.gpr) % 136)
        (F₂ := fun s' => Rg s₀₂ s' ∧ (s'.gpr .a0).toNat = (X + p.len.val s₀₂.gpr) % 136)
        (absorbCall_ct (st := s₀₁.gpr sc) (pa := p.addr s₀₁.gpr) (pl := p.len.val s₀₁.gpr) (rate := 136)
          (pos := X)
          fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], ka_args he₁ hp₁ hX hab.1,
          by rw [hsc', ea, el]; exact ka_args he₂ hp₂ hX hab.2, (ka_covers he₁ hp₁ hab.1.rg).1,
          (ka_covers he₁ hp₁ hab.1.rg).2, by rw [hsc', ea, el]; exact (ka_covers he₂ hp₂ hab.2.rg).1,
          by rw [hsc']; exact (ka_covers he₂ hp₂ hab.2.rg).2⟩)
        fun a b hab =>
        ⟨absorb_call (ka_args he₁ hp₁ hX hab.1) (ka_covers he₁ hp₁ hab.1.rg).1 (ka_covers he₁ hp₁ hab.1.rg).2
          fun s' rd' wr' sp' cs' _ _ r' => ⟨hab.1.rg.of rd' wr' sp' cs', r'⟩,
         absorb_call (ka_args he₂ hp₂ hX hab.2) (ka_covers he₂ hp₂ hab.2.rg).1 (ka_covers he₂ hp₂ hab.2.rg).2
          fun s' rd' wr' sp' cs' _ _ r' => ⟨hab.2.rg.of rd' wr' sp' cs', r'⟩⟩)
        (fun _ _ h => h) fun _ _ ⟨⟨g₁, r₁⟩, ⟨g₂, r₂⟩⟩ => ⟨g₁, g₂, r₁, by rw [el]; exact r₂⟩
    · refine RelCT.mono (absorbs_ct hsc he₁ he₂ hsp hsc' ps false ((X + p.len.val s₀₁.gpr) % 136)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (fun q hq => hrs q (List.mem_cons_of_mem _ hq))
        (Nat.mod_lt _ (by decide))) (fun _ _ h => h)
        fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, by simpa using e₁, by simpa using e₂⟩

/-! ## The whole hash -/

/-- After the arguments of a `pad` from position `Y`. -/
structure PA (sc : Reg) (Y : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  a0 : s.gpr .a0 = s₀.gpr sc
  a1 : s.gpr .a1 = BitVec.ofNat 64 136
  a2 : s.gpr .a2 = BitVec.ofNat 64 Y

/-- After the arguments of the `squeeze`. -/
structure SA (sc f : Reg) (o : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  a0 : s.gpr .a0 = s₀.gpr sc
  a1 : s.gpr .a1 = BitVec.ofNat 64 136
  a2 : s.gpr .a2 = BitVec.ofNat 64 0
  a3 : s.gpr .a3 = s₀.gpr f + BitVec.ofNat 64 o
  a4 : s.gpr .a4 = BitVec.ofNat 64 114

theorem hash_regs {sc f : Reg} {ps : List Piece} {g₁ g₂ : Reg → BitVec 64}
    (h : ∀ r ∈ hashRegs sc f ps, g₁ r = g₂ r) :
    g₁ sc = g₂ sc ∧ g₁ f = g₂ f ∧ ∀ p ∈ ps, ∀ r ∈ p.regs, g₁ r = g₂ r :=
  ⟨h sc (by simp [hashRegs]), h f (by simp [hashRegs]), fun p hp r hr => h r (by
    simp only [hashRegs, List.mem_cons, List.mem_flatMap]; exact .inr (.inr ⟨p, hp, hr⟩))⟩

theorem hash_ct {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop}
    {hint : VG.Taint.Hint taint.T}
    (hz : (taint.check (Taint.ofRegs [sc]) (.block (Impl.Sha3.RISCV64.zeroState sc)) hint).isSome = true)
    (hP : ∀ a b, P a b → HashOk sc f o ps a ∧ HashOk sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r) :
    RelCT isa P (hash sc ps f o) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ HashOk sc f o ps x.1 ∧
    HashOk sc f o ps x.2 ∧ x.1.sp = x.2.sp ∧ ∀ r ∈ hashRegs sc f ps, x.1.gpr r = x.2.gpr r)
    (RelCT.exists_ fun ⟨s₀₁, s₀₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, hP a b h⟩) (fun _ _ h => h)
  by_cases hH : HashOk sc f o ps s₀₁ ∧ HashOk sc f o ps s₀₂ ∧ s₀₁.sp = s₀₂.sp ∧
    ∀ r ∈ hashRegs sc f ps, s₀₁.gpr r = s₀₂.gpr r
  swap
  · exact RelCT.of_false fun a b h => hH ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨h₁, h₂, hsp, hrg⟩ := hH
  obtain ⟨esc, ef, eps⟩ := hash_regs hrg
  have hsc := h₁.psc
  refine RelCT.mono (P := fun a b => a = s₀₁ ∧ b = s₀₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  unfold Impl.Ed448.RISCV64.Whole.hash
  -- The state set to zero.
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (taint_block [sc] (fun a b hab => by
      rw [hab.1, hab.2, hsp]) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, esc]) hz)
      fun a b hab => ⟨by rw [hab.1]; exact WP.mono (zeroState_ok hsc rfl h₁.env) fun _ h => ⟨h.1.rd, h.1.wr,
          h.1.sp, h.1.cs⟩,
        by rw [hab.2]; exact WP.mono (zeroState_ok hsc rfl h₂.env) fun _ h => ⟨h.1.rd, h.1.wr, h.1.sp, h.1.cs⟩⟩)
      (fun _ _ h => h) fun _ _ h => h) ?_
  -- The absorbs.
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < 136 ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.mono (absorbs_ct hsc h₁.env h₂.env hsp esc ps true 0 (fun p hp => ⟨h₁.ins p hp, h₂.ins p hp⟩) eps
      (by decide)) (fun _ _ h => ⟨h.1, h.2, rfl, rfl⟩) fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, ?_, ?_⟩) ?_
  · cases ps with
    | nil => exact absurd rfl h₁.ne
    | cons _ _ => exact e₁
  · cases ps with
    | nil => exact absurd rfl h₁.ne
    | cons _ _ => exact e₂
  -- The padding.
  refine RelCT.mono (P := fun a b => ∃ Y, Y < 136 ∧ Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.exists_ fun Y => ?_) (fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨Y, hY, g₁, g₂, e₁, e₂⟩) (fun _ _ h => h)
  by_cases hY : Y < 136
  swap
  · exact RelCT.of_false fun a b h => hY h.1
  have pa : ∀ (s₀ s : State), Rg s₀ s → Pos false s = Y → WP isa (.block (padArgs sc)) s (PA sc Y s₀) :=
    fun s₀ s hg hX => WP.mono (padArgs_ok hsc) fun _ ⟨o', g0, g1, g2, _⟩ =>
      ⟨hg.only o', by rw [g0, hg.cs _ hsc], g1,
        by rw [g2, ← hX, show Pos false s = (s.gpr .a0).toNat from rfl, ofNat_toNat]⟩
  refine RelCT.seq (R := fun a b => PA sc Y s₀₁ a ∧ PA sc Y s₀₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨pa _ _ hab.2.1 hab.2.2.2.1, pa _ _ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, KEnv (s₀.gpr sc) s₀ → PA sc Y s₀ s → PadArgs s (s₀.gpr sc) 136 Y := fun he h =>
    ⟨h.a0, h.a1, h.a2, rate136, hY, by rw [h.rg.sp]; exact he.spal, by rw [h.rg.sp]; exact he.sp,
      by rw [h.rg.sp]; exact he.d.sub_right (st_sub _)⟩
  have cK : ∀ {s₀ s : State}, KEnv (s₀.gpr sc) s₀ → Rg s₀ s →
      Covers ([] ++ [⟨s₀.gpr sc, 200⟩]) (s.rd ++ s.wr) ∧ Covers [⟨s₀.gpr sc, 200⟩] s.wr :=
    fun he hg => ⟨by rw [List.nil_append]; exact cov_right (by rw [hg.wr]; exact cov_st he.w),
      by rw [hg.wr]; exact cov_st he.w⟩
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (padCall_ct (st := s₀₁.gpr sc) (rate := 136) (pos := Y)
      fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hPA h₁.env hab.1, by rw [esc]; exact hPA h₂.env hab.2,
        (cK h₁.env hab.1.rg).1, (cK h₁.env hab.1.rg).2, by rw [esc]; exact (cK h₂.env hab.2.rg).1,
        by rw [esc]; exact (cK h₂.env hab.2.rg).2⟩) fun a b hab =>
      ⟨pad_call (hPA h₁.env hab.1) (cK h₁.env hab.1.rg).1 (cK h₁.env hab.1.rg).2
        fun s' rd' wr' sp' cs' _ _ => hab.1.rg.of rd' wr' sp' cs',
       pad_call (hPA h₂.env hab.2) (cK h₂.env hab.2.rg).1 (cK h₂.env hab.2.rg).2
        fun s' rd' wr' sp' cs' _ _ => hab.2.rg.of rd' wr' sp' cs'⟩)
      (fun _ _ h => h) fun _ _ h => h) ?_
  -- The squeeze.
  have sa : ∀ (s₀ s : State), Rg s₀ s → WP isa (.block (squeezeArgs sc f o)) s (SA sc f o s₀) :=
    fun s₀ s hg => WP.mono (squeezeArgs_ok hsc h₁.pf h₁.po) fun _ ⟨o', g0, g1, g2, g3, g4⟩ =>
      ⟨hg.only o', by rw [g0, hg.cs _ hsc], g1, g2, by rw [g3, hg.cs _ h₁.pf], g4⟩
  refine RelCT.seq (R := fun a b => SA sc f o s₀₁ a ∧ SA sc f o s₀₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨sa _ _ hab.1, sa _ _ hab.2⟩) ?_
  have hSA : ∀ {s₀ s : State}, HashOk sc f o ps s₀ → SA sc f o s₀ s →
      SqueezeArgs s (s₀.gpr sc) (s₀.gpr f + BitVec.ofNat 64 o) 136 0 114 :=
    fun hh h => ⟨h.a0, h.a1, h.a2, h.a3, h.a4, rate136, by decide, by decide,
      by rw [h.rg.sp]; exact hh.env.spal, by rw [h.rg.sp]; exact hh.env.sp, hh.dsc.symm.sub_left (st_sub _),
      by rw [h.rg.sp]; exact hh.env.d.sub_right (st_sub _), by rw [h.rg.sp]; exact hh.dsp⟩
  have cS : ∀ {s₀ s : State}, HashOk sc f o ps s₀ → Rg s₀ s →
      Covers [⟨s₀.gpr sc, 200⟩, ⟨s₀.gpr f + BitVec.ofNat 64 o, 114⟩] s.wr := fun hh hg => by
    rw [hg.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_st hh.env.w a n ⟨_, List.mem_cons_self, hc⟩
    · exact hh.w a n ⟨_, List.mem_cons_self, hc⟩
  exact squeezeCall_ct (st := s₀₁.gpr sc) (pa := s₀₁.gpr f + BitVec.ofNat 64 o) (rate := 136) (pl := 114)
    (pos := 0)
    fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hSA h₁ hab.1, by rw [esc, ef]; exact hSA h₂ hab.2,
      by rw [List.nil_append]; exact cov_right (cS h₁ hab.1.rg), cS h₁ hab.1.rg,
      by rw [esc, ef, List.nil_append]; exact cov_right (cS h₂ hab.2.rg), by rw [esc, ef]; exact cS h₂ hab.2.rg⟩

end VG.Proof.Ed448.RISCV64.Whole
