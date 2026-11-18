module

-- separate module: built in parallel with `Sign/Inst` and `Verify/Inst`, which `Inst` also imports
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Message
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Message.Common
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.Message
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Sign
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Sign
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Pieces
public import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Pieces
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT

/-! ### `MlDsa.RISCV64.Message.VerifyCT`, which only this module used -/

section

/-! ### `MlDsa.RISCV64.Message.SignCT`, which this module and modules that import it used -/

section

/-! ### `Sha3.RISCV64.PiecesCT`, which this module and modules that import it used -/

section

/-!
# SHAKE256 of pieces on RISC-V, in constant time

As on PPC64LE (`Proof/Sha3/PPC64LE/PiecesCT.lean`), and as Ed448's whole
functions' hash (`Proof/Ed448/RISCV64/Whole/HashCT.lean`), for any output
length: two runs of `hash` from states that agree on the registers it reads
(`hashRegs`) and on the stack pointer leak the same trace (`hash_ct`). The
sponge functions' calls are related through their own constant-time proofs
(`Proof/Sha3/RISCV64/Stream/CallsCT.lean`), on the same arguments in both
runs; the blocks that set their arguments access no memory, and the Keccak
state is zeroed through `sc` (the taint analysis).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Pieces

open VG VG.RISCV64 VG.Impl.Sha3.RISCV64.Pieces
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

theorem Rg.of {s₀ s s' : State} (hg : Rg s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Rg s₀ s' :=
  ⟨hrd.trans hg.rd, hwr.trans hg.wr, hsp.trans hg.sp, fun r hr => (hcs r hr).trans (hg.cs r hr)⟩

theorem Rg.only {s₀ s s' : State} (hg : Rg s₀ s) (h : Only s s') : Rg s₀ s' := hg.of h.rd h.wr h.sp h.cs

/-- The registers a piece reads. -/
def _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.regs (p : Piece) : List Reg :=
  p.base :: match p.len with
    | .imm _ => []
    | .reg r => [r]

/-- The registers `hash` reads. -/
def hashRegs (sc f : Reg) (ps : List Piece) : List Reg := sc :: f :: ps.flatMap Piece.regs

/-- A state `hash sc ps f o` may run from. -/
structure HashOk (N n : Nat) (sc f : Reg) (o : Nat) (ps : List Piece) (s : State) : Prop where
  psc : sc ∈ preserved
  pf : f ∈ preserved
  po : o < 2048
  pn : n < 2048
  ne : ps ≠ []
  env : KEnv N (s.gpr sc) s
  ins : ∀ p ∈ ps, PieceOk N (s.gpr sc) s p
  w : Covers [⟨s.gpr f + BitVec.ofNat 64 o, n⟩] s.wr
  dsc : Region.Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, n⟩ ⟨s.gpr sc, N⟩
  dsp : (below s.sp 1168).Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, n⟩

/-- A piece of two states that agree on its registers. -/
theorem _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.agree {g₁ g₂ : Reg → BitVec 64} {p : Piece}
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

theorem ka_ok {N : Nat} {sc : Reg} (hsc : sc ∈ preserved) {s₀ s : State} {first : Bool} {X : Nat} {p : Piece}
    (hp : PieceOk N (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) (hX : Pos first s = X) :
    WP isa (.block (absorbArgs sc first p)) s (KA sc p X s₀) :=
  WP.mono (absorbArgs_ok hsc first hp.base hp.off hp.len) fun s₁ ⟨o₁, g0, g1, g2, g3, g4⟩ =>
    ⟨hg.only o₁, by rw [g0, hg.cs _ hsc], g1, by
      rw [g2, ← hX]; cases first
      · show s.gpr .a0 = BitVec.ofNat 64 (s.gpr .a0).toNat; rw [ofNat_toNat]
      · rfl,
      by rw [g3, Piece.addr_eq hp.base hg.cs], by rw [g4, Len.val_eq hp.len hg.cs]⟩

theorem ka_args {N : Nat} {sc : Reg} {s₀ s : State} {p : Piece} {X : Nat} (he : KEnv N (s₀.gpr sc) s₀)
    (hp : PieceOk N (s₀.gpr sc) s₀ p) (hX : X < 136) (h : KA sc p X s₀ s) :
    AbsorbArgs s (s₀.gpr sc) (p.addr s₀.gpr) 136 X (p.len.val s₀.gpr) :=
  ⟨h.a0, h.a1, h.a2, h.a3, h.a4, rate136, hX, Len.val_lt _ hp.len, by rw [h.rg.sp]; exact he.spal,
    by rw [h.rg.sp]; exact he.sp, hp.dsc.sub_right (st_sub _ he.big), by rw [h.rg.sp]; exact he.d.sub_right (st_sub _ he.big),
    by rw [h.rg.sp]; exact hp.dsp⟩

theorem ka_covers {N : Nat} {sc : Reg} {s₀ s : State} {p : Piece} (he : KEnv N (s₀.gpr sc) s₀)
    (hp : PieceOk N (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) :
    Covers ([⟨p.addr s₀.gpr, p.len.val s₀.gpr⟩] ++ [⟨s₀.gpr sc, 200⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨s₀.gpr sc, 200⟩] s.wr := by
  have cw : Covers [⟨s₀.gpr sc, 200⟩] s.wr := by rw [hg.wr]; exact cov_st he.big he.w
  exact ⟨cov_app (by rw [hg.rd, hg.wr]; exact hp.cov) (cov_right cw), cw⟩

theorem absorbs_ct {N : Nat} {sc : Reg} (hsc : sc ∈ preserved) {s₀₁ s₀₂ : State} (he₁ : KEnv N (s₀₁.gpr sc) s₀₁)
    (he₂ : KEnv N (s₀₂.gpr sc) s₀₂) (hsp : s₀₁.sp = s₀₂.sp) (hsc' : s₀₁.gpr sc = s₀₂.gpr sc) :
    ∀ (ps : List Piece) (first : Bool) (X : Nat),
      (∀ p ∈ ps, PieceOk N (s₀₁.gpr sc) s₀₁ p ∧ PieceOk N (s₀₂.gpr sc) s₀₂ p) →
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
structure SA (n : Nat) (sc f : Reg) (o : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  a0 : s.gpr .a0 = s₀.gpr sc
  a1 : s.gpr .a1 = BitVec.ofNat 64 136
  a2 : s.gpr .a2 = BitVec.ofNat 64 0
  a3 : s.gpr .a3 = s₀.gpr f + BitVec.ofNat 64 o
  a4 : s.gpr .a4 = BitVec.ofNat 64 n

theorem hash_regs {sc f : Reg} {ps : List Piece} {g₁ g₂ : Reg → BitVec 64}
    (h : ∀ r ∈ hashRegs sc f ps, g₁ r = g₂ r) :
    g₁ sc = g₂ sc ∧ g₁ f = g₂ f ∧ ∀ p ∈ ps, ∀ r ∈ p.regs, g₁ r = g₂ r :=
  ⟨h sc (by simp [hashRegs]), h f (by simp [hashRegs]), fun p hp r hr => h r (by
    simp only [hashRegs, List.mem_cons, List.mem_flatMap]; exact .inr (.inr ⟨p, hp, hr⟩))⟩

theorem hash_ct {N n : Nat} {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop}
    {hint : VG.Taint.Hint taint.T}
    (hz : (taint.check (Taint.ofRegs [sc]) (.block (Impl.Sha3.RISCV64.zeroState sc)) hint).isSome = true)
    (hP : ∀ a b, P a b → HashOk N n sc f o ps a ∧ HashOk N n sc f o ps b ∧ a.sp = b.sp ∧
      ∀ r ∈ hashRegs sc f ps, a.gpr r = b.gpr r) :
    RelCT isa P (hash sc ps f o n) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ HashOk N n sc f o ps x.1 ∧
    HashOk N n sc f o ps x.2 ∧ x.1.sp = x.2.sp ∧ ∀ r ∈ hashRegs sc f ps, x.1.gpr r = x.2.gpr r)
    (RelCT.exists_ fun ⟨s₀₁, s₀₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, hP a b h⟩) (fun _ _ h => h)
  by_cases hH : HashOk N n sc f o ps s₀₁ ∧ HashOk N n sc f o ps s₀₂ ∧ s₀₁.sp = s₀₂.sp ∧
    ∀ r ∈ hashRegs sc f ps, s₀₁.gpr r = s₀₂.gpr r
  swap
  · exact RelCT.of_false fun a b h => hH ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨h₁, h₂, hsp, hrg⟩ := hH
  obtain ⟨esc, ef, eps⟩ := hash_regs hrg
  have hsc := h₁.psc
  refine RelCT.mono (P := fun a b => a = s₀₁ ∧ b = s₀₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  unfold Impl.Sha3.RISCV64.Pieces.hash
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
  have hPA : ∀ {s₀ s : State}, KEnv N (s₀.gpr sc) s₀ → PA sc Y s₀ s → PadArgs s (s₀.gpr sc) 136 Y := fun he h =>
    ⟨h.a0, h.a1, h.a2, rate136, hY, by rw [h.rg.sp]; exact he.spal, by rw [h.rg.sp]; exact he.sp,
      by rw [h.rg.sp]; exact he.d.sub_right (st_sub _ he.big)⟩
  have cK : ∀ {s₀ s : State}, KEnv N (s₀.gpr sc) s₀ → Rg s₀ s →
      Covers ([] ++ [⟨s₀.gpr sc, 200⟩]) (s.rd ++ s.wr) ∧ Covers [⟨s₀.gpr sc, 200⟩] s.wr :=
    fun he hg => ⟨by rw [List.nil_append]; exact cov_right (by rw [hg.wr]; exact cov_st he.big he.w),
      by rw [hg.wr]; exact cov_st he.big he.w⟩
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
  have sa : ∀ (s₀ s : State), Rg s₀ s → WP isa (.block (squeezeArgs sc f o n)) s (SA n sc f o s₀) :=
    fun s₀ s hg => WP.mono (squeezeArgs_ok hsc h₁.pf h₁.po h₁.pn) fun _ ⟨o', g0, g1, g2, g3, g4⟩ =>
      ⟨hg.only o', by rw [g0, hg.cs _ hsc], g1, g2, by rw [g3, hg.cs _ h₁.pf], g4⟩
  refine RelCT.seq (R := fun a b => SA n sc f o s₀₁ a ∧ SA n sc f o s₀₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨sa _ _ hab.1, sa _ _ hab.2⟩) ?_
  have hSA : ∀ {s₀ s : State}, HashOk N n sc f o ps s₀ → SA n sc f o s₀ s →
      SqueezeArgs s (s₀.gpr sc) (s₀.gpr f + BitVec.ofNat 64 o) 136 0 n :=
    fun hh h => ⟨h.a0, h.a1, h.a2, h.a3, h.a4, rate136, by decide, by have := hh.pn; omega_using [this],
      by rw [h.rg.sp]; exact hh.env.spal, by rw [h.rg.sp]; exact hh.env.sp, hh.dsc.symm.sub_left (st_sub _ hh.env.big),
      by rw [h.rg.sp]; exact hh.env.d.sub_right (st_sub _ hh.env.big), by rw [h.rg.sp]; exact hh.dsp⟩
  have cS : ∀ {s₀ s : State}, HashOk N n sc f o ps s₀ → Rg s₀ s →
      Covers [⟨s₀.gpr sc, 200⟩, ⟨s₀.gpr f + BitVec.ofNat 64 o, n⟩] s.wr := fun hh hg => by
    rw [hg.wr]
    intro a m ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_st hh.env.big hh.env.w a m ⟨_, List.mem_cons_self, hc⟩
    · exact hh.w a m ⟨_, List.mem_cons_self, hc⟩
  exact squeezeCall_ct (st := s₀₁.gpr sc) (pa := s₀₁.gpr f + BitVec.ofNat 64 o) (rate := 136) (pl := n)
    (pos := 0)
    fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hSA h₁ hab.1, by rw [esc, ef]; exact hSA h₂ hab.2,
      by rw [List.nil_append]; exact cov_right (cS h₁ hab.1.rg), cS h₁ hab.1.rg,
      by rw [esc, ef, List.nil_append]; exact cov_right (cS h₂ hab.2.rg), by rw [esc, ef]; exact cS h₂ hab.2.rg⟩

end VG.Proof.Sha3.RISCV64.Pieces

end

end

/-!
# ML-DSA on RISC-V, `sign_message`: constant time

Two runs from states that satisfy `MSPre` and agree on the arguments in
registers, the stack pointer and `signMessageLeak` (`MSPub`) leak the same
trace (`signMessage_ct`): the length check and the branch on it from
`ctx_len`; the setup from the arguments (`enter_taint`); the hash of `μ` by
`hash_ct`, from the registers the invariant gives the same values in both
runs; the arguments of the call and the restores by the taint analysis
(`ct_prog`); and the call of the signing function on `μ` by its own
constant time, whose leakage `signLeak` of the key, `μ` and the randomness
is `signMessageLeak` of the inputs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Sha3.RISCV64.Pieces (Piece hash)
open VG.Proof.Sha3.RISCV64.Pieces (HashOk hashRegs hash_ct)
open VG.RISCV64.Steps (Upd)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Code the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem ct_prog {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T} (h : (VG.RISCV64.taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- The argument registers of `sign_message`. -/
abbrev mArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The setup, from the arguments, for any parameter set: the taint analysis reads no immediate. -/
theorem enter_taint (p : Params) : (VG.RISCV64.taint.check (Taint.ofRegs mArgs)
    (.block (enter .a7 p signRegs signMs))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs mArgs) (.block (enter .a7 mlDsa44 signRegs signMs)))).isSome =
    true := rfl

/-- What two runs agree on: `signMessageContract`'s public part. -/
def MSPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    signMessageLeak p (skB p s₁) (msgB s₁) (ctxB s₁) (rndB s₁) =
      signMessageLeak p (skB p s₂) (msgB s₂) (ctxB s₂) (rndB s₂) ∧
    ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r

theorem signV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ signRegs, signV p s₁ r = signV p s₂ r := by
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 8 exact h _ (by decide)
  show eAt p (s₁.gpr .a7) = eAt p (s₂.gpr .a7)
  rw [h .a7 (by decide)]

theorem sinv_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} (h : ∀ r ∈ mArgs, s₁.gpr r = s₂.gpr r)
    (ha : SInv p STK s₁ a) (hb : SInv p STK s₂ b) : ∀ r ∈ signRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((signV_eq h r hr).trans (hb.regs r hr).symm)

/-- The hash of `μ` may run. -/
theorem ms1_hashOk {p : Params} {q : Bool} {STK : Nat} {s t : State} (hF : MFacts p) (hp : MSPre p q STK s) (h48 : 1168 ≤ STK)
    (h : MS1 p STK s t) :
    HashOk 840 64 .s8 .s8 oMU ((⟨.s0, 64, .imm 64⟩ : Piece) :: fmtPieces) t := by
  have hi := h.inv
  obtain ⟨ke, hin⟩ := signHash_env hF hp h48 hi
  have g30 := s_e hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact ke, by rw [g30]; exact hin,
    by rw [g30]; exact e_cov hp hi.wr (by decide), by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (below48 hp h48)).sub_right (e_sub (by decide))⟩

theorem signMessage_ct {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.signEK p q stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MSPre p q STK) (MSPub p) (signMessage n f p) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MSPre p q STK x.1 ∧ MSPre p q STK x.2 ∧
    MSPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : MSPre p q STK s₁ ∧ MSPre p q STK s₂ ∧ MSPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, psp, pl, pr⟩ := hH
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  unfold signMessage top
  -- The length check.
  refine RelCT.seq (R := fun a b => a = s₁.write .t1 (s₁.gpr .a4 >>> 8) ∧ b = s₂.write .t1 (s₂.gpr .a4 >>> 8))
    (RelCT.mono (relct_wp (ct_prog [.a4] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p7]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (Upd.write _ _ _).gpr, (Upd.write _ _ _).gpr, p7]) ?_ ?_
  · by_cases hcl : (s₁.gpr .a4).toNat < 256
    swap
    · refine RelCT.of_false fun a b ⟨hab, hc⟩ => hcl ?_
      rw [hab.1, eval_zero, (Upd.write _ _ _).gpr, shr8_zero] at hc
      exact of_decide_eq_true (Option.some.inj hc)
    have hcl₂ : (s₂.gpr .a4).toNat < 256 := by rw [← p7]; exact hcl
    have hu₁ := Upd.write s₁ .t1 (s₁.gpr .a4 >>> 8)
    have hu₂ := Upd.write s₂ .t1 (s₂.gpr .a4 >>> 8)
    -- The setup.
    refine RelCT.seq (R := fun a b => MS1 p STK s₁ a ∧ MS1 p STK s₂ b)
      (RelCT.mono (relct_wp (ct_prog mArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pr r hr) (enter_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨signSetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            signSetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MS2 p STK s₁ a ∧ MS2 p STK s₂ b)
      (relct_wp (hash_ct (by taint_decide) fun a b h => ⟨ms1_hashOk hF hp₁ h48 h.1, ms1_hashOk hF hp₂ h48 h.2,
          h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => sinv_regs pr h.1.inv h.2.inv r
            (by revert r hr; decide)⟩)
        fun a b hab => ⟨signHash_ok hF hp₁ h48 hab.1, signHash_ok hF hp₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => SInv p STK s₁ a ∧ SInv p STK s₂ b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (signCall_ok hF hp₁ hf hS hab.1) fun _ h => h.1,
        WP.mono (signCall_ok hF hp₂ hf hS hab.2) fun _ h => h.1⟩)
      (ct_prog [.s8] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact sinv_regs pr hab.1 hab.2 _ (by decide))
        (by taint_decide))
    refine RelCT.seq (R := fun a b => SA p STK s₁ a ∧ SA p STK s₂ b)
      (relct_wp (ct_prog [.s0, .s5, .s6, .s7, .s8] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
        (fun a b hab r hr => sinv_regs pr hab.1.inv hab.2.inv r (by revert r hr; decide)) (by taint_decide))
        fun a b hab => ⟨signArgs_ok hab.1, signArgs_ok hab.2⟩) ?_
    refine RelCT.call hver.1 hver.2.1 (sRd p q s₁) (sWr p s₁) fun a b hab => ?_
    have hpre₁ := signCall_pre hF hp₁ (Nat.le_trans hstk hS) hab.1
    have hpre₂ := signCall_pre hF hp₂ (Nat.le_trans hstk hS) hab.2
    have eRd : sRd p q s₂ = sRd p q s₁ := by simp only [sRd, skR, rndR, pr _ (by decide : Reg.a0 ∈ mArgs),
      pr _ (by decide : Reg.a5 ∈ mArgs), pr _ (by decide : Reg.a7 ∈ mArgs)]
    have eWr : sWr p s₂ = sWr p s₁ := by simp only [sWr, sigR, pr _ (by decide : Reg.a6 ∈ mArgs),
      pr _ (by decide : Reg.a7 ∈ mArgs)]
    rw [eRd, eWr] at hpre₂
    refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
    have k₁ := hab.1.ms.inv
    have k₂ := hab.2.ms.inv
    refine sign_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a0, hab.2.a0, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a1, hab.2.a1, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a2, hab.2.a2, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a3, hab.2.a3, pr _ (by decide)]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a4, hab.2.a4, pr _ (by decide)]
    · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.a0 ∉ linkRegs by decide),
        ce_gpr _ _ _ (show Reg.a1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.a2 ∉ linkRegs by decide),
        hab.1.a0, hab.1.a1, hab.1.a2, hab.2.a0, hab.2.a1, hab.2.a2]
      have ks := skE_sub hF q
      have hl : p.skLen < 2 ^ 64 := by have := hF.skl; omega_using [this]
      rw [s_keep k₁ (R := ⟨s₁.gpr .a0, p.skLen⟩) hl (hp₁.kg.sub_left (ks s₁)) (hp₁.kc.sub_left (ks s₁))
          (hp₁.bk.sub_right (ks s₁)),
        hab.1.ms.mu, s_keep k₁ (R := rndR s₁) (show (32 : Nat) < 2 ^ 64 by decide) hp₁.rg hp₁.rc hp₁.br,
        s_keep k₂ (R := ⟨s₂.gpr .a0, p.skLen⟩) hl (hp₂.kg.sub_left (ks s₂)) (hp₂.kc.sub_left (ks s₂))
          (hp₂.bk.sub_right (ks s₂)),
        hab.2.ms.mu, s_keep k₂ (R := rndR s₂) (show (32 : Nat) < 2 ^ 64 by decide) hp₂.rg hp₂.rc hp₂.br]
      simp only [signMessageLeak] at pl
      rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl),
        Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl₂)] at pl
      simp only [Proof.MlKem.bytesAt_length] at pl
      exact pl
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.RISCV64.Message

end

end

/-! ### `MlDsa.RISCV64.Message.Verify`, which only this module used -/

section

/-!
# ML-DSA on RISC-V, `verify_message_cached`: correctness

As signing (`Sign.lean`), with `sig` in `a5` and `scratch` in `a6`: from a
state satisfying `MVCPre`, `verifyMessageCached n f p` returns 2 if the
context string is longer than 255 bytes; otherwise it saves our caller's
registers in the 1 KiB at `E` (`MV1`), keeping `tr` in `s6` too, computes `μ`
of the formatted message from the 64 bytes at `tr`, which are `H(pk, 64)`
(`MV3`), and calls the verification function on `μ` `f`, whose result is the
result (`verifyMessageCached_wp`). The steps are proved for the registers
`rs` that hold `V` (`VInvG`), of which `VL` says what they need.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64 VG.Proof.X25519.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea restore_ok restoreList)
open VG.Impl.Sha3.RISCV64.Pieces (Piece Len hash)
open VG.Proof.Sha3.RISCV64.Pieces (Kept PieceOk KEnv kW hash_ok)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The invariant -/

/-- What the registers hold: the arguments, and `E`. -/
def verifyV (p : Params) (s : State) : Reg → BitVec 64
  | .s0 => s.gpr .a0 | .s1 => s.gpr .a1 | .s2 => s.gpr .a2 | .s3 => s.gpr .a3 | .s4 => s.gpr .a4
  | .s5 => s.gpr .a5 | .s7 => s.gpr .a6 | .s8 => eAt p (s.gpr .a6) | _ => 0

/-- The registers `verifyV` gives: the arguments but `tr`, and `E`. -/
abbrev vRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s7, .s8]

/-- What the registers hold with a cached `tr`: as `verifyV`, and `tr` in `s6`. -/
def cachedV (p : Params) (s : State) : Reg → BitVec 64
  | .s6 => s.gpr .a7 | r => verifyV p s r

/-- What the body may write. -/
abbrev vW (p : Params) (STK : Nat) (s : State) : List Region := [vscrR p s, below s.sp STK]

/-- Between the steps of a body that keeps the registers `rs`, which hold `V`. -/
abbrev VInvG (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) : State → Prop :=
  Inv s (eAt p (s.gpr .a6)) oSV rs V (vW p STK s)

/-- What the steps need of the registers `rs` that the body keeps, holding `V`: they are callee-saved, they
and the link register fit in the 80 bytes at `oSV`, and they hold what `verifyV` says of `vRegs`. -/
structure VL (p : Params) (s : State) (rs : List Reg) (V : Reg → BitVec 64) : Prop where
  pres : ∀ r ∈ rs, r ∈ preserved
  len : rs.length ≤ 9
  regs : ∀ r ∈ vRegs, r ∈ rs ∧ V r = verifyV p s r

theorem vl_cached (p : Params) (s : State) : VL p s signRegs (cachedV p s) := by
  refine ⟨signRegs_pres, by decide, fun r hr => ?_⟩
  simp only [vRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩

section
variable {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s : State} {rs : List Reg} {V : Reg → BitVec 64}
  (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p q STK X s) (h48 : 1168 ≤ STK)

include hL in
theorem v_reg {t : State} (h : VInvG p STK s rs V t) {r : Reg} (hr : r ∈ vRegs) :
    t.gpr r = verifyV p s r :=
  (h.regs r (hL.regs r hr).1).trans (hL.regs r hr).2

include hL in
theorem v_e {t : State} (h : VInvG p STK s rs V t) : t.gpr .s8 = eAt p (s.gpr .a6) := v_reg hL h (by decide)

include hL in
theorem vslot_len : oSV + 8 * (rs.length + 1) ≤ oHdr := by
  have := hL.len; simp only [oSV, oHdr]; omega_using [this]

include hL in
theorem vslot_sub : Region.Sub (slotArea (eAt p (s.gpr .a6)) oSV rs) (vscrR p s) :=
  e_sub (by have := vslot_len hL; simp only [oHdr] at this; omega_using [this])

include hL in
theorem vslot_e {d n : Nat} (h : d + n ≤ oSV ∨ oSV + 80 ≤ d) (h₁ : d + n ≤ 1024) :
    (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 d, n⟩ :=
  e_e (h.symm.imp (fun h' => by have := hL.len; omega_using [h', this]) id) (by have := vslot_len hL; simp only [oHdr] at this; omega_using [this])
    h₁

include hL in
theorem vslot_e0 {n : Nat} (h : n ≤ oSV) :
    (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨eAt p (s.gpr .a6), n⟩ :=
  (e_e0 h (by have := vslot_len hL; simp only [oHdr] at this; omega_using [this])).symm

include hL hF in
theorem vslot_w : (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint ⟨s.gpr .a6, scratchWords p * 8⟩ :=
  (e_w hF (by have := vslot_len hL; simp only [oHdr] at this; omega_using [this])).symm

include hp h48 in
theorem vbelow48 : Region.Sub (below s.sp 1168) (below s.sp STK) := below_sub h48 (by have := hp.stk; omega_arith)

include hL hp h48 in
theorem vslot_b : (slotArea (eAt p (s.gpr .a6)) oSV rs).Disjoint (below s.sp 1168) :=
  (hp.bx.symm.sub_left (vslot_sub hL)).sub_right (vbelow48 hp h48)

include hF hp in
theorem ve_in {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    InRegions t.wr (eAt p (s.gpr .a6) + BitVec.ofNat 64 d) n := by
  rw [hw, hp.wr, e_add]
  exact in_base List.mem_cons_self (by rw [msw]; omega_arith) (by have := hF.e; omega_arith)

include hp in
theorem ve_cov {t : State} (hw : t.wr = s.wr) {d n : Nat} (h : d + n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 d, n⟩] t.wr := by
  rw [hw, hp.wr]
  refine Covers.of_sub fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact ⟨vscrR p s, List.mem_cons_self, oE p + d, e_add _ _ _, by simp only [msw]; omega_arith⟩

include hp in
theorem ve_cov0 {t : State} (hw : t.wr = s.wr) {n : Nat} (h : n ≤ 1024) :
    RISCV64.Covers [⟨eAt p (s.gpr .a6), n⟩] t.wr := by
  have := ve_cov hp hw (d := 0) (n := n) (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The inputs, while the body runs: none of them is in `vW`. -/
theorem v_keep {t : State} (h : VInvG p STK s rs V t) {R : Region} (hn : R.len < 2 ^ 64)
    (hc : R.Disjoint (vscrR p s)) (hb : (below s.sp STK).Disjoint R) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len := by
  refine Proof.Sha3.RISCV64.Pieces.bytes_keep h.frame hn fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hc
  · exact hb.symm

end

/-! ## The setup -/

/-- After the setup: the invariant, and `0 ‖ ctx_len` at `oHdr(E)`. -/
structure MV1 (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (t : State) : Prop where
  inv : VInvG p STK s rs V t
  hdr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat]

/-- The setup that saves the registers `rs` and moves the arguments into them by `ms`, `E` into the last. -/
theorem vsetup_ok {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s u : State} {rs : List Reg} {V : Reg → BitVec 64}
    {ms : List (Reg × Reg)} (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p q STK X s)
    (hfits : Spill.Fits (slots oSV rs)) (hlo : oSV + 8 * (rs.length + 1) < 2 ^ 64)
    (hsl : ∀ q ∈ slots oSV rs, q.2 + 8 ≤ 1024) (hms : ms.map Prod.fst = rs) (hsrc : ∀ q ∈ ms, q.2 ∉ rs)
    (hnd : rs.Nodup)
    (hv : ∀ q ∈ ms, (q.2 = .t2 ∧ V q.1 = eAt p (s.gpr .a6)) ∨ (q.2 ≠ .t2 ∧ q.2 ≠ .t1 ∧ V q.1 = s.gpr q.2))
    (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) (hsp : u.sp = s.sp)
    (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a6 p rs ms)) u (MV1 p STK s rs V) := by
  unfold enter
  refine WP.block_append_iff.mpr (WP.mono (base_ok p hF (by decide) u) fun u₁ ⟨h₁, l₁⟩ => ?_)
  have g9 : u.gpr .a6 = s.gpr .a6 := hu _ (by decide)
  rw [g9] at h₁
  have hw₁ : u₁.wr = s.wr := h₁.wr.trans hwr
  refine setup_ok (v := V) (W := vW p STK s) (by rw [h₁.gpr]; exact e_al hp.alx hp.fx) hfits hlo
    (fun q hq => by rw [h₁.gpr]; exact ve_in hF hp hw₁ (hsl q hq))
    ⟨vscrR p s, by simp, by rw [h₁.gpr]; exact vslot_sub hL⟩ hms hsrc hnd (fun q hq => by
      rcases hv q hq with ⟨e2, ev⟩ | ⟨e2, e1, ev⟩
      · rw [ev, e2, h₁.gpr]
      · rw [ev, h₁.other _ e2, hu _ e1])
    fun t₁ i₁ _ => ?_
  rw [h₁.gpr] at i₁
  have i₁ : VInvG p STK s rs V t₁ := inv_rebase i₁ hL.pres (h₁.rd.trans hrd) hw₁ (h₁.sp.trans hsp)
    (l₁.trans hlr)
    (fun r hr => (h₁.other r fun e => by revert hr; rw [e]; decide).trans (hu r fun e => by revert hr; rw [e]; decide))
    (h₁.mem.trans hm)
  have g30 : t₁.gpr .s8 = eAt p (s.gpr .a6) := v_e hL i₁
  have g26 : t₁.gpr .s4 = s.gpr .a4 := v_reg hL i₁ (by decide)
  refine hdr_ok (o := oHdr) (by decide) (by decide) (by decide) (by rw [g30]; exact ve_in hF hp i₁.wr (by decide))
    (by rw [g30]; exact ve_in hF hp i₁.wr (by decide)) fun t ht hrd' hwr' hsp' hg => WP.block_nil ⟨?_, ?_⟩
  · refine i₁.step hL.pres hrd' hwr' hsp' (fun r hr => hg r fun e => by revert hr; rw [e]; decide)
      (ht ▸ hdrMem_frame _ _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr, g30]; exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · rw [List.mem_singleton.mp hr, g30]; exact vslot_e hL (.inr (by decide)) (by decide)
  · rw [ht, g30, g26, show s.gpr .a4 = BitVec.ofNat 64 (s.gpr .a4).toNat by simp, hdrMem_bytes]
    simp

theorem cachedSetup_ok {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s u : State} (hF : MFacts p)
    (hp : MVPre p q STK X s) (hu : ∀ r, r ≠ .t1 → u.gpr r = s.gpr r) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.gpr .ra = s.gpr .ra) (hm : u.mem = s.mem) :
    WP isa (.block (enter .a6 p signRegs cachedMs)) u (MV1 p STK s signRegs (cachedV p s)) :=
  vsetup_ok (vl_cached p s) hF hp (by decide) (by decide) (by decide) rfl (by decide) (by decide) (fun q hq => by
      simp only [cachedMs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      iterate 8 exact .inr ⟨by decide, by decide, rfl⟩
      exact .inl ⟨rfl, rfl⟩)
    hu hrd hwr hsp hlr hm

/-! ## `tr` and `μ` -/

/-- The public key. -/
abbrev pkB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .a0) p.pkLen

/-- The signature. -/
abbrev vsigB (p : Params) (s : State) : List Byte := bytesAt s.mem (s.gpr .a5) p.sigLen

/-- What a hash keeps of the invariant. -/
theorem vinv_hash {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s t t' : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hL : VL p s rs V) (hp : MVPre p q STK X s) (h48 : 1168 ≤ STK)
    (hi : VInvG p STK s rs V t)
    (k : Kept ([⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩] ++ kW 840 (eAt p (s.gpr .a6)) t.sp) t t') :
    VInvG p STK s rs V t' := by
  have hsp : t.sp = s.sp := hi.sp
  refine inv_kept hi hL.pres k (fun r hr => ?_) fun r hr => ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨vscrR p s, by simp, e_sub (by decide)⟩
    · exact ⟨vscrR p s, by simp, e_sub0 (by decide)⟩
    · exact ⟨below s.sp STK, by simp, by rw [hsp]; exact vbelow48 hp h48⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact vslot_e hL (.inl (by decide)) (by decide)
    · exact vslot_e0 hL (by decide)
    · rw [hsp]; exact vslot_b hL hp h48

/-- After `μ`: the invariant, and `μ` at `oMU(E)`. -/
structure MV3 (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (t : State) : Prop where
  inv : VInvG p STK s rs V t
  mu : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU) 64 = messageRep (pkTr (pkB p s)) (fmtB s)

section
variable {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s t : State} {rs : List Reg} {V : Reg → BitVec 64}
  (hF : MFacts p) (hp : MVPre p q STK X s) (h48 : 1168 ≤ STK)
include hF hp h48

omit hF in
theorem vke (hi : VInvG p STK s rs V t) : KEnv 840 (eAt p (s.gpr .a6)) t :=
  ⟨by decide, ve_cov0 hp hi.wr (by decide), e_al hp.alx hp.fx, by rw [hi.sp]; exact hp.al,
    by rw [hi.sp]; have := hp.stk; omega_arith,
    by rw [hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub0 (by decide))⟩

omit hF in
/-- The pieces of the formatted message after the first, `q₀`. -/
theorem mu_ins (hL : VL p s rs V) (hi : VInvG p STK s rs V t) {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) :
    ∀ q ∈ q₀ :: fmtPieces, PieceOk 840 (eAt p (s.gpr .a6)) t q := by
  have g23 : t.gpr .s1 = s.gpr .a1 := v_reg hL hi (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := v_reg hL hi (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := v_reg hL hi (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  have eS := e_sub0 (p := p) (x := s.gpr .a6) (n := 840) (by decide)
  have cr : ∀ R ∈ [pkR p s q, msgR s, ctxR s, vsigR p s], RISCV64.Covers [R] (t.rd ++ t.wr) := fun R hR => by
    rw [hi.rd, hp.rd]
    exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ hR, hc⟩
  intro q hq
  simp only [fmtPieces, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact h₀
  · exact pieceOk_of (R := ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr, 2⟩)
      (by simp only [Piece.R, Piece.addr, Len.val, g30]) (by decide) (by decide) (show 2 < 2048 by decide)
      (Proof.Sha3.RISCV64.Pieces.cov_right (ve_cov hp hi.wr (by decide))) (e_e0 (by decide) (by decide)).symm
      (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))
  · exact pieceOk_of (R := ctxR s) (by simp only [Piece.R, Piece.addr, Len.val, g25, g26, BitVec.add_zero])
      (by decide) (by decide) (show Reg.s4 ∈ preserved by decide) (cr _ (by simp))
      (hp.cc.sub_right eS) (by rw [hsp]; exact hp.bc.sub_left b48)
  · exact pieceOk_of (R := msgR s) (by simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero])
      (by decide) (by decide) (show Reg.s2 ∈ preserved by decide) (cr _ (by simp))
      (hp.mc.sub_right eS) (by rw [hsp]; exact hp.bm.sub_left b48)

omit hF in
omit hF in
/-- `μ` from the first piece `q₀`, which holds `tr`. -/
theorem muHash_ok (hL : VL p s rs V) (hi : VInvG p STK s rs V t)
    (hdr : bytesAt t.mem (eAt p (s.gpr .a6) + BitVec.ofNat 64 oHdr) 2 = [0, BitVec.ofNat 8 (s.gpr .a4).toNat])
    {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) (hb : q₀.bytes t.mem t.gpr = pkTr (pkB p s)) :
    WP isa (muHash q₀) t (MV3 p STK s rs V) := by
  have g23 : t.gpr .s1 = s.gpr .a1 := v_reg hL hi (by decide)
  have g24 : t.gpr .s2 = s.gpr .a2 := v_reg hL hi (by decide)
  have g25 : t.gpr .s3 = s.gpr .a3 := v_reg hL hi (by decide)
  have g26 : t.gpr .s4 = s.gpr .a4 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  have hsp : t.sp = s.sp := hi.sp
  have b48 := vbelow48 hp h48
  unfold muHash
  refine WP.mono (hash_ok (N := 840) (n := 64) (o := oMU) (out := eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU)
    (by decide) (by decide) (by decide) (by decide) g30 (by rw [g30]) (vke hp h48 hi) (by simp)
    (mu_ins hp h48 hL hi h₀) (ve_cov hp hi.wr (by decide)) (e_e0 (by decide) (by decide)).symm
    (by rw [hsp]; exact (hp.bx.sub_left b48).sub_right (e_sub (by decide)))) fun t' ⟨k', d'⟩ => ⟨?_, ?_⟩
  · exact vinv_hash hL hp h48 hi k'
  · rw [d', List.map_cons, hb]
    have kc : bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat = ctxB s :=
      v_keep hi (R := ctxR s) (BitVec.isLt _) hp.cc hp.bc
    have km : bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = msgB s :=
      v_keep hi (R := msgR s) (BitVec.isLt _) hp.mc hp.bm
    simp only [fmtPieces, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Piece.bytes, Piece.addr, Len.val, g23, g24, g25, g26, g30, BitVec.add_zero]
    rw [hdr, kc, km]
    simp only [messageRep, H, List.append_assoc]

omit hF in
end

/-! ## `μ` from a cached `tr` -/

section
variable {p : Params} {q : Bool} {STK : Nat} {s t : State} (hc : MVCPre p q STK s) (h48 : 1168 ≤ STK)
include hc h48

/-- The first piece of `μ`: `tr`, at `s6`. -/
theorem trPiece_ok (hi : VInvG p STK s signRegs (cachedV p s) t) :
    PieceOk 840 (eAt p (s.gpr .a6)) t ⟨.s6, 0, .imm 64⟩ := by
  have g28 : t.gpr .s6 = s.gpr .a7 := hi.regs _ (by decide)
  exact pieceOk_of (R := trR s) (by simp only [Piece.R, Piece.addr, Len.val, g28, BitVec.add_zero])
    (by decide) (by decide) (show 64 < 2048 by decide)
    (cov_rd (by rw [hi.rd, hc.mv.rd]; exact cov_in0 (k := 64) (List.mem_append_right _ List.mem_cons_self) (Nat.le_refl _)))
    (hc.tc.symm.sub_right (e_sub0 (by decide))) (by rw [hi.sp]; exact hc.bt.sub_left (vbelow48 hc.mv h48))

theorem cachedHash_ok (h : MV1 p STK s signRegs (cachedV p s) t) :
    WP isa (muHash ⟨.s6, 0, .imm 64⟩) t (MV3 p STK s signRegs (cachedV p s)) := by
  have hi := h.inv
  have g28 : t.gpr .s6 = s.gpr .a7 := hi.regs _ (by decide)
  refine muHash_ok hc.mv h48 (vl_cached p s) hi h.hdr (trPiece_ok hc h48 hi) ?_
  simp only [Piece.bytes, Piece.addr, Len.val, g28, BitVec.add_zero]
  rw [v_keep hi (R := trR s) (show (64 : Nat) < 2 ^ 64 by decide) hc.tc.symm hc.bt, hc.tr]

end

/-! ## The call of the verification function on `μ` -/

/-- The arguments of the call. -/
abbrev verifyArgs : List Instr := [mov .a0 .s0, .addi .a1 .s8 oMU, mov .a2 .s5, mov .a3 .s7]

theorem args4_ok {t : State} {a b c d : Reg} {i j k l : Nat} (hi : i < 2048) (hj : j < 2048) (hk : k < 2048) (hl : l < 2048)
    (hs : ∀ x ∈ [b, c, d], x ∈ preserved) {Q : State → Prop}
    (K : ∀ u, u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r ∈ preserved, u.gpr r = t.gpr r) →
      u.gpr .a0 = t.gpr a + BitVec.ofNat 64 i →
      u.gpr .a1 = t.gpr b + BitVec.ofNat 64 j → u.gpr .a2 = t.gpr c + BitVec.ofNat 64 k →
      u.gpr .a3 = t.gpr d + BitVec.ofNat 64 l → Q u) :
    WP isa (.block [.addi .a0 a i, .addi .a1 b j, .addi .a2 c k, .addi .a3 d l]) t Q := by
  have pb := Ed25519.RISCV64.Whole.pres_args (hs b (by simp))
  have pc := Ed25519.RISCV64.Whole.pres_args (hs c (by simp))
  have pd := Ed25519.RISCV64.Whole.pres_args (hs d (by simp))
  exact Steps.wp_addi hi fun u₁ h₁ => Steps.wp_addi hj fun u₂ h₂ => Steps.wp_addi hk fun u₃ h₃ =>
    Steps.wp_addi hl fun u₄ h₄ => WP.block_nil <|
    K u₄ (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]) (by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd])
      (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]) (by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]) (fun r hr => by
        obtain ⟨p3, p4, p5, p6, -⟩ := Ed25519.RISCV64.Whole.pres_args hr
        rw [h₄.other _ p6, h₃.other _ p5, h₂.other _ p4, h₁.other _ p3])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr])
      (by rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ pb.1])
      (by rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ pc.2.1, h₁.other _ pc.1])
      (by rw [h₄.gpr, h₃.other _ pd.2.2.1, h₂.other _ pd.2.1, h₁.other _ pd.1])

/-- What the verification function on `μ` returns. -/
abbrev vres (p : Params) (s : State) (r : BitVec 32) : Prop :=
  let v := fun b => verifyMu p b (pkB p s) (messageRep (pkTr (pkB p s)) (fmtB s)) (vsigB p s)
  (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true)

/-- After the arguments of the call: `μ`, and the arguments in `a0`–`a3`. -/
structure VA (p : Params) (STK : Nat) (s : State) (rs : List Reg) (V : Reg → BitVec 64) (u : State) : Prop where
  ms : MV3 p STK s rs V u
  a0 : u.gpr .a0 = s.gpr .a0
  a1 : u.gpr .a1 = eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU
  a2 : u.gpr .a2 = s.gpr .a5
  a3 : u.gpr .a3 = s.gpr .a6

theorem verifyArgs_ok {p : Params} {STK : Nat} {s t : State} {rs : List Reg} {V : Reg → BitVec 64}
    (hL : VL p s rs V) (h : MV3 p STK s rs V t) :
    WP isa (.block verifyArgs) t (VA p STK s rs V) := by
  have hi := h.inv
  have g22 : t.gpr .s0 = s.gpr .a0 := v_reg hL hi (by decide)
  have g27 : t.gpr .s5 = s.gpr .a5 := v_reg hL hi (by decide)
  have g29 : t.gpr .s7 = s.gpr .a6 := v_reg hL hi (by decide)
  have g30 := v_e hL hi
  unfold verifyArgs mov
  refine args4_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u um urd' uwr' usp' upres a3 a4 a5 a6 =>
    ⟨⟨hi.step hL.pres urd' uwr' usp' upres (by rw [um]; exact Frame.refl _ _)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil), by rw [um]; exact h.mu⟩,
      ?_, ?_, ?_, ?_⟩
  · rw [a3, g22, BitVec.add_zero]
  · rw [a4, g30]
  · rw [a5, g27, BitVec.add_zero]
  · rw [a6, g29, BitVec.add_zero]

/-- What the verification function on `μ` reads and writes. -/
abbrev vRd (p : Params) (q : Bool) (s : State) : List Region :=
  [pkR p s q, ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩, vsigR p s]
abbrev vWr (p : Params) (s : State) : List Region := [⟨s.gpr .a6, scratchWords p * 8⟩]

/-- The call's precondition, and its regions. -/
theorem verifyCall_pre {p : Params} {q : Bool} {STK stk : Nat} {X : List Region} {s u : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hF : MFacts p) (hp : MVPre p q STK X s)
    (hk : q = true → PreparedPublicKey p s.mem (s.gpr .a0)) (hstk : stk ≤ STK) (h : VA p STK s rs V u) :
    (PreparedKey.verifyEK p q stk).pre (u.callEntry.withRegions (vRd p q s) (vWr p s)) ∧
      RISCV64.Covers (vRd p q s ++ vWr p s) (u.rd ++ u.wr) ∧ RISCV64.Covers (vWr p s) u.wr := by
  have iu := h.ms.inv
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  have hE := hF.e
  have fx := hp.fx
  rw [msw] at fx
  have hsw : scratchWords p * 8 ≤ oE p := by simp only [oE]; omega_arith
  have usp : u.sp = s.sp := iu.sp
  have urd : u.rd = s.rd := iu.rd
  have uwr : u.wr = s.wr := iu.wr
  have bs : Region.Sub (below s.sp stk) (below s.sp STK) := below_sub (by omega_arith) (by omega_arith)
  have muS : Region.Sub ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩ (vscrR p s) := e_sub (by decide)
  have muW : Region.Disjoint ⟨s.gpr .a6, scratchWords p * 8⟩ ⟨eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU, 64⟩ :=
    e_w hF (by decide)
  have muF : (eAt p (s.gpr .a6) + BitVec.ofNat 64 oMU).toNat + 64 ≤ 2 ^ 64 := e_fit hp.fx (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · refine verify_pre ((ce_gpr _ _ _ (by decide)).trans h.a0) ((ce_gpr _ _ _ (by decide)).trans h.a1)
      ((ce_gpr _ _ _ (by decide)).trans h.a2) ((ce_gpr _ _ _ (by decide)).trans h.a3) rfl rfl
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; omega_arith)
      (by simp only [State.withRegions_sp, State.callEntry_sp, usp]; exact hp.al) hp.alx
      (hp.kc.sub_right w_sub) muW.symm (hp.gc.sub_right w_sub) ?_ ?_ ?_ ?_ hp.fk muF hp.fg (by omega_arith) ?_
    case' refine_5 =>
      intro hq
      have hk' := hk hq
      subst hq
      have hl : preparedPublicKeyBytes p < 2 ^ 64 := by have := hF.ppk; omega_arith
      exact PreparedKey.preparedPublic_of_bytes (v_keep iu (R := pkR p s true) hl hp.kc hp.bk) hk'
    all_goals simp only [State.withRegions_sp, State.callEntry_sp, usp]
    · exact hp.bk.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right muS
    · exact hp.bg.sub_left bs
    · exact (hp.bx.sub_left bs).sub_right w_sub
  · rw [urd, uwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨pkR p s q, by simp, 0, by simp, by simp⟩
    · exact ⟨vscrR p s, by simp, oE p + oMU, e_add _ _ _, e_len p (d := oMU) (n := 64) (by decide)⟩
    · exact ⟨vsigR p s, by simp, 0, by simp, by simp⟩
    · exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega_arith⟩
  · rw [uwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨vscrR p s, by simp, 0, by simp, by simp only [msw]; omega_arith⟩

theorem verifyCall_ok {p : Params} {q : Bool} {STK S : Nat} {X : List Region} {s t : State} {rs : List Reg}
    {V : Reg → BitVec 64} (hL : VL p s rs V) (hF : MFacts p) (hp : MVPre p q STK X s)
    (hk : q = true → PreparedPublicKey p s.mem (s.gpr .a0)) {f : Prog isa} (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String}
    (h : MV3 p STK s rs V t) :
    WP isa (.seq (.block verifyArgs) (.call n f)) t fun t' => VInvG p STK s rs V t' ∧
      vres p s ((t'.gpr .a0).setWidth 32) := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have hstkS : STK ≤ s.sp.toNat := hp.stk
  refine WP.seq (WP.mono (verifyArgs_ok hL h) fun u hu => ?_)
  have iu := hu.ms.inv
  have usp : u.sp = s.sp := iu.sp
  obtain ⟨hpre, hc, hw⟩ := verifyCall_pre hF hp hk (Nat.le_trans hstk hS) hu
  have hd : sdepth f < 2 ^ 64 := by have := hf.stack; omega_arith
  refine WP.callAny hver.1 hpre hc hw (fun s' rd' wr' sp' fr' cs' post' => ?_) hd
  refine ⟨iu.step hL.pres rd' wr' sp' cs' fr' (fun r hr => ?_) fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨vscrR p s, by simp, w_sub⟩
    · exact ⟨below s.sp STK, by simp, by rw [usp]; exact below_sub (by have := hf.stack; omega_arith) (by omega_arith)⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact vslot_w hL hF
    · rw [usp]
      exact (hp.bx.symm.sub_left (vslot_sub hL)).sub_right (below_sub (by have := hf.stack; omega_arith) (by omega_arith))
  · have hq := verify_post post'
    simp only [State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
      State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), hu.a0, hu.a1, hu.a2] at hq
    have ks := pkE_sub hF q s
    rw [v_keep iu (R := ⟨s.gpr .a0, p.pkLen⟩) (by have := hF.pk; show p.pkLen < 2 ^ 64; omega_arith)
      (hp.kc.sub_left ks) (hp.bk.sub_right ks), hu.ms.mu,
      v_keep iu (R := vsigR p s) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega_arith) hp.gc hp.bg] at hq
    exact hq

theorem verifyMessageCached_wp {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String} {s : State}
    (hc : MVCPre p q STK s) :
    WP isa (verifyMessageCached n f p) s fun t =>
      abiPreserved s t ∧ (verifyMessageEK p q STK).post s t := by
  have hp := hc.mv
  unfold verifyMessageCached top
  refine WP.seq (Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil ?_))
  have hu := Steps.Upd.write s .t1 (s.gpr .a4 >>> 8)
  refine wp_ite (decide ((s.gpr .a4).toNat < 256)) (by rw [eval_zero, hu.gpr]; exact congrArg some (shr8_zero _))
    (fun hcl => ?_) fun hcl => ?_
  · have hcl' : (s.gpr .a4).toNat < 256 := of_decide_eq_true hcl
    refine WP.seq (WP.mono (cachedSetup_ok hF hp hu.other hu.rd hu.wr hu.sp rfl hu.mem) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (cachedHash_ok hc h48 h₁) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (verifyCall_ok (vl_cached p s) hF hp hc.kp hf hS h₃) fun t₄ ⟨h₄, r₄⟩ => ?_)
    have hrl : ∀ q ∈ restoreList oSV signRegs, q.2 + 8 ≤ 1024 := by decide
    refine restore_ok h₄ (e_al hp.alx hp.fx) (v_e (vl_cached p s) h₄) (by decide) (by decide) (by decide)
      (by decide)
      (fun q hq => by
        have := hrl q hq
        have := e_len p (d := q.2) (n := 8) (by omega_arith)
        have := hF.e
        rw [h₄.rd, h₄.wr, hp.rd, hp.wr, e_add]
        exact ⟨vscrR p s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₅ g₅ sp₅ lr₅ m₅ o₅ => ⟨⟨g₅, sp₅, lr₅⟩, ?_⟩
    cases q
    all_goals simp only [verifyMessageEK, Bool.false_eq_true, ↓reduceIte]
    all_goals first
      | sig_post [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs]
      | sig_post [preparedVerifyMessageContract, preparedVerifyMessageSig, RISCV64.abi, RISCV64.argRegs]
    all_goals rw [Proof.MlDsa.Message.formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hcl'),
      o₅ .a0 (by decide) (by decide)]
    all_goals simp only [verifyInternal, Proof.MlKem.bytesAt_length]
    all_goals exact r₄
  · have hcl' : ¬ (s.gpr .a4).toNat < 256 := of_decide_eq_false hcl
    refine Steps.WP.cons (exec_li (d := .a0) (imm := 2) (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl⟩, ?_⟩)
    · rw [(Steps.Upd.write _ _ _).other _ (Proof.Sha3.RISCV64.Pieces.pres_ne hr).2.1,
        hu.other _ (by revert hr; cases r <;> decide)]
    · cases q
      all_goals simp only [verifyMessageEK, Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | sig_post [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs]
        | sig_post [preparedVerifyMessageContract, preparedVerifyMessageSig, RISCV64.abi, RISCV64.argRegs]
      all_goals rw [Proof.MlDsa.Message.formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_arith)]
      all_goals rfl

end VG.Proof.MlDsa.RISCV64.Message

end

end

/-!
# ML-DSA on RISC-V, `verify_message_cached`: constant time

As signing's (`SignCT.lean`): two runs from states that satisfy `MVCPre` and
agree on the arguments in registers, the stack pointer and the inputs, the
leakage of `verifyMessageCachedContract` (`MVCPub`), leak the same trace
(`verifyMessageCached_ct`). The hash of `μ` is related by `hash_ct`, and the
call of the verification function on `μ` by its own constant time, whose
leakage is its inputs: the key and the signature, and `μ`, which both runs
compute from the same inputs (`verifyCall_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Impl.Sha3.RISCV64.Pieces (Piece hash)
open VG.Proof.Sha3.RISCV64.Pieces (HashOk PieceOk hash_ct)
open VG.RISCV64.Steps (Upd)
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The argument registers of `verify_message_cached` but `tr` (`a7`). -/
abbrev vArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6]

/-- The registers `rs` agree in two runs whose invariants say they hold the same. -/
theorem vinvG_regs {p : Params} {STK : Nat} {s₁ s₂ a b : State} {rs : List Reg} {V₁ V₂ : Reg → BitVec 64}
    (h : ∀ r ∈ rs, V₁ r = V₂ r) (ha : VInvG p STK s₁ rs V₁ a) (hb : VInvG p STK s₂ rs V₂ b) :
    ∀ r ∈ rs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((h r hr).trans (hb.regs r hr).symm)

section
variable {p : Params} {q : Bool} {STK : Nat} {X : List Region} {s t : State} (hF : MFacts p) (hp : MVPre p q STK X s)
  (h48 : 1168 ≤ STK)
include hF hp h48

omit hF in
/-- The hash of `μ` may run, from the first piece `q₀`. -/
theorem mu_hashOk {rs : List Reg} {V : Reg → BitVec 64} (hL : VL p s rs V) (hi : VInvG p STK s rs V t)
    {q₀ : Piece} (h₀ : PieceOk 840 (eAt p (s.gpr .a6)) t q₀) :
    HashOk 840 64 .s8 .s8 oMU (q₀ :: fmtPieces) t := by
  have g30 := v_e hL hi
  exact ⟨by decide, by decide, by decide, by decide, by simp, by rw [g30]; exact vke hp h48 hi,
    by rw [g30]; exact mu_ins hp h48 hL hi h₀, by rw [g30]; exact ve_cov hp hi.wr (by decide),
    by rw [g30]; exact (e_e0 (by decide) (by decide)).symm,
    by rw [g30, hi.sp]; exact (hp.bx.sub_left (vbelow48 hp h48)).sub_right (e_sub (by decide))⟩

omit hF in
end

/-- The call of the verification function on `μ`, in two runs that agree on `MVCPub`'s inputs, and whose
invariants say the registers `rs` hold the same. -/
theorem verifyCall_ct {p : Params} {q : Bool} {STK S : Nat} {X₁ X₂ : List Region} {s₁ s₂ : State} {rs : List Reg}
    {V₁ V₂ : Reg → BitVec 64} (hF : MFacts p) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String}
    (hL₁ : VL p s₁ rs V₁) (hL₂ : VL p s₂ rs V₂) (hp₁ : MVPre p q STK X₁ s₁) (hp₂ : MVPre p q STK X₂ s₂)
    (hk₁ : q = true → PreparedPublicKey p s₁.mem (s₁.gpr .a0)) (hk₂ : q = true → PreparedPublicKey p s₂.mem (s₂.gpr .a0))
    (psp : s₁.sp = s₂.sp)
    (pr : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r) (hV : ∀ r ∈ rs, V₁ r = V₂ r)
    (ek : pkB p s₁ = pkB p s₂) (em : msgB s₁ = msgB s₂) (ec : ctxB s₁ = ctxB s₂) (eg : vsigB p s₁ = vsigB p s₂) :
    RelCT isa (fun a b => MV3 p STK s₁ rs V₁ a ∧ MV3 p STK s₂ rs V₂ b) (.seq (.block verifyArgs) (.call n f))
      fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hf.verified
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  refine RelCT.seq (R := fun a b => VA p STK s₁ rs V₁ a ∧ VA p STK s₂ rs V₂ b)
    (relct_wp (ct_prog [.s0, .s5, .s7, .s8] (fun a b hab => hab.1.inv.sp.trans (psp.trans hab.2.inv.sp.symm))
      (fun a b hab r hr => vinvG_regs hV hab.1.inv hab.2.inv r (hL₁.regs r (by revert r hr; decide)).1)
      (by taint_decide))
      fun a b hab => ⟨verifyArgs_ok hL₁ hab.1, verifyArgs_ok hL₂ hab.2⟩) ?_
  refine RelCT.call hver.1 hver.2.1 (vRd p q s₁) (vWr p s₁) fun a b hab => ?_
  have hpre₁ := verifyCall_pre hF hp₁ hk₁ (Nat.le_trans hstk hS) hab.1
  have hpre₂ := verifyCall_pre hF hp₂ hk₂ (Nat.le_trans hstk hS) hab.2
  have eRd : vRd p q s₂ = vRd p q s₁ := by simp only [vRd, pkR, vsigR, pr _ (by decide : Reg.a0 ∈ vArgs),
    pr _ (by decide : Reg.a5 ∈ vArgs), pr _ (by decide : Reg.a6 ∈ vArgs)]
  have eWr : vWr p s₂ = vWr p s₁ := by simp only [vWr, pr _ (by decide : Reg.a6 ∈ vArgs)]
  rw [eRd, eWr] at hpre₂
  refine ⟨hpre₁.1, hpre₂.1, ?_, hpre₁.2.1, hpre₁.2.2, hpre₂.2.1, hpre₂.2.2⟩
  have k₁ := hab.1.ms.inv
  have k₂ := hab.2.ms.inv
  refine verify_pub (by simp only [State.withRegions_sp, State.callEntry_sp, k₁.sp, k₂.sp, psp]) ?_ ?_ ?_ ?_ ?_
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a0, hab.2.a0, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a1, hab.2.a1, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a2, hab.2.a2, pr _ (by decide)]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), hab.1.a3, hab.2.a3, pr _ (by decide)]
  · simp only [State.withRegions_mem, State.callEntry_mem, ce_gpr _ _ _ (show Reg.a0 ∉ linkRegs by decide),
      ce_gpr _ _ _ (show Reg.a1 ∉ linkRegs by decide), ce_gpr _ _ _ (show Reg.a2 ∉ linkRegs by decide),
      hab.1.a0, hab.1.a1, hab.1.a2, hab.2.a0, hab.2.a1, hab.2.a2]
    have ks := pkE_sub hF q
    have hl : p.pkLen < 2 ^ 64 := by have := hF.pk; omega_using [this]
    rw [v_keep k₁ (R := ⟨s₁.gpr .a0, p.pkLen⟩) hl (hp₁.kc.sub_left (ks s₁)) (hp₁.bk.sub_right (ks s₁)),
      hab.1.ms.mu, v_keep k₁ (R := vsigR p s₁) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega_using [this]) hp₁.gc hp₁.bg,
      v_keep k₂ (R := ⟨s₂.gpr .a0, p.pkLen⟩) hl (hp₂.kc.sub_left (ks s₂)) (hp₂.bk.sub_right (ks s₂)),
      hab.2.ms.mu, v_keep k₂ (R := vsigR p s₂) (by have := hF.sgl; show p.sigLen < 2 ^ 64; omega_using [this]) hp₂.gc hp₂.bg]
    simp only [pkB, vsigB, fmtB, ctxB, msgB] at ek em ec eg ⊢
    rw [ek, em, ec, eg, p7]

/-- The argument registers of `verify_message_cached`. -/
abbrev vcArgs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

theorem cachedEnter_taint (p : Params) : (VG.RISCV64.taint.check (Taint.ofRegs vcArgs)
    (.block (enter .a6 p signRegs cachedMs))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs vcArgs) (.block (enter .a6 mlDsa44 signRegs cachedMs)))).isSome =
    true := rfl

/-- What two runs agree on: `verifyMessageCachedContract`'s public part. -/
def MVCPub (p : Params) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧
    leakBytes (pkB p s₁ ++ msgB s₁ ++ ctxB s₁ ++ vsigB p s₁) = leakBytes (pkB p s₂ ++ msgB s₂ ++ ctxB s₂ ++ vsigB p s₂) ∧
    ∀ r ∈ vcArgs, s₁.gpr r = s₂.gpr r

theorem cachedV_eq {p : Params} {s₁ s₂ : State} (h : ∀ r ∈ vcArgs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ signRegs, cachedV p s₁ r = cachedV p s₂ r := by
  intro r hr
  simp only [signRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 8 exact h _ (by decide)
  show eAt p (s₁.gpr .a6) = eAt p (s₂.gpr .a6)
  rw [h .a6 (by decide)]

theorem verifyMessageCached_ct {p : Params} {q : Bool} {STK S : Nat} (hF : MFacts p) (h48 : 1168 ≤ STK) {f : Prog isa}
    (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S) (hS : S ≤ STK) {n : String} :
    ConstantTime isa (MVCPre p q STK) (MVCPub p) (verifyMessageCached n f p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ MVCPre p q STK x.1 ∧
    MVCPre p q STK x.2 ∧ MVCPub p x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩)
    (fun _ _ h => h)
  by_cases hH : MVCPre p q STK s₁ ∧ MVCPre p q STK s₂ ∧ MVCPub p s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hc₁, hc₂, psp, pl, pr⟩ := hH
  have hp₁ := hc₁.mv
  have hp₂ := hc₂.mv
  have pv : ∀ r ∈ vArgs, s₁.gpr r = s₂.gpr r := fun r hr => pr r (by revert r hr; decide)
  have hV := cachedV_eq (p := p) pr
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have p7 : s₁.gpr .a4 = s₂.gpr .a4 := pr _ (by decide)
  obtain ⟨ek, em, ec, eg⟩ := Proof.MlDsa.Message.leak4 (by simp [Proof.MlKem.bytesAt_length])
    (by simp [Proof.MlKem.bytesAt_length, pr .a2 (by decide)]) (by simp [Proof.MlKem.bytesAt_length, p7]) pl
  unfold verifyMessageCached top
  -- The length check.
  refine RelCT.seq (R := fun a b => a = s₁.write .t1 (s₁.gpr .a4 >>> 8) ∧ b = s₂.write .t1 (s₂.gpr .a4 >>> 8))
    (RelCT.mono (relct_wp (ct_prog [.a4] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p7]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl),
       by rw [hab.2]; exact Steps.WP.cons (exec_shift_d (by decide)) (WP.block_nil rfl)⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by
    rw [hab.1, hab.2, eval_zero, eval_zero, (Upd.write _ _ _).gpr, (Upd.write _ _ _).gpr, p7]) ?_ ?_
  · have hu₁ := Upd.write s₁ .t1 (s₁.gpr .a4 >>> 8)
    have hu₂ := Upd.write s₂ .t1 (s₂.gpr .a4 >>> 8)
    -- The setup.
    refine RelCT.seq (R := fun a b => MV1 p STK s₁ signRegs (cachedV p s₁) a ∧
        MV1 p STK s₂ signRegs (cachedV p s₂) b)
      (RelCT.mono (relct_wp (ct_prog vcArgs (fun a b hab => by
          rw [hab.1.1, hab.1.2, hu₁.sp, hu₂.sp, psp]) (fun a b hab r hr => by
          rw [hab.1.1, hab.1.2, hu₁.other _ (by revert r; decide), hu₂.other _ (by revert r; decide)]
          exact pr r hr) (cachedEnter_taint p)) fun a b hab => by
          rw [hab.1.1, hab.1.2]
          exact ⟨cachedSetup_ok hF hp₁ hu₁.other hu₁.rd hu₁.wr hu₁.sp rfl hu₁.mem,
            cachedSetup_ok hF hp₂ hu₂.other hu₂.rd hu₂.wr hu₂.sp rfl hu₂.mem⟩) (fun _ _ h => h) fun _ _ h => h) ?_
    -- `μ`.
    refine RelCT.seq (R := fun a b => MV3 p STK s₁ signRegs (cachedV p s₁) a ∧
        MV3 p STK s₂ signRegs (cachedV p s₂) b)
      (relct_wp (hash_ct (by taint_decide) fun a b h =>
          ⟨mu_hashOk hp₁ h48 (vl_cached p s₁) h.1.inv (trPiece_ok hc₁ h48 h.1.inv),
            mu_hashOk hp₂ h48 (vl_cached p s₂) h.2.inv (trPiece_ok hc₂ h48 h.2.inv),
            h.1.inv.sp.trans (psp.trans h.2.inv.sp.symm), fun r hr => vinvG_regs hV h.1.inv h.2.inv r
              (by revert r hr; decide)⟩)
        fun a b hab => ⟨cachedHash_ok hc₁ h48 hab.1, cachedHash_ok hc₂ h48 hab.2⟩) ?_
    -- The call.
    refine RelCT.seq (R := fun a b => VInvG p STK s₁ signRegs (cachedV p s₁) a ∧
        VInvG p STK s₂ signRegs (cachedV p s₂) b)
      (relct_wp ?_ fun a b hab => ⟨WP.mono (verifyCall_ok (vl_cached p s₁) hF hp₁ hc₁.kp hf hS hab.1) fun _ h => h.1,
        WP.mono (verifyCall_ok (vl_cached p s₂) hF hp₂ hc₂.kp hf hS hab.2) fun _ h => h.1⟩)
      (ct_prog [.s8] (fun a b hab => hab.1.sp.trans (psp.trans hab.2.sp.symm))
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact vinvG_regs hV hab.1 hab.2 _ (by decide))
        (by taint_decide))
    exact verifyCall_ct (n := n) hF hf hS (vl_cached p s₁) (vl_cached p s₂) hp₁ hp₂ hc₁.kp hc₂.kp psp pv hV ek em ec eg
  · -- `ctx_len ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1, hab.1.2, (Upd.write _ _ _).sp, (Upd.write _ _ _).sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.MlDsa.RISCV64.Message

end

end

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message_cached`: their contracts

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message_cached` meet their
contracts with `S` bytes of stack, for any verified function on `μ` with at
most `S` bytes of stack (at least the 1168 the sponge functions' frames
take): by correctness (`signMessage_wp`, `verifyMessageCached_wp`) and
constant time (`signMessage_ct`, `verifyMessageCached_ct`). The contracts'
satisfiability (by `msSat`, `mvcSat`) is evaluated once
`S` is known.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Message
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A state that satisfies `signMessageContract`'s precondition. -/
def msSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a3 => 0x9000 | .a5 => 0xA000 | .a6 => 0xB000 | .a7 => 0x20000
    | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

/-- The memory of `mvcSat`: zeros, but `tr` at `0xC000`, which is `H` of a key of zeros. -/
def mvcMem (p : Params) : Mem := fun a =>
  if 0xC000 ≤ a.toNat ∧ a.toNat < 0xC040 then (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0xC000) 0
  else 0

/-- A state that satisfies `verifyMessageCachedContract`'s precondition. -/
def mvcSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a3 => 0x9000 | .a5 => 0xA000 | .a6 => 0x20000 | .a7 => 0xC000 | _ => 0
  sp := 0x100000
  mem := mvcMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, p.sigLen⟩, ⟨0xC000, 64⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

theorem mvcMem_key {p : Params} (hp : p.pkLen ≤ 0xB000) :
    bytesAt (mvcMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega_using [hp, hi]
  simp only [mvcMem, he]
  split
  · rename_i h; omega
  · rfl

/-- `mvcSat`'s `tr` is `H` of its key. -/
theorem mvcMem_tr {p : Params} (hp : p.pkLen ≤ 0xB000) :
    bytesAt (mvcMem p) 0xC000 64 = pkTr (bytesAt (mvcMem p) 0x1000 p.pkLen) := by
  rw [mvcMem_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0xC000 : Addr) + BitVec.ofNat 64 i).toNat = 0xC000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega_using [hi]
  simp only [mvcMem, he, show 0xC000 ≤ 0xC000 + i ∧ 0xC000 + i < 0xC040 by omega_using [hi], and_self, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_using [hl, hi]), Option.getD_some]

/-- `vg_mldsa*_sign_message` (or, with a prepared key `q`,
`vg_mldsa*_sign_message_prepared`) of the parameter set `p`, calling the
signing function on `μ` `f`, named `n`, meets its contract with `S` bytes of
stack. -/
theorem signMessage_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {q : Bool} {S : Nat}
    (h48 : 1168 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => PreparedKey.signEK p q stk) S) (n : String)
    (hsat : ∃ s, (signMessageEK p q S).pre s) :
    Verified RISCV64.target (signMessage n f p) (signMessageEK p q S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega_using [h48]⟩
  refine ⟨fun s hs => signMessage_wp hF h48 hf (Nat.le_refl _) (mspre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  have hpub' : MSPub p s₁ s₂ := by
    cases q
    · simp only [signMessageEK, Bool.false_eq_true, ↓reduceIte] at hpub
      sig_pub [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [mArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
    · simp only [signMessageEK, ↓reduceIte] at hpub
      sig_pub [preparedSignMessageContract, preparedSignMessageSig, RISCV64.abi, RISCV64.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [mArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  exact signMessage_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mspre_of h₁) (mspre_of h₂) hpub' e₁ e₂

/-- `vg_mldsa*_verify_message_cached` (or, with a prepared key `q`,
`vg_mldsa*_verify_message_prepared`) of the parameter set `p`, calling the
verification function on `μ` `f`, named `n`, meets its contract with `S`
bytes of stack. -/
theorem verifyMessageCached_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {q : Bool}
    {S : Nat} (h48 : 1168 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => PreparedKey.verifyEK p q stk) S)
    (n : String) (hsat : ∃ s, (verifyMessageEK p q S).pre s) :
    Verified RISCV64.target (verifyMessageCached n f p) (verifyMessageEK p q S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega_using [h48]⟩
  refine ⟨fun s hs => verifyMessageCached_wp hF h48 hf (Nat.le_refl _) (mvcpre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  have hpub' : MVCPub p s₁ s₂ := by
    cases q
    · simp only [verifyMessageEK, Bool.false_eq_true, ↓reduceIte] at hpub
      sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [vcArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
    · simp only [verifyMessageEK, ↓reduceIte] at hpub
      sig_pub [preparedVerifyMessageContract, preparedVerifyMessageSig, RISCV64.abi, RISCV64.argRegs] at hpub
      obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
      refine ⟨hsp, hl, fun r hr => ?_⟩
      simp only [vcArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  exact verifyMessageCached_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mvcpre_of h₁) (mvcpre_of h₂) hpub'
    e₁ e₂

end VG.Proof.MlDsa.RISCV64.Message
