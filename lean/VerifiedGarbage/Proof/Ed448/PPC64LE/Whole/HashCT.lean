module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall

/-!
# Ed448's whole functions on PPC64LE: the hash in constant time

As ML-KEM's on this target (`Proof/MlKem/PPC64LE/HashCT.lean`): two runs of
`hash` from states that agree on the registers it reads (`hashRegs`) and on
the stack pointer leak the same trace (`hash_ct`). The sponge functions save
and restore registers in their working space, which a taint analysis would
take to be secret afterwards, so their calls are related through their own
constant-time proofs, on the same arguments in both runs (the positions being
those of the same lengths); the blocks that set their arguments access no
memory, and the Keccak state is zeroed through `sc` (the taint analysis).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Proof.MlKem.PPC64LE (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call absorb_pre pad_pre
  squeeze_pre ce_gpr)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Impl.Ed25519.PPC64LE.Whole (mov)

/-! ## Blocks that access no memory -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .lbz .. | .stb .. | .loadRev .. | .storeRev .. | .push _ | .pop _
  | .alloc _ | .lxvd2x .. | .stxvd2x .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : VG.PPC64LE.addrs i s = [] := by
  cases i <;> first | rfl | simp [noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [addrs_noMem hm.1 s]
      simpa using execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noMem h e₁, execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

/-- The empty block. -/
theorem relct_nil {P : State → State → Prop} : RelCT isa P (.block []) P := fun _ _ _ _ _ _ hp e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

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
def _root_.VG.Impl.Ed448.PPC64LE.Whole.Piece.regs (p : Piece) : List Reg :=
  p.base :: match p.len with
    | .imm _ => []
    | .reg r => [r]

/-- The registers `hash` reads. -/
def hashRegs (sc f : Reg) (ps : List Piece) : List Reg := sc :: f :: ps.flatMap Piece.regs

/-- A state `hash sc ps f o` may run from. -/
structure HashOk (sc f : Reg) (o : Nat) (ps : List Piece) (s : State) : Prop where
  psc : sc ∈ preserved
  pf : f ∈ preserved
  po : o < 2 ^ 15
  ne : ps ≠ []
  env : KEnv (s.gpr sc) s
  ins : ∀ p ∈ ps, PieceOk (s.gpr sc) s p
  w : PPC64LE.Covers [⟨s.gpr f + BitVec.ofNat 64 o, 114⟩] s.wr
  dsc : Region.Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, 114⟩ ⟨s.gpr sc, 8192⟩
  dsp : (below s.sp 48).Disjoint ⟨s.gpr f + BitVec.ofNat 64 o, 114⟩

/-- A piece of two states that agree on its registers. -/
theorem _root_.VG.Impl.Ed448.PPC64LE.Whole.Piece.agree {g₁ g₂ : Reg → BitVec 64} {p : Piece} (h : ∀ r ∈ p.regs, g₁ r = g₂ r) :
    p.addr g₁ = p.addr g₂ ∧ p.len.val g₁ = p.len.val g₂ := by
  obtain ⟨b, o, l⟩ := p
  refine ⟨by simp only [Piece.addr, h b (by simp [Piece.regs])], ?_⟩
  cases l with
  | imm n => rfl
  | reg r => exact congrArg BitVec.toNat (h r (by simp [Piece.regs]))

/-! ## The calls of the sponge functions -/

section
variable {sc : Addr} {pa : Addr} {pl : Nat} {pos : Nat}

abbrev kWr (sc : Addr) : List Region := [⟨sc, 200⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩]

/-- Both runs call `absorb` on the same arguments. -/
theorem absorbCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      AbsorbArgs a sc pa (sc + BitVec.ofNat 64 200) 136 pos pl ∧
      AbsorbArgs b sc pa (sc + BitVec.ofNat 64 200) 136 pos pl ∧
      PPC64LE.Covers ([⟨pa, pl⟩] ++ kWr sc) (a.rd ++ a.wr) ∧ PPC64LE.Covers (kWr sc) a.wr ∧
      PPC64LE.Covers ([⟨pa, pl⟩] ++ kWr sc) (b.rd ++ b.wr) ∧ PPC64LE.Covers (kWr sc) b.wr) :
    RelCT isa P callAbsorb fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct
    Proof.Sha3.PPC64LE.Stream.absorb_ct [⟨pa, pl⟩] (kWr sc) fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨absorb_pre ha, absorb_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.absorbPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hsp, and_self]

/-- Both runs call `pad` on the same arguments. -/
theorem padCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      PadArgs a sc (sc + BitVec.ofNat 64 200) 136 pos ∧ PadArgs b sc (sc + BitVec.ofNat 64 200) 136 pos ∧
      PPC64LE.Covers ([] ++ kWr sc) (a.rd ++ a.wr) ∧ PPC64LE.Covers (kWr sc) a.wr ∧
      PPC64LE.Covers ([] ++ kWr sc) (b.rd ++ b.wr) ∧ PPC64LE.Covers (kWr sc) b.wr) :
    RelCT isa P callPad fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct
    Proof.Sha3.PPC64LE.Stream.pad_ct [] (kWr sc) fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨pad_pre ha, pad_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.padPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r7, hb.r3, hb.r4, hb.r5, hb.r7, hsp, and_self]

/-- Both runs call `squeeze` on the same arguments. -/
theorem squeezeCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      SqueezeArgs a sc pa (sc + BitVec.ofNat 64 200) 136 pos pl ∧
      SqueezeArgs b sc pa (sc + BitVec.ofNat 64 200) 136 pos pl ∧
      PPC64LE.Covers ([] ++ [⟨sc, 200⟩, ⟨pa, pl⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩]) (a.rd ++ a.wr) ∧
      PPC64LE.Covers [⟨sc, 200⟩, ⟨pa, pl⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩] a.wr ∧
      PPC64LE.Covers ([] ++ [⟨sc, 200⟩, ⟨pa, pl⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩]) (b.rd ++ b.wr) ∧
      PPC64LE.Covers [⟨sc, 200⟩, ⟨pa, pl⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩] b.wr) :
    RelCT isa P callSqueeze fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct
    Proof.Sha3.PPC64LE.Stream.squeeze_ct [] [⟨sc, 200⟩, ⟨pa, pl⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩]
    fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨squeeze_pre ha, squeeze_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.squeezePPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hsp, and_self]

end

/-! ## The absorbs -/

/-- After the arguments of an `absorb` of piece `p` from position `X`. -/
structure KA (sc : Reg) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r3 : s.gpr .r3 = s₀.gpr sc
  r4 : s.gpr .r4 = BitVec.ofNat 64 136
  r5 : s.gpr .r5 = BitVec.ofNat 64 X
  r6 : s.gpr .r6 = p.addr s₀.gpr
  r7 : s.gpr .r7 = BitVec.ofNat 64 (p.len.val s₀.gpr)
  r8 : s.gpr .r8 = s₀.gpr sc + BitVec.ofNat 64 200

theorem ka_ok {sc : Reg} (hsc : sc ∈ preserved) {s₀ s : State} {first : Bool} {X : Nat} {p : Piece}
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) (hX : Pos first s = X) :
    WP isa (.block (absorbArgs sc first p)) s (KA sc p X s₀) :=
  WP.mono (absorbArgs_ok hsc first hp.base hp.off hp.len) fun s₁ ⟨o₁, g3, g4, g5, g6, g7, g8⟩ =>
    ⟨hg.only o₁, by rw [g3, hg.cs _ hsc], g4, by
      rw [g5, ← hX]; cases first
      · show s.gpr .r3 = BitVec.ofNat 64 (s.gpr .r3).toNat; rw [ofNat_toNat]
      · rfl,
      by rw [g6, Piece.addr_eq hp.base hg.cs], by rw [g7, Len.val_eq hp.len hg.cs], by rw [g8, hg.cs _ hsc]⟩

theorem ka_args {sc : Reg} {s₀ s : State} {p : Piece} {X : Nat} (he : KEnv (s₀.gpr sc) s₀)
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hX : X < 136) (h : KA sc p X s₀ s) :
    AbsorbArgs s (s₀.gpr sc) (p.addr s₀.gpr) (s₀.gpr sc + BitVec.ofNat 64 200) 136 X (p.len.val s₀.gpr) :=
  ⟨h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, rate136, hX, Len.val_lt _ hp.len, by rw [h.rg.sp]; exact he.sp,
    st_kw _, hp.dsc.sub_right (st_sub _), hp.dsc.sub_right (kw_sub _),
    by rw [h.rg.sp]; exact he.d.sub_right (st_sub _), by rw [h.rg.sp]; exact hp.dsp,
    by rw [h.rg.sp]; exact he.d.sub_right (kw_sub _)⟩

theorem ka_covers {sc : Reg} {s₀ s : State} {p : Piece} (he : KEnv (s₀.gpr sc) s₀)
    (hp : PieceOk (s₀.gpr sc) s₀ p) (hg : Rg s₀ s) :
    PPC64LE.Covers ([⟨p.addr s₀.gpr, p.len.val s₀.gpr⟩] ++ kWr (s₀.gpr sc)) (s.rd ++ s.wr) ∧
      PPC64LE.Covers (kWr (s₀.gpr sc)) s.wr := by
  have cw : PPC64LE.Covers (kWr (s₀.gpr sc)) s.wr := by rw [hg.wr]; exact cov_st he.w
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
        (F₁ := fun s' => Rg s₀₁ s' ∧ (s'.gpr .r3).toNat = (X + p.len.val s₀₁.gpr) % 136)
        (F₂ := fun s' => Rg s₀₂ s' ∧ (s'.gpr .r3).toNat = (X + p.len.val s₀₂.gpr) % 136)
        (absorbCall_ct (sc := s₀₁.gpr sc) (pa := p.addr s₀₁.gpr) (pl := p.len.val s₀₁.gpr) (pos := X)
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
  r3 : s.gpr .r3 = s₀.gpr sc
  r4 : s.gpr .r4 = BitVec.ofNat 64 136
  r5 : s.gpr .r5 = BitVec.ofNat 64 Y
  r7 : s.gpr .r7 = s₀.gpr sc + BitVec.ofNat 64 200

/-- After the arguments of the `squeeze`. -/
structure SA (sc f : Reg) (o : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r3 : s.gpr .r3 = s₀.gpr sc
  r4 : s.gpr .r4 = BitVec.ofNat 64 136
  r5 : s.gpr .r5 = BitVec.ofNat 64 0
  r6 : s.gpr .r6 = s₀.gpr f + BitVec.ofNat 64 o
  r7 : s.gpr .r7 = BitVec.ofNat 64 114
  r8 : s.gpr .r8 = s₀.gpr sc + BitVec.ofNat 64 200

theorem hash_regs {sc f : Reg} {ps : List Piece} {g₁ g₂ : Reg → BitVec 64}
    (h : ∀ r ∈ hashRegs sc f ps, g₁ r = g₂ r) :
    g₁ sc = g₂ sc ∧ g₁ f = g₂ f ∧ ∀ p ∈ ps, ∀ r ∈ p.regs, g₁ r = g₂ r :=
  ⟨h sc (by simp [hashRegs]), h f (by simp [hashRegs]), fun p hp r hr => h r (by
    simp only [hashRegs, List.mem_cons, List.mem_flatMap]; exact .inr (.inr ⟨p, hp, hr⟩))⟩

theorem hash_ct {sc f : Reg} {o : Nat} {ps : List Piece} {P : State → State → Prop}
    {hint : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hz : (VG.PPC64LE.taint.check (Taint.ofRegs [sc]) (.block (Impl.MlKem.PPC64LE.zeroState sc)) hint).isSome =
      true)
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
  unfold Impl.Ed448.PPC64LE.Whole.hash
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
    fun s₀ s hg hX => WP.mono (padArgs_ok hsc) fun _ ⟨o', g3, g4, g5, _, g7⟩ =>
      ⟨hg.only o', by rw [g3, hg.cs _ hsc], g4,
        by rw [g5, ← hX, show Pos false s = (s.gpr .r3).toNat from rfl, ofNat_toNat], by rw [g7, hg.cs _ hsc]⟩
  refine RelCT.seq (R := fun a b => PA sc Y s₀₁ a ∧ PA sc Y s₀₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab =>
      ⟨pa _ _ hab.2.1 hab.2.2.2.1, pa _ _ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, KEnv (s₀.gpr sc) s₀ → PA sc Y s₀ s →
      PadArgs s (s₀.gpr sc) (s₀.gpr sc + BitVec.ofNat 64 200) 136 Y := fun he h =>
    ⟨h.r3, h.r4, h.r5, h.r7, rate136, hY, by rw [h.rg.sp]; exact he.sp, st_kw _,
      by rw [h.rg.sp]; exact he.d.sub_right (st_sub _), by rw [h.rg.sp]; exact he.d.sub_right (kw_sub _)⟩
  have cK : ∀ {s₀ s : State}, KEnv (s₀.gpr sc) s₀ → Rg s₀ s →
      PPC64LE.Covers ([] ++ kWr (s₀.gpr sc)) (s.rd ++ s.wr) ∧ PPC64LE.Covers (kWr (s₀.gpr sc)) s.wr :=
    fun he hg => ⟨by simpa using cov_right (by rw [hg.wr]; exact cov_st he.w),
      by rw [hg.wr]; exact cov_st he.w⟩
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (padCall_ct (sc := s₀₁.gpr sc) (pos := Y)
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
    fun s₀ s hg => WP.mono (squeezeArgs_ok hsc h₁.pf h₁.po) fun _ ⟨o', g3, g4, g5, g6, g7, g8⟩ =>
      ⟨hg.only o', by rw [g3, hg.cs _ hsc], g4, g5, by rw [g6, hg.cs _ h₁.pf], g7, by rw [g8, hg.cs _ hsc]⟩
  refine RelCT.seq (R := fun a b => SA sc f o s₀₁ a ∧ SA sc f o s₀₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨sa _ _ hab.1, sa _ _ hab.2⟩) ?_
  have hSA : ∀ {s₀ s : State}, HashOk sc f o ps s₀ → SA sc f o s₀ s →
      SqueezeArgs s (s₀.gpr sc) (s₀.gpr f + BitVec.ofNat 64 o) (s₀.gpr sc + BitVec.ofNat 64 200) 136 0 114 :=
    fun hh h => ⟨h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, rate136, by decide, by decide,
      by rw [h.rg.sp]; exact hh.env.sp, hh.dsc.symm.sub_left (st_sub _), st_kw _, hh.dsc.sub_right (kw_sub _),
      by rw [h.rg.sp]; exact hh.env.d.sub_right (st_sub _), by rw [h.rg.sp]; exact hh.dsp,
      by rw [h.rg.sp]; exact hh.env.d.sub_right (kw_sub _)⟩
  have cS : ∀ {s₀ s : State}, HashOk sc f o ps s₀ → Rg s₀ s →
      PPC64LE.Covers [⟨s₀.gpr sc, 200⟩, ⟨s₀.gpr f + BitVec.ofNat 64 o, 114⟩,
        ⟨s₀.gpr sc + BitVec.ofNat 64 200, 640⟩] s.wr := fun hh hg => by
    rw [hg.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_st hh.env.w a n ⟨_, List.mem_cons_self, hc⟩
    · exact hh.w a n ⟨_, List.mem_cons_self, hc⟩
    · exact cov_st hh.env.w a n ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
  exact squeezeCall_ct (sc := s₀₁.gpr sc) (pa := s₀₁.gpr f + BitVec.ofNat 64 o) (pl := 114) (pos := 0)
    fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hSA h₁ hab.1, by rw [esc, ef]; exact hSA h₂ hab.2,
      by simpa using cov_right (cS h₁ hab.1.rg), cS h₁ hab.1.rg,
      by rw [esc, ef]; simpa using cov_right (cS h₂ hab.2.rg), by rw [esc, ef]; exact cS h₂ hab.2.rg⟩

end VG.Proof.Ed448.PPC64LE.Whole
