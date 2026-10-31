module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.Covers

import VerifiedGarbage.Proof.MlKem.PPC64LE.Prims
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Prims
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# ML-KEM on PPC64LE: the hash routine in constant time

As on 32-bit ARM (`Proof/MlKem/Arm/HashCT.lean`): two runs of `hash` from
states whose buffers are the same (`HashOk` of the same layout, and the same
stack pointer) leak the same trace (`hash_ct`). The blocks that set up the
arguments access no memory (`relct_noMem`), the Keccak state is zeroed
through `r31` (the taint analysis), and the calls of the sponge functions are
on the same arguments in both runs (`absorbCall_ct`, …), the positions being
those of the same lengths.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.Sha3 (rates)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-! ## Blocks that access no memory -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .lbz .. | .stb .. | .loadRev .. | .storeRev .. | .push _ | .pop _
  | .alloc _ | .lxvd2x .. | .lxvd2xTbl .. | .stxvd2x .. => false
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

theorem kargs_noMem (rate : Nat) (first : Bool) (p : Piece) :
    (spongeArgs rate first p).all noMem = true := by cases first <;> rfl

theorem pargs_noMem (rate sfx : Nat) :
    ([mov .r5 .r3, mov .r3 .r31, .li .r4 rate, .li .r6 sfx, .addi .r7 .r31 oWork] : List Instr).all noMem =
      true := rfl

/-! ## The calls of the sponge functions -/

section
variable {L : Lay} {idx : Reg → Nat} {p : Piece} {rate pos : Nat}

/-- The regions a call for the piece `p` reads, and those it writes. -/
abbrev pRd (L : Lay) (idx : Reg → Nat) (p : Piece) : List Region :=
  [⟨L.ptr (idx p.base) + BitVec.ofNat 64 p.off, p.len⟩]

abbrev kWr (L : Lay) : List Region := [⟨L.ptr 0, 200⟩, ⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]

/-- Both runs call `absorb` on the same arguments. -/
theorem absorbCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      AbsorbArgs a (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off)
        (L.ptr 0 + BitVec.ofNat 64 200) rate pos p.len ∧
      AbsorbArgs b (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off)
        (L.ptr 0 + BitVec.ofNat 64 200) rate pos p.len ∧
      Covers (pRd L idx p ++ kWr L) (a.rd ++ a.wr) ∧ Covers (kWr L) a.wr ∧
      Covers (pRd L idx p ++ kWr L) (b.rd ++ b.wr) ∧ Covers (kWr L) b.wr) :
    RelCT isa P callAbsorb fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct
    Proof.Sha3.PPC64LE.Stream.absorb_ct (pRd L idx p) (kWr L) fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨absorb_pre ha, absorb_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.absorbPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hsp, and_self]

/-- Both runs call `squeeze` on the same arguments. -/
theorem squeezeCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      SqueezeArgs a (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off)
        (L.ptr 0 + BitVec.ofNat 64 200) rate pos p.len ∧
      SqueezeArgs b (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off)
        (L.ptr 0 + BitVec.ofNat 64 200) rate pos p.len ∧
      Covers ([] ++ (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]))
        (a.rd ++ a.wr) ∧
      Covers (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]) a.wr ∧
      Covers ([] ++ (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]))
        (b.rd ++ b.wr) ∧
      Covers (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]) b.wr) :
    RelCT isa P callSqueeze fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct
    Proof.Sha3.PPC64LE.Stream.squeeze_ct []
    (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]) fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨squeeze_pre ha, squeeze_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.squeezePPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r6 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r8 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hsp, and_self]

/-- Both runs call `pad` on the same arguments. -/
theorem padCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧
      PadArgs a (L.ptr 0) (L.ptr 0 + BitVec.ofNat 64 200) rate pos ∧
      PadArgs b (L.ptr 0) (L.ptr 0 + BitVec.ofNat 64 200) rate pos ∧
      Covers ([] ++ kWr L) (a.rd ++ a.wr) ∧ Covers (kWr L) a.wr ∧
      Covers ([] ++ kWr L) (b.rd ++ b.wr) ∧ Covers (kWr L) b.wr) :
    RelCT isa P callPad fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct
    Proof.Sha3.PPC64LE.Stream.pad_ct [] (kWr L) fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨pad_pre ha, pad_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.padPPC64LE, ce_gpr _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r4 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.r7 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp,
    ha.r3, ha.r4, ha.r5, ha.r7, hb.r3, hb.r4, hb.r5, hb.r7, hsp, and_self]

end

/-! ## The absorbs -/

/-- After the arguments of an `absorb` or a `squeeze` of piece `p` from
position `X`. -/
structure KA (L : Lay) (idx : Reg → Nat) (rate : Nat) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r3 : s.gpr .r3 = L.ptr 0
  r4 : s.gpr .r4 = BitVec.ofNat 64 rate
  r5 : s.gpr .r5 = BitVec.ofNat 64 X
  r6 : s.gpr .r6 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off
  r7 : s.gpr .r7 = BitVec.ofNat 64 p.len
  r8 : s.gpr .r8 = L.ptr 0 + BitVec.ofNat 64 200

theorem ka_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s : State} (hc : Ctx L s₀)
    {first : Bool} {X : Nat} {p : Piece} {w : Bool} (hp : PieceOk L idx s₀ w p) (hg : Rg s₀ s)
    (hX : Pos first s = X) :
    WP isa (.block (spongeArgs rate first p)) s (KA L idx rate p X s₀) :=
  WP.mono (kargs_ok first hp.base (rate_imm hrate) hp.oenc hp.lenc) fun s₁ ⟨o₁, g3, g4, g5, g6, g7, g8⟩ =>
    ⟨hg.kept (o₁.kept []), by rw [g3, (hg.ctx hc).r31], g4, by rw [g5, pos_r5, hX],
      by rw [g6, hg.cs _ hp.base, hp.ptr], g7, by rw [g8, (hg.ctx hc).r31]⟩

/-- `Rg` through a call. -/
theorem rg_of {s₀ s s' : State} (hg : Rg s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Rg s₀ s' :=
  ⟨hrd.trans hg.rd, hwr.trans hg.wr, hsp.trans hg.sp, fun r hr => (hcs r hr).trans (hg.cs r hr)⟩

/-- The covering facts of an input piece's call. -/
theorem covR_all {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (hc : Ctx L s₀)
    (hp : PieceOk L idx s₀ false p) (hg : Rg s₀ s) :
    Covers (pRd L idx p ++ kWr L) (s.rd ++ s.wr) ∧ Covers (kWr L) s.wr :=
  ⟨covers_append (hp.covR hg) (covers_wr (covers_kregs (hg.ctx hc))), covers_kregs (hg.ctx hc)⟩

theorem absorbs_ct {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀₁ s₀₂ : State}
    (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂) (hsp : s₀₁.sp = s₀₂.sp) :
    ∀ (ps : List Piece) (first : Bool) (X : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀₁ false p ∧ PieceOk L idx s₀₂ false p) → X < rate →
      RelCT isa (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos first a = X ∧ Pos first b = X) (absorbs rate first ps)
        (fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ Pos (first && ps.isEmpty) a = Y ∧
          Pos (first && ps.isEmpty) b = Y)
  | [], first, X, _, hX =>
    RelCT.mono relct_nil (fun _ _ h => h) fun _ _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, X, hX, by simpa using h3, by simpa using h4⟩
  | p :: ps, first, X, hps, hX => by
    obtain ⟨hp₁, hp₂⟩ := hps p (List.mem_cons_self ..)
    have rpos := rate_pos hrate
    refine RelCT.seq (R := fun a b => KA L idx rate p X s₀₁ a ∧ KA L idx rate p X s₀₂ b)
      (relct_wp (relct_noMem (kargs_noMem _ _ _)) fun a b hab =>
        ⟨ka_ok hrate hc₁ hp₁ hab.1 hab.2.2.1, ka_ok hrate hc₂ hp₂ hab.2.1 hab.2.2.2⟩) ?_
    have hA : ∀ {s₀ s : State}, Ctx L s₀ → PieceOk L idx s₀ false p → KA L idx rate p X s₀ s →
        AbsorbArgs s (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (L.ptr 0 + BitVec.ofNat 64 200)
          rate X p.len := fun hc hp h =>
      absorbArgs_of hrate (h.rg.ctx hc) hp hX h.r3 h.r4 h.r5 h.r6 h.r7 h.r8
    refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = (X + p.len) % rate ∧
      Pos false b = (X + p.len) % rate) ?_ ?_
    · refine RelCT.mono (relct_wp (F₁ := fun s' => Rg s₀₁ s' ∧ (s'.gpr .r3).toNat = (X + p.len) % rate)
        (F₂ := fun s' => Rg s₀₂ s' ∧ (s'.gpr .r3).toNat = (X + p.len) % rate)
        (absorbCall_ct fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hA hc₁ hp₁ hab.1,
          hA hc₂ hp₂ hab.2, (covR_all hc₁ hp₁ hab.1.rg).1, (covR_all hc₁ hp₁ hab.1.rg).2,
          (covR_all hc₂ hp₂ hab.2.rg).1, (covR_all hc₂ hp₂ hab.2.rg).2⟩)
        fun a b hab =>
        ⟨absorb_call (hA hc₁ hp₁ hab.1) (covR_all hc₁ hp₁ hab.1.rg).1 (covR_all hc₁ hp₁ hab.1.rg).2
          fun s' rd' wr' sp' cs' _ _ r' => ⟨rg_of hab.1.rg rd' wr' sp' cs', r'⟩,
         absorb_call (hA hc₂ hp₂ hab.2) (covR_all hc₂ hp₂ hab.2.rg).1 (covR_all hc₂ hp₂ hab.2.rg).2
          fun s' rd' wr' sp' cs' _ _ r' => ⟨rg_of hab.2.rg rd' wr' sp' cs', r'⟩⟩)
        (fun _ _ h => h) fun _ _ ⟨⟨g₁, r₁⟩, ⟨g₂, r₂⟩⟩ => ⟨g₁, g₂, r₁, r₂⟩
    · refine RelCT.mono (absorbs_ct hrate hc₁ hc₂ hsp ps false ((X + p.len) % rate)
        (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (Nat.mod_lt _ rpos)) (fun _ _ h => h)
        fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, by simpa using e₁, by simpa using e₂⟩

/-! ## The whole hash -/

/-- A state `hash` may run from. -/
structure HashOk (L : Lay) (idx : Reg → Nat) (ins outs : List Piece) (s : State) : Prop where
  ctx : Ctx L s
  ins : ∀ p ∈ ins, PieceOk L idx s false p
  outs : ∀ p ∈ outs, PieceOk L idx s true p

/-- After the arguments of a `pad` from position `Y`. -/
structure PA (L : Lay) (rate sfx Y : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  r3 : s.gpr .r3 = L.ptr 0
  r4 : s.gpr .r4 = BitVec.ofNat 64 rate
  r5 : s.gpr .r5 = BitVec.ofNat 64 Y
  r6 : s.gpr .r6 = BitVec.ofNat 64 sfx
  r7 : s.gpr .r7 = L.ptr 0 + BitVec.ofNat 64 200

/-- The covering facts of an output piece's call. -/
theorem covW_all {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (hc : Ctx L s₀)
    (hp : PieceOk L idx s₀ true p) (hg : Rg s₀ s) :
    Covers ([] ++ (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]))
        (s.rd ++ s.wr) ∧
      Covers (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]) s.wr := by
  have hcs := hg.ctx hc
  have cw : Covers (⟨L.ptr 0, 200⟩ :: pRd L idx p ++ [⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩]) s.wr := by
    rw [hcs.kregs.1]
    exact covers_cons' (hcs.cs (by decide))
      (covers_append (hp.covW hg) (covers_cons' (hcs.cs (by decide)) covers_nil'))
  exact ⟨by simpa using covers_wr cw, cw⟩

theorem hash_ct {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates) (hsfx : sfx < 32768)
    {ins : List Piece} {q : Piece} (hne : ins ≠ []) {P : State → State → Prop}
    (hP : ∀ a b, P a b → HashOk L idx ins [q] a ∧ HashOk L idx ins [q] b ∧ a.sp = b.sp) :
    RelCT isa P (hash rate sfx ins [q]) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ HashOk L idx ins [q] x.1 ∧
    HashOk L idx ins [q] x.2 ∧ x.1.sp = x.2.sp) (RelCT.exists_ fun ⟨s₀₁, s₀₂⟩ => ?_)
    (fun a b h => ⟨(a, b), rfl, rfl, hP a b h⟩) (fun _ _ h => h)
  by_cases hH : HashOk L idx ins [q] s₀₁ ∧ HashOk L idx ins [q] s₀₂ ∧ s₀₁.sp = s₀₂.sp
  swap
  · exact RelCT.of_false fun a b h => hH ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨h₁, h₂, hsp⟩ := hH
  have hc₁ := h₁.ctx
  have hc₂ := h₂.ctx
  have rpos := rate_pos hrate
  refine RelCT.mono (P := fun a b => a = s₀₁ ∧ b = s₀₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  -- the state set to zero
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (taint_block [.r31] (fun a b hab => by
      rw [hab.1, hab.2, hsp]) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r31, hc₂.r31]) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact WP.mono (zeroState_ok hc₁) fun _ h => h.1.rg,
        by rw [hab.2]; exact WP.mono (zeroState_ok hc₂) fun _ h => h.1.rg⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  -- the absorbs
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ ∃ Y, Y < rate ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.mono (absorbs_ct hrate hc₁ hc₂ hsp ins true 0 (fun p hp => ⟨h₁.ins p hp, h₂.ins p hp⟩) rpos)
      (fun _ _ h => ⟨h.1, h.2, rfl, rfl⟩) fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨g₁, g₂, Y, hY, ?_, ?_⟩) ?_
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₁
  · cases ins with
    | nil => exact absurd rfl hne
    | cons _ _ => exact e₂
  -- the padding
  refine RelCT.mono (P := fun a b => ∃ Y, Y < rate ∧ Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = Y ∧ Pos false b = Y)
    (RelCT.exists_ fun Y => ?_) (fun _ _ ⟨g₁, g₂, Y, hY, e₁, e₂⟩ => ⟨Y, hY, g₁, g₂, e₁, e₂⟩) (fun _ _ h => h)
  by_cases hY : Y < rate
  swap
  · exact RelCT.of_false fun a b h => hY h.1
  have pa : ∀ (s₀ s : State), Ctx L s₀ → Rg s₀ s → Pos false s = Y →
      WP isa (.block [mov .r5 .r3, mov .r3 .r31, .li .r4 rate, .li .r6 sfx, .addi .r7 .r31 oWork]) s
        (PA L rate sfx Y s₀) := fun s₀ s hc hg hX =>
    WP.mono (pargs_ok (rate_imm hrate) hsfx) fun _ ⟨o', g3, g4, g5, g6, g7⟩ =>
      ⟨hg.kept (o'.kept []), by rw [g3, (hg.ctx hc).r31], g4,
        by rw [g5, ← hX, show Pos false s = (s.gpr .r3).toNat from rfl, BitVec.ofNat_toNat,
          BitVec.setWidth_eq], g6, by rw [g7, (hg.ctx hc).r31]⟩
  refine RelCT.seq (R := fun a b => PA L rate sfx Y s₀₁ a ∧ PA L rate sfx Y s₀₂ b)
    (relct_wp (relct_noMem (pargs_noMem _ _)) fun a b hab =>
      ⟨pa _ _ hc₁ hab.2.1 hab.2.2.2.1, pa _ _ hc₂ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, Ctx L s₀ → PA L rate sfx Y s₀ s →
      PadArgs s (L.ptr 0) (L.ptr 0 + BitVec.ofNat 64 200) rate Y := fun hc h =>
    padArgs_of hrate (h.rg.ctx hc) hY h.r3 h.r4 h.r5 h.r7
  have cK : ∀ {s₀ s : State}, Ctx L s₀ → Rg s₀ s →
      Covers ([] ++ kWr L) (s.rd ++ s.wr) ∧ Covers (kWr L) s.wr := fun hc hg =>
    ⟨by simpa using covers_wr (covers_kregs (hg.ctx hc)), covers_kregs (hg.ctx hc)⟩
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (padCall_ct fun a b hab =>
      ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hPA hc₁ hab.1, hPA hc₂ hab.2, (cK hc₁ hab.1.rg).1,
        (cK hc₁ hab.1.rg).2, (cK hc₂ hab.2.rg).1, (cK hc₂ hab.2.rg).2⟩) fun a b hab =>
      ⟨pad_call (hPA hc₁ hab.1) (cK hc₁ hab.1.rg).1 (cK hc₁ hab.1.rg).2
        fun s' rd' wr' sp' cs' _ _ => rg_of hab.1.rg rd' wr' sp' cs',
       pad_call (hPA hc₂ hab.2) (cK hc₂ hab.2.rg).1 (cK hc₂ hab.2.rg).2
        fun s' rd' wr' sp' cs' _ _ => rg_of hab.2.rg rd' wr' sp' cs'⟩)
      (fun _ _ h => h) fun _ _ h => h) ?_
  -- the squeeze
  have hq₁ := h₁.outs q (List.mem_singleton_self _)
  have hq₂ := h₂.outs q (List.mem_singleton_self _)
  refine RelCT.seq (R := fun a b => KA L idx rate q 0 s₀₁ a ∧ KA L idx rate q 0 s₀₂ b)
    (relct_wp (relct_noMem (kargs_noMem _ _ _)) fun a b hab =>
      ⟨ka_ok hrate hc₁ hq₁ hab.1 rfl, ka_ok hrate hc₂ hq₂ hab.2 rfl⟩) ?_
  have hS : ∀ {s₀ s : State}, Ctx L s₀ → PieceOk L idx s₀ true q → KA L idx rate q 0 s₀ s →
      SqueezeArgs s (L.ptr 0) (L.ptr (idx q.base) + BitVec.ofNat 64 q.off) (L.ptr 0 + BitVec.ofNat 64 200)
        rate 0 q.len := fun hc hq h =>
    squeezeArgs_of hrate (h.rg.ctx hc) hq (Nat.zero_le _) h.r3 h.r4 h.r5 h.r6 h.r7 h.r8
  refine RelCT.seq (R := fun _ _ => True) (squeezeCall_ct fun a b hab =>
    ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hS hc₁ hq₁ hab.1, hS hc₂ hq₂ hab.2,
      (covW_all hc₁ hq₁ hab.1.rg).1, (covW_all hc₁ hq₁ hab.1.rg).2, (covW_all hc₂ hq₂ hab.2.rg).1,
      (covW_all hc₂ hq₂ hab.2.rg).2⟩) relct_nil

end VG.Proof.MlKem.PPC64LE
