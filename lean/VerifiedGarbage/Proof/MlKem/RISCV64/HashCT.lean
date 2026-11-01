module

public import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Prims
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
public import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Prims
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.CallsCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ML-KEM on RISC-V: the hash routine in constant time

As on PPC64LE (`Proof/MlKem/PPC64LE/HashCT.lean`): two runs of `hash` from
states whose buffers are the same (`HashOk` of the same layout, and the same
stack pointer) leak the same trace (`hash_ct`). The blocks that set up the
arguments access no memory (`relct_noMem`), the Keccak state is zeroed
through `s11` (the taint analysis), and the calls of the sponge functions are
on the same arguments in both runs (`absorbCall_ct`, …), the positions being
those of the same lengths.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.Sha3 (rates)
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)
open VG.Impl.Sha3.RISCV64.Stream (mov)

theorem addrOf_noMem (d b : Reg) (off : Nat) : (addrOf d b off).all noMem = true := by
  unfold addrOf; split <;> rfl

theorem kargs_noMem (rate : Nat) (first : Bool) (p : Piece) :
    (spongeArgs rate first p).all noMem = true := by
  simp only [spongeArgs, List.all_append, addrOf_noMem]
  cases first <;> rfl

theorem pargs_noMem (rate sfx : Nat) :
    ([mov .a2 .a0, mov .a0 .s11, .li .a1 rate, .li .a3 sfx] : List Instr).all noMem = true := rfl

/-! ## The absorbs -/

/-- After the arguments of an `absorb` or a `squeeze` of piece `p` from
position `X`. -/
structure KA (L : Lay) (idx : Reg → Nat) (rate : Nat) (p : Piece) (X : Nat) (s₀ s : State) : Prop where
  rg : Rg s₀ s
  a0 : s.gpr .a0 = L.ptr 0
  a1 : s.gpr .a1 = BitVec.ofNat 64 rate
  a2 : s.gpr .a2 = BitVec.ofNat 64 X
  a3 : s.gpr .a3 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off
  a4 : s.gpr .a4 = BitVec.ofNat 64 p.len

theorem ka_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s : State} (hc : Ctx L s₀)
    {first : Bool} {X : Nat} {p : Piece} {w : Bool} (hp : PieceOk L idx s₀ w p) (hg : Rg s₀ s)
    (hX : Pos first s = X) :
    WP isa (.block (spongeArgs rate first p)) s (KA L idx rate p X s₀) :=
  WP.mono (kargs_ok first hp.base (rate_imm hrate) hp.oenc hp.lenc) fun s₁ ⟨o₁, g3, g4, g5, g6, g7⟩ =>
    ⟨hg.kept (o₁.kept []), by rw [g3, (hg.ctx hc).s11], g4, by rw [g5, pos_r5, hX],
      by rw [g6, hg.cs _ hp.base, hp.ptr], g7⟩

/-- `Rg` through a call. -/
theorem rg_of {s₀ s s' : State} (hg : Rg s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Rg s₀ s' :=
  ⟨hrd.trans hg.rd, hwr.trans hg.wr, hsp.trans hg.sp, fun r hr => (hcs r hr).trans (hg.cs r hr)⟩

/-- The covering facts of an input piece's call. -/
theorem covR_all {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (hc : Ctx L s₀)
    (hp : PieceOk L idx s₀ false p) (hg : Rg s₀ s) :
    Covers ([L.P idx p] ++ [(⟨L.ptr 0, 200⟩ : Region)]) (s.rd ++ s.wr) ∧
      Covers [(⟨L.ptr 0, 200⟩ : Region)] s.wr :=
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
        AbsorbArgs s (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) rate X p.len := fun hc hp h =>
      absorbArgs_of hrate (h.rg.ctx hc) hp hX h.a0 h.a1 h.a2 h.a3 h.a4
    refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b ∧ Pos false a = (X + p.len) % rate ∧
      Pos false b = (X + p.len) % rate) ?_ ?_
    · refine RelCT.mono (relct_wp (F₁ := fun s' => Rg s₀₁ s' ∧ (s'.gpr .a0).toNat = (X + p.len) % rate)
        (F₂ := fun s' => Rg s₀₂ s' ∧ (s'.gpr .a0).toNat = (X + p.len) % rate)
        (Proof.Sha3.RISCV64.Stream.absorbCall_ct (st := L.ptr 0)
          (pa := L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (rate := rate) (pos := X) (pl := p.len)
          fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hA hc₁ hp₁ hab.1,
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
  a0 : s.gpr .a0 = L.ptr 0
  a1 : s.gpr .a1 = BitVec.ofNat 64 rate
  a2 : s.gpr .a2 = BitVec.ofNat 64 Y
  a3 : s.gpr .a3 = BitVec.ofNat 64 sfx

/-- The covering facts of an output piece's call. -/
theorem covW_all {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (hc : Ctx L s₀)
    (hp : PieceOk L idx s₀ true p) (hg : Rg s₀ s) :
    Covers ([] ++ [(⟨L.ptr 0, 200⟩ : Region), L.P idx p]) (s.rd ++ s.wr) ∧
      Covers [(⟨L.ptr 0, 200⟩ : Region), L.P idx p] s.wr := by
  have hcs := hg.ctx hc
  have cw : Covers [(⟨L.ptr 0, 200⟩ : Region), L.P idx p] s.wr := by
    rw [hcs.kregs.1]
    exact covers_cons' (hcs.cs (by decide)) (covers_cons' (hp.covW hg) covers_nil')
  exact ⟨by simpa using covers_wr cw, cw⟩

theorem hash_ct {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates) (hsfx : sfx < 2048)
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
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂) (taint_block [.s11] (fun a b hab => by
      rw [hab.1, hab.2, hsp]) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.s11, hc₂.s11]) (by taint_decide))
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
      WP isa (.block [mov .a2 .a0, mov .a0 .s11, .li .a1 rate, .li .a3 sfx]) s
        (PA L rate sfx Y s₀) := fun s₀ s hc hg hX =>
    WP.mono (pargs_ok (rate_imm hrate) hsfx) fun _ ⟨o', g3, g4, g5, g6⟩ =>
      ⟨hg.kept (o'.kept []), by rw [g3, (hg.ctx hc).s11], g4,
        by rw [g5, ← hX, show Pos false s = (s.gpr .a0).toNat from rfl, BitVec.ofNat_toNat,
          BitVec.setWidth_eq], g6⟩
  refine RelCT.seq (R := fun a b => PA L rate sfx Y s₀₁ a ∧ PA L rate sfx Y s₀₂ b)
    (relct_wp (relct_noMem (pargs_noMem _ _)) fun a b hab =>
      ⟨pa _ _ hc₁ hab.2.1 hab.2.2.2.1, pa _ _ hc₂ hab.2.2.1 hab.2.2.2.2⟩) ?_
  have hPA : ∀ {s₀ s : State}, Ctx L s₀ → PA L rate sfx Y s₀ s → PadArgs s (L.ptr 0) rate Y := fun hc h =>
    padArgs_of hrate (h.rg.ctx hc) hY h.a0 h.a1 h.a2
  have cK : ∀ {s₀ s : State}, Ctx L s₀ → Rg s₀ s →
      Covers ([] ++ [(⟨L.ptr 0, 200⟩ : Region)]) (s.rd ++ s.wr) ∧ Covers [(⟨L.ptr 0, 200⟩ : Region)] s.wr :=
    fun hc hg => ⟨by simpa using covers_wr (covers_kregs (hg.ctx hc)), covers_kregs (hg.ctx hc)⟩
  refine RelCT.seq (R := fun a b => Rg s₀₁ a ∧ Rg s₀₂ b)
    (RelCT.mono (relct_wp (F₁ := Rg s₀₁) (F₂ := Rg s₀₂)
      (Proof.Sha3.RISCV64.Stream.padCall_ct (st := L.ptr 0) (rate := rate) (pos := Y) fun a b hab =>
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
      SqueezeArgs s (L.ptr 0) (L.ptr (idx q.base) + BitVec.ofNat 64 q.off) rate 0 q.len := fun hc hq h =>
    squeezeArgs_of hrate (h.rg.ctx hc) hq (Nat.zero_le _) h.a0 h.a1 h.a2 h.a3 h.a4
  refine RelCT.seq (R := fun _ _ => True)
    (Proof.Sha3.RISCV64.Stream.squeezeCall_ct (st := L.ptr 0)
      (pa := L.ptr (idx q.base) + BitVec.ofNat 64 q.off) (rate := rate) (pos := 0) (pl := q.len)
      fun a b hab => ⟨by rw [hab.1.rg.sp, hab.2.rg.sp, hsp], hS hc₁ hq₁ hab.1, hS hc₂ hq₂ hab.2,
      (covW_all hc₁ hq₁ hab.1.rg).1, (covW_all hc₁ hq₁ hab.1.rg).2, (covW_all hc₂ hq₂ hab.2.rg).1,
      (covW_all hc₂ hq₂ hab.2.rg).2⟩) relct_nil

end VG.Proof.MlKem.RISCV64
