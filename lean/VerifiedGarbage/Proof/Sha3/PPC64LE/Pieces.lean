module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Pieces
import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHAKE256 of pieces on PPC64LE

As Ed448's whole functions' hash was proven, for any output length:
`hash sc ps f o n` (`Impl/Sha3/PPC64LE/Pieces.lean`) leaves `SHAKE256` of
the concatenation of the pieces `ps`, `n` bytes, at `o(f)` (`hash_ok`): from
the zeroed state, each `absorb` continues the message from the position the
previous one returned, then the padding and the `squeeze`, through the
sponge functions' calls (`Proof/MlKem/PPC64LE/KCall.lean`). The pieces'
pointers and lengths are in callee-saved registers, which the calls keep. A
hash changes only its scratch space (`N` bytes at `sc`, at least the 840 the
Keccak state and the sponge functions' working space take), the output, the
48 bytes below the stack pointer and registers other than the callee-saved
ones (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Pieces

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Pieces VG.Proof.X25519.PPC64LE
open VG.Proof.MlKem.PPC64LE (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)
open VG.Spec.Sha3 (Repr stateAt)

/-! ## What a step keeps -/

/-- The permissions, the stack pointer and the callee-saved registers are kept, and memory outside
`W`. -/
structure Kept (W : List Region) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame W s.mem s'.mem

theorem Kept.refl (W : List Region) (s : State) : Kept W s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Kept.trans {W : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept W s₁ s₂) (h₂ : Kept W s₂ s₃) :
    Kept W s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr),
    h₁.frame.trans h₂.frame⟩

theorem Kept.mono {W W' : List Region} {s s' : State} (h : Kept W s s')
    (hw : ∀ r ∈ W, ∃ R ∈ W', Region.Sub r R) : Kept W' s s' :=
  ⟨h.rd, h.wr, h.sp, h.cs, h.frame.sub hw⟩

/-- A block that writes only registers other than the callee-saved ones. -/
theorem Kept.of_regs {W : List Region} {s s' : State} (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (h : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Kept W s s' :=
  ⟨hrd, hwr, hsp, h, by rw [hm]; exact Frame.refl _ _⟩

/-! ## The scratch space and the pieces -/

/-- The scratch space at `sc`, and the 48 bytes below the stack pointer that the callees' frames
take. -/
structure KEnv (N : Nat) (sc : Addr) (t : State) : Prop where
  big : 840 ≤ N
  w : PPC64LE.Covers [⟨sc, N⟩] t.wr
  sp : 48 ≤ t.sp.toNat
  d : (below t.sp 48).Disjoint ⟨sc, N⟩

theorem KEnv.kept {N : Nat} {sc : Addr} {W : List Region} {t u : State} (h : KEnv N sc t) (hk : Kept W t u) :
    KEnv N sc u :=
  ⟨h.big, hk.wr ▸ h.w, hk.sp ▸ h.sp, hk.sp ▸ h.d⟩

/-- A length's value. -/
def _root_.VG.Impl.Sha3.PPC64LE.Pieces.Len.val (g : Reg → BitVec 64) : Len → Nat
  | .imm n => n
  | .reg r => (g r).toNat

/-- A length's register is callee-saved, or it fits `li`. -/
def _root_.VG.Impl.Sha3.PPC64LE.Pieces.Len.Ok : Len → Prop
  | .imm n => n < 2 ^ 15
  | .reg r => r ∈ preserved

/-- Where a piece is. -/
def _root_.VG.Impl.Sha3.PPC64LE.Pieces.Piece.addr (g : Reg → BitVec 64) (p : Piece) : Addr := g p.base + BitVec.ofNat 64 p.off

/-- A piece's region. -/
abbrev _root_.VG.Impl.Sha3.PPC64LE.Pieces.Piece.R (g : Reg → BitVec 64) (p : Piece) : Region := ⟨p.addr g, p.len.val g⟩

/-- A piece's bytes. -/
abbrev _root_.VG.Impl.Sha3.PPC64LE.Pieces.Piece.bytes (m : Mem) (g : Reg → BitVec 64) (p : Piece) : List Byte :=
  Spec.Sha3.bytesAt m (p.addr g) (p.len.val g)

/-- A piece that can be hashed from `s`, with the scratch space at `sc`. -/
structure PieceOk (N : Nat) (sc : Addr) (s : State) (p : Piece) : Prop where
  base : p.base ∈ preserved
  off : p.off < 2 ^ 15
  len : p.len.Ok
  cov : PPC64LE.Covers [p.R s.gpr] (s.rd ++ s.wr)
  dsc : Region.Disjoint (p.R s.gpr) ⟨sc, N⟩
  dsp : (below s.sp 48).Disjoint (p.R s.gpr)

theorem _root_.VG.Impl.Sha3.PPC64LE.Pieces.Len.val_eq {g g' : Reg → BitVec 64} {l : Len} (hl : l.Ok) (h : ∀ r ∈ preserved, g' r = g r) :
    l.val g' = l.val g := by
  cases l with
  | imm n => rfl
  | reg r => exact congrArg BitVec.toNat (h r hl)

theorem _root_.VG.Impl.Sha3.PPC64LE.Pieces.Piece.addr_eq {g g' : Reg → BitVec 64} {p : Piece} (hb : p.base ∈ preserved)
    (h : ∀ r ∈ preserved, g' r = g r) : p.addr g' = p.addr g := by
  unfold Piece.addr; rw [h _ hb]

theorem _root_.VG.Impl.Sha3.PPC64LE.Pieces.Len.val_lt (g : Reg → BitVec 64) {l : Len} (hl : l.Ok) : l.val g < 2 ^ 64 := by
  cases l with
  | imm n => show n < 2 ^ 64; exact Nat.lt_trans hl (by decide)
  | reg r => exact (g r).isLt

theorem _root_.VG.Impl.Sha3.PPC64LE.Pieces.Len.set_eq (g : Reg → BitVec 64) (l : Len) :
    BitVec.ofNat 64 (l.val g) = match l with | .imm n => BitVec.ofNat 64 n | .reg r => g r := by
  cases l with
  | imm n => rfl
  | reg r => show BitVec.ofNat 64 (g r).toNat = g r; simp

/-! ## The arguments -/

theorem pres_ne {r : Reg} (h : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 := by
  revert r; decide

/-- What an argument block keeps. -/
structure Only (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.kept {s s' : State} (h : Only s s') (W : List Region) : Kept W s s' :=
  Kept.of_regs h.mem h.rd h.wr h.sp h.cs

theorem absorbArgs_ok {s : State} {sc : Reg} (hsc : sc ∈ preserved) (first : Bool) {p : Piece}
    (hb : p.base ∈ preserved) (ho : p.off < 2 ^ 15) (hl : p.len.Ok) :
    WP isa (.block (absorbArgs sc first p)) s fun s' => Only s s' ∧
      s'.gpr .r3 = s.gpr sc ∧ s'.gpr .r4 = BitVec.ofNat 64 136 ∧
      s'.gpr .r5 = (if first then BitVec.ofNat 64 0 else s.gpr .r3) ∧
      s'.gpr .r6 = p.addr s.gpr ∧ s'.gpr .r7 = BitVec.ofNat 64 (p.len.val s.gpr) ∧
      s'.gpr .r8 = s.gpr sc + BitVec.ofNat 64 200 := by
  obtain ⟨n0, n3, n4, n5, n6, n7, n8⟩ := pres_ne hsc
  obtain ⟨b0, b3, b4, b5, b6, b7, b8⟩ := pres_ne hb
  obtain ⟨base, off, len⟩ := p
  cases len with
  | imm n =>
    have hn : n < 2 ^ 15 := hl
    cases first <;>
    · prun [absorbArgs, Len.set, Impl.Sha3.PPC64LE.Stream.mov, KW, hn, ho, n0, n3, n4, n5, n6, n7, n8, b0, b3,
        b4, b5, b6, b7, b8, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7, Ne.symm n8,
        Bool.false_eq_true, ite_true, ite_false, Len.val, Piece.addr, BitVec.add_zero]
      exact ⟨by pres_tac, rfl, rfl, rfl, rfl⟩
  | reg r =>
    have hr : r ∈ preserved := hl
    obtain ⟨r0, r3, r4, r5, r6, r7, r8⟩ := pres_ne hr
    cases first <;>
    · prun [absorbArgs, Len.set, Impl.Sha3.PPC64LE.Stream.mov, KW, ho, n0, n3, n4, n5, n6, n7, n8, b0, b3,
        b4, b5, b6, b7, b8, r0, r3, r4, r5, r6, r7, r8, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
        Ne.symm n7, Ne.symm n8, Bool.false_eq_true, ite_true, ite_false, Len.val, Piece.addr, BitVec.add_zero,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact ⟨by pres_tac, rfl, rfl, rfl, rfl⟩

theorem padArgs_ok {s : State} {sc : Reg} (hsc : sc ∈ preserved) :
    WP isa (.block (padArgs sc)) s fun s' => Only s s' ∧
      s'.gpr .r3 = s.gpr sc ∧ s'.gpr .r4 = BitVec.ofNat 64 136 ∧ s'.gpr .r5 = s.gpr .r3 ∧
      s'.gpr .r6 = BitVec.ofNat 64 0x1f ∧ s'.gpr .r7 = s.gpr sc + BitVec.ofNat 64 200 := by
  obtain ⟨n0, n3, n4, n5, n6, n7, n8⟩ := pres_ne hsc
  prun [padArgs, Impl.Sha3.PPC64LE.Stream.mov, KW, n0, n3, n4, n5, n6, n7, n8, Ne.symm n3, Ne.symm n4,
    Ne.symm n5, Ne.symm n6, Ne.symm n7, BitVec.add_zero]
  exact ⟨by pres_tac, rfl, rfl, rfl, rfl⟩

theorem squeezeArgs_ok {s : State} {sc f : Reg} (hsc : sc ∈ preserved) (hf : f ∈ preserved) {o n : Nat}
    (ho : o < 2 ^ 15) (hn : n < 2 ^ 15) :
    WP isa (.block (squeezeArgs sc f o n)) s fun s' => Only s s' ∧
      s'.gpr .r3 = s.gpr sc ∧ s'.gpr .r4 = BitVec.ofNat 64 136 ∧ s'.gpr .r5 = BitVec.ofNat 64 0 ∧
      s'.gpr .r6 = s.gpr f + BitVec.ofNat 64 o ∧ s'.gpr .r7 = BitVec.ofNat 64 n ∧
      s'.gpr .r8 = s.gpr sc + BitVec.ofNat 64 200 := by
  obtain ⟨n0, n3, n4, n5, n6, n7, n8⟩ := pres_ne hsc
  obtain ⟨f0, f3, f4, f5, f6, f7, f8⟩ := pres_ne hf
  prun [squeezeArgs, Impl.Sha3.PPC64LE.Stream.mov, KW, ho, hn, n0, n3, n4, n5, n6, n7, n8, f0, f3, f4, f5, f6, f7,
    f8, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7, Ne.symm n8, BitVec.add_zero]
  exact ⟨by pres_tac, rfl, rfl, rfl, rfl⟩

/-! ## Regions -/

/-- What a hash may write besides its output: the scratch space and the callees' frames. -/
abbrev kW (N : Nat) (sc sp : Addr) : List Region := [⟨sc, N⟩, below sp 48]

theorem st_sub {N : Nat} (sc : Addr) (hN : 840 ≤ N) : Region.Sub ⟨sc, 200⟩ ⟨sc, N⟩ := by
  simpa using Offset.sub_base sc (d := 0) (n := 200) (k := N) (by omega)

theorem kw_sub {N : Nat} (sc : Addr) (hN : 840 ≤ N) : Region.Sub ⟨sc + BitVec.ofNat 64 200, 640⟩ ⟨sc, N⟩ :=
  Offset.sub_base sc (by omega)

theorem st_kw (sc : Addr) : Region.Disjoint ⟨sc, 200⟩ ⟨sc + BitVec.ofNat 64 200, 640⟩ :=
  Offset.base_disjoint sc (by decide) (by decide)

theorem cov_st {N : Nat} {ws : List Region} {sc : Addr} (hN : 840 ≤ N) (hw : PPC64LE.Covers [⟨sc, N⟩] ws) :
    PPC64LE.Covers [⟨sc, 200⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩] ws := by
  refine fun a n h => hw a n (Covers.of_sub (fun r hr => ?_) a n h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by simp, by simp; omega⟩
  · exact ⟨_, List.mem_cons_self, 200, rfl, by simp; omega⟩

theorem cov_app {xs ys ws : List Region} (h₁ : PPC64LE.Covers xs ws) (h₂ : PPC64LE.Covers ys ws) :
    PPC64LE.Covers (xs ++ ys) ws := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ a n ⟨r, hr, hc⟩
  · exact h₂ a n ⟨r, hr, hc⟩

theorem cov_right {xs rd wr : List Region} (h : PPC64LE.Covers xs wr) : PPC64LE.Covers xs (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The sponge's regions, within `kW`. -/
theorem frame_kw {N : Nat} {sc sp : Addr} {m m' : Mem} (hN : 840 ≤ N)
    (h : Frame [⟨sc, 200⟩, ⟨sc + BitVec.ofNat 64 200, 640⟩, below sp 48] m m') : Frame (kW N sc sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, st_sub sc hN⟩
    · exact ⟨_, List.mem_cons_self, kw_sub sc hN⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- Bytes outside the regions a frame writes. -/
theorem bytes_keep {W : List Region} {m m' : Mem} (hf : Frame W m m') {p : Addr} {n : Nat}
    (hn : n < 2 ^ 64) (hd : ∀ r ∈ W, Region.Disjoint ⟨p, n⟩ r) :
    Spec.Sha3.bytesAt m' p n = Spec.Sha3.bytesAt m p n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr hc => ?_
  have hi' := List.mem_range.mp hi
  exact hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

/-- A piece's bytes while a hash runs. -/
theorem PieceOk.bytes {N : Nat} {sc : Addr} {s₀ s : State} {p : Piece} (hp : PieceOk N sc s₀ p)
    (hk : Kept (kW N sc s₀.sp) s₀ s) :
    Spec.Sha3.bytesAt s.mem (p.addr s.gpr) (p.len.val s.gpr) = p.bytes s₀.mem s₀.gpr := by
  rw [Piece.addr_eq hp.base hk.cs, Len.val_eq hp.len hk.cs]
  refine bytes_keep hk.frame (Len.val_lt _ hp.len) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.dsc
  · exact hp.dsp.symm

theorem rate136 : (136 : Nat) ∈ Spec.Sha3.rates := by decide

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## The absorbs -/

/-- The position before an absorption: 0 at the first. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r3).toNat

theorem absorbs_ok {N : Nat} {sc : Reg} {scA : Addr} (hsc : sc ∈ preserved) {s₀ : State} (hs : s₀.gpr sc = scA)
    (he : KEnv N scA s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk N scA s₀ p) → Kept (kW N scA s₀.sp) s₀ s → Repr s.mem scA 136 msg →
      Pos first s = msg.length % 136 →
      WP isa (absorbs sc first ps) s fun s' =>
        Kept (kW N scA s₀.sp) s₀ s' ∧
        Repr s'.mem scA 136 (msg ++ (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten).length % 136 := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p List.mem_cons_self
    refine WP.seq (WP.mono (absorbArgs_ok hsc first hp.base hp.off hp.len)
      fun s₁ ⟨o₁, g3, g4, g5, g6, g7, g8⟩ => ?_)
    have hks : ∀ r ∈ preserved, s₁.gpr r = s₀.gpr r := fun r hr => (o₁.cs r hr).trans (hk.cs r hr)
    have hk₁ : Kept (kW N scA s₀.sp) s₀ s₁ := hk.trans (o₁.kept _)
    have e₁ := he.kept hk₁
    have gsc : s.gpr sc = scA := by rw [hk.cs _ hsc, hs]
    rw [gsc] at g3 g8
    rw [Piece.addr_eq hp.base hk.cs] at g6
    rw [Len.val_eq hp.len hk.cs] at g7
    have hpl : Pos first s < 136 := by rw [hpos]; exact Nat.mod_lt _ (by decide)
    have g5' : s₁.gpr .r5 = BitVec.ofNat 64 (Pos first s) := by
      rw [g5]; cases first
      · show s.gpr .r3 = BitVec.ofNat 64 (s.gpr .r3).toNat; rw [ofNat_toNat]
      · rfl
    have hsp : s₁.sp = s₀.sp := hk₁.sp
    have dsp : (below s₁.sp 48).Disjoint (p.R s₀.gpr) := by rw [hsp]; exact hp.dsp
    have dK : (below s₁.sp 48).Disjoint ⟨scA, N⟩ := e₁.d
    have hA : AbsorbArgs s₁ scA (p.addr s₀.gpr) (scA + BitVec.ofNat 64 200) 136 (Pos first s)
        (p.len.val s₀.gpr) :=
      ⟨g3, g4, g5', g6, g7, g8, rate136, hpl, Len.val_lt _ hp.len, e₁.sp, st_kw scA,
        hp.dsc.sub_right (st_sub scA he.big), hp.dsc.sub_right (kw_sub scA he.big), dK.sub_right (st_sub scA he.big), dsp,
        dK.sub_right (kw_sub scA he.big)⟩
    have cw : PPC64LE.Covers [⟨scA, 200⟩, ⟨scA + BitVec.ofNat 64 200, 640⟩] s₁.wr := cov_st he.big e₁.w
    have cr : PPC64LE.Covers [p.R s₀.gpr] (s₁.rd ++ s₁.wr) := by rw [hk₁.rd, hk₁.wr]; exact hp.cov
    refine WP.seq (absorb_call hA (cov_app cr (cov_right cw)) cw fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ r₂ ret₂ => ?_)
    have hk₂ : Kept (kW N scA s₀.sp) s₀ s₂ := hk₁.trans ⟨rd₂, wr₂, sp₂, cs₂, by rw [← hsp]; exact frame_kw he.big f₂⟩
    have eb : Spec.Sha3.bytesAt s₁.mem (p.addr s₀.gpr) (p.len.val s₀.gpr) = p.bytes s₀.mem s₀.gpr := by
      have := hp.bytes hk₁
      rwa [Piece.addr_eq hp.base hks, Len.val_eq hp.len hks] at this
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ p.bytes s₀.mem s₀.gpr) (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      hk₂ rep ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r3).toNat = _
      rw [ret₂, hpos, List.length_append,
        show (p.bytes s₀.mem s₀.gpr).length = p.len.val s₀.gpr by simp [Spec.Sha3.bytesAt], Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The whole hash -/

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem zeroState_ok {N : Nat} {sc : Reg} {scA : Addr} (hsc : sc ∈ preserved) {s : State} (hs : s.gpr sc = scA)
    (he : KEnv N scA s) :
    WP isa (.block (Impl.MlKem.PPC64LE.zeroState sc)) s fun s' =>
      Kept (kW N scA s.sp) s s' ∧ stateAt s'.mem scA = Spec.Sha3.zero := by
  rw [Impl.MlKem.PPC64LE.zeroState, WP.block_append_iff]
  have hli : WP isa (.block [.li .r0 0]) s fun s₁ => s₁ = s.write .r0 (BitVec.ofNat 64 0) := by
    prun []
  refine WP.mono hli fun s₁ e₁ => ?_
  subst e₁
  have esc : (s.write .r0 (BitVec.ofNat 64 0)).gpr sc = scA := by
    rw [RegUpd.gpr_write_of_ne _ _ (pres_ne hsc).1, hs]
  refine WP.mono (Proof.MlKem.PPC64LE.Sample.zeroLanes_ok sc (pres_ne hsc).1
    (s₁ := s.write .r0 (BitVec.ofNat 64 0)) (by rw [RegUpd.gpr_write_self]; rfl) fun k hk => by
      rw [esc, RegUpd.wr_write]
      have := he.big
      exact he.w _ _ (in_base List.mem_cons_self (by omega) (by omega)))
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [esc] at hf hz
  refine ⟨⟨by rw [h₂.rd, RegUpd.rd_write], by rw [h₂.wr, RegUpd.wr_write], by rw [h₂.sp, RegUpd.sp_write],
    fun r hr => ?_, ?_⟩, Proof.MlKem.PPC64LE.Sample.stateAt_zero hz⟩
  · rw [h₂.gpr]
    exact RegUpd.gpr_write_of_ne _ _ fun e => (pres_ne hr).1 e
  · rw [RegUpd.mem_write] at hf
    exact hf.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self, st_sub scA he.big⟩

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze]

/-- `hash`: `SHAKE256` of the pieces `ps`, `n` bytes, into `o(f)`. -/
theorem hash_ok {N n : Nat} {sc f : Reg} {scA out : Addr} (hsc : sc ∈ preserved) (hf : f ∈ preserved) {o : Nat}
    (ho : o < 2 ^ 15) (hn : n < 2 ^ 15) {s₀ : State} (hs : s₀.gpr sc = scA) (hout : s₀.gpr f + BitVec.ofNat 64 o = out)
    (he : KEnv N scA s₀) {ps : List Piece} (hne : ps ≠ []) (hin : ∀ p ∈ ps, PieceOk N scA s₀ p)
    (hw : PPC64LE.Covers [⟨out, n⟩] s₀.wr) (dsc : Region.Disjoint ⟨out, n⟩ ⟨scA, N⟩)
    (dsp : (below s₀.sp 48).Disjoint ⟨out, n⟩) :
    WP isa (hash sc ps f o n) s₀ fun s' =>
      Kept ([⟨out, n⟩] ++ kW N scA s₀.sp) s₀ s' ∧
      Spec.Sha3.bytesAt s'.mem out n = Spec.Sha3.shake256 (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten n := by
  unfold Impl.Sha3.PPC64LE.Pieces.hash
  refine WP.seq (WP.mono (zeroState_ok hsc hs he) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hsc hs he ps true s₁ [] hin k₁ (repr_nil z₁) (by simp [Pos]))
    fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ps.isEmpty = false := by cases ps; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  refine WP.seq (WP.mono (padArgs_ok hsc) fun s₃ ⟨o₃, g3, g4, g5, g6, g7⟩ => ?_)
  have hk₃ : Kept (kW N scA s₀.sp) s₀ s₃ := k₂.trans (o₃.kept _)
  have e₃ := he.kept hk₃
  rw [k₂.cs _ hsc, hs] at g3 g7
  have hpl : (s₂.gpr .r3).toNat < 136 := by
    rw [show (s₂.gpr .r3).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ (by decide)
  have hP : PadArgs s₃ scA (scA + BitVec.ofNat 64 200) 136 (s₂.gpr .r3).toNat :=
    ⟨g3, g4, by rw [g5, ofNat_toNat], g7, rate136, hpl, e₃.sp, st_kw scA, e₃.d.sub_right (st_sub scA he.big),
      e₃.d.sub_right (kw_sub scA he.big)⟩
  have cw := cov_st he.big e₃.w
  refine WP.seq (pad_call hP (by simpa using cov_right cw) cw fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ st₄ => ?_)
  have hk₄ : Kept (kW N scA s₀.sp) s₀ s₄ := hk₃.trans ⟨rd₄, wr₄, sp₄, cs₄, by rw [← hk₃.sp]; exact frame_kw he.big f₄⟩
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [g6] at st
  -- The squeeze.
  refine WP.seq (WP.mono (squeezeArgs_ok hsc hf ho hn) fun s₅ ⟨o₅, h3, h4, h5, h6, h7, h8⟩ => ?_)
  have hk₅ : Kept (kW N scA s₀.sp) s₀ s₅ := hk₄.trans (o₅.kept _)
  have e₅ := he.kept hk₅
  rw [hk₄.cs _ hsc, hs] at h3 h8
  rw [hk₄.cs _ hf, hout] at h6
  have dsp₅ : (below s₅.sp 48).Disjoint ⟨out, n⟩ := by rw [hk₅.sp]; exact dsp
  have hS : SqueezeArgs s₅ scA out (scA + BitVec.ofNat 64 200) 136 0 n :=
    ⟨h3, h4, h5, h6, h7, h8, rate136, by decide, by omega, e₅.sp, dsc.symm.sub_left (st_sub scA he.big),
      st_kw scA, dsc.sub_right (kw_sub scA he.big), e₅.d.sub_right (st_sub scA he.big), dsp₅, e₅.d.sub_right (kw_sub scA he.big)⟩
  have cw₅ : PPC64LE.Covers [⟨scA, 200⟩, ⟨out, n⟩, ⟨scA + BitVec.ofNat 64 200, 640⟩] s₅.wr := by
    rw [hk₅.wr]
    intro a m ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_st he.big he.w a m ⟨_, List.mem_cons_self, hc⟩
    · exact hw a m ⟨_, List.mem_cons_self, hc⟩
    · exact cov_st he.big he.w a m ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
  refine squeeze_call hS (by simpa using cov_right cw₅) cw₅ fun s₆ rd₆ wr₆ sp₆ cs₆ f₆ b₆ _ _ => ?_
  refine ⟨(hk₅.mono fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩).trans
    ⟨rd₆, wr₆, sp₆, cs₆, ?_⟩, ?_⟩
  · rw [← hk₅.sp]
    exact f₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, st_sub scA he.big⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, kw_sub scA he.big⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [b₆, o₅.mem, st, squeezeFrom_zero]
    rfl

end VG.Proof.Sha3.PPC64LE.Pieces
