module

public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Zero
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448's whole functions on RISC-V: `SHAKE256` of pieces

As on PPC64LE (`Proof/Ed448/PPC64LE/Whole/Hash.lean`): `hash sc ps f o`
(`Impl/Ed448/RISCV64/Whole.lean`) leaves `SHAKE256` of the concatenation of
the pieces `ps`, 114 bytes, at `o(f)` (`hash_ok`): from the zeroed state,
each `absorb` continues the message from the position the previous one
returned, then the padding and the `squeeze`, through the sponge functions'
calls (`Proof/Sha3/RISCV64/Stream/Calls.lean`). The pieces' pointers and
lengths are in callee-saved registers, which the calls keep. A hash changes
only `scratch`, the output, the 1168 bytes below the stack pointer and
registers other than the callee-saved ones (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)
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

/-- The scratch space at `sc`, a multiple of 8, and the 1168 bytes below the stack pointer, 16-byte
aligned, that the callees' frames take. -/
structure KEnv (sc : Addr) (t : State) : Prop where
  w : (⟨sc, 8192⟩ : Region) ∈ t.wr
  al : sc.toNat % 8 = 0
  spal : t.sp.toNat % 16 = 0
  sp : 1168 ≤ t.sp.toNat
  d : (below t.sp 1168).Disjoint ⟨sc, 8192⟩

theorem KEnv.kept {sc : Addr} {W : List Region} {t u : State} (h : KEnv sc t) (hk : Kept W t u) : KEnv sc u :=
  ⟨hk.wr ▸ h.w, h.al, hk.sp ▸ h.spal, hk.sp ▸ h.sp, hk.sp ▸ h.d⟩

/-- A length's value. -/
def _root_.VG.Impl.Ed448.RISCV64.Whole.Len.val (g : Reg → BitVec 64) : Len → Nat
  | .imm n => n
  | .reg r => (g r).toNat

/-- A length's register is callee-saved, or it fits `li`. -/
def _root_.VG.Impl.Ed448.RISCV64.Whole.Len.Ok : Len → Prop
  | .imm n => n < 2048
  | .reg r => r ∈ preserved

/-- Where a piece is. -/
def _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.addr (g : Reg → BitVec 64) (p : Piece) : Addr :=
  g p.base + BitVec.ofNat 64 p.off

/-- A piece's region. -/
abbrev _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.R (g : Reg → BitVec 64) (p : Piece) : Region :=
  ⟨p.addr g, p.len.val g⟩

/-- A piece's bytes. -/
abbrev _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.bytes (m : Mem) (g : Reg → BitVec 64) (p : Piece) : List Byte :=
  Spec.Sha3.bytesAt m (p.addr g) (p.len.val g)

/-- A piece that can be hashed from `s`, with the scratch space at `sc`. -/
structure PieceOk (sc : Addr) (s : State) (p : Piece) : Prop where
  base : p.base ∈ preserved
  off : p.off < 2048
  len : p.len.Ok
  cov : Covers [p.R s.gpr] (s.rd ++ s.wr)
  dsc : Region.Disjoint (p.R s.gpr) ⟨sc, 8192⟩
  dsp : (below s.sp 1168).Disjoint (p.R s.gpr)

theorem _root_.VG.Impl.Ed448.RISCV64.Whole.Len.val_eq {g g' : Reg → BitVec 64} {l : Len} (hl : l.Ok)
    (h : ∀ r ∈ preserved, g' r = g r) : l.val g' = l.val g := by
  cases l with
  | imm n => rfl
  | reg r => exact congrArg BitVec.toNat (h r hl)

theorem _root_.VG.Impl.Ed448.RISCV64.Whole.Piece.addr_eq {g g' : Reg → BitVec 64} {p : Piece}
    (hb : p.base ∈ preserved) (h : ∀ r ∈ preserved, g' r = g r) : p.addr g' = p.addr g := by
  unfold Piece.addr; rw [h _ hb]

theorem _root_.VG.Impl.Ed448.RISCV64.Whole.Len.val_lt (g : Reg → BitVec 64) {l : Len} (hl : l.Ok) :
    l.val g < 2 ^ 64 := by
  cases l with
  | imm n => show n < 2 ^ 64; exact Nat.lt_trans hl (by decide)
  | reg r => exact (g r).isLt

/-! ## The arguments -/

theorem pres_ne {r : Reg} (h : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 := by
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

/-- An `Upd` of a register other than the callee-saved ones keeps them. -/
theorem updOnly {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) (hd : d ∉ preserved) : Only s s' :=
  ⟨fun r hr => h.other r fun e => hd (e ▸ hr), h.mem, h.rd, h.wr, h.sp⟩

theorem Only.trans {s₁ s₂ s₃ : State} (h₁ : Only s₁ s₂) (h₂ : Only s₂ s₃) : Only s₁ s₃ :=
  ⟨fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem absorbArgs_ok {s : State} {sc : Reg} (hsc : sc ∈ preserved) (first : Bool) {p : Piece}
    (hb : p.base ∈ preserved) (ho : p.off < 2048) (hl : p.len.Ok) :
    WP isa (.block (absorbArgs sc first p)) s fun s' => Only s s' ∧
      s'.gpr .a0 = s.gpr sc ∧ s'.gpr .a1 = BitVec.ofNat 64 136 ∧
      s'.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) ∧
      s'.gpr .a3 = p.addr s.gpr ∧ s'.gpr .a4 = BitVec.ofNat 64 (p.len.val s.gpr) := by
  obtain ⟨n0, n3, n4, n5, n6, n7⟩ := pres_ne hsc
  obtain ⟨b0, b3, b4, b5, b6, b7⟩ := pres_ne hb
  obtain ⟨base, off, len⟩ := p
  unfold absorbArgs
  refine wp_addi ho fun u₁ h₁ => ?_
  have k₂ : ∀ u₂ : State, Only u₁ u₂ → u₂.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) →
      u₂.gpr .a3 = u₁.gpr .a3 → u₂.gpr sc = s.gpr sc → (∀ r ∈ preserved, u₂.gpr r = s.gpr r) →
      WP isa (.block [Impl.Ed25519.RISCV64.Whole.mov .a0 sc, .li .a1 136, Len.set len]) u₂ fun s' => Only s s' ∧
        s'.gpr .a0 = s.gpr sc ∧ s'.gpr .a1 = BitVec.ofNat 64 136 ∧
        s'.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) ∧
        s'.gpr .a3 = Piece.addr s.gpr ⟨base, off, len⟩ ∧
        s'.gpr .a4 = BitVec.ofNat 64 (Len.val s.gpr len) := by
    intro u₂ o₂ g2 g3 gsc gcs
    have o₁ := updOnly h₁ (by decide)
    refine wp_mv fun u₃ h₃ => wp_li (by decide) fun u₄ h₄ => ?_
    have o₃ := updOnly h₃ (by decide)
    have o₄ := updOnly h₄ (by decide)
    have ga3 : u₁.gpr .a3 = Piece.addr s.gpr ⟨base, off, len⟩ := h₁.gpr
    cases len with
    | imm n =>
      have hn : n < 2048 := hl
      refine wp_li hn fun u₅ h₅ => WP.block_nil ⟨o₁.trans (o₂.trans (o₃.trans (o₄.trans (updOnly h₅ (by decide))))),
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, gsc]
      · rw [h₅.other _ (by decide), h₄.gpr]
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), g2]
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), g3, ga3]
      · rw [h₅.gpr]; rfl
    | reg r =>
      have hr : r ∈ preserved := hl
      obtain ⟨r0, r3, r4, r5, r6, r7⟩ := pres_ne hr
      refine wp_mv fun u₅ h₅ => WP.block_nil ⟨o₁.trans (o₂.trans (o₃.trans (o₄.trans (updOnly h₅ (by decide))))),
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, gsc]
      · rw [h₅.other _ (by decide), h₄.gpr]
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), g2]
      · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), g3, ga3]
      · rw [h₅.gpr, h₄.other _ r4, h₃.other _ r3, gcs r hr]
        show s.gpr r = BitVec.ofNat 64 (s.gpr r).toNat
        simp
  have o₁ := updOnly h₁ (by decide)
  cases first with
  | true =>
    refine wp_li (by decide) fun u₂ h₂ => k₂ u₂ (updOnly h₂ (by decide)) h₂.gpr (h₂.other _ (by decide))
      (by rw [h₂.other _ n5, h₁.other _ n6]) fun r hr => by rw [(updOnly h₂ (by decide)).cs r hr, o₁.cs r hr]
  | false =>
    refine wp_mv fun u₂ h₂ => k₂ u₂ (updOnly h₂ (by decide)) (by rw [h₂.gpr, h₁.other _ (by decide)]; rfl)
      (h₂.other _ (by decide)) (by rw [h₂.other _ n5, h₁.other _ n6]) fun r hr => by
        rw [(updOnly h₂ (by decide)).cs r hr, o₁.cs r hr]

theorem padArgs_ok {s : State} {sc : Reg} (hsc : sc ∈ preserved) :
    WP isa (.block (padArgs sc)) s fun s' => Only s s' ∧
      s'.gpr .a0 = s.gpr sc ∧ s'.gpr .a1 = BitVec.ofNat 64 136 ∧ s'.gpr .a2 = s.gpr .a0 ∧
      s'.gpr .a3 = BitVec.ofNat 64 0x1f := by
  obtain ⟨n0, n3, n4, n5, n6, n7⟩ := pres_ne hsc
  unfold padArgs
  refine wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ => wp_li (by decide) fun u₄ h₄ =>
    WP.block_nil ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
      (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ n5]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₄.gpr]

theorem squeezeArgs_ok {s : State} {sc f : Reg} (_hsc : sc ∈ preserved) (hf : f ∈ preserved) {o : Nat}
    (ho : o < 2048) :
    WP isa (.block (squeezeArgs sc f o)) s fun s' => Only s s' ∧
      s'.gpr .a0 = s.gpr sc ∧ s'.gpr .a1 = BitVec.ofNat 64 136 ∧ s'.gpr .a2 = BitVec.ofNat 64 0 ∧
      s'.gpr .a3 = s.gpr f + BitVec.ofNat 64 o ∧ s'.gpr .a4 = BitVec.ofNat 64 114 := by
  obtain ⟨f0, f3, f4, f5, f6, f7⟩ := pres_ne hf
  unfold squeezeArgs
  refine wp_mv fun u₁ h₁ => wp_li (by decide) fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ =>
    wp_addi ho fun u₄ h₄ => wp_li (by decide) fun u₅ h₅ =>
    WP.block_nil ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
      ((updOnly h₄ (by decide)).trans (updOnly h₅ (by decide))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr]
  · rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ f5, h₂.other _ f4, h₁.other _ f3]
  · rw [h₅.gpr]

/-! ## Regions -/

/-- What a hash may write besides its output: the scratch space and the callees' frames. -/
abbrev kW (sc sp : Addr) : List Region := [⟨sc, 8192⟩, below sp 1168]

theorem st_sub (sc : Addr) : Region.Sub ⟨sc, 200⟩ ⟨sc, 8192⟩ := Region.sub_prefix (by decide)

theorem cov_st {ws : List Region} {sc : Addr} (hw : (⟨sc, 8192⟩ : Region) ∈ ws) :
    Covers [⟨sc, 200⟩] ws :=
  Covers.one ⟨_, hw, Offset.contains_base sc (d := 0) (n := 200) (k := 8192) (by decide) (by decide) |>
    fun h => by simpa using h⟩

theorem cov_app {xs ys ws : List Region} (h₁ : Covers xs ws) (h₂ : Covers ys ws) :
    Covers (xs ++ ys) ws := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ a n ⟨r, hr, hc⟩
  · exact h₂ a n ⟨r, hr, hc⟩

theorem cov_right {xs rd wr : List Region} (h : Covers xs wr) : Covers xs (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The sponge's regions, within `kW`. -/
theorem frame_kw {sc sp : Addr} {m m' : Mem}
    (h : Frame [⟨sc, 200⟩, below sp 1168] m m') : Frame (kW sc sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, st_sub sc⟩
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
theorem PieceOk.bytes {sc : Addr} {s₀ s : State} {p : Piece} (hp : PieceOk sc s₀ p)
    (hk : Kept (kW sc s₀.sp) s₀ s) :
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
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .a0).toNat

theorem absorbs_ok {sc : Reg} {scA : Addr} (hsc : sc ∈ preserved) {s₀ : State} (hs : s₀.gpr sc = scA)
    (he : KEnv scA s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk scA s₀ p) → Kept (kW scA s₀.sp) s₀ s → Repr s.mem scA 136 msg →
      Pos first s = msg.length % 136 →
      WP isa (absorbs sc first ps) s fun s' =>
        Kept (kW scA s₀.sp) s₀ s' ∧
        Repr s'.mem scA 136 (msg ++ (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten).length % 136 := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p List.mem_cons_self
    refine WP.seq (WP.mono (absorbArgs_ok hsc first hp.base hp.off hp.len)
      fun s₁ ⟨o₁, g0, g1, g2, g3, g4⟩ => ?_)
    have hks : ∀ r ∈ preserved, s₁.gpr r = s₀.gpr r := fun r hr => (o₁.cs r hr).trans (hk.cs r hr)
    have hk₁ : Kept (kW scA s₀.sp) s₀ s₁ := hk.trans (o₁.kept _)
    have e₁ := he.kept hk₁
    have gsc : s.gpr sc = scA := by rw [hk.cs _ hsc, hs]
    rw [gsc] at g0
    rw [Piece.addr_eq hp.base hk.cs] at g3
    rw [Len.val_eq hp.len hk.cs] at g4
    have hpl : Pos first s < 136 := by rw [hpos]; exact Nat.mod_lt _ (by decide)
    have g2' : s₁.gpr .a2 = BitVec.ofNat 64 (Pos first s) := by
      rw [g2]; cases first
      · show s.gpr .a0 = BitVec.ofNat 64 (s.gpr .a0).toNat; rw [ofNat_toNat]
      · rfl
    have hsp : s₁.sp = s₀.sp := hk₁.sp
    have dsp : (below s₁.sp 1168).Disjoint (p.R s₀.gpr) := by rw [hsp]; exact hp.dsp
    have dK : (below s₁.sp 1168).Disjoint ⟨scA, 8192⟩ := e₁.d
    have hA : AbsorbArgs s₁ scA (p.addr s₀.gpr) 136 (Pos first s) (p.len.val s₀.gpr) :=
      ⟨g0, g1, g2', g3, g4, rate136, hpl, Len.val_lt _ hp.len, e₁.spal, e₁.sp,
        hp.dsc.sub_right (st_sub scA), dK.sub_right (st_sub scA), dsp⟩
    have cw : Covers [⟨scA, 200⟩] s₁.wr := cov_st e₁.w
    have cr : Covers [p.R s₀.gpr] (s₁.rd ++ s₁.wr) := by rw [hk₁.rd, hk₁.wr]; exact hp.cov
    refine WP.seq (absorb_call hA (cov_app cr (cov_right cw)) cw fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ r₂ ret₂ => ?_)
    have hk₂ : Kept (kW scA s₀.sp) s₀ s₂ := hk₁.trans ⟨rd₂, wr₂, sp₂, cs₂, by rw [← hsp]; exact frame_kw f₂⟩
    have eb : Spec.Sha3.bytesAt s₁.mem (p.addr s₀.gpr) (p.len.val s₀.gpr) = p.bytes s₀.mem s₀.gpr := by
      have := hp.bytes hk₁
      rwa [Piece.addr_eq hp.base hks, Len.val_eq hp.len hks] at this
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ p.bytes s₀.mem s₀.gpr) (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      hk₂ rep ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .a0).toNat = _
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

theorem zeroState_ok {sc : Reg} {scA : Addr} (hsc : sc ∈ preserved) {s : State} (hs : s.gpr sc = scA)
    (he : KEnv scA s) :
    WP isa (.block (Impl.Sha3.RISCV64.zeroState sc)) s fun s' =>
      Kept (kW scA s.sp) s s' ∧ stateAt s'.mem scA = Spec.Sha3.zero := by
  refine WP.mono (Proof.Sha3.RISCV64.Stream.zeroState_ok (pres_ne hsc).1 (by rw [hs]; exact he.al)
    fun k hk => by rw [hs]; exact Proof.X25519.RISCV64.in_base he.w (by omega) (by omega)) fun s' ⟨hg, hrd, hwr, hsp, hf, hz⟩ => ?_
  rw [hs] at hf hz
  refine ⟨⟨hrd, hwr, hsp, fun r hr => hg r (pres_ne hr).1, ?_⟩, hz⟩
  exact hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self, st_sub scA⟩

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze]

/-- `hash`: `SHAKE256` of the pieces `ps`, 114 bytes, into `o(f)`. -/
theorem hash_ok {sc f : Reg} {scA out : Addr} (hsc : sc ∈ preserved) (hf : f ∈ preserved) {o : Nat}
    (ho : o < 2048) {s₀ : State} (hs : s₀.gpr sc = scA) (hout : s₀.gpr f + BitVec.ofNat 64 o = out)
    (he : KEnv scA s₀) {ps : List Piece} (hne : ps ≠ []) (hin : ∀ p ∈ ps, PieceOk scA s₀ p)
    (hw : Covers [⟨out, 114⟩] s₀.wr) (dsc : Region.Disjoint ⟨out, 114⟩ ⟨scA, 8192⟩)
    (dsp : (below s₀.sp 1168).Disjoint ⟨out, 114⟩) :
    WP isa (hash sc ps f o) s₀ fun s' =>
      Kept ([⟨out, 114⟩] ++ kW scA s₀.sp) s₀ s' ∧
      Spec.Sha3.bytesAt s'.mem out 114 = Spec.Sha3.shake256 (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten 114 := by
  unfold Impl.Ed448.RISCV64.Whole.hash
  refine WP.seq (WP.mono (zeroState_ok hsc hs he) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hsc hs he ps true s₁ [] hin k₁ (repr_nil z₁) (by simp [Pos]))
    fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ps.isEmpty = false := by cases ps; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  refine WP.seq (WP.mono (padArgs_ok hsc) fun s₃ ⟨o₃, g0, g1, g2, g3⟩ => ?_)
  have hk₃ : Kept (kW scA s₀.sp) s₀ s₃ := k₂.trans (o₃.kept _)
  have e₃ := he.kept hk₃
  rw [k₂.cs _ hsc, hs] at g0
  have hpl : (s₂.gpr .a0).toNat < 136 := by
    rw [show (s₂.gpr .a0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ (by decide)
  have hP : PadArgs s₃ scA 136 (s₂.gpr .a0).toNat :=
    ⟨g0, g1, by rw [g2, ofNat_toNat], rate136, hpl, e₃.spal, e₃.sp, e₃.d.sub_right (st_sub scA)⟩
  have cw := cov_st e₃.w
  refine WP.seq (pad_call hP (by simpa using cov_right cw) cw fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ st₄ => ?_)
  have hk₄ : Kept (kW scA s₀.sp) s₀ s₄ := hk₃.trans ⟨rd₄, wr₄, sp₄, cs₄, by rw [← hk₃.sp]; exact frame_kw f₄⟩
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [g3] at st
  -- The squeeze.
  refine WP.seq (WP.mono (squeezeArgs_ok hsc hf ho) fun s₅ ⟨o₅, h0, h1, h2, h3, h4⟩ => ?_)
  have hk₅ : Kept (kW scA s₀.sp) s₀ s₅ := hk₄.trans (o₅.kept _)
  have e₅ := he.kept hk₅
  rw [hk₄.cs _ hsc, hs] at h0
  rw [hk₄.cs _ hf, hout] at h3
  have dsp₅ : (below s₅.sp 1168).Disjoint ⟨out, 114⟩ := by rw [hk₅.sp]; exact dsp
  have hS : SqueezeArgs s₅ scA out 136 0 114 :=
    ⟨h0, h1, h2, h3, h4, rate136, by decide, by decide, e₅.spal, e₅.sp, dsc.symm.sub_left (st_sub scA),
      e₅.d.sub_right (st_sub scA), dsp₅⟩
  have cw₅ : Covers [⟨scA, 200⟩, ⟨out, 114⟩] s₅.wr := by
    rw [hk₅.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_st he.w a n ⟨_, List.mem_cons_self, hc⟩
    · exact hw a n ⟨_, List.mem_cons_self, hc⟩
  refine squeeze_call hS (by simpa using cov_right cw₅) cw₅ fun s₆ rd₆ wr₆ sp₆ cs₆ f₆ b₆ _ _ => ?_
  refine ⟨(hk₅.mono fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩).trans
    ⟨rd₆, wr₆, sp₆, cs₆, ?_⟩, ?_⟩
  · rw [← hk₅.sp]
    exact f₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, st_sub scA⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [b₆, o₅.mem, st, squeezeFrom_zero]
    rfl

end VG.Proof.Ed448.RISCV64.Whole
