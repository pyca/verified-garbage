module

-- separate module: the setup and the steps, built in parallel with `Contracts`, which `Sign` also imports
import VerifiedGarbage.Impl.MlDsa.RISCV64.Message
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Frame
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Impl.Sha3.RISCV64.Pieces
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Zero
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Sha3.RISCV64.Pieces`, which this module and modules that import it used -/

section

/-!
# SHAKE256 of pieces on RISC-V

As on PPC64LE (`Proof/Sha3/PPC64LE/Pieces.lean`), and as Ed448's whole
functions' hash was proven (`Proof/Ed448/RISCV64/Whole/Hash.lean`), for any
output length: `hash sc ps f o n` (`Impl/Sha3/RISCV64/Pieces.lean`) leaves
`SHAKE256` of the concatenation of the pieces `ps`, `n` bytes, at `o(f)`
(`hash_ok`): from the zeroed state, each `absorb` continues the message from
the position the previous one returned, then the padding and the `squeeze`,
through the sponge functions' calls (`Proof/Sha3/RISCV64/Stream/Calls.lean`).
The pieces' pointers and lengths are in callee-saved registers, which the
calls keep. A hash changes only its scratch space (`N` bytes at `sc`, at least
the 200 of the Keccak state), the output, the 1168 bytes below the stack
pointer and registers other than the callee-saved ones (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Pieces

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Sha3.RISCV64.Pieces
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
structure KEnv (N : Nat) (sc : Addr) (t : State) : Prop where
  big : 200 ≤ N
  w : Covers [⟨sc, N⟩] t.wr
  al : sc.toNat % 8 = 0
  spal : t.sp.toNat % 16 = 0
  sp : 1168 ≤ t.sp.toNat
  d : (below t.sp 1168).Disjoint ⟨sc, N⟩

theorem KEnv.kept {N : Nat} {sc : Addr} {W : List Region} {t u : State} (h : KEnv N sc t) (hk : Kept W t u) :
    KEnv N sc u :=
  ⟨h.big, hk.wr ▸ h.w, h.al, hk.sp ▸ h.spal, hk.sp ▸ h.sp, hk.sp ▸ h.d⟩

/-- A length's value. -/
def _root_.VG.Impl.Sha3.RISCV64.Pieces.Len.val (g : Reg → BitVec 64) : Len → Nat
  | .imm n => n
  | .reg r => (g r).toNat

/-- A length's register is callee-saved, or it fits `li`. -/
def _root_.VG.Impl.Sha3.RISCV64.Pieces.Len.Ok : Len → Prop
  | .imm n => n < 2048
  | .reg r => r ∈ preserved

/-- Where a piece is. -/
def _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.addr (g : Reg → BitVec 64) (p : Piece) : Addr :=
  g p.base + BitVec.ofNat 64 p.off

/-- A piece's region. -/
abbrev _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.R (g : Reg → BitVec 64) (p : Piece) : Region :=
  ⟨p.addr g, p.len.val g⟩

/-- A piece's bytes. -/
abbrev _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.bytes (m : Mem) (g : Reg → BitVec 64) (p : Piece) : List Byte :=
  Spec.Sha3.bytesAt m (p.addr g) (p.len.val g)

/-- A piece that can be hashed from `s`, with the scratch space at `sc`. -/
structure PieceOk (N : Nat) (sc : Addr) (s : State) (p : Piece) : Prop where
  base : p.base ∈ preserved
  off : p.off < 2048
  len : p.len.Ok
  cov : Covers [p.R s.gpr] (s.rd ++ s.wr)
  dsc : Region.Disjoint (p.R s.gpr) ⟨sc, N⟩
  dsp : (below s.sp 1168).Disjoint (p.R s.gpr)

theorem _root_.VG.Impl.Sha3.RISCV64.Pieces.Len.val_eq {g g' : Reg → BitVec 64} {l : Len} (hl : l.Ok)
    (h : ∀ r ∈ preserved, g' r = g r) : l.val g' = l.val g := by
  cases l with
  | imm n => rfl
  | reg r => exact congrArg BitVec.toNat (h r hl)

theorem _root_.VG.Impl.Sha3.RISCV64.Pieces.Piece.addr_eq {g g' : Reg → BitVec 64} {p : Piece}
    (hb : p.base ∈ preserved) (h : ∀ r ∈ preserved, g' r = g r) : p.addr g' = p.addr g := by
  unfold Piece.addr; rw [h _ hb]

theorem _root_.VG.Impl.Sha3.RISCV64.Pieces.Len.val_lt (g : Reg → BitVec 64) {l : Len} (hl : l.Ok) :
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
      WP isa (.block [Impl.Sha3.RISCV64.Stream.mov .a0 sc, .li .a1 136, Len.set len]) u₂ fun s' => Only s s' ∧
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

theorem squeezeArgs_ok {s : State} {sc f : Reg} (_hsc : sc ∈ preserved) (hf : f ∈ preserved) {o n : Nat}
    (ho : o < 2048) (hn : n < 2048) :
    WP isa (.block (squeezeArgs sc f o n)) s fun s' => Only s s' ∧
      s'.gpr .a0 = s.gpr sc ∧ s'.gpr .a1 = BitVec.ofNat 64 136 ∧ s'.gpr .a2 = BitVec.ofNat 64 0 ∧
      s'.gpr .a3 = s.gpr f + BitVec.ofNat 64 o ∧ s'.gpr .a4 = BitVec.ofNat 64 n := by
  obtain ⟨f0, f3, f4, f5, f6, f7⟩ := pres_ne hf
  unfold squeezeArgs
  refine wp_mv fun u₁ h₁ => wp_li (by decide) fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ =>
    wp_addi ho fun u₄ h₄ => wp_li hn fun u₅ h₅ =>
    WP.block_nil ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
      ((updOnly h₄ (by decide)).trans (updOnly h₅ (by decide))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr]
  · rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ f5, h₂.other _ f4, h₁.other _ f3]
  · rw [h₅.gpr]

/-! ## Regions -/

/-- What a hash may write besides its output: the scratch space and the callees' frames. -/
abbrev kW (N : Nat) (sc sp : Addr) : List Region := [⟨sc, N⟩, below sp 1168]

theorem st_sub {N : Nat} (sc : Addr) (hN : 200 ≤ N) : Region.Sub ⟨sc, 200⟩ ⟨sc, N⟩ := Region.sub_prefix hN

theorem cov_st {N : Nat} {ws : List Region} {sc : Addr} (hN : 200 ≤ N) (hw : Covers [⟨sc, N⟩] ws) :
    Covers [⟨sc, 200⟩] ws :=
  fun a n h => hw a n (Covers.of_sub (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, 0, by simp, by simp; omega_using [hN]⟩) a n h)

theorem cov_app {xs ys ws : List Region} (h₁ : Covers xs ws) (h₂ : Covers ys ws) :
    Covers (xs ++ ys) ws := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁ a n ⟨r, hr, hc⟩
  · exact h₂ a n ⟨r, hr, hc⟩

theorem cov_right {xs rd wr : List Region} (h : Covers xs wr) : Covers xs (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The sponge's regions, within `kW`. -/
theorem frame_kw {N : Nat} {sc sp : Addr} {m m' : Mem} (hN : 200 ≤ N)
    (h : Frame [⟨sc, 200⟩, below sp 1168] m m') : Frame (kW N sc sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, st_sub sc hN⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- Bytes outside the regions a frame writes. -/
theorem bytes_keep {W : List Region} {m m' : Mem} (hf : Frame W m m') {p : Addr} {n : Nat}
    (hn : n < 2 ^ 64) (hd : ∀ r ∈ W, Region.Disjoint ⟨p, n⟩ r) :
    Spec.Sha3.bytesAt m' p n = Spec.Sha3.bytesAt m p n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr hc => ?_
  have hi' := List.mem_range.mp hi
  exact hd r hr _ (Offset.contains_base p (by omega_using [hi']) (by omega_using [hn, hi'])) hc

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
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .a0).toNat

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
      fun s₁ ⟨o₁, g0, g1, g2, g3, g4⟩ => ?_)
    have hks : ∀ r ∈ preserved, s₁.gpr r = s₀.gpr r := fun r hr => (o₁.cs r hr).trans (hk.cs r hr)
    have hk₁ : Kept (kW N scA s₀.sp) s₀ s₁ := hk.trans (o₁.kept _)
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
    have dK : (below s₁.sp 1168).Disjoint ⟨scA, N⟩ := e₁.d
    have hA : AbsorbArgs s₁ scA (p.addr s₀.gpr) 136 (Pos first s) (p.len.val s₀.gpr) :=
      ⟨g0, g1, g2', g3, g4, rate136, hpl, Len.val_lt _ hp.len, e₁.spal, e₁.sp,
        hp.dsc.sub_right (st_sub scA he.big), dK.sub_right (st_sub scA he.big), dsp⟩
    have cw : Covers [⟨scA, 200⟩] s₁.wr := cov_st he.big e₁.w
    have cr : Covers [p.R s₀.gpr] (s₁.rd ++ s₁.wr) := by rw [hk₁.rd, hk₁.wr]; exact hp.cov
    refine WP.seq (absorb_call hA (cov_app cr (cov_right cw)) cw fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ r₂ ret₂ => ?_)
    have hk₂ : Kept (kW N scA s₀.sp) s₀ s₂ := hk₁.trans ⟨rd₂, wr₂, sp₂, cs₂, by rw [← hsp]; exact frame_kw he.big f₂⟩
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

theorem zeroState_ok {N : Nat} {sc : Reg} {scA : Addr} (hsc : sc ∈ preserved) {s : State} (hs : s.gpr sc = scA)
    (he : KEnv N scA s) :
    WP isa (.block (Impl.Sha3.RISCV64.zeroState sc)) s fun s' =>
      Kept (kW N scA s.sp) s s' ∧ stateAt s'.mem scA = Spec.Sha3.zero := by
  refine WP.mono (Proof.Sha3.RISCV64.Stream.zeroState_ok (pres_ne hsc).1 (by rw [hs]; exact he.al)
    fun k hk => by rw [hs]; exact cov_st he.big he.w _ _ ⟨_, List.mem_cons_self, Offset.contains_base scA (by omega_using [hk]) (by omega_using [hk])⟩) fun s' ⟨hg, hrd, hwr, hsp, hf, hz⟩ => ?_
  rw [hs] at hf hz
  refine ⟨⟨hrd, hwr, hsp, fun r hr => hg r (pres_ne hr).1, ?_⟩, hz⟩
  exact hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self, st_sub scA he.big⟩

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze]

/-- `hash`: `SHAKE256` of the pieces `ps`, `n` bytes, into `o(f)`. -/
theorem hash_ok {N n : Nat} {sc f : Reg} {scA out : Addr} (hsc : sc ∈ preserved) (hf : f ∈ preserved) {o : Nat}
    (ho : o < 2048) (hn : n < 2048) {s₀ : State} (hs : s₀.gpr sc = scA) (hout : s₀.gpr f + BitVec.ofNat 64 o = out)
    (he : KEnv N scA s₀) {ps : List Piece} (hne : ps ≠ []) (hin : ∀ p ∈ ps, PieceOk N scA s₀ p)
    (hw : Covers [⟨out, n⟩] s₀.wr) (dsc : Region.Disjoint ⟨out, n⟩ ⟨scA, N⟩)
    (dsp : (below s₀.sp 1168).Disjoint ⟨out, n⟩) :
    WP isa (hash sc ps f o n) s₀ fun s' =>
      Kept ([⟨out, n⟩] ++ kW N scA s₀.sp) s₀ s' ∧
      Spec.Sha3.bytesAt s'.mem out n = Spec.Sha3.shake256 (ps.map (Piece.bytes s₀.mem s₀.gpr)).flatten n := by
  unfold Impl.Sha3.RISCV64.Pieces.hash
  refine WP.seq (WP.mono (zeroState_ok hsc hs he) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hsc hs he ps true s₁ [] hin k₁ (repr_nil z₁) (by simp [Pos]))
    fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ps.isEmpty = false := by cases ps; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  refine WP.seq (WP.mono (padArgs_ok hsc) fun s₃ ⟨o₃, g0, g1, g2, g3⟩ => ?_)
  have hk₃ : Kept (kW N scA s₀.sp) s₀ s₃ := k₂.trans (o₃.kept _)
  have e₃ := he.kept hk₃
  rw [k₂.cs _ hsc, hs] at g0
  have hpl : (s₂.gpr .a0).toNat < 136 := by
    rw [show (s₂.gpr .a0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ (by decide)
  have hP : PadArgs s₃ scA 136 (s₂.gpr .a0).toNat :=
    ⟨g0, g1, by rw [g2, ofNat_toNat], rate136, hpl, e₃.spal, e₃.sp, e₃.d.sub_right (st_sub scA he.big)⟩
  have cw := cov_st he.big e₃.w
  refine WP.seq (pad_call hP (by simpa using cov_right cw) cw fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ st₄ => ?_)
  have hk₄ : Kept (kW N scA s₀.sp) s₀ s₄ := hk₃.trans ⟨rd₄, wr₄, sp₄, cs₄, by rw [← hk₃.sp]; exact frame_kw he.big f₄⟩
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [g3] at st
  -- The squeeze.
  refine WP.seq (WP.mono (squeezeArgs_ok hsc hf ho hn) fun s₅ ⟨o₅, h0, h1, h2, h3, h4⟩ => ?_)
  have hk₅ : Kept (kW N scA s₀.sp) s₀ s₅ := hk₄.trans (o₅.kept _)
  have e₅ := he.kept hk₅
  rw [hk₄.cs _ hsc, hs] at h0
  rw [hk₄.cs _ hf, hout] at h3
  have dsp₅ : (below s₅.sp 1168).Disjoint ⟨out, n⟩ := by rw [hk₅.sp]; exact dsp
  have hS : SqueezeArgs s₅ scA out 136 0 n :=
    ⟨h0, h1, h2, h3, h4, rate136, by decide, by omega_using [hn], e₅.spal, e₅.sp, dsc.symm.sub_left (st_sub scA he.big),
      e₅.d.sub_right (st_sub scA he.big), dsp₅⟩
  have cw₅ : Covers [⟨scA, 200⟩, ⟨out, n⟩] s₅.wr := by
    rw [hk₅.wr]
    intro a m ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_st he.big he.w a m ⟨_, List.mem_cons_self, hc⟩
    · exact hw a m ⟨_, List.mem_cons_self, hc⟩
  refine squeeze_call hS (by simpa using cov_right cw₅) cw₅ fun s₆ rd₆ wr₆ sp₆ cs₆ f₆ b₆ _ _ => ?_
  refine ⟨(hk₅.mono fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩).trans
    ⟨rd₆, wr₆, sp₆, cs₆, ?_⟩, ?_⟩
  · rw [← hk₅.sp]
    exact f₆.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, st_sub scA he.big⟩
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [b₆, o₅.mem, st, squeezeFrom_zero]
    rfl

end VG.Proof.Sha3.RISCV64.Pieces

end

end

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message_cached`: the steps

As Ed448's whole functions on this target (`Proof/Ed448/RISCV64/Whole/`),
whose invariant `Inv` (`Proof/Ed25519/RISCV64/Whole/Frame.lean`) they share:
the registers `rs` and the link register saved at `oSV(E)`, then the
arguments moved into `rs` (`setup_ok`, by `movs_ok`); the two bytes
`0 ‖ ctx_len` stored at `oHdr(E)` (`hdr_ok`); a hash, or any step that keeps
the callee-saved registers and writes within the body's regions, apart from
the slots, keeps `Inv` (`inv_kept`); the branch on `ctx_len >> 8`
(`wp_ite`, `shr8_zero`); and the moves of a call's arguments (`args4_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64 VG.Proof.X25519.RISCV64
open VG.Impl.Ed25519.RISCV64.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.RISCV64.Whole (Inv slotArea save_ok)
open VG.Impl.Sha3.RISCV64.Pieces (Piece Len)
open VG.Proof.Sha3.RISCV64.Pieces (Kept PieceOk)

/-- `mov`s from registers that none of them writes, to distinct registers. -/
theorem movs_ok : ∀ (ms : List (Reg × Reg)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ ms, p.2 ∉ ms.map Prod.fst) → (ms.map Prod.fst).Nodup →
    (∀ u, u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      (∀ p ∈ ms, u.gpr p.1 = s.gpr p.2) → (∀ r, r ∉ ms.map Prod.fst → u.gpr r = s.gpr r) →
      WP isa (.block rest) u Q) →
    WP isa (.block (ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  intro ms
  induction ms with
  | nil => exact fun _ _ k => k _ rfl rfl rfl rfl (fun _ h => absurd h List.not_mem_nil) fun _ _ => rfl
  | cons p ms ih =>
    intro s rest Q hs hn k
    obtain ⟨d, n⟩ := p
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons, List.cons_append]
    refine Steps.wp_mv fun u hu => ih (fun q hq => fun h => hs q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ h))
      hn'.2 fun u' m' rd' wr' sp' hm ho => k u' (m'.trans hu.mem) (rd'.trans hu.rd) (wr'.trans hu.wr)
        (sp'.trans hu.sp) (fun q hq => ?_) fun r hr => ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hn'.1, hu.gpr]
      · have hq2 : q.2 ≠ d := fun e => hs q (List.mem_cons_of_mem _ hq) (e ▸ List.mem_cons_self)
        rw [hm q hq, hu.other _ hq2]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hu.other r hr.1]

/-- The saves at `o(F)` (`F`, a multiple of 8, in `f`), then the moves `ms` into the registers `rs`,
which hold `v`: the invariant holds after them. -/
theorem setup_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {ms : List (Reg × Reg)} {v : Reg → BitVec 64}
    {W : List Region} {rest : List Instr} {Q : State → Prop} (hal : (s.gpr f).toNat % 8 = 0)
    (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (hW : ∃ R ∈ W, Region.Sub (slotArea (s.gpr f) o rs) R) (hms : ms.map Prod.fst = rs)
    (hsrc : ∀ p ∈ ms, p.2 ∉ rs) (hnd : rs.Nodup) (hv : ∀ p ∈ ms, v p.1 = s.gpr p.2)
    (k : ∀ u, Inv s (s.gpr f) o rs v W u → (∀ r, r ∉ rs → u.gpr r = s.gpr r) → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine save_ok hal hfits hlo hin fun u hu hsv hfr => ?_
  refine movs_ok ms (fun p hp => hms ▸ hsrc p hp) (hms ▸ hnd)
    fun u' m' rd' wr' sp' hm ho => k u' ⟨rd'.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, fun r hr => ?_,
      fun r hr hn => ?_, m' ▸ hsv, m' ▸ hfr.sub fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hW⟩ fun r hn => ?_
  · rw [← hms] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [hm p hp, hv p hp, hu.gpr _ (by simp)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simp)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simp)]

/-- A step that keeps the callee-saved registers, writing within `W` and apart from the slots. -/
theorem inv_kept {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hk : Kept Wc t t')
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' :=
  h.step hrs hk.rd hk.wr hk.sp hk.cs hk.frame hsub hd

/-- `Inv` from a state that agrees with `s` on what it records. -/
theorem inv_rebase {s u t : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W : List Region}
    (h : Inv u F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.gpr .ra = s.gpr .ra) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    Inv s F o rs v W t where
  rd := h.rd.trans hrd
  wr := h.wr.trans hwr
  sp := h.sp.trans hsp
  regs := h.regs
  pres r hr hn := (h.pres r hr hn).trans (hg r hr)
  saved p hp := by
    rw [h.saved p hp]
    obtain ⟨⟨r, i⟩, hm', rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, hlt, he⟩ := List.mem_zipIdx hm'
    have hm'' : r ∈ rs ++ [.ra] := by rw [he]; exact List.getElem_mem _
    rcases List.mem_append.mp hm'' with h' | h'
    · exact hg r (hrs r h')
    · rw [List.mem_singleton.mp h']; exact hlr
  frame := hm ▸ h.frame

/-! ## Pieces and regions -/

theorem pieceOk_of {N : Nat} {t : State} {sc : Addr} {p : Piece} {R : Region} (hR : p.R t.gpr = R)
    (hb : p.base ∈ preserved) (ho : p.off < 2048) (hl : p.len.Ok) (hc : RISCV64.Covers [R] (t.rd ++ t.wr))
    (hd : R.Disjoint ⟨sc, N⟩) (hb' : (below t.sp 1168).Disjoint R) : PieceOk N sc t p :=
  ⟨hb, ho, hl, hR ▸ hc, hR ▸ hd, hR ▸ hb'⟩

theorem cov_in {ws : List Region} {P : Addr} {k d n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : d + n ≤ k) :
    RISCV64.Covers [⟨P + BitVec.ofNat 64 d, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, d, rfl, h⟩

theorem cov_in0 {ws : List Region} {P : Addr} {k n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : n ≤ k) :
    RISCV64.Covers [⟨P, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem cov_rd {rd wr ws : List Region} (h : RISCV64.Covers ws rd) : RISCV64.Covers ws (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## The header -/

/-- The memory after the two bytes `0 ‖ c` at `a`. -/
abbrev hdrMem (m : Mem) (a : Addr) (c : BitVec 64) : Mem :=
  (m.writeW a ((0 : BitVec 64).setWidth 8)).writeW (a + BitVec.ofNat 64 1) (c.setWidth 8)

theorem hdrMem_bytes (m : Mem) (a : Addr) (c : Nat) :
    Spec.Sha3.bytesAt (hdrMem m a (BitVec.ofNat 64 c)) a 2 = [0, BitVec.ofNat 8 c] := by
  have hne : a ≠ a + BitVec.ofNat 64 1 := fun e => by
    have := congrArg (fun x => (x - a).toNat) e
    simp only [BitVec.sub_self, Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [Spec.Sha3.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil,
    show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a, hdrMem]
  rw [Proof.MlDsa.Message.byte_writeW_self, Proof.MlDsa.Message.byte_writeW_other _ hne,
    Proof.MlDsa.Message.byte_writeW_self]
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem hdrMem_frame (m : Mem) (a : Addr) (c : BitVec 64) : Frame [⟨a, 2⟩] m (hdrMem m a c) := by
  refine Frame.write (Frame.write (Frame.refl _ _) List.mem_cons_self _ ?_) List.mem_cons_self _ ?_
  · simpa using Offset.contains_base a (d := 0) (n := 1) (k := 2) (by decide) (by decide)
  · exact Offset.contains_base a (d := 1) (n := 1) (k := 2) (by decide) (by decide)

/-- `0 ‖ c` at `o(f)` (`c` in `cr`). -/
theorem hdr_ok {s : State} {f cr : Reg} (hf0 : f ≠ .t0) (hc0 : cr ≠ .t0) {o : Nat} (ho : o + 1 < 2048)
    (hw : InRegions s.wr (s.gpr f + BitVec.ofNat 64 o) 1) (hw1 : InRegions s.wr (s.gpr f + BitVec.ofNat 64 (o + 1)) 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = hdrMem s.mem (s.gpr f + BitVec.ofNat 64 o) (s.gpr cr) → t.rd = s.rd → t.wr = s.wr →
      t.sp = s.sp → (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (([.li .t0 0, .store .b .t0 f o, .store .b cr f (o + 1)] : List Instr) ++ is)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine Steps.wp_li (by decide) fun u₁ h₁ => ?_
  have g : u₁.gpr f = s.gpr f := h₁.other _ hf0
  refine Steps.wp_sb (by omega_using [ho]) rfl (by rw [h₁.wr, g]; exact hw) fun u₂ h₂ => ?_
  refine Steps.wp_sb ho rfl (by rw [h₂.wr, h₁.wr, h₂.gpr, g]; exact hw1) fun u₃ h₃ => ?_
  refine k u₃ ?_ (by rw [h₃.rd, h₂.rd, h₁.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr]) (by rw [h₃.sp, h₂.sp, h₁.sp])
    fun r hr => by rw [h₃.gpr, h₂.gpr, h₁.other _ hr]
  rw [h₃.mem, h₂.gpr, h₂.mem, h₁.mem, g, h₁.gpr, h₁.other _ hc0, hdrMem, Proof.MlDsa.Message.add_add]
  rfl

/-! ## The branch on the length of the context -/

theorem wp_ite {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, s', Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, s', Exec.iteT hc e, q⟩

theorem shr8_zero (x : BitVec 64) : (x >>> 8 == 0#64) = decide (x.toNat < 256) := by
  have h : (x >>> 8).toNat = x.toNat / 256 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · simp only [hx, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h, Nat.div_eq_of_lt hx]; rfl)
  · simp only [hx, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [h] at this
    exact hx (by simp at this; omega_using [this])

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0#64) := rfl

end VG.Proof.MlDsa.RISCV64.Message
