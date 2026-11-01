module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.Prims
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: the hash routine

As on PPC64LE (`Proof/MlKem/PPC64LE/HashTop.lean`). `hash`
(`Impl/MlKem/RISCV64/Top.lean`) computes the sponge of the concatenation of
its input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues the
message from the position the previous one returned, the padding, and each
`squeeze` continues the output. It changes only the Keccak state, the
outputs, the 1168 bytes below the stack pointer, and registers that are not
callee-saved.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)
open VG.Proof.Sha3.RISCV64.Stream (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)
open VG.Impl.Sha3.RISCV64.Stream (mov)

theorem pres_ne {r : Reg} (h : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 := by
  revert r; decide

/-- Writes of registers other than the callee-saved ones keep them. -/
theorem Only.of_writes {s s' : State} (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (h : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Only s s' :=
  ⟨h, hm, hrd, hwr, hsp⟩

theorem updOnly {s s' : State} {d : Reg} {v : BitVec 64} (h : Wp.Upd s s' d v) (hd : d ∉ preserved) : Only s s' :=
  ⟨fun r hr => h.other r fun e => hd (e ▸ hr), h.mem, h.rd, h.wr, h.sp⟩

/-! ## Addresses at offsets below 32 KiB -/

theorem lui_val : ∀ h < 9, sext32 (BitVec.ofNat 20 h ++ (0 : BitVec 12)) = BitVec.ofNat 64 (4096 * h) := by
  decide

theorem addrOf_val {off : Nat} :
    BitVec.ofNat 64 (4096 * ((off + 2048) / 4096)) +
      BitVec.ofInt 64 ((off : Int) - 4096 * ((off + 2048) / 4096 : Nat)) = BitVec.ofNat 64 off := by
  generalize (off + 2048) / 4096 = q
  have e : (off : Int) = ((4096 * q : Nat) : Int) + ((off : Int) - 4096 * (q : Int)) := by
    rw [Int.natCast_mul]; omega
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add, ← e, BitVec.ofInt_natCast]

/-- `d ← b + off` (`addrOf`). -/
theorem wp_addrOf {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {off : Nat} (hb : b ≠ d)
    (h : off < 32768) (k : ∀ s', Wp.Upd s s' d (s.gpr b + BitVec.ofNat 64 off) → WP isa (.block is) s' Q) :
    WP isa (.block (addrOf d b off ++ is)) s Q := by
  unfold addrOf
  split
  · exact Wp.wp_addi (by assumption) k
  · rename_i hlt
    have hq : (off + 2048) / 4096 < 9 := by omega
    refine Wp.WP.cons exec_lui (Wp.WP.cons (exec_addi (by unfold imm12; omega)) (Wp.WP.cons exec_add
      (k _ ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩)))
    · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hb, lui_val _ hq, addrOf_val]
    · simp only [RegUpd.gpr_write_of_ne _ _ hr]

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved)
    (hre : rate < 2048) (hoe : p.off < 32768) (hle : p.len < 2048) :
    WP isa (.block (spongeArgs rate first p)) s fun s' => Only s s' ∧
      s'.gpr .a0 = s.gpr .s11 ∧ s'.gpr .a1 = BitVec.ofNat 64 rate ∧
      s'.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) ∧
      s'.gpr .a3 = s.gpr p.base + BitVec.ofNat 64 p.off ∧ s'.gpr .a4 = BitVec.ofNat 64 p.len := by
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := pres_ne hb
  have k : ∀ u : State, Only s u → u.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) →
      u.gpr .s11 = s.gpr .s11 → u.gpr p.base = s.gpr p.base →
      WP isa (.block (mov .a0 .s11 :: .li .a1 rate :: (addrOf .a3 p.base p.off ++ [.li .a4 p.len]))) u fun s' =>
        Only s s' ∧ s'.gpr .a0 = s.gpr .s11 ∧ s'.gpr .a1 = BitVec.ofNat 64 rate ∧
        s'.gpr .a2 = (if first then BitVec.ofNat 64 0 else s.gpr .a0) ∧
        s'.gpr .a3 = s.gpr p.base + BitVec.ofNat 64 p.off ∧ s'.gpr .a4 = BitVec.ofNat 64 p.len := by
    intro u o g2 g11 gb
    refine Wp.wp_mv fun u₁ h₁ => Wp.wp_li hre fun u₂ h₂ => wp_addrOf b4 hoe fun u₃ h₃ => Wp.wp_li hle fun u₄ h₄ =>
      WP.block_nil ⟨o.trans ((updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans
        ((updOnly h₃ (by decide)).trans (updOnly h₄ (by decide))))), ?_, ?_, ?_, ?_, ?_⟩
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, g11]
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
    · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), g2]
    · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ b2, h₁.other _ b1, gb]
    · rw [h₄.gpr]
  simp only [spongeArgs, List.cons_append, List.nil_append]
  cases first with
  | true =>
    exact Wp.wp_li (by decide) fun u h => k u (updOnly h (by decide)) h.gpr (h.other _ (by decide))
      (h.other _ b3)
  | false =>
    exact Wp.wp_mv fun u h => k u (updOnly h (by decide)) h.gpr (h.other _ (by decide)) (h.other _ b3)

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : rate < 2048) (hse : sfx < 2048) :
    WP isa (.block [mov .a2 .a0, mov .a0 .s11, .li .a1 rate, .li .a3 sfx]) s
      fun s' => Only s s' ∧ s'.gpr .a0 = s.gpr .s11 ∧ s'.gpr .a1 = BitVec.ofNat 64 rate ∧
        s'.gpr .a2 = s.gpr .a0 ∧ s'.gpr .a3 = BitVec.ofNat 64 sfx := by
  refine Wp.wp_mv fun u₁ h₁ => Wp.wp_mv fun u₂ h₂ => Wp.wp_li hre fun u₃ h₃ => Wp.wp_li hse fun u₄ h₄ =>
    WP.block_nil ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
      (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₄.gpr]

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Lay.fit_off {L : Lay} (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i)
    (hl : 0 < l) : (L.ptr i + BitVec.ofNat 64 o).toNat + l ≤ 2 ^ 64 := by
  have := hL.fit i hi
  have := (L.ptr i).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem Lay.R_zero (L : Lay) (i l : Nat) : (⟨L.ptr i, l⟩ : Region) = L.R i 0 l := by
  simp only [Lay.R, BitVec.add_zero]

theorem Ctx.sep00 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega_arith

theorem Ctx.sep01 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 1168) : sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega_arith

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : sepB sz a b = true) : sepB sz b a = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega_arith

/-- The regions of the sponge functions: the state and the stack below. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (1, 0, 1168)]

theorem Ctx.kregs {L : Lay} {s : State} (hc : Ctx L s) :
    (⟨L.ptr 0, 200⟩ : Region) = L.R 0 0 200 ∧ below s.sp 1168 = L.R 1 0 1168 :=
  ⟨Lay.R_zero _ _ _, hc.bel⟩

theorem RL_kRegs (L : Lay) : L.RL kRegs = [L.R 0 0 200, L.R 1 0 1168] := rfl

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : p.off < 32768
  lenc : p.len < 2048
  pos : 0 < p.len
  sep : sepAll L.sizes (idx p.base, p.off, p.len) kRegs = true
  cov : (⟨L.ptr (idx p.base), L.size (idx p.base)⟩ : Region) ∈ (if w then s.wr else s.rd ++ s.wr)

/-- The region of a piece. -/
abbrev Lay.P (L : Lay) (idx : Reg → Nat) (p : Piece) : Region := L.R (idx p.base) p.off p.len

/-- The bytes of a piece. -/
abbrev Lay.pb (L : Lay) (idx : Reg → Nat) (m : Mem) (p : Piece) : List Byte :=
  bytesAt m (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) p.len

theorem sepAll_head {sz : List Nat} {a w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz a (w :: W) = true) : sepB sz a w = true := by
  simp only [sepAll, List.all_cons, Bool.and_eq_true] at h; exact h.1

theorem sepB_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} (h : sepB sz (i, o, l) w = true) :
    i < sz.length ∧ o + l ≤ sz.getD i 0 := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.2⟩

theorem PieceOk.bounds {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    idx p.base < L.sizes.length ∧ p.off + p.len ≤ L.size (idx p.base) :=
  sepB_bounds (sepAll_head h.sep)

theorem PieceOk.sepK {L : Lay} {idx : Reg → Nat} {s : State} {w : Bool} {p : Piece} (h : PieceOk L idx s w p) :
    sepB L.sizes (idx p.base, p.off, p.len) (0, 0, 200) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 1168) = true := by
  have := h.sep
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2⟩

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .a0).toNat

theorem pos_r5 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 64 0 else s.gpr .a0) = BitVec.ofNat 64 (Pos first s) := by
  cases first
  · simp only [Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega_arith

theorem rates_lt {rate : Nat} (h : rate ∈ rates) : rate ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega_arith

/-- The registers and permissions of `s₀`. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : Kept rs s₀ s) : Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : Rg s₀ s) (hk : Kept rs s s') : Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], fun r hr => by rw [hk.cs r hr, h.cs r hr]⟩

theorem Rg.ctx {L : Lay} {s₀ s : State} (hc : Ctx L s₀) (h : Rg s₀ s) : Ctx L s :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .s11 (by decide), hc.s11], by rw [h.sp]; exact hc.sp1168,
    by rw [h.sp]; exact hc.al, hc.al0, by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

theorem PieceOk.covR {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ false p)
    (hg : Rg s₀ s) : Covers [L.P idx p] (s.rd ++ s.wr) := by
  have := h.cov
  simp only [Bool.false_eq_true, ite_false] at this
  rw [hg.rd, hg.wr]
  exact Lay.covers this h.bounds.2

theorem PieceOk.covW {L : Lay} {idx : Reg → Nat} {s₀ s : State} {p : Piece} (h : PieceOk L idx s₀ true p)
    (hg : Rg s₀ s) : Covers [L.P idx p] s.wr := by
  have := h.cov
  simp only [ite_true] at this
  rw [hg.wr]
  exact Lay.covers this h.bounds.2

theorem covers_kregs {L : Lay} {s : State} (hc : Ctx L s) :
    Covers [(⟨L.ptr 0, 200⟩ : Region)] s.wr := by
  rw [hc.kregs.1]
  exact hc.cs (by decide)

/-- The sponge's regions in a state's terms are those of `kRegs`. -/
theorem kregs_eq {L : Lay} {s : State} (hc : Ctx L s) :
    [(⟨L.ptr 0, 200⟩ : Region), below s.sp 1168] = L.RL kRegs := by
  rw [hc.kregs.1, hc.kregs.2]; rfl

/-! ## The arguments of the sponge functions -/

theorem absorbArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hp : PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g3 : s₁.gpr .a0 = L.ptr 0) (g4 : s₁.gpr .a1 = BitVec.ofNat 64 rate) (g5 : s₁.gpr .a2 = BitVec.ofNat 64 pos)
    (g6 : s₁.gpr .a3 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (g7 : s₁.gpr .a4 = BitVec.ofNat 64 p.len) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, g6, g7, hrate, hpos, by have := hp.lenc; omega_arith, hc₁.al, hc₁.sp1168, ?_, ?_, ?_⟩
  · rw [e0]; exact Lay.disj hL hp.sepK.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2]; exact Lay.disj hL (sepB_symm hp.sepK.2)

theorem squeezeArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hp : PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g3 : s₁.gpr .a0 = L.ptr 0) (g4 : s₁.gpr .a1 = BitVec.ofNat 64 rate) (g5 : s₁.gpr .a2 = BitVec.ofNat 64 pos)
    (g6 : s₁.gpr .a3 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (g7 : s₁.gpr .a4 = BitVec.ofNat 64 p.len) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, g6, g7, hrate, hpos, by have := hp.lenc; omega_arith, hc₁.al, hc₁.sp1168, ?_, ?_, ?_⟩
  · rw [e0]; exact Lay.disj hL (sepB_symm hp.sepK.1)
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2]; exact Lay.disj hL (sepB_symm hp.sepK.2)

theorem padArgs_of {L : Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) (g3 : s₁.gpr .a0 = L.ptr 0) (g4 : s₁.gpr .a1 = BitVec.ofNat 64 rate)
    (g5 : s₁.gpr .a2 = BitVec.ofNat 64 pos) :
    PadArgs s₁ (L.ptr 0) rate pos := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, hrate, hpos, hc₁.al, hc₁.sp1168, ?_⟩
  rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-! ## The absorbs -/

theorem rate_imm {rate : Nat} (h : rate ∈ rates) : rate < 2048 := by have := rates_lt h; omega_arith

theorem absorbs_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ : State}
    (hc : Ctx L s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, PieceOk L idx s₀ false p) →
      Kept (L.RL kRegs) s₀ s → Repr s.mem (L.ptr 0) rate msg →
      Pos first s = msg.length % rate →
      WP isa (absorbs rate first ps) s fun s' =>
        Kept (L.RL kRegs) s₀ s' ∧
        Repr s'.mem (L.ptr 0) rate (msg ++ (ps.map (L.pb idx s₀.mem)).flatten) ∧
        Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (L.pb idx s₀.mem)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => WP.block_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have hcs := hk.rg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base (rate_imm hrate) hp.oenc hp.lenc)
      fun s₁ ⟨o₁, g3, g4, g5, g6, g7⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base, hp.ptr]
    rw [hcs.s11] at g3
    rw [gb] at g6
    rw [pos_r5] at g5
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    have hg₁ : Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA := absorbArgs_of hrate hc₁ hp hpos' g3 g4 g5 g6 g7
    have cw := covers_kregs hc₁
    refine WP.seq (absorb_call hA (covers_append (hp.covR hg₁) (covers_wr cw)) cw
      fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ r₂ ret₂ => ?_)
    have k₂ : Kept (L.RL kRegs) s₁ s₂ := ⟨cs₂, sp₂, rd₂, wr₂, by rw [← kregs_eq hc₁]; exact f₂⟩
    have hk₂ : Kept (L.RL kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.lenc; omega_arith)
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .a0).toNat = _
      rw [ret₂, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false, ← List.append_assoc]
        at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The triple of a piece. -/
abbrev trip (idx : Reg → Nat) (p : Piece) : Nat × Nat × Nat := (idx p.base, p.off, p.len)

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (L : Lay) (idx : Reg → Nat) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => L.pb idx m p = squeezeFrom rate P c p.len ∧ Outs L idx m rate P (c + p.len) ps

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W = true) (h' : sepAll sz a W' = true) : sepAll sz a (W ++ W') = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩

theorem sepAll_map {α : Type} {sz : List Nat} {a : Nat × Nat × Nat} {ps : List α} {f : α → Nat × Nat × Nat}
    (h : ∀ q ∈ ps, sepB sz a (f q) = true) : sepAll sz a (ps.map f) = true := by
  simp only [sepAll, List.all_map, List.all_eq_true, Function.comp]; exact h

theorem squeezes_ok {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ : State}
    (hc : Ctx L s₀) {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, PieceOk L idx s₀ true p) → ps.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true) →
      Rg s₀ s → Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (L.ptr 0)) (Pos first s) d = squeezeFrom rate P c d) →
      WP isa (squeezes rate first ps) s fun s' =>
        Kept (L.RL (kRegs ++ ps.map (trip idx))) s s' ∧ Outs L idx s'.mem rate P c ps := by
  intro ps
  induction ps with
  | nil => exact fun _ s _ _ _ _ _ _ => WP.block_nil ⟨Kept.refl _ _, trivial⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have hL := hc.ok
    have rpos := rate_pos hrate
    have rle := rates_lt hrate
    have hcs := hg.ctx hc
    refine WP.seq (WP.mono (kargs_ok first hp.base (rate_imm hrate) hp.oenc hp.lenc)
      fun s₁ ⟨o₁, g3, g4, g5, g6, g7⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base, hp.ptr]
    rw [hcs.s11] at g3
    rw [gb] at g6
    rw [pos_r5] at g5
    have hg₁ : Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS := squeezeArgs_of hrate hc₁ hp hple g3 g4 g5 g6 g7
    have cw : Covers [(⟨L.ptr 0, 200⟩ : Region), L.P idx p] s₁.wr := by
      rw [hc₁.kregs.1]
      exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg₁) covers_nil')
    refine WP.seq (squeeze_call hS (covers_wr cw) cw fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ r₂ n₂ => ?_)
    have k₂ : Kept [L.R 0 0 200, L.P idx p, L.R 1 0 1168] s₁ s₂ := ⟨cs₂, sp₂, rd₂, wr₂, by
      rw [← hc₁.kregs.1, ← hc₁.kregs.2]; exact f₂⟩
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) p.len = _
      rw [b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (L.ptr 0)) (Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₂ = (s₂.gpr .a0).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega_arith) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (sepAll_append hp.sep (sepAll_map pw.1)) (by have := hp.lenc; omega_arith)

/-! ## The whole hash -/

theorem zeroState_ok {L : Lay} {s : State} (hc : Ctx L s) :
    WP isa (.block (zeroState .s11)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (L.ptr 0) = Spec.Sha3.zero := by
  rw [zeroState, WP.block_append_iff]
  have hli : WP isa (.block [.li .t0 0]) s fun s₁ => s₁ = s.write .t0 (BitVec.ofNat 64 0) := by
    crun []
  refine WP.mono hli fun s₁ e₁ => ?_
  subst e₁
  have e31 : (s.write .t0 (BitVec.ofNat 64 0)).gpr .s11 = L.ptr 0 := by
    simp only [State.write, show Reg.s11 ≠ Reg.t0 by decide, ite_false]; exact hc.s11
  have fit := hc.fit
  have al0 := hc.al0
  refine WP.mono (Sample.zeroLanes_ok .s11 (s₁ := s.write .t0 (BitVec.ofNat 64 0))
    (by simp [State.write]) (fun k hk => by
      rw [e31]
      exact hc.cs (o := 8 * k) (l := 8) (by omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (fun k hk => by rw [e31, BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e31] at hf hz
  refine ⟨⟨fun r hr => ?_, by rw [h₂.sp]; rfl, by rw [h₂.rd]; rfl,
    by rw [h₂.wr]; rfl, ?_⟩, Sample.stateAt_zero hz⟩
  · rw [h₂.gpr]
    simp only [State.write, (pres_ne hr).1, ite_false]
  · show Frame [L.R 0 0 200] s.mem s₂.mem
    rw [← Lay.R_zero]; exact hf

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 64 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : sfx < 2 ^ 64)]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hash_ok {L : Lay} {idx : Reg → Nat} {rate sfx : Nat} (hrate : rate ∈ rates)
    (hsfx : sfx < 256) {s₀ : State} (hc : Ctx L s₀) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk L idx s₀ false p) (hout : ∀ p ∈ outs, PieceOk L idx s₀ true p)
    (hpw : outs.Pairwise (fun p q => sepB L.sizes (trip idx p) (trip idx q) = true)) :
    WP isa (hash rate sfx ins outs) s₀ fun s' =>
      Kept (L.RL (kRegs ++ outs.map (trip idx))) s₀ s' ∧
      Outs L idx s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (L.pb idx s₀.mem)).flatten)) 0
        outs := by
  have rpos := rate_pos hrate
  refine WP.seq (WP.mono (zeroState_ok hc) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (absorbs_ok hrate hc ins true s₁ [] hin (k₁.monoL (by simp))
    (VG.Proof.MlKem.repr_nil z₁) (by simp [Pos])) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false] at p₂
  rw [List.nil_append] at r₂ p₂
  have hc₂ := k₂.rg.ctx hc
  refine WP.seq (WP.mono (pargs_ok (rate_imm hrate) (by omega_arith : sfx < 2048))
    fun s₃ ⟨o₃, g3, g4, g5, g6⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.s11] at g3
  have hP : PadArgs s₃ (L.ptr 0) rate (s₂.gpr .a0).toNat :=
    padArgs_of hrate hc₃ (by rw [show (s₂.gpr .a0).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos)
      g3 g4 (by rw [g5, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have cw := covers_kregs hc₃
  refine WP.seq (pad_call hP (covers_wr cw) cw fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ st₄ => ?_)
  have k₄ : Kept (L.RL kRegs) s₃ s₄ := ⟨cs₄, sp₄, rd₄, wr₄, by rw [← kregs_eq hc₃]; exact f₄⟩
  have st := st₄ _ (by rw [o₃.mem]; exact r₂) p₂
  rw [g6, sfx8 hsfx] at st
  have hg₄ : Rg s₀ s₄ := (k₂.trans ((o₃.kept _).trans k₄)).rg
  refine WP.mono (squeezes_ok hrate hc outs true s₄ 0 hout hpw hg₄ (Nat.zero_le _)
    (fun d => by rw [st]; rfl)) fun s' ⟨k', o'⟩ => ⟨?_, o'⟩
  exact ((k₂.trans ((o₃.kept _).trans k₄)).monoL fun w hw => List.mem_append_left _ hw).trans k'

/-- The 64 bytes of `G(c)` squeezed at once: both of its outputs. -/
theorem G_split (c : List Byte) :
    Spec.Sha3.squeezeFrom 72 (VG.Proof.MlKem.padded 72 Spec.Sha3.sha3Suffix c) 0 64 =
      (Spec.MlKem.G c).1 ++ (Spec.MlKem.G c).2 := by
  simp only [Spec.MlKem.G, VG.Proof.MlKem.sha3_512_eq, List.take_append_drop]

end VG.Proof.MlKem.RISCV64
