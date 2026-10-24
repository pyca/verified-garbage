module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KCall
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Prims
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: the hash routine

As on 32-bit ARM (`Proof/MlKem/Arm/HashTop.lean`). `hash`
(`Impl/MlKem/PPC64LE/Top.lean`) computes the sponge of the concatenation of
its input pieces, and writes consecutive output to its output pieces
(`hash_ok`): from the all-zero state (`repr_nil`), each `absorb` continues the
message from the position the previous one returned, the padding, and each
`squeeze` continues the output. It changes only the Keccak state and working
space, the outputs, the 48 bytes below the stack pointer, and registers that
are not callee-saved.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

theorem pres_ne {r : Reg} (h : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 := by
  revert r; decide

/-- Writes of registers other than the callee-saved ones keep them. -/
theorem Only.of_writes {s s' : State} (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (h : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Only s s' :=
  ⟨h, hm, hrd, hwr, hsp⟩

/-- The arguments of an `absorb` or a `squeeze`. -/
theorem kargs_ok {s : State} {rate : Nat} (first : Bool) {p : Piece} (hb : p.base ∈ preserved)
    (hre : rate < 32768) (hoe : p.off < 32768) (hle : p.len < 32768) :
    WP isa (.block (spongeArgs rate first p)) s fun s' => Only s s' ∧
      s'.gpr .r3 = s.gpr .r31 ∧ s'.gpr .r4 = BitVec.ofNat 64 rate ∧
      s'.gpr .r5 = (if first then BitVec.ofNat 64 0 else s.gpr .r3) ∧
      s'.gpr .r6 = s.gpr p.base + BitVec.ofNat 64 p.off ∧ s'.gpr .r7 = BitVec.ofNat 64 p.len ∧
      s'.gpr .r8 = s.gpr .r31 + BitVec.ofNat 64 200 := by
  obtain ⟨n0, n3, n4, n5, n6, n7, n8⟩ := pres_ne hb
  have hw : oWork < 32768 := by decide
  cases first <;>
  · prun [spongeArgs, posArg, hw, hre, hoe, hle, n0, n3, n4, n5, n6, n7, n8, Ne.symm n3, Ne.symm n4, Ne.symm n5,
      Bool.false_eq_true, ite_true, ite_false]
    exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

/-- The arguments of a `pad`. -/
theorem pargs_ok {s : State} {rate sfx : Nat} (hre : rate < 32768) (hse : sfx < 32768) :
    WP isa (.block [mov .r5 .r3, mov .r3 .r31, .li .r4 rate, .li .r6 sfx, .addi .r7 .r31 oWork]) s
      fun s' => Only s s' ∧ s'.gpr .r3 = s.gpr .r31 ∧ s'.gpr .r4 = BitVec.ofNat 64 rate ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r6 = BitVec.ofNat 64 sfx ∧ s'.gpr .r7 = s.gpr .r31 + BitVec.ofNat 64 200 := by
  have hw : oWork < 32768 := by decide
  prun [hw, hre, hse]
  exact ⟨⟨by pres_tac, rfl, rfl, rfl, rfl⟩, trivial⟩

/-! ## Regions in `scratch` and below the stack pointer -/

theorem Lay.fit_off {L : Lay} (hL : L.Ok) {i o l : Nat} (hi : i < L.sizes.length) (h : o + l ≤ L.size i)
    (hl : 0 < l) : (L.ptr i + BitVec.ofNat 64 o).toNat + l ≤ 2 ^ 64 := by
  have := hL.fit i hi
  have := (L.ptr i).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem Lay.R_zero (L : Lay) (i l : Nat) : (⟨L.ptr i, l⟩ : Region) = L.R i 0 l := by
  simp only [Lay.R, BitVec.add_zero]

theorem Ctx.sep00 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 32768) (h : o + l ≤ o' ∨ o' + l' ≤ o) : sepB L.sizes (0, o, l) (0, o', l') = true := by
  have := hc.len; have := hc.sz0
  simp only [sepB, Lay.size] at this ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega

theorem Ctx.sep01 {L : Lay} {s : State} (hc : Ctx L s) {o l o' l' : Nat} (h₁ : o + l ≤ 32768)
    (h₂ : o' + l' ≤ 48) : sepB L.sizes (0, o, l) (1, o', l') = true := by
  have h0 := hc.len; have h1 := hc.sz0; have h2 := hc.sz1
  simp only [Lay.size] at h1 h2
  simp only [sepB, h2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  omega

theorem sepB_symm {sz : List Nat} {a b : Nat × Nat × Nat} (h : sepB sz a b = true) : sepB sz b a = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
  omega

/-- The regions of the sponge functions: the state, the working space and the stack below. -/
abbrev kRegs : List (Nat × Nat × Nat) := [(0, 0, 200), (0, 200, 640), (1, 0, 48)]

theorem Ctx.kregs {L : Lay} {s : State} (hc : Ctx L s) :
    (⟨L.ptr 0, 200⟩ : Region) = L.R 0 0 200 ∧ below s.sp 48 = L.R 1 0 48 :=
  ⟨Lay.R_zero _ _ _, hc.bel⟩

theorem RL_kRegs (L : Lay) : L.RL kRegs = [L.R 0 0 200, L.R 0 200 640, L.R 1 0 48] := rfl

/-! ## Pieces -/

/-- Piece `p` is the region `L.R (idx p.base) p.off p.len`, which the state
may read (or write, if `w`), apart from the sponge's regions. -/
structure PieceOk (L : Lay) (idx : Reg → Nat) (s : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved
  ptr : s.gpr p.base = L.ptr (idx p.base)
  oenc : p.off < 32768
  lenc : p.len < 32768
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
      sepB L.sizes (idx p.base, p.off, p.len) (0, 200, 640) = true ∧
      sepB L.sizes (idx p.base, p.off, p.len) (1, 0, 48) = true := by
  have := h.sep
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .r3).toNat

theorem pos_r5 (first : Bool) (s : State) :
    (if first then BitVec.ofNat 64 0 else s.gpr .r3) = BitVec.ofNat 64 (Pos first s) := by
  cases first
  · simp only [Pos, Bool.false_eq_true, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem rates_lt {rate : Nat} (h : rate ∈ rates) : rate ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

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
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r31 (by decide), hc.r31], by rw [h.sp]; exact hc.sp48,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

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
    Covers [(⟨L.ptr 0, 200⟩ : Region), ⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩] s.wr := by
  rw [hc.kregs.1]
  exact covers_cons' (hc.cs (by decide)) (covers_cons' (hc.cs (by decide)) covers_nil')

/-- The sponge's regions in a state's terms are those of `kRegs`. -/
theorem kregs_eq {L : Lay} {s : State} (hc : Ctx L s) :
    [(⟨L.ptr 0, 200⟩ : Region), ⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩, below s.sp 48] = L.RL kRegs := by
  rw [hc.kregs.1, hc.kregs.2]; rfl

/-! ## The arguments of the sponge functions -/

theorem absorbArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hp : PieceOk L idx s₀ false p) {pos : Nat} (hpos : pos < rate)
    (g3 : s₁.gpr .r3 = L.ptr 0) (g4 : s₁.gpr .r4 = BitVec.ofNat 64 rate) (g5 : s₁.gpr .r5 = BitVec.ofNat 64 pos)
    (g6 : s₁.gpr .r6 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (g7 : s₁.gpr .r7 = BitVec.ofNat 64 p.len)
    (g8 : s₁.gpr .r8 = L.ptr 0 + BitVec.ofNat 64 200) :
    AbsorbArgs s₁ (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (L.ptr 0 + BitVec.ofNat 64 200)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, g6, g7, g8, hrate, hpos, by have := hp.lenc; omega, hc₁.sp48, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e0]; exact Lay.disj hL hp.sepK.1
  · exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [e2]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

theorem squeezeArgs_of {L : Lay} {idx : Reg → Nat} {rate : Nat} (hrate : rate ∈ rates) {s₀ s₁ : State}
    {p : Piece} (hc₁ : Ctx L s₁) (hp : PieceOk L idx s₀ true p) {pos : Nat} (hpos : pos ≤ rate)
    (g3 : s₁.gpr .r3 = L.ptr 0) (g4 : s₁.gpr .r4 = BitVec.ofNat 64 rate) (g5 : s₁.gpr .r5 = BitVec.ofNat 64 pos)
    (g6 : s₁.gpr .r6 = L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (g7 : s₁.gpr .r7 = BitVec.ofNat 64 p.len)
    (g8 : s₁.gpr .r8 = L.ptr 0 + BitVec.ofNat 64 200) :
    SqueezeArgs s₁ (L.ptr 0) (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) (L.ptr 0 + BitVec.ofNat 64 200)
      rate pos p.len := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, g6, g7, g8, hrate, hpos, by have := hp.lenc; omega, hc₁.sp48, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact Lay.disj hL (sepB_symm hp.sepK.1)
  · rw [e0]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · exact Lay.disj hL hp.sepK.2.1
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2]; exact Lay.disj hL (sepB_symm hp.sepK.2.2)
  · rw [e2]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

theorem padArgs_of {L : Lay} {rate : Nat} (hrate : rate ∈ rates) {s₁ : State} (hc₁ : Ctx L s₁) {pos : Nat}
    (hpos : pos < rate) (g3 : s₁.gpr .r3 = L.ptr 0) (g4 : s₁.gpr .r4 = BitVec.ofNat 64 rate)
    (g5 : s₁.gpr .r5 = BitVec.ofNat 64 pos) (g7 : s₁.gpr .r7 = L.ptr 0 + BitVec.ofNat 64 200) :
    PadArgs s₁ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 64 200) rate pos := by
  have hL := hc₁.ok
  obtain ⟨e0, e2⟩ := hc₁.kregs
  refine ⟨g3, g4, g5, g7, hrate, hpos, hc₁.sp48, ?_, ?_, ?_⟩
  · rw [e0]; exact Lay.disj hL (hc₁.sep00 (by decide) (by decide) (by decide))
  · rw [e2, e0]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))
  · rw [e2]; exact Lay.disj hL (sepB_symm (hc₁.sep01 (by decide) (by decide)))

/-! ## The absorbs -/

theorem rate_imm {rate : Nat} (h : rate ∈ rates) : rate < 32768 := by have := rates_lt h; omega

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
      fun s₁ ⟨o₁, g3, g4, g5, g6, g7, g8⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hk.cs _ hp.base, hp.ptr]
    rw [hcs.r31] at g3 g8
    rw [gb] at g6
    rw [pos_r5] at g5
    have hpos' : Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    have hg₁ : Rg s₀ s₁ := hk.rg.kept (o₁.kept [])
    have hA := absorbArgs_of hrate hc₁ hp hpos' g3 g4 g5 g6 g7 g8
    have cw := covers_kregs hc₁
    refine WP.seq (absorb_call hA (covers_append (hp.covR hg₁) (covers_wr cw)) cw
      fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ r₂ ret₂ => ?_)
    have k₂ : Kept (L.RL kRegs) s₁ s₂ := ⟨cs₂, sp₂, rd₂, wr₂, by rw [← kregs_eq hc₁]; exact f₂⟩
    have hk₂ : Kept (L.RL kRegs) s₀ s₂ := hk.trans ((o₁.kept _).trans k₂)
    have eb : bytesAt s₁.mem (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) p.len = L.pb idx s₀.mem p := by
      rw [o₁.mem]
      exact Lay.bytes_keep hL hk.frame hp.sep (by have := hp.lenc; omega)
    have rep := r₂ msg (by rw [o₁.mem]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₂ (msg ++ L.pb idx s₀.mem p) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₂ rep
      ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₂.gpr .r3).toNat = _
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
      fun s₁ ⟨o₁, g3, g4, g5, g6, g7, g8⟩ => ?_)
    have hc₁ := hcs.only o₁
    have gb : s.gpr p.base = L.ptr (idx p.base) := by rw [hg.cs _ hp.base, hp.ptr]
    rw [hcs.r31] at g3 g8
    rw [gb] at g6
    rw [pos_r5] at g5
    have hg₁ : Rg s₀ s₁ := hg.kept (o₁.kept [])
    have hS := squeezeArgs_of hrate hc₁ hp hple g3 g4 g5 g6 g7 g8
    have cw : Covers [(⟨L.ptr 0, 200⟩ : Region), L.P idx p, ⟨L.ptr 0 + BitVec.ofNat 64 200, 640⟩] s₁.wr := by
      rw [hc₁.kregs.1]
      exact covers_cons' (hc₁.cs (by decide)) (covers_cons' (hp.covW hg₁)
        (covers_cons' (hc₁.cs (by decide)) covers_nil'))
    refine WP.seq (squeeze_call hS (covers_wr cw) cw fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ r₂ n₂ => ?_)
    have k₂ : Kept [L.R 0 0 200, L.P idx p, L.R 0 200 640, L.R 1 0 48] s₁ s₂ := ⟨cs₂, sp₂, rd₂, wr₂, by
      rw [← hc₁.kregs.1, ← hc₁.kregs.2]; exact f₂⟩
    have out₂ : L.pb idx s₂.mem p = squeezeFrom rate P c p.len := by
      show bytesAt s₂.mem (L.ptr (idx p.base) + BitVec.ofNat 64 p.off) p.len = _
      rw [b₂, o₁.mem, hcont]
    have cont₂ : ∀ d, squeezeFrom rate (stateAt s₂.mem (L.ptr 0)) (Pos false s₂) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show Pos false s₂ = (s₂.gpr .r3).toNat from rfl, n₂, o₁.mem]
      exact squeezeFrom_shift rpos (by omega) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    have hg₂ : Rg s₀ s₂ := hg₁.kept k₂
    refine WP.mono (ih false s₂ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₂ r₂ cont₂)
      fun s' ⟨k', o'⟩ => ⟨?_, ?_, o'⟩
    · refine (o₁.kept _).trans ((k₂.mono fun r hr => ?_).trans (k'.monoL fun w hw => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [Lay.RL, List.map_append, List.map_cons, List.mem_append, List.mem_cons, List.mem_map]
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · simp only [List.mem_append, List.mem_map, List.map_cons, List.mem_cons] at hw ⊢
        rcases hw with hw | ⟨q, hq, rfl⟩
        · exact .inl hw
        · exact .inr (.inr ⟨q, hq, rfl⟩)
    · rw [← out₂]
      exact Lay.bytes_keep hL k'.frame (sepAll_append hp.sep (sepAll_map pw.1)) (by have := hp.lenc; omega)

/-! ## The whole hash -/

theorem zeroState_ok {L : Lay} {s : State} (hc : Ctx L s) :
    WP isa (.block (zeroState .r31)) s fun s' =>
      Kept (L.RL [(0, 0, 200)]) s s' ∧ stateAt s'.mem (L.ptr 0) = Spec.Sha3.zero := by
  rw [zeroState, WP.block_append_iff]
  have hli : WP isa (.block [.li .r0 0]) s fun s₁ => s₁ = s.write .r0 (BitVec.ofNat 64 0) := by
    prun []
  refine WP.mono hli fun s₁ e₁ => ?_
  subst e₁
  have e31 : (s.write .r0 (BitVec.ofNat 64 0)).gpr .r31 = L.ptr 0 := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), hc.r31]
  refine WP.mono (Sample.zeroLanes_ok .r31 (by decide) (s₁ := s.write .r0 (BitVec.ofNat 64 0))
    (by rw [RegUpd.gpr_write_self]; rfl) fun k hk => by
      rw [e31, RegUpd.wr_write]
      exact hc.cs (o := 8 * k) (l := 8) (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e31] at hf hz
  refine ⟨⟨fun r hr => ?_, by rw [h₂.sp, RegUpd.sp_write], by rw [h₂.rd, RegUpd.rd_write],
    by rw [h₂.wr, RegUpd.wr_write], ?_⟩, Sample.stateAt_zero hz⟩
  · rw [h₂.gpr]
    exact RegUpd.gpr_write_of_ne _ _ fun e => (pres_ne hr).1 e
  · rw [RegUpd.mem_write] at hf
    show Frame [L.R 0 0 200] s.mem s₂.mem
    rw [← Lay.R_zero]; exact hf

theorem sfx8 {sfx : Nat} (h : sfx < 256) : (BitVec.ofNat 64 sfx).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sfx < 2 ^ 64)]

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
  refine WP.seq (WP.mono (pargs_ok (rate_imm hrate) (by omega : sfx < 32768))
    fun s₃ ⟨o₃, g3, g4, g5, g6, g7⟩ => ?_)
  have hc₃ := hc₂.only o₃
  rw [hc₂.r31] at g3 g7
  have hP : PadArgs s₃ (L.ptr 0) (L.ptr 0 + BitVec.ofNat 64 200) rate (s₂.gpr .r3).toNat :=
    padArgs_of hrate hc₃ (by rw [show (s₂.gpr .r3).toNat = Pos false s₂ from rfl, p₂]; exact Nat.mod_lt _ rpos)
      g3 g4 (by rw [g5, BitVec.ofNat_toNat, BitVec.setWidth_eq]) g7
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

end VG.Proof.MlKem.PPC64LE
