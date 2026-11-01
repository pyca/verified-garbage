module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.RISCV64.Calls
public import VerifiedGarbage.Proof.MlKem.RISCV64.KemLay
public import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: sampling with `PRF` and `SamplePolyCBD`

As on PPC64LE (`Proof/MlKem/PPC64LE/Prf.lean`). `K.prfLoop withNtt N₀ N₁`
writes `SamplePolyCBD₂(PRF₂(σ, N))` (its NTT if `withNtt`) to polynomial
`k + N` for `N₀ ≤ N < N₁` (`prfLoop_ok`), with `σ` at offset 952 of
`scratch`, and changes only the regions of `prfW`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom rates)

/-! ## What changes, but for some callee-saved registers -/

/-- `s'` differs from `s` only in memory within `rs`, in registers that are
not callee-saved, and in the callee-saved registers `xs`. -/
structure KeptX (xs : List Reg) (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ∉ xs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.x {rs : List Region} {s s' : State} (h : Kept rs s s') (xs : List Reg) : KeptX xs rs s s' :=
  ⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.trans {xs : List Reg} {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : KeptX xs rs s₁ s₂)
    (h₂ : KeptX xs rs s₂ s₃) : KeptX xs rs s₁ s₃ :=
  ⟨fun r hr hx => by rw [h₂.cs r hr hx, h₁.cs r hr hx], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem KeptX.sub {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem KeptX.mono {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

theorem KeptX.weaken {xs ys : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hx : ∀ x ∈ xs, x ∈ ys) : KeptX ys rs s s' :=
  ⟨fun r hr hy => h.cs r hr fun hm => hy (hx r hm), h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.monoL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s s' : State}
    (h : KeptX xs (L.RL W) s s') (hs : ∀ w ∈ W, w ∈ W') : KeptX xs (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

theorem Only.x {s s' : State} (h : Only s s') (xs : List Reg) (rs : List Region) : KeptX xs rs s s' :=
  (h.kept rs).x xs

theorem KeptX.ctx {L : Lay} {xs : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (h11 : Reg.s11 ∉ xs) (hc : Ctx L s) : Ctx L s' :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .s11 (by decide) h11, hc.s11], by rw [h.sp]; exact hc.sp1168,
    by rw [h.sp]; exact hc.al, hc.al0, by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

/-- A region of `scratch` apart from the region `w` of `scratch` or of the stack. -/
def sep0 (o l : Nat) (w : Nat × Nat × Nat) : Bool :=
  (w.1 == 0 && decide (w.2.1 + w.2.2 ≤ 32768) && (decide (o + l ≤ w.2.1) || decide (w.2.1 + w.2.2 ≤ o))) ||
    (w.1 == 1 && decide (w.2.1 + w.2.2 ≤ 1168))

theorem Ctx.sepAll0 {L : Lay} {s : State} (hc : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768)
    {W : List (Nat × Nat × Nat)} (h : W.all (sep0 o l) = true) : sepAll L.sizes (0, o, l) W = true := by
  refine List.all_eq_true.mpr fun w hw => ?_
  have h' := List.all_eq_true.mp h w hw
  obtain ⟨i, a, b⟩ := w
  simp only [sep0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  rcases h' with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
  · subst h1; exact hc.sep00 hl h2 h3
  · subst h1; exact hc.sep01 hl h2

/-- A part of a buffer inside a bigger one. -/
theorem Lay.R_sub_R (L : Lay) {i a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l') :
    Region.Sub (L.R i a l) (L.R i b l') :=
  Offset.sub _ h₁ h₂

/-- A part of `scratch` inside a bigger one. -/
theorem Ctx.sub0 {L : Lay} {s : State} (_hc : Ctx L s) {a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l')
    (_h₃ : b + l' ≤ 32768) : Region.Sub (L.R 0 a l) (L.R 0 b l') :=
  Lay.R_sub_R L h₁ h₂

/-- `w` inside `w'`, a region of `scratch` or of the stack. -/
def subB0 (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2) &&
    ((w'.1 == 0 && decide (w'.2.1 + w'.2.2 ≤ 32768)) || (w'.1 == 1 && decide (w'.2.1 + w'.2.2 ≤ 1168)))

theorem Ctx.subL {L : Lay} {s : State} (_hc : Ctx L s) {W W' : List (Nat × Nat × Nat)}
    (h : W.all (fun w => W'.any (subB0 w)) = true) : ∀ r ∈ L.RL W, ∃ r' ∈ L.RL W', Region.Sub r r' := by
  intro r hr
  obtain ⟨⟨i, a, l⟩, hw, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨i', b, l'⟩, hw', hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h _ hw)
  simp only [subB0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨e, h₁⟩, h₂⟩, -⟩ := hs
  subst e
  exact ⟨L.R i b l', List.mem_map.mpr ⟨_, hw', rfl⟩, Lay.R_sub_R L h₁ h₂⟩

theorem KeptX.subL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s₀ s s' : State} (hc : Ctx L s₀)
    (h : KeptX xs (L.RL W) s s') (hb : W.all (fun w => W'.any (subB0 w)) = true) : KeptX xs (L.RL W') s s' :=
  h.sub (hc.subL hb)

/-! ## Offsets -/

/-- `w` inside `w'`. -/
def inB (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2)

/-- Arithmetic on the offsets in `scratch`, with the bounds on `k` of the
`KemLay.WF` in the context, if any. -/
tactic_template "offs" : tactic => `(tactic| (
                   (try have := (‹KemLay.WF _›).k1)
                   (try have := (‹KemLay.WF _›).k4)
                   (try have := (‹KemLay.WF _›).du)
                   (try have := (‹KemLay.WF _›).dv)
                   (try simp only [oPoly, oPrf, oSeed, oSigma, KemLay.jAcc, KemLay.jTmp, KemLay.jAhat, KemLay.jSample,
                     KemLay.jNtt, KemLay.jCt, oK, oKbar, oMsg, oHek, oSave, oG, oCin, KemLay.ekLen, KemLay.ctLen,
                     KemLay.uLen, KemLay.vLen])
                   omega_arith))

/-- Decides a fact about offsets and regions: by evaluation, or, for one that
depends on the parameter set (of the `KemLay.WF` in the context), by `omega`
on the offsets. -/
tactic_template "kdecide" : tactic => `(tactic| first
                   | decide
                   | (
                   (try have := (‹KemLay.WF _›).k1)
                   (try have := (‹KemLay.WF _›).k4)
                   (try have := (‹KemLay.WF _›).du)
                   (try have := (‹KemLay.WF _›).dv)
                   (try simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.all_append, List.any_append, sep0,
                     subB0, inB, sepB, sepAll, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
                     oPoly, oPrf, oSeed, oSigma, KemLay.jAcc, KemLay.jTmp, KemLay.jAhat, KemLay.jSample, KemLay.jNtt,
                     KemLay.jCt, oK, oKbar, oMsg, oHek, oSave, oG, oCin, KemLay.ekLen, KemLay.ctLen, KemLay.uLen,
                     KemLay.vLen, KemLay.dkLen, Bool.and_true, Bool.or_false,
                     Bool.true_and, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
                     decide_eq_true_eq, true_and, and_true, not_true_eq_false, not_false_eq_true, false_or, or_false, true_or,
                     or_true])
                   omega_arith))

theorem setWidth8_ofNat {N : Nat} (h : N < 2 ^ 64) : (BitVec.ofNat 64 N).setWidth 8 = BitVec.ofNat 8 N := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `a - b` is nonzero exactly when `a ≠ b`. -/
theorem ofNat_sub_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => hne (by
      have := BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
      rw [e] at this; simpa using this.symm)
    rw [bne_iff_ne.mpr this]; simp [h]

/-! ## Counters -/

theorem count_ok {s : State} {c : Reg} {n k : Nat} (hc : c ∈ preserved) (hk : k + 1 < 2 ^ 64)
    (hn : n ≤ 2048) (h : s.gpr c = BitVec.ofNat 64 k) :
    WP isa (.block (count c n)) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 64 (k + 1) ∧ (s'.gpr .t0 != 0) = decide (k + 1 ≠ n) := by
  obtain ⟨n0, -⟩ := pres_ne hc
  rw [← List.append_nil (count c n)]
  refine wp_count hn n0 fun s' g gt go m rd wr sp => WP.block_nil ⟨⟨fun r hr hx => ?_, sp, rd, wr, ?_⟩, ?_, ?_⟩
  · exact go r (fun e => hx (by rw [e]; exact List.mem_singleton_self _)) (pres_ne hr).1
  · rw [m]; exact Frame.refl _ _
  · rw [g, h, ← BitVec.ofNat_add]
  · rw [gt, h, ← BitVec.ofNat_add]; exact ofNat_sub_ne hk (by omega_arith)

/-! ## One `PRF` -/

/-- Polynomial `k + N`: `SamplePolyCBD₂(PRF₂(σ, N))`, or its NTT. -/
def prfOut (withNtt : Bool) (σ : List Byte) (N : Nat) : Poly :=
  if withNtt then ntt (VG.Proof.MlKem.cbd σ N) else VG.Proof.MlKem.cbd σ N

/-- What one `PRF` changes. -/
abbrev prfW (K : KemLay) (N : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (1, 0, 1168), (0, 984, 1), (0, 1056, 128), (0, oPoly (K.k + N), 1024),
    (0, oPoly K.jNtt, 1024)]

theorem bytes_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem sb6_ok {L : Lay} {s : State} (hc : Ctx L s) {N : Nat} (hN : N < 2 ^ 64)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 N) :
    WP isa (.block [.store .b .s6 .s11 (oSigma + 32)]) s fun s₁ =>
      KeptX [] (L.RL [(0, 984, 1)]) s s₁ ∧ s₁.mem = s.mem.writeW (L.A 0 984) (BitVec.ofNat 8 N) := by
  have i984 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 984) 1 :=
    hc.cs (o := 984) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine wp_sb (a := L.A 0 984) (by decide) (by rw [hc.s11]) i984 fun s₁ m₁ => WP.block_nil ⟨⟨fun r _ _ => by
    rw [m₁.gpr], m₁.sp, m₁.rd, m₁.wr, ?_⟩, by rw [m₁.mem, h6, setWidth8_ofNat hN]⟩
  rw [m₁.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem rate136 : 136 ∈ rates := by decide

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem cbdArgs_ok {s : State} {P : BitVec 64} {N : Nat} (hN : N ≤ 2 * K.k) (h11 : s.gpr .s11 = P)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 N) :
    WP isa (.block (.addi .a0 .s11 oPrf :: slotAt .a1 .s6 K.k)) s fun s' => Only s s' ∧
      s'.gpr .a0 = P + BitVec.ofNat 64 oPrf ∧
      s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly (K.k + N)) := by
  have k4 := hK.k4
  rw [← List.append_nil (slotAt .a1 .s6 K.k)]
  refine wp_addi (by decide) fun s₁ h₁ => wp_slotAt (i := N) (by omega_arith) (by omega_arith) (by decide)
    (by rw [h₁.other _ (by decide), h6]) fun s₂ h₂ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans (updOnly h₂ (by decide)), ?_, ?_⟩
  · rw [h₂.other _ (by decide), h₁.gpr, h11]
  · rw [h₂.gpr, h₁.other _ (by decide), h11]; unfold oPoly; congr 2; omega_arith

theorem nttArgs_ok {s : State} {P : BitVec 64} {N : Nat} (hN : N ≤ 2 * K.k) (h11 : s.gpr .s11 = P)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 N) :
    WP isa (.block (slotAt .a0 .s6 K.k ++ polyAddr .a1 K.jNtt)) s fun s' =>
      Only s s' ∧
      s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly (K.k + N)) ∧
      s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly K.jNtt) := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .a1 K.jNtt)]
  refine wp_slotAt (i := N) (by omega_arith) (by omega_arith) (by decide) h6 fun s₁ h₁ =>
    wp_polyAddr (by offs) (by decide) fun s₂ h₂ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans (updOnly h₂ (by decide)), ?_, ?_⟩
  · rw [h₂.other _ (by decide), h₁.gpr, h11]; unfold oPoly; congr 2; omega_arith
  · rw [h₂.gpr, h₁.other _ (by decide), h11]

theorem prfBody_ok {L : Lay} {s : State} (hc : Ctx L s) (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) (h6 : s.gpr .s6 = BitVec.ofNat 64 N) {σ : List Byte}
    (hσ : bytesAt s.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfBody withNtt N₁) s fun s' => KeptX [.s6] (L.RL (prfW K N)) s s' ∧
      s'.gpr .s6 = BitVec.ofNat 64 (N + 1) ∧ (s'.gpr .t0 != 0) = decide (N + 1 ≠ N₁) ∧
      PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := by
  have hL := hc.ok
  have k4 := hK.k4
  refine WP.seq (WP.mono (sb6_ok hc (by omega_arith) h6) fun s₁ ⟨k₁, m₁⟩ => ?_)
  have hc₁ := k₁.ctx (by decide) hc
  have g6₁ : s₁.gpr .s6 = BitVec.ofNat 64 N := by rw [k₁.cs .s6 (by decide) (by decide), h6]
  have bσ : bytesAt s₁.mem (L.A 0 oSigma) 33 = σ ++ [BitVec.ofNat 8 N] := by
    show bytesAt s₁.mem (L.ptr 0 + BitVec.ofNat 64 952) (32 + 1) = _
    rw [bytesAt_add, bytes_one, ptr_add]
    congr 1
    · rw [← hσ]
      exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
    · rw [m₁, writeW8_apply, ite_eq_left rfl]
  have hin : ∀ p ∈ [(⟨.s11, oSigma, 33⟩ : Piece)], PieceOk L (fun _ => 0) s₁ false p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨by decide, hc₁.s11, by decide, by decide, by decide, hc₁.sepAll0 (by decide) (by decide),
      mem_rd_wr hc₁.cw⟩
  have hout : ∀ p ∈ [(⟨.s11, oPrf, 128⟩ : Piece)], PieceOk L (fun _ => 0) s₁ true p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨by decide, hc₁.s11, by decide, by decide, by decide, hc₁.sepAll0 (by decide) (by decide), hc₁.cw⟩
  refine WP.seq (WP.mono (hash_ok (idx := fun _ => 0) rate136 (by decide) hc₁
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have hc₂ := hc₁.kept k₂
  have g6₂ : s₂.gpr .s6 = BitVec.ofNat 64 N := by rw [k₂.cs .s6 (by decide), g6₁]
  have prfB : bytesAt s₂.mem (L.A 0 oPrf) 128 = prf 2 σ (BitVec.ofNat 8 N) := by
    have := o₂.1
    simp only [Lay.pb, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    rw [bσ] at this
    rw [this, VG.Proof.MlKem.prf_eq]; rfl
  refine WP.seq (WP.mono (cbdArgs_ok hK (by omega_arith) hc₂.s11 g6₂) fun s₃ ⟨o₃, g3, g4⟩ => ?_)
  have hc₃ := hc₂.only o₃
  refine WP.seq (cbd2L hL g3 g4 (hc.sep00 (by offs) (by offs) (by offs))
    (mem_rd_wr hc₃.cw) hc₃.cw (hc.alP _) fun s₄ k₄ p₄ => ?_)
  rw [o₃.mem, prfB] at p₄
  have hc₄ := hc₃.kept k₄
  have g6₄ : s₄.gpr .s6 = BitVec.ofNat 64 N := by
    rw [k₄.cs .s6 (by decide), o₃.cs .s6 (by decide), g6₂]
  have fin : ∀ s₅, KeptX [.s6] (L.RL [(0, oPoly (K.k + N), 1024), (0, oPoly K.jNtt, 1024)]) s₄ s₅ →
      s₅.gpr .s6 = BitVec.ofNat 64 N → PolyIs s₅.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) →
      WP isa (.block (count .s6 N₁)) s₅ fun s' => KeptX [.s6] (L.RL (prfW K N)) s s' ∧
        s'.gpr .s6 = BitVec.ofNat 64 (N + 1) ∧ (s'.gpr .t0 != 0) = decide (N + 1 ≠ N₁) ∧
        PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := fun s₅ k₅ g6₅ p₅ =>
    WP.mono (count_ok (by decide) (by omega_arith) (by omega_arith) g6₅) fun s' ⟨k', g', z'⟩ => ⟨by
      exact ((k₁.weaken (by simp)).monoL (W' := prfW K N) (by simp)).trans (((k₂.x _).monoL (by simp)).trans
        ((o₃.x _ _).trans (((k₄.x _).monoL (by simp)).trans ((k₅.monoL (by simp)).trans
          (k'.mono (fun _ h => absurd h List.not_mem_nil)))))),
      g', z', polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₅⟩
  cases withNtt
  · refine WP.seq (WP.block_nil ?_)
    exact fin s₄ ((Kept.refl _ _).x _) g6₄ p₄
  · refine WP.seq (WP.seq (WP.mono (nttArgs_ok hK (by omega_arith) hc₄.s11 g6₄) fun s₅ ⟨o₅, g3', g4'⟩ => ?_))
    have hc₅ := hc₄.only o₅
    refine nttL hL g3' g4' (hc.sep00 (by offs) (by offs) (by offs)) hc₅.cw hc₅.cw (by rw [o₅.mem]; exact p₄)
      (hc.alP _) (hc.alP _) fun s₆ k₆ p₆ => fin s₆ (((o₅.kept _).trans k₆).x _) ?_ p₆
    rw [k₆.cs .s6 (by decide), o₅.cs .s6 (by decide), g6₄]

end

/-! ## The loop -/

/-- What the loop changes: the regions of `prfW`, with all its polynomials. -/
abbrev prfLW (K : KemLay) (N₀ N₁ : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (1, 0, 1168), (0, 984, 1), (0, 1056, 128), (0, oPoly (K.k + N₀), 1024 * (N₁ - N₀)),
    (0, oPoly K.jNtt, 1024)]

structure PrfInv (K : KemLay) (L : Lay) (withNtt : Bool) (σ : List Byte) (N₀ N₁ : Nat) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  kx : KeptX [.s6] (L.RL (prfLW K N₀ N₁)) s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 (N₀ + t)
  sig : bytesAt s.mem (L.A 0 oSigma) 32 = σ
  slots : ∀ N, N₀ ≤ N → N < N₀ + t → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N)

theorem prfW_sig {K : KemLay} (hK : K.WF) : ∀ N < 2 * K.k + 1, (prfW K N).all (sep0 oSigma 32) = true := by
  have := hK.k4
  intro N hN
  simp only [prfW, List.all_cons, List.all_nil, sep0, oPoly, KemLay.jNtt, oSigma, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega_arith

theorem prfW_slot {K : KemLay} (hK : K.WF) {N N' : Nat} (hN : N < 2 * K.k + 1) (hN' : N' < 2 * K.k + 1)
    (h : N' ≠ N) : (prfW K N).all (sep0 (oPoly (K.k + N')) 1024) = true := by
  have := hK.k4
  simp only [prfW, List.all_cons, List.all_nil, sep0, oPoly, KemLay.jNtt, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega_arith

theorem li6_ok {s : State} {N : Nat} (he : N < 2048) :
    WP isa (.block [.li .s6 N]) s fun s' =>
      KeptX [.s6] [] s s' ∧ s'.gpr .s6 = BitVec.ofNat 64 N ∧ s'.mem = s.mem :=
  wp_li he fun s' h => WP.block_nil ⟨⟨fun r _ hx => h.other r fun e => hx (by rw [e]; exact List.mem_singleton_self _),
    h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩, h.gpr, h.mem⟩

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem prfStep_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat}
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} {t : Nat} (ht : t < N₁ - N₀) {s : State}
    (h : PrfInv K L withNtt σ N₀ N₁ s₀ t s) :
    WP isa (K.prfBody withNtt N₁) s fun s' =>
      PrfInv K L withNtt σ N₀ N₁ s₀ (t + 1) s' ∧ (s'.gpr .t0 != 0) = decide (t + 1 ≠ N₁ - N₀) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hcs := h.kx.ctx (by decide) hc
  refine WP.mono (prfBody_ok hK hcs withNtt (N := N₀ + t) (by omega_arith) hN₁ h.s6 h.sig) fun s' ⟨k', g', z', p'⟩ =>
    ⟨⟨h.kx.trans (k'.sub fun r hr => ?_), by rw [g', Nat.add_assoc], ?_, fun N h1 h2 => ?_⟩, ?_⟩
  · simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.R 0 0 200, by simp, fun _ h => h⟩
    · exact ⟨L.R 1 0 1168, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 984 1, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 1056 128, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 (oPoly (K.k + N₀)) (1024 * (N₁ - N₀)), by simp, hc.sub0 (by offs) (by offs) (by offs)⟩
    · exact ⟨L.R 0 (oPoly K.jNtt) 1024, by simp, fun _ h => h⟩
  · rw [← h.sig]
    exact Lay.bytes_keep hL k'.frame (hc.sepAll0 (by decide) (prfW_sig hK _ (by omega_arith))) (by decide)
  · by_cases e : N = N₀ + t
    · subst e; exact p'
    · exact Lay.polyIs_keep hL k'.frame (hc.sepAll0 (by offs) (prfW_slot hK (by omega_arith) (by omega_arith) e))
        (h.slots N h1 (by omega_arith))
  · rw [z']; simp only [decide_eq_decide]; omega_arith

theorem prfLoop_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} (hσ : bytesAt s₀.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfLoop withNtt N₀ N₁) s₀ fun s => KeptX [.s6] (L.RL (prfLW K N₀ N₁)) s₀ s ∧
      ∀ N, N₀ ≤ N → N < N₁ → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := by
  have k4 := hK.k4
  refine WP.seq (WP.mono (li6_ok (by omega_arith)) fun s₁ ⟨k₁, g₁, m₁⟩ => ?_)
  exact wp_loop_nz (PrfInv K L withNtt σ N₀ N₁ s₀) (N := N₁ - N₀) (by omega_arith)
    (fun t ht s h => prfStep_ok hK hc withNtt hN₁ ht h)
    (fun s h => ⟨h.kx, fun N h1 h2 => h.slots N h1 (by omega_arith)⟩)
    ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ,
      fun N h1 h2 => absurd h2 (by omega_arith)⟩

end

end VG.Proof.MlKem.RISCV64
