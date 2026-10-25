module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.SelectX
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The odd window method on x86-64: the selection woven into the addition

What the selection of digit `j - 1`'s entry keeps between the addition's
field operations (`SelP`): the broadcasts of its magnitude `a` and of one,
the counter and the accumulators after entries `1 … e` (`SelS`: 32 bytes at
a time with AVX2, `AccY`, else 16, `AccX`), of the table at `rdi + tbl` as
in the memory `mem` it started from, whose bytes the state still holds. The
field operations keep it (`SelP.stab`), writing neither the vector registers
nor the table; each part of the selection advances it (`selChunkO_ok`),
writing no register but `rdx` (`SideKeepF`); `selSetP_ok` starts it and
`storeP_ok` stores the accumulators to `T`, which then holds entry `a`
(`jselOut`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable {K : JacWinCfg} {size : Nat}

/-- The table's address. -/
abbrev tblX (K : JacWinCfg) (base : Addr) : Addr := base + BitVec.ofNat 64 K.tbl

/-- The selection's registers after entries `1 … e` for the magnitude `a`,
the table as in `mem`. -/
def SelS (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  if K.avx2 then
    (∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) ∧
    (∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) ∧
    (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (e + 1))) ∧
    AccY t mem (tblX K base) K.st a e K.np32 (qY K.np16)
  else
    t.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) ∧ t.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) ∧
    t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (e + 1)) ∧ AccX t mem (tblX K base) K.st a e K.np16

/-- The selection between the addition's operations: `SelS`, the table's
bytes as in `mem`, in the regions, and `rdi` the working space. -/
structure SelP (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop where
  ha : a ≤ 16
  sel : SelS K base mem a e t
  tblm : ∀ b < 16 * K.st, t.mem (tblX K base + BitVec.ofNat 64 b) = mem (tblX K base + BitVec.ofNat 64 b)
  reg : InRegions (t.rd ++ t.wr) (tblX K base) (16 * K.st)
  rdi : t.gpr .rdi = base

theorem SelS.of_vec {base : Addr} {mem : Mem} {a e : Nat} {t t' : State} (h : SelS K base mem a e t)
    (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) : SelS K base mem a e t' := by
  unfold SelS at h ⊢
  have hl := lane_congr hx hy
  split
  · next hv =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h
    exact ⟨fun l hl' => by rw [hl]; exact h.1 l hl', fun l hl' => by rw [hl]; exact h.2.1 l hl',
      fun l hl' => by rw [hl]; exact h.2.2.1 l hl', fun c hc l hl' => by rw [hl]; exact h.2.2.2 c hc l hl'⟩
  · next hv =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h
    exact ⟨by rw [hx]; exact h.1, by rw [hx]; exact h.2.1, by rw [hx]; exact h.2.2.1,
      fun c hc => by rw [hx]; exact h.2.2.2 c hc⟩

/-- The table's entries: `16 st = 80 (8 n)` bytes. -/
theorem st16 (K : JacWinCfg) : 16 * K.st = 80 * (8 * K.M.n) := by
  unfold JacWinCfg.st; omega_arith

/-- A range apart from the table's 80 slots is apart from each of its bytes. -/
theorem tbl_byte_apart (hL : JacWinLay K size) {w : Nat × Nat}
    (hw : ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) {b : Nat} (hb : b < 16 * K.st) :
    K.tbl + b + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.tbl + b := by
  have h0 := hL.n0
  rw [st16] at hb
  have hi : b / (8 * K.M.n) < 80 := (Nat.div_lt_iff_lt_mul (by omega_arith)).mpr (by rw [Nat.mul_comm]; omega_arith)
  have h1 := Nat.div_mul_le_self b (8 * K.M.n)
  have h2 := Nat.lt_div_mul_add (a := b) (show 0 < 8 * K.M.n by omega_arith)
  have := hw _ hi
  unfold jg at this
  rw [Nat.mul_comm (8 * K.M.n)] at this
  generalize b / (8 * K.M.n) * (8 * K.M.n) = q at h1 h2 this
  omega_arith

/-- Byte `b` of the table: `off base (tbl + b)`. -/
theorem tblX_off (K : JacWinCfg) (base : Addr) (b : Nat) :
    tblX K base + BitVec.ofNat 64 b = off base (K.tbl + b) := Offset.add_add base _ _

/-- The table's bytes survive a write that misses its slots. -/
theorem tblm_unch (hL : JacWinLay K size) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hU : Unch base W m m') (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    ∀ b < 16 * K.st, m' (tblX K base + BitVec.ofNat 64 b) = m (tblX K base + BitVec.ofNat 64 b) := by
  intro b hb
  have hg := hL.grid_le
  have := st16 K
  rw [tblX_off]
  exact hU.byte (fun w hw => tbl_byte_apart hL (hW w hw) hb) (by omega_arith)

/-- A slot but the grid's, and the temporary area, miss the table's slots. -/
theorem other_tbl_apart (hL : JacWinLay K size) {o : Nat} (ho : o ∈ jwOther K) :
    ∀ w ∈ [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hL.jg_apart (List.mem_append_right _ ho) (i := i) (by omega_arith)).symm
  · exact hL.lay.tmp _ (jg_mem (by omega_arith))

/-- A field operation writing a slot but the grid's keeps the selection
(`programBI_ok`'s `hstab`). -/
theorem SelP.stab (hL : JacWinLay K size) {base : Addr} {mem : Mem} {a e o : Nat} (ho : o ∈ jwOther K)
    (hn : base.toNat + size ≤ 2 ^ 64) {t t' : State} (h : SelP K base mem a e t)
    (hk : OpKeep K.M base o t t') (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) :
    SelP K base mem a e t' :=
  ⟨h.ha, h.sel.of_vec hx hy, fun b hb => by
    rw [tblm_unch hL hk.unch hn (other_tbl_apart hL ho) b hb]; exact h.tblm b hb,
    by rw [hk.rd, hk.wr]; exact h.reg, by rw [hk.gpr _ (rdi_not_clob _)]; exact h.rdi⟩

/-- `rdx = rdi + tbl`. -/
theorem tblRdx_ok (hL : JacWinLay K size) (s : State) {base : Addr} (hd : s.gpr .rdi = base) :
    WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]) s fun t =>
      t.gpr .rdx = tblX K base ∧ Keeps [.rdx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  have ht := hL.tbl31
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, imm32_sext ht, hd, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- An entry's pieces: ten for four words. -/
theorem np_four (hL : JacWinLay K size) (hn4 : K.M.n = 4) :
    K.np16 = 10 ∧ K.np32 = 5 ∧ K.st = 16 * K.np16 := by
  obtain ⟨-, hst, -⟩ := np16_eq hL
  unfold JacWinCfg.np32 JacWinCfg.np16 at *
  rw [hn4] at *
  exact ⟨rfl, rfl, hst⟩

theorem AccX.congr {t : State} {m m' : Mem} {X : Addr} {n H a e : Nat} (ha : a ≤ H)
    (h : ∀ b < 16 * n * H, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b))
    (hA : AccX t m X (16 * n) a e n) : AccX t m' X (16 * n) a e n :=
  fun c hc => by rw [hA c hc]; exact accVal_congr ha hc h

theorem chunkO_le (K : JacWinCfg) {i : Nat} (hi : i < K.nAddO) :
    K.chunkO i ≤ K.chunkO (i + 1) ∧ K.chunkO (i + 1) ≤ 16 := by
  unfold JacWinCfg.chunkO
  exact ⟨Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega_arith)),
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm K.nAddO]; exact Nat.mul_le_mul_left _ (by omega_arith))⟩

/-- A part of the selection (`programBI_ok`'s `hside`): entries `chunkO i + 1`
to `chunkO (i + 1)`. -/
theorem selChunkO_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} (i : Nat)
    (hi : i < K.nAddO) {t : State} (h : SelP K base mem a (K.chunkO i) t) :
    WP isa (.block (K.selChunkO i)) t fun t' => SelP K base mem a (K.chunkO (i + 1)) t' ∧
      ForwardField.SideKeepF t t' := by
  obtain ⟨hlo, hhi⟩ := chunkO_le K hi
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  unfold JacWinCfg.selChunkO
  split
  · next he => exact WP.block_nil ⟨by rw [he]; exact h, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (tblRdx_ok hL t h.rdi) fun t₁ ⟨x₁, k₁, xx₁, xy₁⟩ => ?_
  have hm₁ : t₁.mem = t.mem := k₁.2.1
  have hT : ∀ b < 16 * K.np16 * 16, mem (tblX K base + BitVec.ofNat 64 b) =
      t₁.mem (tblX K base + BitVec.ofNat 64 b) := fun b hb => by
    rw [hm₁]; exact (h.tblm b (by rw [hst]; omega_arith)).symm
  have hT' : ∀ b < 16 * K.np16 * 16, t₁.mem (tblX K base + BitVec.ofNat 64 b) =
      mem (tblX K base + BitVec.ofNat 64 b) := fun b hb => (hT b hb).symm
  have hreg : InRegions (t₁.rd ++ t₁.wr) (tblX K base) (16 * K.st) := by
    rw [k₁.2.2.1, k₁.2.2.2]; exact h.reg
  have hS₁ := h.sel.of_vec xx₁ xy₁
  have hdi : t₁.gpr .rdi = base := by rw [k₁.1 _ (by decide)]; exact h.rdi
  have side : ∀ {t' : State}, t'.mem = t₁.mem → t'.rd = t₁.rd → t'.wr = t₁.wr →
      (∀ r, r ≠ .rdx → t'.gpr r = t₁.gpr r) → ForwardField.SideKeepF t t' := fun hm hr hw hg =>
    ⟨fun r hr' => by rw [hg r hr', k₁.1 r (by simpa using hr')], by rw [hm, hm₁], by rw [hr, k₁.2.2.1],
      by rw [hw, k₁.2.2.2]⟩
  have hlo' : K.chunkO i + (K.chunkO (i + 1) - K.chunkO i) = K.chunkO (i + 1) := by omega_arith
  unfold SelS at hS₁
  unfold JacWinCfg.selEntryP
  cases hv : K.avx2
  · -- SSE2
    rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at hS₁
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b13, b12, b11, acc⟩ := hS₁
    refine WP.mono (selEntriesFromX_ok (X := tblX K base) (st := K.st) (np := K.np16) (lo := K.chunkO i)
      (by omega_arith) (by have := h.ha; omega_arith) (K.chunkO (i + 1) - K.chunkO i) (by omega_arith) t₁ x₁ b13 b12 b11
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ (by omega_arith)
        have := Nat.mul_le_mul_left K.st (show K.chunkO i + e + 1 ≤ 16 by omega_arith)
        rw [Nat.mul_succ] at this
        omega_arith)
      (by rw [hst] at acc ⊢; exact AccX.congr (H := 16) h.ha hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < K.np16, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega_arith)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < K.np16, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega_arith)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelS
    rw [hv, ite_eq_right_of_eq_false _ _ (by simp)]
    refine ⟨by rw [k'.xmm _ n13]; exact b13, by rw [k'.xmm _ n12]; exact b12, by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    rw [hst] at a' ⊢
    exact AccX.congr (H := 16) h.ha (fun b hb => (h.tblm b (by rw [hst]; omega_arith))) a'
  · -- AVX2
    rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at hS₁
    simp only [↓reduceIte]
    obtain ⟨b13, b12, b14, acc⟩ := hS₁
    have hq : ∀ c, qY K.np16 c + 2 ≤ K.np16 := fun c => qY_le c (by omega_arith)
    have hnp : K.np32 = (K.np16 + 1) / 2 := rfl
    refine WP.mono (selEntriesFromY_ok (X := tblX K base) (st := K.st) (np := K.np32) (q := qY K.np16)
      (lo := K.chunkO i) (by omega_arith) (by have := h.ha; omega_arith) (K.chunkO (i + 1) - K.chunkO i) (by omega_arith) t₁ x₁
      b13 b12 b14
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ (by omega_arith)
        have := Nat.mul_le_mul_left K.st (show K.chunkO i + e + 1 ≤ 16 by omega_arith)
        rw [Nat.mul_succ] at this
        have := hq c
        omega_arith)
      (by rw [hst, hnp] at acc ⊢; exact AccY.congr (H := 16) h.ha (by omega_arith) hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < K.np32, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega_arith)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < K.np32, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega_arith)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelS
    rw [hv, ite_eq_left_of_eq_true _ _ (by simp)]
    refine ⟨fun l hl => by rw [k'.lane _ n13 l]; exact b13 l hl, fun l hl => by rw [k'.lane _ n12 l]; exact b12 l hl,
      by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    rw [hst, hnp] at a' ⊢
    exact AccY.congr (H := 16) h.ha (by omega_arith) (fun b hb => (h.tblm b (by rw [hst]; omega_arith))) a'

/-- The selection set up for the magnitude `r8 = a ≤ 16`, through `rcx`: no
entry kept yet, of any table. -/
theorem selSetP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (s : State) {base : Addr} (mem : Mem) {a : Nat}
    (ha : a ≤ 16) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block K.selSetP) s fun t => SelS K base mem a 0 t ∧ Keeps [.rcx] s t := by
  obtain ⟨h10, h5, -⟩ := np_four hL hn4
  unfold JacWinCfg.selSetP SelS
  cases hv : K.avx2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetX_ok s (by omega_arith) h8) fun s₁ ⟨b13, b12, b11, k₁⟩ => ?_
    refine WP.mono (clearAcc_ok K.np16 (by omega_arith) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm11 ∨ r = .xmm12 ∨ r = .xmm13 → ¬ ∃ c < K.np16, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨n11, n12, n13, -, -⟩ := selAcc_neX c (by omega_arith)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨by rw [k.xmm _ (nacc _ (by simp))]; exact b13, by rw [k.xmm _ (nacc _ (by simp))]; exact b12,
      by rw [k.xmm _ (nacc _ (by simp))]; exact b11, fun c hc => by
        rw [z c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩
  · simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetY_ok s (by omega_arith) h8) fun s₁ ⟨b13, b12, b14, k₁⟩ => ?_
    refine WP.mono (clearAccY_ok K.np32 (by omega_arith) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm12 ∨ r = .xmm13 ∨ r = .xmm14 → ¬ ∃ c < K.np32, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨-, n12, n13, n14, -⟩ := selAcc_neY c (by omega_arith)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b13 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b12 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b14 l hl, fun c hc l hl => by
        rw [z c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩

/-- The accumulators after the sixteen entries stored to `T`. -/
theorem storeP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} {t : State}
    (hs : Scr t base size) (h : SelS K base mem a 16 t) :
    WP isa (.block K.storeP) t fun t' =>
      (∀ c < K.np16, t'.mem.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.np16) t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  have hT : K.T + 16 * K.np16 ≤ size := by
    have := hL.grid_le; rw [hL.T80]; unfold jg; rw [h10, hn4] at *; omega_arith
  unfold JacWinCfg.storeP
  unfold SelS at h
  cases hv : K.avx2
  · rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeAcc_ok K.np16 t hs hT) fun t' ⟨a', O', g', r', w', _⟩ =>
      ⟨fun c hc => by rw [a' c hc]; exact h.2.2.2 c hc, O', g', r', w'⟩
  · rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at h
    simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (storeAccY_ok (o := K.T) (n := K.np16) (q := qY K.np16)
      (V := accVal mem (tblX K base) K.st (16 * ·) a 16) hT K.np32 t hs (fun c _ => qY_le c (by omega_arith))
      (fun c hc l hl => h.2.2.2 c hc l hl)) fun t₁ ⟨a₁, O₁, g₁, r₁, w₁, _⟩ => ?_
    refine WP.mono (vzeroupper_ok t₁) fun t' ⟨m', g', r', w'⟩ =>
      ⟨fun j hj => ?_, by rw [m']; exact O₁, by rw [g', g₁], by rw [r', r₁], by rw [w', w₁]⟩
    obtain ⟨c, hc, l, hl, e⟩ := qY_cover (n := K.np16) (by omega_arith) hj
    have := a₁ c (by unfold JacWinCfg.np32; exact hc) l hl
    rw [e] at this
    rw [m']
    exact this

/-- `T`'s five coordinates after `storeP_ok`: entry `a`'s, as in `mem`. -/
theorem jselOut (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem mem' : Mem} {a : Nat}
    (ha : 1 ≤ a ∧ a ≤ 16)
    (h : ∀ c < K.np16, mem'.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) :
    ∀ c < 5, wordsVal mem' base (jg K (80 + c)) K.M.n = wordsVal mem base (jg K (5 * (a - 1) + c)) K.M.n := by
  obtain ⟨h10, -, hst⟩ := np_four hL hn4
  intro c hc
  rw [hst] at h
  have hw := accVal_word (mem := mem) (mem' := mem') (base := base) (n := K.np16) (o := K.T) h
  have hX : ∀ d, word mem (tblX K base) d = word mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  have h2n : 2 * K.np16 = 5 * K.M.n := by rw [h10, hn4]
  have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 5 by omega_arith)
  rw [Nat.mul_succ] at hcn
  have eT : ∀ i, jg K (80 + c) + 8 * i = K.T + 8 * (K.M.n * c + i) := fun i => by
    rw [hL.T80]; unfold jg; rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc 8 K.M.n c]; omega_arith
  refine wordsVal_congr₂ _ _ _ fun i hi => ?_
  have e := hw (K.M.n * c + i) (by omega_arith)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ha), hX] at e
  rw [eT, e, ← hst]
  congr 1; unfold jg JacWinCfg.st
  rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
    rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
    Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c]
  omega_arith

end VG.Proof.Weierstrass.X86_64
