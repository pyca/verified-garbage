module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.SelectX
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Weierstrass.X86_64.SelWeave
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# x86-64: a table's selection in parts, woven among other code

What the selection of an entry's first `np` 16-byte pieces, of the sixteen
entries `st` bytes apart at `rdi + tbl`, keeps between its parts
(`SelW`): the broadcasts of the magnitude `a` and of one, the counter and
the accumulators after entries `1 … e` (`SelSW`: 32 bytes at a time with
AVX2, `AccY`, else 16, `AccX`), of the table as in the memory `mem` it
started from, whose bytes the state still holds. Code between the parts
keeps it if it writes neither the vector registers nor the table
(`SelW.stab`); each part advances it (`selChunkW_ok`), writing no register
but `rdx` (`SideKeepF`); `selSetW_ok` starts it and `storeW_ok` stores the
accumulators.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The selection's registers after entries `1 … e` for the magnitude `a`,
of the table at `X` as in `mem`, entries `st` bytes apart, `np` pieces. -/
def SelSW (avx2 : Bool) (X : Addr) (st np : Nat) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  if avx2 then
    (∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) ∧
    (∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) ∧
    (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (e + 1))) ∧
    AccY t mem X st a e ((np + 1) / 2) (qY np)
  else
    t.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) ∧ t.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) ∧
    t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (e + 1)) ∧ AccX t mem X st a e np

/-- The selection between the parts: `SelSW`, the table's sixteen entries at
`rdi + tbl` as in `mem`, in the regions, and `rdi` the working space. -/
structure SelW (avx2 : Bool) (tbl st np : Nat) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop where
  ha : a ≤ 16
  sel : SelSW avx2 (base + BitVec.ofNat 64 tbl) st np mem a e t
  tblm : ∀ b < 16 * st, t.mem (base + BitVec.ofNat 64 tbl + BitVec.ofNat 64 b) =
    mem (base + BitVec.ofNat 64 tbl + BitVec.ofNat 64 b)
  reg : InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 tbl) (16 * st)
  rdi : t.gpr .rdi = base

theorem SelSW.of_vec {avx2 : Bool} {X : Addr} {st np : Nat} {mem : Mem} {a e : Nat} {t t' : State}
    (h : SelSW avx2 X st np mem a e t) (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) :
    SelSW avx2 X st np mem a e t' := by
  unfold SelSW at h ⊢
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

/-- What a selection's reads of piece `i < np` of entry `a ≤ 16` find depends
only on the table's bytes. -/
theorem accValS_congr {m m' : Mem} {X : Addr} {st np a e i : Nat} (hst : 16 * np ≤ st) (ha : a ≤ 16)
    (hi : i < np) (h : ∀ b < 16 * st, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b)) :
    accVal m X st (16 * ·) a e i = accVal m' X st (16 * ·) a e i := by
  unfold accVal
  split
  · next h1 =>
    have h2 := Nat.mul_le_mul_left st (show a - 1 + 1 ≤ 16 by omega)
    rw [Nat.mul_succ] at h2
    dsimp only
    exact Mem.readW_congr fun b hb => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h _ (by rw [Nat.mul_comm 16 st]; omega)
  · rfl

theorem AccX.congrS {t : State} {m m' : Mem} {X : Addr} {st np a e : Nat} (hst : 16 * np ≤ st) (ha : a ≤ 16)
    (h : ∀ b < 16 * st, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b))
    (hA : AccX t m X st a e np) : AccX t m' X st a e np :=
  fun c hc => by rw [hA c hc]; exact accValS_congr hst ha hc h

theorem AccY.congrS {t : State} {m m' : Mem} {X : Addr} {st np a e : Nat} (hst : 16 * np ≤ st) (h2 : 2 ≤ np)
    (ha : a ≤ 16) (h : ∀ b < 16 * st, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b))
    (hA : AccY t m X st a e ((np + 1) / 2) (qY np)) : AccY t m' X st a e ((np + 1) / 2) (qY np) :=
  fun c hc l hl => by
    rw [hA c hc l hl]
    exact accValS_congr hst ha (by have := qY_le c h2; omega) h

/-- Code that writes only outside the table, and keeps the vector registers,
the regions and `rdi`, keeps the selection. -/
theorem SelW.stab {avx2 : Bool} {tbl st np : Nat} {base : Addr} {mem : Mem} {a e : Nat} {t t' : State}
    (h : SelW avx2 tbl st np base mem a e t) {W : List (Nat × Nat)} (hU : Unch base W t.mem t'.mem)
    (hW : ∀ w ∈ W, ∀ b < 16 * st, tbl + b + 1 ≤ w.1 ∨ w.1 + w.2 ≤ tbl + b) (htb : tbl + 16 * st ≤ 2 ^ 64)
    (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : SelW avx2 tbl st np base mem a e t' :=
  ⟨h.ha, h.sel.of_vec hx hy, fun b hb => by
    have e : t'.mem (base + BitVec.ofNat 64 (tbl + b)) = t.mem (base + BitVec.ofNat 64 (tbl + b)) :=
      hU.byte (fun w hw => hW w hw b hb) (by omega)
    rw [← Offset.add_add] at e
    rw [e]; exact h.tblm b hb,
    by rw [hrd, hwr]; exact h.reg, by rw [hdi]; exact h.rdi⟩

/-- `rdx = rdi + tbl`. -/
theorem tblRdxW_ok (s : State) {base : Addr} {tbl : Nat} (ht : tbl < 2 ^ 31) (hd : s.gpr .rdi = base) :
    WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 tbl))]) s fun t =>
      t.gpr .rdx = base + BitVec.ofNat 64 tbl ∧ Keeps [.rdx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, imm32_sext ht, hd, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem chunkW_le {N i : Nat} (hi : i < N) : chunkW N i ≤ chunkW N (i + 1) ∧ chunkW N (i + 1) ≤ 16 := by
  unfold chunkW
  exact ⟨Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega)),
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm N]; exact Nat.mul_le_mul_left _ (by omega))⟩

theorem chunkW_zero (N : Nat) : chunkW N 0 = 0 := by
  rw [chunkW, Nat.mul_zero, Nat.zero_div]

theorem chunkW_last {N : Nat} (h : 0 < N) : chunkW N N = 16 := by
  rw [chunkW, Nat.mul_div_cancel _ h]

/-- A part of the selection: entries `chunkW N i + 1` to `chunkW N (i + 1)`. -/
theorem selChunkW_ok {avx2 : Bool} {tbl st np N : Nat} (hnp : 2 ≤ np ∧ np ≤ 10) (hst : 16 * np ≤ st)
    (htbl : tbl < 2 ^ 31) (hst64 : 16 * st < 2 ^ 64) {base : Addr} {mem : Mem} {a : Nat} (i : Nat)
    (hi : i < N) {t : State} (h : SelW avx2 tbl st np base mem a (chunkW N i) t) :
    WP isa (.block (selChunkW avx2 tbl st np N i)) t fun t' => SelW avx2 tbl st np base mem a (chunkW N (i + 1)) t' ∧
      ForwardField.SideKeepF t t' := by
  obtain ⟨hlo, hhi⟩ := chunkW_le hi
  unfold selChunkW
  split
  · next he => exact WP.block_nil ⟨by rw [he]; exact h, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (tblRdxW_ok t htbl h.rdi) fun t₁ ⟨x₁, k₁, xx₁, xy₁⟩ => ?_
  have hm₁ : t₁.mem = t.mem := k₁.2.1
  have hT : ∀ b < 16 * st, mem (base + BitVec.ofNat 64 tbl + BitVec.ofNat 64 b) =
      t₁.mem (base + BitVec.ofNat 64 tbl + BitVec.ofNat 64 b) := fun b hb => by
    rw [hm₁]; exact (h.tblm b hb).symm
  have hreg : InRegions (t₁.rd ++ t₁.wr) (base + BitVec.ofNat 64 tbl) (16 * st) := by
    rw [k₁.2.2.1, k₁.2.2.2]; exact h.reg
  have hS₁ := h.sel.of_vec xx₁ xy₁
  have hdi : t₁.gpr .rdi = base := by rw [k₁.1 _ (by decide)]; exact h.rdi
  have side : ∀ {t' : State}, t'.mem = t₁.mem → t'.rd = t₁.rd → t'.wr = t₁.wr →
      (∀ r, r ≠ .rdx → t'.gpr r = t₁.gpr r) → ForwardField.SideKeepF t t' := fun hm hr hw hg =>
    ⟨fun r hr' => by rw [hg r hr', k₁.1 r (by simpa using hr')], by rw [hm, hm₁], by rw [hr, k₁.2.2.1],
      by rw [hw, k₁.2.2.2]⟩
  have hlo' : chunkW N i + (chunkW N (i + 1) - chunkW N i) = chunkW N (i + 1) := by omega
  unfold SelSW at hS₁
  unfold selEntryW
  cases hv : avx2
  · -- SSE2
    rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at hS₁
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b13, b12, b11, acc⟩ := hS₁
    refine WP.mono (selEntriesFromX_ok (X := base + BitVec.ofNat 64 tbl) (st := st) (np := np) (lo := chunkW N i)
      (by omega) (by have := h.ha; omega) (chunkW N (i + 1) - chunkW N i) (by omega) t₁ x₁ b13 b12 b11
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ hst64
        have := Nat.mul_le_mul_left st (show chunkW N i + e + 1 ≤ 16 by omega)
        rw [Nat.mul_succ] at this
        rw [Nat.mul_comm 16 st]
        omega)
      (AccX.congrS hst h.ha hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < np, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < np, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelSW
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by rw [k'.xmm _ n13]; exact b13, by rw [k'.xmm _ n12]; exact b12, by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    exact AccX.congrS hst h.ha (fun b hb => h.tblm b hb) a'
  · -- AVX2
    rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at hS₁
    simp only [↓reduceIte]
    obtain ⟨b13, b12, b14, acc⟩ := hS₁
    have hq : ∀ c, qY np c + 2 ≤ np := fun c => qY_le c (by omega)
    refine WP.mono (selEntriesFromY_ok (X := base + BitVec.ofNat 64 tbl) (st := st) (np := (np + 1) / 2) (q := qY np)
      (lo := chunkW N i) (by omega) (by have := h.ha; omega) (chunkW N (i + 1) - chunkW N i) (by omega) t₁ x₁
      b13 b12 b14
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ hst64
        have := Nat.mul_le_mul_left st (show chunkW N i + e + 1 ≤ 16 by omega)
        rw [Nat.mul_succ] at this
        have := hq c
        rw [Nat.mul_comm 16 st]
        omega)
      (AccY.congrS hst hnp.1 h.ha hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < (np + 1) / 2, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < (np + 1) / 2, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelSW
    simp only [↓reduceIte]
    refine ⟨fun l hl => by rw [k'.lane _ n13 l]; exact b13 l hl, fun l hl => by rw [k'.lane _ n12 l]; exact b12 l hl,
      by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    exact AccY.congrS hst hnp.1 h.ha (fun b hb => h.tblm b hb) a'

/-- The selection set up for the magnitude `r8 = a ≤ 16`, through `rcx`: no
entry kept yet, of any table. -/
theorem selSetW_ok {avx2 : Bool} {np : Nat} (hnp : 2 ≤ np ∧ np ≤ 10) (s : State) (X : Addr) (st : Nat) (mem : Mem)
    {a : Nat} (ha : a ≤ 16) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block (selSetW avx2 np)) s fun t => SelSW avx2 X st np mem a 0 t ∧ Keeps [.rcx] s t := by
  unfold selSetW SelSW
  cases hv : avx2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetX_ok s (by omega) h8) fun s₁ ⟨b13, b12, b11, k₁⟩ => ?_
    refine WP.mono (clearAcc_ok np (by omega) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm11 ∨ r = .xmm12 ∨ r = .xmm13 → ¬ ∃ c < np, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨n11, n12, n13, -, -⟩ := selAcc_neX c (by omega)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨by rw [k.xmm _ (nacc _ (by simp))]; exact b13, by rw [k.xmm _ (nacc _ (by simp))]; exact b12,
      by rw [k.xmm _ (nacc _ (by simp))]; exact b11, fun c hc => by
        rw [z c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩
  · simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetY_ok s (by omega) h8) fun s₁ ⟨b13, b12, b14, k₁⟩ => ?_
    refine WP.mono (clearAccY_ok ((np + 1) / 2) (by omega) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm12 ∨ r = .xmm13 ∨ r = .xmm14 → ¬ ∃ c < (np + 1) / 2, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨-, n12, n13, n14, -⟩ := selAcc_neY c (by omega)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b13 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b12 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b14 l hl, fun c hc l hl => by
        rw [z c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩

/-- The accumulators after the sixteen entries stored to `o`. -/
theorem storeW_ok {avx2 : Bool} {np : Nat} (hnp : 2 ≤ np ∧ np ≤ 10) {base : Addr} {size o : Nat}
    {X : Addr} {st : Nat} {mem : Mem} {a : Nat} {t : State}
    (hs : Scr t base size) (hT : o + 16 * np ≤ size) (h : SelSW avx2 X st np mem a 16 t) :
    WP isa (.block (storeW avx2 o np)) t fun t' =>
      (∀ c < np, t'.mem.readW (off base (o + 16 * c)) 128 = accVal mem X st (16 * ·) a 16 c) ∧
      Outside base o (16 * np) t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  unfold storeW
  unfold SelSW at h
  cases hv : avx2
  · rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeAcc_ok np t hs hT) fun t' ⟨a', O', g', r', w', _⟩ =>
      ⟨fun c hc => by rw [a' c hc]; exact h.2.2.2 c hc, O', g', r', w'⟩
  · rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at h
    simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (storeAccY_ok (o := o) (n := np) (q := qY np)
      (V := accVal mem X st (16 * ·) a 16) hT ((np + 1) / 2) t hs (fun c _ => qY_le c (by omega))
      (fun c hc l hl => h.2.2.2 c hc l hl)) fun t₁ ⟨a₁, O₁, g₁, r₁, w₁, _⟩ => ?_
    refine WP.mono (vzeroupper_ok t₁) fun t' ⟨m', g', r', w'⟩ =>
      ⟨fun j hj => ?_, by rw [m']; exact O₁, by rw [g', g₁], by rw [r', r₁], by rw [w', w₁]⟩
    obtain ⟨c, hc, l, hl, e⟩ := qY_cover (n := np) (by omega) hj
    have := a₁ c hc l hl
    rw [e] at this
    rw [m']
    exact this

end VG.Proof.Weierstrass.X86_64
