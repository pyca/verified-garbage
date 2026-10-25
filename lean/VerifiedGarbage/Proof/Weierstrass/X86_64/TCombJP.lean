module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit

/-!
# The pipelined comb on x86-64

`TCombCfg.combJP` (`Impl/Weierstrass/X86_64/TCombJ.lean`): window `1`'s
entry is selected and negated before the loop (`tentryJ_ok`); iteration `j`
then adds window `j`'s entry while it selects window `j + 1`'s, its loads
spread among the addition's field operations (`maddJI_ok`, with the
selection's state `SelI` as the side code's), and stores and negates it
after the addition's own selections (`stepJP_ok`); window `J - 1` is added
by `stepJ`'s code (`tailJ_ok`). The selection's state lives in vector
registers, which the operations, of scalar code, leave alone, and in the
memory of the tables, past the working space, which they do not write.
`tcombJ_ok`: `combJ`, pipelined or not, computes `[k]G`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

theorem dec_eq (i : Nat) :
    BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 i := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, ← inc_eq i,
    show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.add_sub_cancel]

/-- `rbx = j + 1`. -/
theorem incRbxJ_ok (s : State) {j : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (j + 1) ∧ Keeps [.rbx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb, inc_eq, ite_true]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rbx = j`, from `j + 1`. -/
theorem decRbxJ_ok (s : State) {j : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 j ∧ Keeps [.rbx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb, dec_eq, ite_true]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rdx` = table `rbx + 1`'s address (`selSetup`'s, a table on). -/
theorem selSetupNext_ok (K : TCombCfg) (s : State) {j : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j)
    (hT : s.syms K.tsym = T) (htb : K.tblBytes < 2 ^ 31) :
    WP isa (.block K.selSetupNext) s fun t => t.gpr .rdx = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      Keeps [.rax, .rcx, .rdx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.syms = s.syms := by
  subst hT
  apply WP.of_runBlock
  simp only [TCombCfg.selSetupNext, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, execMul, State.setReg32, imm32_eq htb, hb, inc_eq, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show K.tblBytes < 2 ^ 64 by omega_arith), Nat.mod_mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- Entries `lo + 1 … lo + h` of the table at `rdx = X` kept in the
accumulators (holding entries `1 … lo`) under the masks of `a`, the counter
from `lo + 1`. -/
theorem selEntriesFromY_ok {st np : Nat} {q : Nat → Nat} {X : Addr} {a lo : Nat} (hn : np ≤ 11)
    (ha : a < 2 ^ 31) :
    ∀ h, lo + h < 2 ^ 31 → ∀ (s : State), s.gpr .rdx = X →
    (∀ l < 2, s.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) →
    (∀ l < 2, s.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) →
    (∀ l < 2, s.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (lo + 1))) →
    (∀ e < h, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (lo + e) + 16 * q c)) 32) →
    AccY s s.mem X st a lo np q →
    WP isa (.block ((List.range h).flatMap fun e => selEntryY st np q (lo + e + 1))) s fun t =>
      AccY t s.mem X st a (lo + h) np q ∧ (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (lo + h + 1))) ∧
      YKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h14, _, h0 => WP.block_nil ⟨h0, h14, YKeep.refl _ _ _⟩
  | h + 1, hh, s, hx, h13, h12, h14, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selEntriesFromY_ok hn ha h (by omega_arith) s hx h13 h12 h14 (fun e he => hr e (by omega_arith)) h0)
      fun s₁ ⟨a₁, c₁, k₁⟩ => ?_
    have n13 : ¬ ((∃ c < np, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neY c (by omega_arith)).2.2.1 h.symm
      all_goals exact absurd h (by decide)
    have n12 : ¬ ((∃ c < np, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neY c (by omega_arith)).2.1 h.symm
      all_goals exact absurd h (by decide)
    refine WP.mono (selEntryY_ok (X := X) (m := lo + h + 1) hn (by omega_arith) hh ha
      (by rw [k₁.gpr _ List.not_mem_nil, hx]) (fun l hl => by rw [k₁.lane _ n13 l, h13 l hl])
      (fun l hl => by rw [k₁.lane _ n12 l, h12 l hl]) c₁
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega_arith) c hc)
      (fun c hc l hl => by rw [a₁ c hc l hl, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, c₂, k₂⟩ =>
      ⟨fun c hc l hl => by rw [a₂ c hc l hl, k₁.mem, ← Nat.add_assoc], by
        rw [show lo + (h + 1) + 1 = lo + h + 1 + 1 by omega_arith]; exact c₂, k₁.trans k₂⟩

/-! ## The selection's state during the addition -/

/-- What a selection's reads of the 16 bytes at piece `i` of entry `a ≤ H`
find depends only on the table's bytes. -/
theorem accVal_congr {m m' : Mem} {X : Addr} {n H a e i : Nat} (ha : a ≤ H) (hi : i < n)
    (h : ∀ b < 16 * n * H, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b)) :
    accVal m X (16 * n) (16 * ·) a e i = accVal m' X (16 * n) (16 * ·) a e i := by
  unfold accVal
  split
  · next h1 =>
    have h2 := Nat.mul_le_mul_left (16 * n) (show a - 1 + 1 ≤ H by omega_arith)
    rw [Nat.mul_succ] at h2
    dsimp only
    exact Mem.readW_congr fun b hb => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h _ (by omega_arith)
  · rfl

/-- The accumulators survive a change of memory that keeps the table's bytes. -/
theorem AccY.congr {t : State} {m m' : Mem} {X : Addr} {n H a e : Nat} (ha : a ≤ H) (h2 : 2 ≤ n)
    (h : ∀ b < 16 * n * H, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b))
    (hA : AccY t m X (16 * n) a e ((n + 1) / 2) (qY n)) : AccY t m' X (16 * n) a e ((n + 1) / 2) (qY n) :=
  fun c hc l hl => by
    rw [hA c hc l hl]
    exact accVal_congr ha (by have := qY_le c h2; omega_arith) h

/-- The lanes of a vector register, from `xmm` and `ymmHi`. -/
theorem lane_congr {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) (r : XReg) (l : Nat) :
    t.lane r l = s.lane r l := by
  simp only [State.lane, hx, hy]

/-- The selection of window `j + 1`'s entry, for the magnitude `a ≤ H`, after
its entries `1 … e`: the broadcasts of `a` and one, the counter, the
accumulators (`AccY`), of the table at `X = T + (j + 1) tblBytes` as in
`mem`, whose bytes the state holds, past the working space and the
temporary area. -/
structure SelX (K : TCombCfg) (base : Addr) (size : Nat) (T : Addr) (j a : Nat) (mem : Mem) (e : Nat)
    (t : State) : Prop where
  ha : a ≤ K.H
  b13 : ∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)
  b12 : ∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)
  b14 : ∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (e + 1))
  acc : AccY t mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) (16 * K.M.n) a e ((K.M.n + 1) / 2) (qY K.M.n)
  reg : InRegions (t.rd ++ t.wr) (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) K.tblBytes
  tblm : ∀ b < K.tblBytes, t.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b) =
    mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b)
  out : ∀ b < K.tblBytes, size ≤ ofs base (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b)
  tmp : K.M.tmp + 8 * K.M.n ≤ size

/-- `SelX`, with `rbx = j` and the tables' static at `T`, which the
selection's parts read. -/
structure SelI (K : TCombCfg) (base : Addr) (size : Nat) (T : Addr) (j a : Nat) (mem : Mem) (e : Nat)
    (t : State) : Prop where
  x : SelX K base size T j a mem e t
  rbx : t.gpr .rbx = BitVec.ofNat 64 j
  tsym : t.syms K.tsym = T

/-- A field operation keeps the selection's state (`fprogBI_ok`'s `hstab`). -/
theorem SelI.stab {K : TCombCfg} {base : Addr} {size : Nat} {T : Addr} {j a e : Nat} {mem : Mem}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) {o : Nat} {t t' : State} (ho : Sl o)
    (h : SelI K base size T j a mem e t) (hk : OpKeep K.M base o t t') (hx : t'.xmm = t.xmm)
    (hy : t'.ymmHi = t.ymmHi) (hsy : t'.syms = t.syms) : SelI K base size T j a mem e t' := by
  have hl := lane_congr hx hy
  have hol := hL.le o ho
  refine ⟨⟨h.x.ha, fun l hl' => by rw [hl]; exact h.x.b13 l hl', fun l hl' => by rw [hl]; exact h.x.b12 l hl',
    fun l hl' => by rw [hl]; exact h.x.b14 l hl', fun c hc l hl' => by rw [hl]; exact h.x.acc c hc l hl',
    by rw [hk.rd, hk.wr]; exact h.x.reg, fun b hb => ?_, h.x.out, h.x.tmp⟩,
    by rw [hk.gpr _ (rbx_not_clob _)]; exact h.rbx, by rw [hsy]; exact h.tsym⟩
  have := h.x.out b hb
  have := h.x.tmp
  rw [hk.mem _ (Or.inr (by omega_arith)) (Or.inr (by omega_arith))]
  exact h.x.tblm b hb

/-- A part of the selection (`fprogBI_ok`'s `hside`): from entry
`chunkLo i` to `chunkLo (i + 1)`. -/
theorem selChunk_ok (K : TCombCfg) {base : Addr} {size : Nat} {T : Addr} {j a : Nat} {mem : Mem}
    (hn : 2 ≤ K.M.n ∧ K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 31) (i : Nat)
    {t : State} (hi : i < K.nOps) (h : SelI K base size T j a mem (K.chunkLo i) t) :
    WP isa (.block (K.selChunk i)) t fun t' => SelI K base size T j a mem (K.chunkLo (i + 1)) t' ∧
      SideKeep K.M t t' := by
  have hlo : K.chunkLo i ≤ K.chunkLo (i + 1) := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega_arith))
  have hhi : K.chunkLo (i + 1) ≤ K.H := by
    unfold TCombCfg.chunkLo
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm K.nOps]; exact Nat.mul_le_mul_left _ (by omega_arith))
  have hnp : (K.M.n + 1) / 2 ≤ 11 := by omega_arith
  unfold TCombCfg.selChunk
  split
  · next he => exact WP.block_nil ⟨by rw [he]; exact h, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · rw [WP.block_append_iff]
    refine WP.mono_syms (selSetupNext_ok K t h.rbx h.tsym htb) fun t₁ ⟨x₁, k₁, xx₁, xy₁, sy₁⟩ _ => ?_
    have hl₁ := lane_congr xx₁ xy₁
    have hm₁ : t₁.mem = t.mem := k₁.2.1
    have htbe : K.tblBytes = 16 * K.M.n * K.H := rfl
    refine WP.mono_syms (selEntriesFromY_ok (st := 16 * K.M.n) (q := qY K.M.n) (lo := K.chunkLo i) (a := a)
      (X := T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) hnp
      (by have := h.x.ha; omega_arith) (K.chunkLo (i + 1) - K.chunkLo i) (by omega_arith) t₁ x₁
      (fun l hl => by rw [hl₁]; exact h.x.b13 l hl) (fun l hl => by rw [hl₁]; exact h.x.b12 l hl)
      (fun l hl => by rw [hl₁]; exact h.x.b14 l hl)
      (fun e he c hc => by
        rw [k₁.2.2.1, k₁.2.2.2]
        refine VG.CallLay.inRegions_sub h.x.reg ?_ (by omega_arith)
        have := Nat.mul_le_mul_left (16 * K.M.n) (show K.chunkLo i + e + 1 ≤ K.H by omega_arith)
        rw [Nat.mul_succ] at this
        have := qY_le c hn.1
        omega_arith)
      (fun c hc l hl => by
        rw [hl₁, hm₁]
        exact AccY.congr (n := K.M.n) (H := K.H) h.x.ha hn.1
          (fun b hb => (h.x.tblm b (by rw [htbe]; exact hb)).symm) h.x.acc c hc l hl))
      fun t' ⟨a', c', k'⟩ sy' => ?_
    have hm' : t'.mem = t.mem := by rw [k'.mem, hm₁]
    have hlo' : K.chunkLo i + (K.chunkLo (i + 1) - K.chunkLo i) = K.chunkLo (i + 1) := by omega_arith
    refine ⟨⟨⟨h.x.ha, fun l hl => ?_, fun l hl => ?_, fun l hl => by rw [← hlo']; exact c' l hl,
      fun c hc l hl => ?_, by rw [k'.rd, k'.wr, k₁.2.2.1, k₁.2.2.2]; exact h.x.reg,
      fun b hb => by rw [hm']; exact h.x.tblm b hb, h.x.out, h.x.tmp⟩,
      by rw [k'.gpr _ List.not_mem_nil, k₁.1 _ (by decide)]; exact h.rbx,
      by rw [sy', sy₁]; exact h.tsym⟩, ⟨fun r hr => ?_, hm', by rw [k'.rd, k₁.2.2.1], by rw [k'.wr, k₁.2.2.2]⟩⟩
    · rw [k'.lane _ (by
        rintro (⟨c, hc, h'⟩ | h' | h' | h')
        · exact (selAcc_neY c (by omega_arith)).2.2.1 h'.symm
        all_goals exact absurd h' (by decide)), hl₁]
      exact h.x.b13 l hl
    · rw [k'.lane _ (by
        rintro (⟨c, hc, h'⟩ | h' | h' | h')
        · exact (selAcc_neY c (by omega_arith)).2.1 h'.symm
        all_goals exact absurd h' (by decide)), hl₁]
      exact h.x.b12 l hl
    · have e1 := a' c hc l hl
      rw [hlo', hm₁] at e1
      rw [e1]
      have hq := qY_le c hn.1
      exact accVal_congr (n := K.M.n) (H := K.H) h.x.ha (by omega_arith)
        fun b hb => h.x.tblm b (by rw [htbe]; exact hb)
    · rw [k'.gpr _ List.not_mem_nil, k₁.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h' => hr (h' ▸ by simp [clob]), fun h' => hr (h' ▸ by simp [clob]),
          fun h' => hr (h' ▸ by simp [clob])⟩)]

/-! ## The loop's invariant through the selections -/

/-- The invariant survives writes to `E`, `-y` and the temporary area that keep
the registers but `powClob`. -/
theorem TCombJAt.after_entry {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {ws : List (BitVec 64)} {s₀ s t : State} {j r r' : Nat} (hL : TCombLay K size)
    (hF : TCombFixed K C base size s₀ k T ws) (I : TCombJAt K C base size k T ws s₀ s j r)
    (hU : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)] s.mem t.mem)
    (hk : KeepRegs (powClob K.M.n) s t) (hs : Scr t base size) (hb : t.gpr .rbx = BitVec.ofNat 64 r')
    (hsy : t.syms = s.syms) : TCombJAt K C base size k T ws s₀ t j r' := by
  have hn := hs.nowrap
  have hsz : size ≤ 2 ^ 64 := by omega_using [hn]
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ combW K.toComb := combEntryW_sub (K := K.toComb)
  have U₁ : Unch base (combW K.toComb) s.mem t.mem := hU.mono hEW
  have hmoW := tcombW_mo hL I.mod
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    hL.comb.wordsVal_entry hsz hU
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have e : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base t x = tmv C K.M.n base s x :=
    fun x hx => by show toM _ _ _ = toM _ _ _; rw [hAx x hx]
  refine ⟨hs, hb, I.keep.trans hk, (I.unch.trans U₁).mono fun w hw => ?_,
    I.mod.unch U₁ (fun w hw => hmoW w (List.mem_append_left _ hw)) hn, fun x hx => by rw [hAx x hx]; exact I.lt x hx,
    by rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact I.rep, fun t' ht => ?_,
    TblMem.of_unch I.tbl (by rw [hk.rd, hk.wr]) U₁ (fun w hw => tcombW_size hL I.mod w (List.mem_append_left _ hw))
      hF.out, by rw [hsy]; exact I.tsym⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact List.mem_append_left _ hw
  · rw [U₁.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact I.bits t' ht

/-- `TEntryPostJ` at a state with the same memory, from itself. -/
theorem TEntryPostJ.self {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {s t u : State}
    (E : TEntryPostJ K C base size k i s t) (hm : u.mem = t.mem) (hs : Scr u base size) :
    TEntryPostJ K C base size k i u u :=
  ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, fun _ _ => rfl, fun x hx => by rw [hm]; exact E.lt x hx,
    by unfold tmv; rw [hm]; exact E.rep, by unfold tmv; rw [hm]; exact E.z⟩

theorem rdi_not_powClob (n : Nat) : Reg.rdi ∉ powClob n := fun h => by
  simp only [powClob, List.mem_cons] at h
  rcases h with h | h
  · cases h
  · exact rdi_not_clob n h

/-- Table `j`'s bytes are past the working space. -/
theorem row_out {K : TCombCfg} {base T : Addr} {size : Nat} {ws : List (BitVec 64)}
    (hout : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    (hlen : K.J * K.tblBytes ≤ 8 * ws.length) {j : Nat} (hj : j < K.J) :
    ∀ b < K.tblBytes, size ≤ ofs base (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 b) := by
  intro b hb
  have h1 := Nat.mul_le_mul_right K.tblBytes (show j + 1 ≤ K.J by omega_arith)
  rw [Nat.succ_mul] at h1
  have h := hout ((j * K.tblBytes + b) / 8) (by omega_arith) ((j * K.tblBytes + b) % 8) (Nat.mod_lt _ (by decide))
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod] at h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h

/-- Before window `j`'s addition (`1 ≤ j`, `j + 1 < J`): the selection of
window `j + 1`'s entry started (`SelI` at `0`), the rest as it was. -/
theorem prepNext_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hV : TCombVals K C tbl) (hb1 : 1 ≤ K.bits)
    {s₀ s : State} (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} (hj : 1 ≤ j) (hjn : j + 2 ≤ K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (E : TEntryPostJ K C base size k j s s) :
    WP isa (.block K.prepNext) s fun t =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ t j ∧
      TEntryPostJ K C base size k j t t ∧ SelI K base size T j (bmag K.w k (j + 1)) s.mem 0 t := by
  have hs := hI.scr
  have hn := hs.nowrap
  have hw := hL.w
  have hnn := hL.n
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hwi : K.w * (j + 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  have hmag : bmag K.w k (j + 1) ≤ K.H := bmag_le hw.1 k (j + 1)
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hnp : (K.M.n + 1) / 2 ≤ 11 := by omega_using [hnn]
  unfold TCombCfg.prepNext
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (incRbxJ_ok s hI.rbx) fun s₁ ⟨b₁, k₁, _, _⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs₁ (k := k) (j := j + 1) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb1 b₁ (fun t ht => by rw [k₁.2.1]; exact hI.bits t ht)
    (Or.inl ⟨rfl, by omega_arith⟩)) fun s₂ ⟨_, r₂, k₂⟩ sy₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (decRbxJ_ok (j := j) s₂ (by rw [k₂.1 _ (by decide), b₁])) fun s₃ ⟨b₃, k₃, _, _⟩ sy₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (selSetY_ok (a := bmag K.w k (j + 1)) s₃ (by omega_using [hmag, hHle]) (by rw [k₃.1 _ (by decide), r₂]))
    fun s₄ ⟨b13, b12, b14, k₄⟩ sy₄ => ?_
  refine WP.mono_syms (clearAccY_ok ((K.M.n + 1) / 2) hnp s₄) fun t ⟨z₅, k₅⟩ sy₅ => ?_
  have hm : t.mem = s.mem := by rw [k₅.mem, k₄.mem, k₃.2.1, k₂.2.1, k₁.2.1]
  have hrd : t.rd = s.rd := by rw [k₅.rd, k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  have hwr : t.wr = s.wr := by rw [k₅.wr, k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  have hsy : t.syms = s.syms := by rw [sy₅, sy₄, sy₃, sy₂, sy₁]
  have hcl : ∀ r, r ∉ powClob K.M.n → t.gpr r = s.gpr r := fun r hr => by
    have hr' : r ∉ [Reg.rbx, .rax, .rcx, .rdx, .r8] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (h ▸ List.mem_cons_self ..), fun h => hr (h ▸ clob_powClob _ (by simp [clob])),
        fun h => hr (h ▸ clob_powClob _ (by simp [clob])), fun h => hr (h ▸ clob_powClob _ (by simp [clob])),
        fun h => hr (h ▸ clob_powClob _ (r8_mem_clob _))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [k₅.gpr r List.not_mem_nil, k₄.gpr r (by simp [hr'.2.2.1]), k₃.1 r (by simp [hr'.1]),
      k₂.1 r (by simp [hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2]), k₁.1 r (by simp [hr'.1])]
  have hk : KeepRegs (powClob K.M.n) s t := ⟨hcl, hrd, hwr⟩
  have hst : Scr t base size := ⟨by rw [hcl _ (rdi_not_powClob _)]; exact hs.rdi, by rw [hwr]; exact hs.wr, hn⟩
  have hbt : t.gpr .rbx = BitVec.ofNat 64 j := by rw [k₅.gpr _ List.not_mem_nil, k₄.gpr _ (by decide), b₃]
  refine ⟨TCombJAt.after_entry hL hF hI (fun x _ => by rw [hm]) hk hst hbt hsy, E.self hm hst,
    ⟨⟨hmag, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun c hc l hl => ?_, ?_, fun b _ => by rw [hm],
      row_out hF.out ?_ (by omega_using [hjn]), hI.mod.tmp⟩, hbt, by rw [hsy]; exact hI.tsym⟩⟩
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega_using [hnp, hc])).2.2.1 h.symm)]; exact b13 l hl
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega_using [hnp, hc])).2.1 h.symm)]; exact b12 l hl
  · rw [k₅.lane _ (fun ⟨c, hc, h⟩ => (selAcc_neY c (by omega_using [hnp, hc])).2.2.2.1 h.symm)]; exact b14 l hl
  · rw [z₅ c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  · have hlen := tcombWords_length (n := K.M.n) (R := 2 ^ (64 * K.M.n)) (p := C.p) hV.len hV.lenH
    obtain ⟨r, hr, hc⟩ := hI.tbl.rd
    refine ⟨r, by rw [hrd, hwr]; exact hr, Region.contains_off hc ?_⟩
    rw [hlen, TCombCfg.tblBytes]
    have h2 := Nat.mul_le_mul_right (16 * K.M.n * K.H) (show j + 1 + 1 ≤ K.J by omega_using [hjn])
    rw [Nat.succ_mul] at h2
    have e : 16 * K.M.n * K.H = 8 * (K.H * (2 * K.M.n)) := by
      rw [Nat.mul_comm K.H, ← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [Nat.mul_left_comm 8 K.J, ← e]
    omega_using [h2]
  · have hlen := tcombWords_length (n := K.M.n) (R := 2 ^ (64 * K.M.n)) (p := C.p) hV.len hV.lenH
    rw [hlen, TCombCfg.tblBytes]
    have e : 16 * K.M.n * K.H = 8 * (K.H * (2 * K.M.n)) := by
      rw [Nat.mul_comm K.H, ← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [e, Nat.mul_left_comm]

/-- `ZF` for `j + 1 = J`, with `rbx = j + 1`. -/
theorem cmpRbxLast_ok (s : State) {j J : Nat} (hj : j + 1 ≤ J) (hJ : J < 2 ^ 31)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 J))]) s fun t =>
      t.zf = some (decide (j + 1 = J)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb, RegUpd.zf_arithFlags, cmp_eq hj hJ]
  refine ⟨trivial, fun r _ => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags]

/-- After window `j`'s additions and selections (`1 ≤ j`, `j + 1 < J`), from
the selection of window `j + 1`'s entry (`SelX` at `H`, of the tables in
`sp`): `rbx = j + 1`, the entry stored to `E`, negated for a negative digit
(`negEntryJ_ok`), and `ZF` for `j + 1 = J - 1`. -/
theorem finNext_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hb1 : 1 ≤ K.bits) (h2 : 2 ≤ K.M.n) {s₀ sp s : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hTM : TblMem sp T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) {j : Nat} (hj : 1 ≤ j) (hjn : j + 2 ≤ K.J)
    (I : TCombJAt K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s (j + 1) j)
    (X : SelX K base size T j (bmag K.w k (j + 1)) sp.mem K.H s) :
    WP isa (.block K.finNext) s fun t =>
      (TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ t (j + 1) ∧
        TEntryPostJ K C base size k (j + 1) t t) ∧ t.zf = some (decide (j + 1 = K.J - 1)) := by
  have hs := I.scr
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnn := hL.n
  have hbl := hL.bits
  have hbw := hL.bits_w
  have hz' : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have ap : ∀ {x y : Nat}, x ∈ combWs K.toComb → y ∈ combWs K.toComb → x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun hx hy h => hL.comb.apart₂ hx hy h
  have hexy := hL.exy
  have hEy := hle K.E.y (by tcomb_mem)
  have hEz := hle K.E.z (by tcomb_mem)
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hnp : (K.M.n + 1) / 2 ≤ 11 := by omega_using [hnn]
  have hwi : K.w * (j + 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  have hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x := by
    have := ap (x := K.E.x) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd)
    have := ap (x := K.E.y) (y := K.E.z) (by tcomb_mem) (by tcomb_mem) (by nd_ne hnd); omega_arith
  -- The bits of `k` are apart from `E`.
  have hbE : ∀ t < K.w * K.J, ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
      (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t :=
    fun t ht w hw => combW_bits hL ht w (combEntryW_sub (K := K.toComb) w hw)
  unfold TCombCfg.finNext
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (incRbxJ_ok s I.rbx) fun s₁ ⟨b₁, k₁, x₁, y₁⟩ sy₁ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hl₁ := lane_congr x₁ y₁
  rw [WP.block_append_iff]
  refine WP.mono_syms (storeAccY_ok (o := K.E.x) (n := K.M.n) (q := qY K.M.n)
    (V := accVal sp.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) (16 * K.M.n) (16 * ·) (bmag K.w k (j + 1)) K.H)
    (by omega_using [hexy, hEy]) ((K.M.n + 1) / 2) s₁ hs₁ (fun c _ => qY_le c h2)
    (fun c hc l hl => by rw [hl₁]; exact X.acc c hc l hl)) fun s₂ ⟨a₂, O₂, g₂, r₂, w₂, _⟩ sy₂ => ?_
  have hs₂ : Scr s₂ base size := ⟨by rw [g₂]; exact hs₁.rdi, by rw [w₂]; exact hs₁.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms (vzeroupper_ok s₂) fun s₃ ⟨m₃, g₃, r₃, w₃⟩ sy₃ => ?_
  have hs₃ : Scr s₃ base size := ⟨by rw [g₃]; exact hs₂.rdi, by rw [w₃]; exact hs₂.wr, hn⟩
  have UE₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)] s₁.mem s₂.mem := by
    rw [hexy]
    exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega_using []]; exact O₂.unch)
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [m₃, UE₂.byte (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hbE t ht _ (by simp)
        · exact hbE t ht _ (by simp)) (by omega_using [hn, hz', hbl, ht]), k₁.2.1]
    exact I.bits t ht
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs₃ (k := k) (j := j + 1) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb1 (by rw [g₃, g₂]; exact b₁) hbits₃ (Or.inl ⟨rfl, by omega_arith⟩))
    fun s₄ ⟨_, r₄, k₄⟩ sy₄ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (selFinish_ok K hs₄ hexy hEy hEz hxz (Nat.lt_trans hV.one_lt hpn) r₄ X.ha
    (by omega_using [hHle]) (fun c hc => by
      obtain ⟨c', hc', l, hl, e⟩ := qY_cover h2 hc
      have h := a₂ c' hc' l hl
      rw [e] at h
      rw [k₄.2.1, m₃]
      exact h)) fun s₅ P₅ sy₅ => ?_
  have hs₅ := hs₄.of_keepRegs P₅.keep (by decide)
  -- What changed, from `s` to `s₅`: `E`.
  have U₅ : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem s₅.mem := by
    have P5u : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s₂.mem s₅.mem := by
      have := P₅.unch; rw [k₄.2.1, m₃] at this; exact this
    have h : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s₁.mem s₅.mem :=
      (UE₂.trans P5u).mono fun w hw => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
        rcases hw with h | h | h | h | h <;> subst h <;> simp
    rw [k₁.2.1] at h
    exact h
  have hmoW := tcombW_mo hL I.mod
  have hmoE : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := fun w hw => hmoW w (List.mem_append_left _
    (combEntryW_sub (K := K.toComb) w (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h <;> subst h <;> simp [combEntryW, TCombCfg.toComb])))
  have hM₅ : ModOkW K.M size C.p s₅.mem base := I.mod.unch U₅ hmoE hn
  have hz₅ : wordsVal s₅.mem base K.zero K.M.n = 0 := by
    have hzW := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
    rw [U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;>
        exact hzW _ (by simp [combW, combWs, TCombCfg.toComb])) (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]),
      I.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
        (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  have hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j + 1) := by
    rw [P₅.keep.gpr _ (by decide), k₄.1 _ (by decide), g₃, g₂]; exact b₁
  have hbits₅ : ∀ t < K.w * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [U₅.byte (fun w hw => hbE t ht w (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
        rcases hw with h | h | h <;> subst h <;> simp))
      (by omega_using [hn, hz', hbl, ht])]
    exact I.bits t ht
  rw [WP.block_append_iff]
  refine WP.mono_syms (negEntryJ_ok hL hC hV hpn hTM (by omega_using [hjn]) hs₅ hM₅ hz₅ hx₅ hbits₅
    P₅.x P₅.y P₅.z) fun s₆ P₆ sy₆ => ?_
  refine WP.mono_syms (cmpRbxLast_ok s₆ (j := j) (J := K.J - 1) (by omega_using [hjn]) (by omega_using [hJ])
    (by rw [P₆.keep.gpr _ (rbx_not_clob _)]; exact hx₅)) fun t ⟨z, kt⟩ syt => ?_
  have hst : Scr t base size := P₆.scr.of_keeps kt (by decide)
  have hU : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)] s.mem t.mem := by
    rw [kt.2.1]
    exact (U₅.trans P₆.unch).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h | h | h | h | h <;> subst h <;> simp
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact clob_powClob _ (by simp [clob])
    · exact clob_powClob _ (by simp [clob])
    · exact clob_powClob _ (by simp [clob])
    · exact clob_powClob _ (r8_mem_clob _)
  have hk : KeepRegs (powClob K.M.n) s t :=
    (((((Keeps.regs k₁).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      ⟨fun r _ => by rw [g₃, g₂], by rw [r₃, r₂], by rw [w₃, w₂]⟩).trans ((Keeps.regs k₄).mono hcl)).trans
      (P₅.keep.mono fun r hr => hcl r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      ((P₆.keep.mono clob_powClob).trans (Keeps.regs kt |>.mono fun _ h => nomatch h))
  have hbt : t.gpr .rbx = BitVec.ofNat 64 (j + 1) := by
    rw [kt.1 _ List.not_mem_nil, P₆.keep.gpr _ (rbx_not_clob _)]; exact hx₅
  refine ⟨⟨TCombJAt.after_entry hL hF I hU hk hst hbt (by rw [syt, sy₆, sy₅, sy₄, sy₃, sy₂, sy₁]),
    P₆.self kt.2.1 hst⟩, z⟩

/-! ## The loop and the comb -/

theorem pipeOk_facts {K : TCombCfg} (hP : K.pipeOk = true) :
    2 ≤ K.M.n ∧ 3 ≤ K.J ∧ ∀ op ∈ maddJ K.S K.A K.E K.D, scalCode (opProg K.M op) = true := by
  simp only [TCombCfg.pipeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hP
  exact ⟨hP.1.1.2, hP.1.2, hP.2⟩

theorem nOps_pos (K : TCombCfg) : 0 < K.nOps := by
  simp only [TCombCfg.nOps, maddJ, List.length_cons]; omega_arith

/-- Window `j` (`1 ≤ j`, `j + 1 < J`) of the pipelined comb, from `E` holding
its entry: window `j + 1`'s entry in `E` after it, and `ZF` for `j + 1 = J - 1`. -/
theorem stepJP_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hP : K.pipeOk = true) {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j + 2 ≤ K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (E : TEntryPostJ K C base size k j s s) :
    WP isa K.stepJP.inline s fun s' =>
      (TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
        TEntryPostJ K C base size k (j + 1) s' s') ∧ s'.zf = some (decide (j + 1 = K.J - 1)) := by
  obtain ⟨h2, -, hsc⟩ := pipeOk_facts hP
  have hnn := hL.n
  have hw := hL.w
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hH : K.chunkLo (0 + K.nOps) = K.H := by
    rw [Nat.zero_add, TCombCfg.chunkLo, Nat.mul_div_cancel _ (nOps_pos K)]
  unfold TCombCfg.stepJP
  simp only [Code.inline]
  refine WP.seq (WP.mono (prepNext_ok hL hV hb1 hF hj hjn hI E) fun sp ⟨Ip, Ep, Sp⟩ => ?_)
  refine tailJ_ok hL hC hM3 hG hV hb1 hB hk hF hj (by omega_arith) Ip Ep rfl
    (X := SelX K base size T j (bmag K.w k (j + 1)) s.mem K.H)
    (fun hI₃ hV₃ => WP.mono (maddJI_ok hL.comb.lay hV.unit hL.comb.add hSl
      (SI := fun i t => SelI K base size T j (bmag K.w k (j + 1)) s.mem (K.chunkLo i) t) (N := K.nOps)
      (fun i t hi h => selChunk_ok K ⟨h2, hnn.2⟩ (by omega_using [hHle]) hL.tbl i hi h)
      (fun _ _ _ _ ho h hk hx hy hsy => SelI.stab hL.comb.lay ho h hk hx hy hsy) hsc (i := 0)
      (Nat.le_of_eq (Nat.zero_add _)) hI₃ hV₃ (by rw [show K.chunkLo 0 = 0 by simp [TCombCfg.chunkLo]]; exact Sp))
      fun s' ⟨P, I, t, S⟩ => ⟨P, I, t, by
        change SelI K base size T j (bmag K.w k (j + 1)) s.mem (K.chunkLo (0 + K.nOps)) s' at S
        rw [hH] at S; exact S.x⟩)
    (fun t t' X hx hy hk hm => ⟨X.ha, fun l hl => by rw [lane_congr hx hy]; exact X.b13 l hl,
      fun l hl => by rw [lane_congr hx hy]; exact X.b12 l hl, fun l hl => by rw [lane_congr hx hy]; exact X.b14 l hl,
      fun c hc l hl => by rw [lane_congr hx hy]; exact X.acc c hc l hl, by rw [hk.rd, hk.wr]; exact X.reg,
      fun b hb => by rw [hm _ (X.out b hb)]; exact X.tblm b hb, X.out, X.tmp⟩)
    fun s₉ I₉ X₉ => finNext_ok hL hC hV hpn hb1 h2 hF hI.tbl hj hjn I₉ X₉

/-- `[k]G` into `A` by the pipelined comb (`combJP`), where it applies. -/
theorem combJP_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) (hP : K.pipeOk = true)
    {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa K.combJP.inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  obtain ⟨-, hJ3, -⟩ := pipeOk_facts hP
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  unfold TCombCfg.combJP
  simp only [Code.inline]
  refine WP.seq (WP.mono (firstJ_ok hL hC hG hV hpn hb1 hs hM hF) fun s₁ I₁ => ?_)
  have hn₁ := I₁.scr.nowrap
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [I₁.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn₁, this]), hF.zero]
  refine WP.seq (WP.mono_syms (tentryJ_ok hL hC hV hpn I₁.scr I₁.mod (i := 1) (by omega_arith) I₁.rbx hb1 (c := true)
    (Or.inl ⟨rfl, Nat.le_refl 1⟩) I₁.bits hz I₁.tsym I₁.tbl) fun s₂ h₂ sy₂ =>
      WP.seq (WP.mono_syms h₂ fun s₃ E₃ sy₃ => ?_))
  have I₃ : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s₃ 1 :=
    TCombJAt.after_entry hL hF I₁ E₃.unch (E₃.keep.mono clob_powClob) E₃.scr
      (by rw [E₃.keep.gpr _ (rbx_not_clob _)]; exact I₁.rbx) (by rw [sy₃, sy₂])
  refine WP.seq (WP.mono (countLoop_ok (Q := fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' (K.J - 1) ∧
        TEntryPostJ K C base size k (K.J - 1) s' s')
    (Inv := fun r s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s'
      (K.J - 1 - r) ∧ TEntryPostJ K C base size k (K.J - 1 - r) s' s') (n := K.J - 2)
    (fun r s' h1 h2 hi => WP.mono (stepJP_ok hL hC hM3 hG hV hpn hb1 hB hk hF hP (j := K.J - 1 - r)
      (by omega_arith) (by omega_arith) hi.1 hi.2) fun s'' ⟨h, z⟩ =>
        ⟨by rw [show K.J - 1 - (r - 1) = K.J - 1 - r + 1 by omega_arith]; exact h, by
          rw [z]; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩)
    (fun s' hi => by rw [Nat.sub_zero] at hi; exact hi) (by omega_arith)
    (by rw [show K.J - 1 - (K.J - 2) = 1 by omega_arith]; exact ⟨I₃, E₃.self rfl E₃.scr⟩)) fun s₄ ⟨I₄, E₄⟩ => ?_)
  refine WP.seq (WP.mono (stepJTail_ok hL hC hM3 hG hV hb1 hB hk hF (j := K.J - 1) (by omega_arith) (by omega_arith) I₄ E₄ rfl)
    fun s₅ ⟨I₅, _⟩ => ?_)
  rw [show K.J - 1 + 1 = K.J by omega_arith] at I₅
  exact outJ_ok hL hC hV hpn hB hk hs hM hF I₅

/-- `[k]G` into `A`, in projective coordinates, for `k < kmax` (`BoothOk`),
pipelined or not (`combJ`): `combJP_ok`, `combJ0_ok`. -/
theorem tcombJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa K.combJ.inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  unfold TCombCfg.combJ
  cases hP : K.pipeOk
  · exact combJ0_ok hL hC hM3 hG hV hpn hb1 hB hk hs hM hF
  · exact combJP_ok hL hC hM3 hG hV hpn hb1 hB hk hP hs hM hF

end VG.Proof.Weierstrass.X86_64
