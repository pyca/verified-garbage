module

-- separate module: the blocks of `forsPk`, a stage of its proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmss
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# SLH-DSA on x86-64, `forsPk`: its blocks

The blocks of `forsPk` (`Impl/SlhDsa/X86_64/Verify.lean`): each lane's tree
`min(t₀ + k, k - 1)`, its leaf number and its signature (`treeOf_ok`), the
prologue and the FORS indices (`fpre_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs setField setFieldR copyWords)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_subi wp_store wp_movzx8 ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add wp_sub wp_and wp_add in_scr in_scr' at_add)

theorem oVar20 : Layout.oVar 2 0 = 2704 := rfl
theorem oVar21 : Layout.oVar 2 1 = 2712 := rfl
theorem oVar24 : Layout.oVar 2 4 = 2736 := rfl
theorem oSave2 (i : Nat) : Layout.oSave 2 i = 2656 + 8 * i := rfl
theorem oFidx_eq : Layout.oFidx = 31328 := rfl
theorem oDigest_eq : Layout.oDigest = 30304 := rfl

/-- `y + x << a`, small. -/
theorem shl_add_nat {x y a : Nat} (h : x * 2 ^ a + y < 2 ^ 64) :
    BitVec.ofNat 64 y + BitVec.ofNat 64 x <<< a = BitVec.ofNat 64 (x * 2 ^ a + y) := by
  have hp := Nat.two_pow_pos a
  have hx : x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x hp) (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show x * 2 ^ a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega), Nat.add_comm]

/-- Lane `k`'s tree `t = min(t₀ + k, k - 1)` (`t₀` in variable 0) in `r10`,
its leaf number `t·2^a + I t` (`I t` the index at `oFidx + 8t`) in `r11`, and
its signature, `sig + n·t·(a + 1)` (`sig` in `r14`), in `rsi`. -/
theorem treeOf_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {k' t₀ : Nat} (hkt : t₀ + k' < 2 ^ 31)
    {s : State} {S sig : Addr} {I : Nat → Nat} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .r10 = BitVec.ofNat 64 (min (t₀ + k') (p.k - 1)) →
      s'.gpr .r11 = BitVec.ofNat 64 (min (t₀ + k') (p.k - 1) * 2 ^ p.a + I (min (t₀ + k') (p.k - 1))) →
      s'.gpr .rsi = sig + BitVec.ofNat 64 (p.n * (min (t₀ + k') (p.k - 1) * (p.a + 1))) →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Verify.treeOf p k' ++ is)) s Q := by
  obtain ⟨t, ht⟩ : ∃ t, t = min (t₀ + k') (p.k - 1) := ⟨_, rfl⟩
  rw [← ht] at k
  have htk : t < p.k := by omega
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  simp only [Impl.SlhDsa.X86_64.Verify.treeOf, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movm (a := at' S (Layout.oVar 2 0))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hbx])
    (by rw [oVar20]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => Levels.wp_cmpi fun s₂' g₂' m₂' r₂' w₂' _ => ?_
  refine wp_mov32i fun s₃ u₃ => wp_sub fun s₄ u₄ => ?_
  refine wp_shri (by decide) (by decide) fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ => ?_
  refine wp_mov32i fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_and fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => ?_
  have hx : s₂'.gpr .r10 = BitVec.ofNat 64 (t₀ + k') := by
    rw [g₂', u₂.gpr, u₁.gpr, hv0, sx_ofNat (by omega)]; exact (BitVec.ofNat_add _ _).symm
  have hx₅ : s₅.gpr .r10 = BitVec.ofNat 64 (t₀ + k') := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hx]
  have ha₅ : s₅.gpr .rax = (BitVec.ofNat 64 (p.k - 1) - BitVec.ofNat 64 (t₀ + k')) >>> 63 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), hx, setw_ofNat32 (by omega)]
  have hc₉ : s₉.gpr .rcx = BitVec.ofNat 64 (t₀ + k') - BitVec.ofNat 64 (p.k - 1) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, hx₅, sx_ofNat (by omega)]
  have hd₉ : s₉.gpr .rdx = 0 - (BitVec.ofNat 64 (p.k - 1) - BitVec.ofNat 64 (t₀ + k')) >>> 63 := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ha₅]; rfl
  have h10 : s₁₁.gpr .r10 = BitVec.ofNat 64 t := by
    rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), hx₅, hc₉, hd₉, ht]
    exact clamp_eq (by omega) (by omega)
  have hg₁₁ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .r10 → s₁₁.gpr g = s.gpr g := fun g h1 h2 h3 h4 => by
    rw [u₁₁.other _ h4, u₁₀.other _ h2, u₉.other _ h3, u₈.other _ h3, u₇.other _ h2, u₆.other _ h2,
      u₅.other _ h1, u₄.other _ h1, u₃.other _ h1, g₂', u₂.other _ h4, u₁.other _ h4]
  have hb₁₁ : s₁₁.gpr .rbx = S := by rw [hg₁₁ _ (by decide) (by decide) (by decide) (by decide), hbx]
  have hm : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂', u₂.mem, u₁.mem]
  have hrd : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, r₂', u₂.rd, u₁.rd]
  have hwr : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂', u₂.wr, u₁.wr]
  have hea : s₁₁.ea (Impl.SlhDsa.X86_64.Fors.fidxR .r10) = at' S (Layout.oFidx + 8 * t) := by
    simp only [Impl.SlhDsa.X86_64.Fors.fidxR, State.ea, hb₁₁, h10, BitVec.ofInt_natCast]
    rw [at', BitVec.add_assoc, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      show t * 8 + Layout.oFidx = Layout.oFidx + 8 * t by omega]
  refine wp_movm hea (by rw [hrd, hwr]; exact in_scr' hw (by rw [oFidx_eq]; omega)) fun s₁₂ u₁₂ => ?_
  refine wp_mov fun s₁₃ u₁₃ => Levels.wp_shl (by omega) (by omega) fun s₁₄ u₁₄ => wp_add fun s₁₅ u₁₅ => ?_
  refine wp_mov fun s₁₆ u₁₆ => Levels.mulN_ok hn (r := .rsi) (tmp := .rax) (by decide) fun s₁₇ h₁₇ g₁₇ m₁₇ r₁₇ w₁₇ => ?_
  refine wp_mov fun s₁₈ u₁₈ => ?_
  have hIt := hIa t htk
  have hta : t * 2 ^ p.a + I t < 2 ^ 32 := by
    have : (t + 1) * 2 ^ p.a ≤ 35 * 2 ^ 14 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) ha)
    rw [Nat.succ_mul] at this; omega
  have h11 : s₁₈.gpr .r11 = BitVec.ofNat 64 (t * 2 ^ p.a + I t) := by
    rw [u₁₈.other _ (by decide), g₁₇ _ (by decide) (by decide), u₁₆.other _ (by decide), u₁₅.gpr,
      u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), h10, hm,
      hI t htk]
    exact shl_add_nat (by omega)
  have htn : t * p.n < 2 ^ 32 := by have := Nat.mul_le_mul (Nat.le_of_lt htk) hn32; omega
  have hsi₁₈ : s₁₈.gpr .rsi = BitVec.ofNat 64 (t * p.n) := by
    rw [u₁₈.other _ (by decide), h₁₇, u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), h10, BitVec.ofNat_mul_ofNat]
  have hax₁₈ : s₁₈.gpr .rax = BitVec.ofNat 64 (t * p.n) := by rw [u₁₈.gpr, ← u₁₈.other .rsi (by decide), hsi₁₈]
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := fun j u => u.gpr .rsi = BitVec.ofNat 64 ((j + 1) * (t * p.n)) ∧
      (∀ g, g ≠ .rsi → u.gpr g = s₁₈.gpr g) ∧ u.mem = s₁₈.mem ∧ u.rd = s₁₈.rd ∧ u.wr = s₁₈.wr) p.a
    ⟨by rw [hsi₁₈, Nat.one_mul], fun _ _ => rfl, rfl, rfl, rfl⟩ fun j hj u ⟨hs, hg, hm', hr', hw'⟩ => ?_)
    fun u ⟨hs, hg, hm', hr', hw'⟩ => ?_)
  · refine wp_add fun u' v' => WP.block_nil ⟨?_, fun g h => by rw [v'.other _ h, hg _ h], by rw [v'.mem, hm'],
      by rw [v'.rd, hr'], by rw [v'.wr, hw']⟩
    rw [v'.gpr, hs, hg _ (by decide), hax₁₈, ← BitVec.ofNat_add, Nat.succ_mul (j + 1)]
  refine wp_add fun s₁₉ u₁₉ => ?_
  have hg₁₈ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s₁₈.gpr g = s.gpr g :=
    fun g h1 h2 h3 h4 h5 h6 => by
      rw [u₁₈.other _ h1, g₁₇ _ h4 h1, u₁₆.other _ h4, u₁₅.other _ h6, u₁₄.other _ h1, u₁₃.other _ h1,
        u₁₂.other _ h6, hg₁₁ _ h1 h2 h3 h5]
  refine k s₁₉ (fun g h1 h2 h3 h4 h5 h6 => by rw [u₁₉.other _ h4, hg _ h4, hg₁₈ _ h1 h2 h3 h4 h5 h6])
    (by rw [u₁₉.mem, hm', u₁₈.mem, m₁₇, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, hm])
    (by rw [u₁₉.rd, hr', u₁₈.rd, r₁₇, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, hrd])
    (by rw [u₁₉.wr, hw', u₁₈.wr, w₁₇, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, hwr])
    (by rw [u₁₉.other _ (by decide), hg _ (by decide), u₁₈.other _ (by decide), g₁₇ _ (by decide) (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), h10])
    (by rw [u₁₉.other _ (by decide), hg _ (by decide), h11]) ?_
  rw [u₁₉.gpr, hs, hg _ (by decide), hg₁₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    h14, BitVec.add_comm]
  congr 2
  rw [Nat.mul_comm (p.a + 1), Nat.mul_comm t p.n, Nat.mul_assoc]

/-! ## The prologue -/

/-- A block of `K` pieces, the piece `j` from `P j` to `P (j + 1)`. -/
theorem wp_rangeFlatMapV {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block (f j)) t (P (j + 1))) →
      WP isa (.block ((List.range K).flatMap f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (wp_rangeFlatMapV K h0 fun j hj => hs j (by omega)) fun t ht => hs K (by omega) t ht)

/-- After `Fors.pro`. -/
structure FPro (s t : State) : Prop where
  bx : t.gpr .rbx = s.gpr .rdi
  r12 : t.gpr .r12 = s.gpr .rdx
  r14 : t.gpr .r14 = s.gpr .rsi
  rbp : t.gpr .rbp = s.gpr .rdi + BitVec.ofNat 64 Layout.oDigest
  r15 : t.gpr .r15 = s.gpr .rdi + BitVec.ofNat 64 Layout.oMsg
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 2 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩] s.mem t.mem

theorem fpro_ok {s : State} (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.SlhDsa.X86_64.Fors.pro) s (FPro s) := by
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩ (at' (s.gpr .rdi) (2656 + 8 * j)) 8 :=
    fun j hj => by
      rw [oSave2, show at' (s.gpr .rdi) (2656 + 8 * j) = at' (s.gpr .rdi) (2656 + 8 * 0) + BitVec.ofNat 64 (8 * j) by
        rw [at_add]]
      exact Offset.contains_base _ (by omega) (by omega)
  unfold Impl.SlhDsa.X86_64.Fors.pro
  refine WP.block_append (WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 2 i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rdi) (Layout.oSave 2 0), 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_) fun t ht => ?_)
  · refine wp_store (a := at' (s.gpr .rdi) (Layout.oSave 2 j)) (by rw [ea_at, g]) (by
      rw [w, oSave2]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, g]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave2, oSave2]; omega) (by rw [oSave2]; omega)
          (by rw [oSave2]; omega)) (by decide), sv i (by omega)]
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (by rw [oSave2]; exact hc j (by omega))
  obtain ⟨g, r, w, sv, f⟩ := ht
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => wp_addi fun t₅ u₅ => ?_
  refine wp_mov fun t₆ u₆ => wp_addi fun t₇ u₇ => WP.block_nil ?_
  have hm₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w],
    fun i hi => by rw [hm₇]; exact sv i hi, by rw [hm₇]; exact f⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), g, sx_ofNat (by rw [oDigest_eq]; omega)]
  · rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), g, sx_ofNat (by rw [show Layout.oMsg = 30496 from rfl]; omega)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]

/-! ## The indices -/

/-- `or r64, r64`. -/
theorem wp_orR {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Proof.Sha3.X86_64.Upd.flags _ _ _ _ _ _))

/-- Three bytes, big-endian. -/
theorem bytes3_val (x y z : Byte) :
    ((x.setWidth 64 <<< 16 ||| y.setWidth 64 <<< 8) ||| z.setWidth 64 : BitVec 64) =
      BitVec.ofNat 64 (x.toNat * 65536 + y.toNat * 256 + z.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show z.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show x.toNat * 2 ^ 16 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show y.toNat * 2 ^ 8 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  have h1 := Nat.two_pow_add_eq_or_of_lt (i := 16) (b := y.toNat * 2 ^ 8) (by omega) x.toNat
  have h2 := Nat.two_pow_add_eq_or_of_lt (i := 8) (b := z.toNat) hz (256 * x.toNat + y.toNat)
  rw [Nat.mul_comm x.toNat, ← h1, show 2 ^ 16 * x.toNat + y.toNat * 2 ^ 8 = 2 ^ 8 * (256 * x.toNat + y.toNat) by omega,
    ← h2]

/-- `v & (2^a - 1)`. -/
theorem and_mask {v a : Nat} (ha : a ≤ 30) :
    BitVec.ofNat 64 v &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ a - 1)) = BitVec.ofNat 64 (v % 2 ^ a) := by
  have hp : 2 ^ a ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) ha
  rw [sx_ofNat (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ a - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos a)) (by omega)),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show a ≤ 64 by omega))]

/-- The digit of index `t`: bits of the three bytes of the digest from byte
`⌊t·a / 8⌋`. -/
def idx3 (m : Mem) (S : Addr) (a t : Nat) : Nat :=
  ((m (at' S (Layout.oDigest + t * a / 8))).toNat * 65536 + (m (at' S (Layout.oDigest + t * a / 8 + 1))).toNat * 256 +
    (m (at' S (Layout.oDigest + t * a / 8 + 2))).toNat) / 2 ^ (24 - t * a % 8 - a) % 2 ^ a

/-- `Fors.index t`: the digit to `oFidx + 8t`. -/
theorem index_ok {a t : Nat} (ha1 : 1 ≤ a) (ha : a ≤ 14) (ht : t * a / 8 + 3 ≤ 64) {s : State} {S : Addr}
    {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (hbp : s.gpr .rbp = S + BitVec.ofNat 64 Layout.oDigest)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (htk : t < 35)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (at' S (Layout.oFidx + 8 * t)) (BitVec.ofNat 64 (idx3 s.mem S a t)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Fors.index a t ++ is)) s Q := by
  have hq := Nat.mod_lt (t * a) (show 0 < 8 by decide)
  have hD := oDigest_eq
  have hdg : ∀ j, j < 3 → (s.ea (Impl.Sha3.X86_64.at_ .rbp (t * a / 8 + j))) = at' S (Layout.oDigest + t * a / 8 + j) :=
    fun j _ => by rw [ea_at, hbp, add_add, Nat.add_assoc]
  simp only [Impl.SlhDsa.X86_64.Fors.index, List.cons_append, List.nil_append]
  refine wp_movzx8 (hdg 0 (by decide)) (in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine Levels.wp_shl (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_movzx8 (a := at' S (Layout.oDigest + t * a / 8 + 1))
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbp, add_add, Nat.add_assoc])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_scr' hw (by omega)) fun s₃ u₃ => ?_
  refine Levels.wp_shl (by decide) (by decide) fun s₄ u₄ => wp_orR fun s₅ u₅ => ?_
  refine wp_movzx8 (a := at' S (Layout.oDigest + t * a / 8 + 2))
    (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbp, add_add, Nat.add_assoc])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_scr' hw (by omega))
    fun s₆ u₆ => ?_
  refine wp_orR fun s₇ u₇ => wp_shri (by omega) (by omega) fun s₈ u₈ => wp_andi fun s₉ u₉ => ?_
  have hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg₉ : ∀ g, g ≠ .rax → g ≠ .rcx → s₉.gpr g = s.gpr g := fun g h1 h2 => by
    rw [u₉.other _ h1, u₈.other _ h1, u₇.other _ h1, u₆.other _ h2, u₅.other _ h1, u₄.other _ h2, u₃.other _ h2,
      u₂.other _ h1, u₁.other _ h1]
  have hrax : s₉.gpr .rax = BitVec.ofNat 64 (idx3 s.mem S a t) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₆.other .rax (by decide), u₅.gpr, u₄.gpr, u₄.other .rax (by decide),
      u₃.gpr, u₃.other .rax (by decide), u₂.gpr, u₁.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      Nat.add_zero, bytes3_val, shr_ofNat _ _ (by
        have := (s.mem (at' S (Layout.oDigest + t * a / 8))).isLt
        have := (s.mem (at' S (Layout.oDigest + t * a / 8 + 1))).isLt
        have := (s.mem (at' S (Layout.oDigest + t * a / 8 + 2))).isLt
        omega), and_mask (by omega)]
    rfl
  refine wp_store (a := at' S (Layout.oFidx + 8 * t)) (by rw [ea_at, hg₉ _ (by decide) (by decide), hbx])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact in_scr hw (by rw [oFidx_eq]; omega))
    fun s' g' m' r' w' => k s' (fun g h1 h2 => by rw [g', hg₉ _ h1 h2])
      (by rw [r', u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [w', u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [m', hrax, hm₉])

/-- `pre` reads only the bytes below `i`. -/
theorem pre_congr {X Y : List Byte} : ∀ i, (∀ j < i, X.getD j 0 = Y.getD j 0) → pre X i = pre Y i
  | 0, _ => rfl
  | i + 1, h => by rw [pre_succ, pre_succ, pre_congr i fun j hj => h j (by omega), h i (by omega)]

/-- The digit `Fors.index t` computes is index `t` of `base_2b(md, a, k)`. -/
theorem idx3_eq {p : Params} (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14) (hmd : p.mdLen + 2 ≤ 64) (m : Mem) (S : Addr)
    {t : Nat} (ht : t < p.k) : idx3 m S p.a t = (base2b (mdAt p m S) p.a p.k).getD t 0 := by
  have hta : t * p.a + p.a ≤ p.k * p.a := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
  have hmd' : p.mdLen = (p.k * p.a + 7) / 8 := rfl
  have hneed : need p.a t ≤ p.mdLen := by
    simp only [need, hmd']; rw [Nat.succ_mul]; omega
  have ho : t * p.a / 8 < p.mdLen := by rw [hmd']; omega
  rw [base2b_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
    Option.getD_some]
  obtain ⟨X, hX⟩ : ∃ X, X = bytesAt m (at' S Layout.oDigest) (p.mdLen + 2) := ⟨_, rfl⟩
  have e : SlhDsa.digitAt (mdAt p m S) p.a t = SlhDsa.digitAt X p.a t := by
    simp only [SlhDsa.digitAt]
    rw [pre_congr (Y := X) _ fun j hj => by
      rw [hX, mdAt, bytesAt_getD _ _ (by omega), bytesAt_getD _ _ (by omega)]]
  rw [e, digitAt_three X ha t, hX, bytesAt_getD _ _ (by omega), bytesAt_getD _ _ (by omega),
    bytesAt_getD _ _ (by omega), at_add, at_add, at_add]
  simp only [idx3, Nat.add_assoc]

/-- The memory after `Fors.pro` and the indices. -/
structure FPre (p : Params) (s : State) (S : Addr) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = s.gpr .rdx
  r14 : t.gpr .r14 = s.gpr .rsi
  r15 : t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 2 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  v0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 0
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 =
    BitVec.ofNat 64 ((base2b (mdAt p s.mem S) p.a p.k).getD i 0)
  frame : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] s.mem t.mem

/-- `forsPk`'s prologue: the registers saved in frame 2, the indices. -/
theorem fpre_ok {p : Params} (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14) (hk : p.k ≤ 35) (hmd : p.mdLen + 2 ≤ 64) {s : State}
    (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (Impl.SlhDsa.X86_64.Fors.pro ++ Impl.SlhDsa.X86_64.Fors.indices p.a p.k)) s
      (FPre p s (s.gpr .rdi)) := by
  obtain ⟨S, hS⟩ : ∃ S, S = s.gpr .rdi := ⟨_, rfl⟩
  rw [← hS] at hw ⊢
  have hmd' : p.mdLen = (p.k * p.a + 7) / 8 := rfl
  have eF := oFidx_eq
  have eD := oDigest_eq
  refine WP.block_append (WP.mono (fpro_ok (by rw [← hS]; exact hw)) fun t ht => ?_)
  have hbx0 : t.gpr .rbx = S := by rw [ht.bx, hS]
  have hbp0 : t.gpr .rbp = S + BitVec.ofNat 64 Layout.oDigest := by rw [ht.rbp, hS]
  have hr150 : t.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg := by rw [ht.r15, hS]
  have hsv0 : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 2 i)) 64 = s.gpr (savedRegs.getD i .rbx) := by
    rw [hS]; exact ht.saved
  have hfr0 : Frame [⟨at' S (Layout.oSave 2 0), 48⟩] s.mem t.mem := by rw [hS]; exact ht.frame
  have hwt : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [ht.wr]; exact hw
  unfold Impl.SlhDsa.X86_64.Fors.indices
  -- the digest, which the saves leave
  have hdig : ∀ {m : Mem}, Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩] s.mem m →
      ∀ q < 64, m (at' S (Layout.oDigest + q)) = s.mem (at' S (Layout.oDigest + q)) := fun hf q hq =>
    frame_at hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [oSave2]; exact Offset.disjoint S (by omega) (by omega) (by omega)
      · exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hidx3 : ∀ {m : Mem}, Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩] s.mem m →
      ∀ j < p.k, idx3 m S p.a j = idx3 s.mem S p.a j := fun hf j hj => by
    have : j * p.a + p.a ≤ p.k * p.a := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    simp only [idx3]
    rw [hdig hf _ (by omega), show Layout.oDigest + j * p.a / 8 + 1 = Layout.oDigest + (j * p.a / 8 + 1) by omega,
      show Layout.oDigest + j * p.a / 8 + 2 = Layout.oDigest + (j * p.a / 8 + 2) by omega,
      hdig hf _ (by omega), hdig hf _ (by omega)]
  have hF2 : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩] s.mem t.mem :=
    hfr0.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  refine WP.block_append (WP.mono (wp_rangeFlatMapV (P := fun j u => (∀ g, g ≠ .rax → g ≠ .rcx → u.gpr g = t.gpr g) ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧
      (∀ i < j, u.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (idx3 s.mem S p.a i)) ∧
      Frame [⟨at' S Layout.oFidx, 8 * j⟩] t.mem u.mem) p.k
    ⟨fun _ _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun j hj u ⟨g, r, w, v, f⟩ => ?_) fun u ⟨g, r, w, v, f⟩ => ?_)
  · have hju : j * p.a / 8 + 3 ≤ 64 := by
      have : j * p.a + p.a ≤ p.k * p.a := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
      omega
    have hFu : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩] s.mem u.mem :=
      hF2.trans (f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub S (by omega) (by omega)⟩)
    have h := index_ok (a := p.a) (t := j) (is := []) ha1 ha hju (s := u) (S := S) (Q := fun u' =>
        (∀ g, g ≠ .rax → g ≠ .rcx → u'.gpr g = t.gpr g) ∧ u'.rd = t.rd ∧ u'.wr = t.wr ∧
        (∀ i < j + 1, u'.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (idx3 s.mem S p.a i)) ∧
        Frame [⟨at' S Layout.oFidx, 8 * (j + 1)⟩] t.mem u'.mem)
      (by rw [g _ (by decide) (by decide), hbx0]) (by rw [g _ (by decide) (by decide), hbp0])
      (by rw [w]; exact hwt) (by omega) fun u' g' r' w' m' => WP.block_nil ⟨fun x h1 h2 => by
        rw [g' _ h1 h2, g _ h1 h2], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rwa [List.append_nil] at h
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, hidx3 hFu _ hj]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), v i (by omega)]
    · rw [m']
      exact (f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains S (by omega) (by omega) (by omega))
  -- variables 0, 4 and 1
  have hbx : u.gpr .rbx = S := by rw [g _ (by decide) (by decide), hbx0]
  refine wp_mov32i fun u₁ v₁ => wp_store (a := at' S (Layout.oVar 2 0))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, v₁.other _ (by decide), hbx])
    (by rw [v₁.wr, w, ht.wr, oVar20]; exact in_scr hw (by omega)) fun u₂ g₂ m₂ r₂ w₂ => ?_
  refine wp_store (a := at' S (Layout.oVar 2 4))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, g₂, v₁.other _ (by decide), hbx])
    (by rw [w₂, v₁.wr, w, ht.wr, oVar24]; exact in_scr hw (by omega)) fun u₃ g₃ m₃ r₃ w₃ => ?_
  refine wp_store (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, g₃, g₂, v₁.other _ (by decide), hbx])
    (by rw [w₃, w₂, v₁.wr, w, ht.wr, oVar21]; exact in_scr hw (by omega)) fun u₄ g₄ m₄ r₄ w₄ => WP.block_nil ?_
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → u₄.gpr r = t.gpr r := fun r h1 h2 => by
    rw [g₄, g₃, g₂, v₁.other _ h1, g _ h1 h2]
  have hm₄ : u₄.mem = ((u.mem.writeW (at' S (Layout.oVar 2 0)) (BitVec.ofNat 64 0)).writeW (at' S (Layout.oVar 2 4))
      (BitVec.ofNat 64 0)).writeW (at' S (Layout.oVar 2 1)) (u₃.gpr .r14) := by
    rw [m₄, m₃, m₂, g₂, v₁.gpr, v₁.mem, mov32_zero]; rfl
  have F₄ : Frame [⟨at' S (Layout.oVar 2 0), 40⟩] u.mem u₄.mem := by
    rw [hm₄]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_
    · rw [oVar20]; exact Offset.contains S (by omega) (by omega) (by omega)
    · rw [oVar24, oVar20]; exact Offset.contains S (by omega) (by omega) (by omega)
    · rw [oVar21, oVar20]; exact Offset.contains S (by omega) (by omega) (by omega)
  have Fs : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] s.mem u₄.mem :=
    (hfr0.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      ((f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub S (by omega) (by omega)⟩).trans
      (F₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have dV : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2704 ∨ 2744 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.oVar 2 0), 40⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [oVar20]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  refine ⟨by rw [hg _ (by decide) (by decide), hbx0], by rw [hg _ (by decide) (by decide), ht.r12],
    by rw [hg _ (by decide) (by decide), ht.r14], by rw [hg _ (by decide) (by decide), hr150],
    by rw [hg _ (by decide) (by decide), ht.sp], by rw [r₄, r₃, r₂, v₁.rd, r, ht.rd],
    by rw [w₄, w₃, w₂, v₁.wr, w, ht.wr], fun i hi => ?_, ?_, fun i hi => ?_, Fs⟩
  · rw [F₄.readW (Region.contains_self _ _) (dV (by rw [oSave2]; omega) (by rw [oSave2]; omega)) (by decide),
      f.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [oSave2]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide)]
    exact hsv0 i hi
  · rw [hm₄, Mem.readW_writeW_sep (Offset.sep _ (by rw [oVar20, oVar21]; omega) (by rw [oVar20]; omega)
      (by rw [oVar21]; omega)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by rw [oVar20, oVar24]; omega)
      (by rw [oVar20]; omega) (by rw [oVar24]; omega)) (by decide), Mem.readW_writeW_self64]
  · rw [F₄.readW (Region.contains_self _ _) (dV (by omega) (by omega)) (by decide), v i hi,
      idx3_eq ha1 ha hmd s.mem S hi]

/-! ## The leaves -/

/-- Lane `k`'s fields `ty`, `kp`, `z`, `i` and its message `X`. -/
structure FLane (p : Params) (S : Addr) (k' kp z i : Nat) (X : List Byte) (m : Mem) : Prop where
  fields : bytesAt m (at' S (Layout.laneA k' + p.n + 16)) 16 = toByte 3 4 ++ toByte kp 4 ++ toByte z 4 ++ toByte i 4
  value : bytesAt m (at' S (Layout.laneA k' + p.n + 32)) p.n = X

/-- Tree `t`'s signature: its private key value at `n·t·(a + 1)`. -/
theorem forsSig_le {p : Params} {t : Nat} (ht : t < p.k) {j : Nat} (hj : j ≤ p.a) :
    p.n * (t * (p.a + 1)) + p.n * j + p.n ≤ p.forsSigLen := by
  have e : p.forsSigLen = p.n * (p.k * (p.a + 1)) := by
    simp only [Params.forsSigLen, Nat.add_comm 1 p.a, Nat.mul_comm _ p.n]
  rw [e, ← Nat.mul_add, ← Nat.mul_succ]
  refine Nat.mul_le_mul_left _ ?_
  have : (t + 1) * (p.a + 1) ≤ p.k * (p.a + 1) := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at this; omega

/-- Lane `k`'s leaf in `forsLeaves`: its address's type (`FORS_TREE`), key
pair, height 0 and tree index the leaf `t·2^a + I t` of its tree
`t = min(t₀ + k, k - 1)`, its message the tree's private key value. -/
theorem leafLane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {k' t₀ kp : Nat} (hk' : k' < 4) (ht₀ : t₀ + 4 < 2 ^ 31) (hkp : kp < 2 ^ 32)
    {s : State} {S sig : Addr} {I : Nat → Nat} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 kp) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      FLane p S k' kp 0 (min (t₀ + k') (p.k - 1) * 2 ^ p.a + I (min (t₀ + k') (p.k - 1)))
        (bytesAt s.mem (sig + BitVec.ofNat 64 (p.n * (min (t₀ + k') (p.k - 1) * (p.a + 1)))) p.n) s'.mem →
      Frame [⟨at' S (Layout.laneA k' + p.n + 16), 16 + p.n⟩] s.mem s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
      setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 3 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11 ++
      copyWords .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  rw [hadr, hmsg]
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hla' : 3296 ≤ Layout.laneA k' := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  obtain ⟨t, ht⟩ : ∃ t, t = min (t₀ + k') (p.k - 1) := ⟨_, rfl⟩
  rw [← ht] at k
  have htk : t < p.k := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneA k' + p.n := ⟨_, rfl⟩
  have hdj : ∀ a c : Nat, a + 4 ≤ c ∨ c + 4 ≤ a → a + 4 ≤ 2 ^ 16 → c + 4 ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 a, 4⟩ r :=
    fun a c h h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have hsub : ∀ {o l : Nat}, A + 16 ≤ o → o + l ≤ A + 32 + p.n →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, l⟩ : Region)], ∃ r' ∈ [(⟨at' S (Layout.laneA k' + p.n + 16), 16 + p.n⟩ : Region)],
        Region.Sub r r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
  simp only [List.append_assoc]
  refine treeOf_ok hn ha1 ha hk1 hk (by omega) hbx h14 hv0 hI hIa hw fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ hsi₁ => ?_
  rw [← ht] at h10₁ h11₁ hsi₁
  have hb₁ : s₁.gpr .rbx = S := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hin : ∀ (u : State) (o : Nat), u.gpr .rbx = S → u.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions u.wr (u.gpr .rbx + BitVec.ofNat 64 o) 4 := fun u o h₁ h₂ ho => by
    rw [h₁, h₂]; exact in_scr hw ho
  refine setField_ok (by decide) (by decide) (hin s₁ _ hb₁ w₁ (by omega)) fun s₂ f₂ => ?_
  rw [hb₁] at f₂
  have hb₂ : s₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 kp := by
    rw [f₂.gpr _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h12]
  refine setFieldR_ok (by decide) (by rw [h12₂, hkp']; exact hkp) (hin s₂ _ hb₂ (by rw [f₂.wr, w₁]) (by omega))
    fun s₃ f₃ => ?_
  rw [hb₂, h12₂, hkp'] at f₃
  have hb₃ : s₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  refine setField_ok (by decide) (by decide) (hin s₃ _ hb₃ (by rw [f₃.wr, f₂.wr, w₁]) (by omega)) fun s₄ f₄ => ?_
  rw [hb₃] at f₄
  have hb₄ : s₄.gpr .rbx = S := by rw [f₄.gpr _ (by decide), hb₃]
  have hIt := hIa t htk
  have hL : t * 2 ^ p.a + I t < 2 ^ 32 := by
    have : (t + 1) * 2 ^ p.a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) ha)
    rw [Nat.succ_mul] at this; omega
  have hL' : (BitVec.ofNat 64 (t * 2 ^ p.a + I t)).toNat = t * 2 ^ p.a + I t := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h11₄ : s₄.gpr .r11 = BitVec.ofNat 64 (t * 2 ^ p.a + I t) := by
    rw [f₄.gpr _ (by decide), f₃.gpr _ (by decide), f₂.gpr _ (by decide), h11₁]
  refine setFieldR_ok (by decide) (by rw [h11₄, hL']; exact hL) (hin s₄ _ hb₄ (by rw [f₄.wr, f₃.wr, f₂.wr, w₁]) (by omega))
    fun s₅ f₅ => ?_
  rw [hb₄, h11₄, hL'] at f₅
  have hb₅ : s₅.gpr .rbx = S := by rw [f₅.gpr _ (by decide), hb₄]
  have hsi₅ : s₅.gpr .rsi = sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1))) := by
    rw [f₅.gpr _ (by decide), f₄.gpr _ (by decide), f₃.gpr _ (by decide), f₂.gpr _ (by decide), hsi₁]
  have hw₅ : s₅.wr = s.wr := by rw [f₅.wr, f₄.wr, f₃.wr, f₂.wr, w₁]
  have hr₅ : s₅.rd = s.rd := by rw [f₅.rd, f₄.rd, f₃.rd, f₂.rd, r₁]
  -- the private key value
  have hsl := forsSig_le htk (Nat.zero_le p.a)
  rw [Nat.mul_zero, Nat.add_zero] at hsl
  refine WP.block_append (WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
    (fun j hj => by rw [hw₅, hb₅]; exact in_scr hw (by omega))
    (fun j hj => ⟨_, List.mem_append_left _ (by rw [hr₅]; exact hsr), by
      rw [hsi₅, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add]
      exact Offset.contains_base sig (by omega) (by omega)⟩)
    (by
      rw [hb₅, hsi₅, BitVec.add_assoc, ← BitVec.ofNat_add, e8, Nat.add_zero]
      exact ((hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S (by omega))).symm)
    (by omega) (by omega)) fun s₆ c₆ => ?_)
  rw [hb₅, hsi₅, e8, BitVec.add_zero] at c₆
  have hsg : bytesAt s₅.mem (sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1)))) p.n =
      bytesAt s.mem (sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1)))) p.n := by
    have hd : ∀ {o : Nat}, o + 4 ≤ 2 ^ 16 → ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, 4⟩ : Region)],
        Region.Disjoint ⟨sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1))), p.n⟩ r := fun ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hss.sub_left (Offset.sub_base sig (by omega))).sub_right (Offset.sub_base S ho)
    rw [bytesAt_frame f₅.frame (hd (by omega)) (by omega), bytesAt_frame f₄.frame (hd (by omega)) (by omega),
      bytesAt_frame f₃.frame (hd (by omega)) (by omega), bytesAt_frame f₂.frame (hd (by omega)) (by omega), m₁]
  have eA : at' S (Layout.laneA k' + p.n + 32) = S + BitVec.ofNat 64 (Layout.laneA k' + (p.n + 32)) := by
    rw [at', Nat.add_assoc]
  refine k s₆ (fun g h1 h2 h3 h4 h5 h6 => by
      rw [c₆.gpr _ h1, f₅.gpr _ h1, f₄.gpr _ h1, f₃.gpr _ h1, f₂.gpr _ h1, g₁ _ h1 h2 h3 h4 h5 h6])
    (by rw [c₆.rd, hr₅]) (by rw [c₆.wr, hw₅]) ⟨?_, ?_⟩ ?_
  · have hm : ∀ {o : Nat}, A + 16 ≤ o → o + 4 ≤ A + 32 →
        bytesAt s₆.mem (S + BitVec.ofNat 64 o) 4 = bytesAt s₅.mem (S + BitVec.ofNat 64 o) 4 := fun h₁ h₂ =>
      bytesAt_frame c₆.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by decide)
    have e₄ : bytesAt s₆.mem (S + BitVec.ofNat 64 (A + 28)) 4 = toByte (t * 2 ^ p.a + I t) 4 := by
      rw [hm (by omega) (by omega), hA, f₅.bytes]
    have e₃ : bytesAt s₆.mem (S + BitVec.ofNat 64 (A + 24)) 4 = toByte 0 4 := by
      rw [hm (by omega) (by omega), bytesAt_frame f₅.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hA,
        f₄.bytes]
    have e₂ : bytesAt s₆.mem (S + BitVec.ofNat 64 (A + 20)) 4 = toByte kp 4 := by
      rw [hm (by omega) (by omega), bytesAt_frame f₅.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hA, f₃.bytes]
    have e₁ : bytesAt s₆.mem (S + BitVec.ofNat 64 (A + 16)) 4 = toByte 3 4 := by
      rw [hm (by omega) (by omega), bytesAt_frame f₅.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), hA, f₂.bytes]
    simp only [List.append_assoc]
    rw [← hA, bytesAt_split4, show A + 16 + 4 = A + 20 by omega, show A + 16 + 8 = A + 24 by omega,
      show A + 16 + 12 = A + 28 by omega, e₁, e₂, e₃, e₄]
  · rw [← hsg]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [eA, c₆.bytes i (List.mem_range.mp hi)]
  · have F₅ : Frame [⟨S + BitVec.ofNat 64 (A + 28), 4⟩] s₄.mem s₅.mem := by rw [hA]; exact f₅.frame
    have F₄ : Frame [⟨S + BitVec.ofNat 64 (A + 24), 4⟩] s₃.mem s₄.mem := by rw [hA]; exact f₄.frame
    have F₃ : Frame [⟨S + BitVec.ofNat 64 (A + 20), 4⟩] s₂.mem s₃.mem := by rw [hA]; exact f₃.frame
    have F₂ : Frame [⟨S + BitVec.ofNat 64 (A + 16), 4⟩] s₁.mem s₂.mem := by rw [hA]; exact f₂.frame
    have F₆ : Frame [⟨S + BitVec.ofNat 64 (A + 32), p.n⟩] s₅.mem s₆.mem := by
      rw [hA, show Layout.laneA k' + p.n + 32 = Layout.laneA k' + (p.n + 32) by omega]; exact c₆.frame
    rw [← m₁]
    exact (F₂.sub (hsub (by omega) (by omega))).trans ((F₃.sub (hsub (by omega) (by omega))).trans
      ((F₄.sub (hsub (by omega) (by omega))).trans ((F₅.sub (hsub (by omega) (by omega))).trans
        (F₆.sub (hsub (by omega) (by omega))))))

/-- Lane `k`'s tree in the group from `t₀`. -/
abbrev tOf (p : Params) (t₀ k' : Nat) : Nat := min (t₀ + k') (p.k - 1)

/-- Lane `k`'s leaf number. -/
abbrev lOf (p : Params) (I : Nat → Nat) (t₀ k' : Nat) : Nat := tOf p t₀ k' * 2 ^ p.a + I (tOf p t₀ k')

/-- Lane `k`'s private key value. -/
abbrev skOf (p : Params) (m : Mem) (sig : Addr) (t₀ k' : Nat) : List Byte :=
  bytesAt m (sig + BitVec.ofNat 64 (p.n * (tOf p t₀ k' * (p.a + 1)))) p.n

/-- The parts of the lanes `A` the leaves write. -/
def laneR (p : Params) (S : Addr) : List Region :=
  (List.range 4).map (fun k => ⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩)

/-- What a group's leaves and heights change: `work` but its table, variable
1 of frame 2, the lanes `A` but their `PK.seed` and `a16`, and the stack below
`sp`. -/
def gFrame (p : Params) (S sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 2 1), 8⟩] ++
    (List.range 4).map (fun k => ⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩) ++ [below sp stack]

theorem gFrame_sub (p : Params) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ gFrame p S sp stack, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r' := by
  intro r hr
  simp only [gFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
      fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), fun _ h => h⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
      Offset.sub S (by rw [oVar21]; simp only [Layout.oVars]; omega) (by rw [oVar21]; simp only [Layout.oVars]; omega)⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_cons_self ..⟩))), fun _ h => h⟩
  · exact below_changes S _ _

/-- A part of `scratch` outside what `gFrame` lists. -/
theorem gFrame_disj {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {o l : Nat} (h₂ : o + l ≤ 2 ^ 16)
    (h : (1600 ≤ o ∧ o + l ≤ 2368) ∨ (2400 ≤ o ∧ o + l ≤ 2712) ∨ (2720 ≤ o ∧ o + l ≤ 3296) ∨
      (∃ k < 4, Layout.laneA k ≤ o ∧ o + l ≤ Layout.laneA k + p.n + 16) ∨ 3808 ≤ o) :
    ∀ r ∈ gFrame p S sp stack, Region.Disjoint ⟨at' S o, l⟩ r := by
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  intro r hr
  simp only [gFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · rcases h with h | h | h | ⟨k, hk, h⟩ | h <;> (try rw [eA] at h) <;> exact Offset.disjoint_base S (by omega) (by omega)
  · rcases h with h | h | h | ⟨k, hk, h⟩ | h <;> (try rw [eA] at h) <;> exact Offset.disjoint S (by omega) (by omega) (by omega)
  · rw [oVar21]
    rcases h with h | h | h | ⟨k, hk, h⟩ | h <;> (try rw [eA] at h) <;> exact Offset.disjoint S (by omega) (by omega) (by omega)
  · rw [eA]; simp only [Layout.strideA]
    rcases h with h | h | h | ⟨k, hk, h⟩ | h
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · rw [eA] at h
      rcases Nat.lt_or_ge k c with h' | h'
      · exact Offset.disjoint S (by omega) (by omega) (by omega)
      · rcases Nat.lt_or_ge c k with h'' | h''
        · exact Offset.disjoint S (by omega) (by omega) (by omega)
        · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
  · exact (hstk.sub_right (Offset.sub_base S h₂)).symm

/-- A region outside `scratch` and the stack is outside `gFrame`. -/
theorem gFrame_disj' {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat} {R : Region}
    (h₁ : R.Disjoint ⟨S, 2 ^ 16⟩) (h₂ : R.Disjoint (below sp stack)) :
    ∀ r ∈ gFrame p S sp stack, R.Disjoint r := by
  intro r hr
  simp only [gFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
  · exact h₁.sub_right (Region.sub_prefix (by decide))
  · exact h₁.sub_right (Offset.sub_base S (by decide))
  · exact h₁.sub_right (Offset.sub_base S (by rw [oVar21]; omega))
  · exact h₁.sub_right (Offset.sub_base S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega))
  · exact h₂

/-- The leaves after the lanes below `K`. -/
structure LvInv (p : Params) (S sig : Addr) (kp t₀ : Nat) (I : Nat → Nat) (s₀ : State) (K : Nat) (u : State) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  frame : Frame (laneR p S) s₀.mem u.mem
  done : ∀ k < K, FLane p S k kp 0 (lOf p I t₀ k) (skOf p s₀.mem sig t₀ k) u.mem

/-- A part of `scratch` outside the lanes `A` is outside `laneR`. -/
theorem laneR_disj {p : Params} (hn : p.n ≤ 32) (S : Addr) {o l : Nat} (h₁ : o + l ≤ 2 ^ 16)
    (h₂ : ∀ c < 4, o + l ≤ Layout.laneA c + p.n + 16 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) :
    ∀ r ∈ laneR p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [laneR, List.mem_map, List.mem_range] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  have := h₂ c hc
  have eA : Layout.laneA c = 3296 + 128 * c := rfl
  rw [eA] at this ⊢
  exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- One lane of the leaves. -/
theorem lvstep {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {S sig : Addr} {kp t₀ K : Nat} {I : Nat → Nat} {s₀ u : State} (hK : K < 4)
    (ht₀ : t₀ + 4 < 2 ^ 31) (hkp : kp < 2 ^ 32)
    (hbx : s₀.gpr .rbx = S) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 kp) (h14 : s₀.gpr .r14 = sig)
    (hv0 : s₀.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s₀.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s₀.wr) (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s₀.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hu : LvInv p S sig kp t₀ I s₀ K u) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', LvInv p S sig kp t₀ I s₀ (K + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.treeOf p K ++
      setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 3 ++
      setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
      setField .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
      setFieldR .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11 ++
      copyWords .rbx (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rsi 0 (p.n / 8)) ++ is)) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hg : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g := hu.gpr
  have hR : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 3296 ∨ 3808 ≤ o) → ∀ r ∈ laneR p S, Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ => laneR_disj hn32 S h₁ fun c hc => by rw [eA]; omega
  have hsigR : ∀ {o l : Nat}, o + l ≤ p.forsSigLen → ∀ r ∈ laneR p S,
      Region.Disjoint ⟨sig + BitVec.ofNat 64 o, l⟩ r := fun h r hr => by
    simp only [laneR, List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact (hss.sub_left (Offset.sub_base sig h)).sub_right (Offset.sub_base S (by rw [eA]; omega))
  refine leafLane_ok hn ha1 ha hk1 hk hK ht₀ hkp (I := I) (by rw [hg _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hbx]) (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h12])
    (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h14])
    (by rw [hu.frame.readW (Region.contains_self _ _) (hR (by rw [oVar20]; omega) (by rw [oVar20]; omega)) (by decide), hv0])
    (fun t ht => by
      rw [hu.frame.readW (Region.contains_self _ _) (hR (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)) (by decide),
        hI t ht])
    hIa (by rw [hu.wr]; exact hw) (by rw [hu.rd]; exact hsr) hsfit hss fun u' g' r' w' li F' => k u' ?_
  have hKd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
      (o + l ≤ Layout.laneA K + p.n + 16 ∨ Layout.laneA K + 2 * p.n + 32 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneA K + p.n + 16), 16 + p.n⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eA] at h₂ ⊢; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hsl := forsSig_le (p := p) (t := tOf p t₀ K) (by simp only [tOf]; omega) (Nat.zero_le p.a)
  rw [Nat.mul_zero, Nat.add_zero] at hsl
  have hsig : skOf p u.mem sig t₀ K = skOf p s₀.mem sig t₀ K :=
    bytesAt_frame hu.frame (hsigR hsl) (by omega)
  refine ⟨fun g h1 h2 h3 h4 h5 h6 => by rw [g' _ h1 h2 h3 h4 h5 h6, hg _ h1 h2 h3 h4 h5 h6],
    by rw [r', hu.rd], by rw [w', hu.wr],
    hu.frame.trans (F'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨K, List.mem_range.mpr hK, rfl⟩, fun _ h => h⟩), fun k' hk' => ?_⟩
  by_cases he : k' = K
  · subst he; rw [← hsig]; exact li
  · have d := hu.done k' (by omega)
    exact ⟨by rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega)]; exact d.fields,
      by rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega)]; exact d.value⟩

/-- A lane's message after the leaves' or a height's call: `PK.seed`, `a16`,
the fields, the `M` bytes after them. -/
theorem lane_msg {p : Params} {m : Mem} {S : Addr} {pkSeed a16 : List Byte} (henv : Env p m S pkSeed a16) {j : Nat}
    (hj : j < 4) (M : Nat) {ty kp z i : Nat}
    (hf : bytesAt m (at' S (Layout.laneA j + p.n + 16)) 16 = toByte ty 4 ++ toByte kp 4 ++ toByte z 4 ++ toByte i 4) :
    bytesAt m (at' S (Layout.oA + Layout.strideA * j)) (p.n + 32 + M) =
      pkSeed ++ adrsOf a16 ty kp z i ++ bytesAt m (at' S (Layout.laneA j + p.n + 32)) M := by
  rw [show p.n + 32 + M = p.n + (16 + (16 + M)) by omega, bytesAt_split2, bytesAt_split2, bytesAt_split2,
    show Layout.oA + Layout.strideA * j + p.n + 16 + 16 = Layout.laneA j + p.n + 32 by rfl]
  rw [show S + BitVec.ofNat 64 (Layout.oA + Layout.strideA * j) = at' S (Layout.laneA j) from rfl, henv.seedA j hj,
    show S + BitVec.ofNat 64 (Layout.oA + Layout.strideA * j + p.n) = at' S (Layout.laneA j + p.n) from rfl,
    henv.adrsA j hj,
    show S + BitVec.ofNat 64 (Layout.oA + Layout.strideA * j + p.n + 16) = at' S (Layout.laneA j + p.n + 16) from rfl, hf]
  simp only [adrsOf, List.append_assoc]

/-- The leaves of a group (`forsLeaves`), from `t₀` (variable 0): each lane's
address (type `FORS_TREE`, key pair `kp`, height 0, its leaf), and its
message `F` of its tree's private key value. -/
theorem forsLeaves_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {kp t₀ : Nat} {I : Nat → Nat} {pkSeed a16 : List Byte}
    (ht₀ : t₀ + 4 < 2 ^ 31) (hkp : kp < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 kp) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      (∀ j < 4, FLane p S j kp 0 (lOf p I t₀ j)
        (F p pkSeed (adrsOf a16 3 kp 0 (lOf p I t₀ j)) (skOf p s.mem sig t₀ j)) s'.mem) →
      Frame (gFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsLeaves p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  unfold Impl.SlhDsa.X86_64.Verify.forsLeaves
  refine WP.seq (WP.mono (Q := LvInv p S sig kp t₀ I s 4) ?_ fun u hu => ?_)
  · rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h₀ : LvInv p S sig kp t₀ I s 0 s := ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
    refine lvstep hn ha1 ha hk1 hk (by decide) ht₀ hkp hbx h12 h14 hv0 hI hIa hw hsr hsfit hss h₀ fun u₁ hu₁ => ?_
    refine lvstep hn ha1 ha hk1 hk (by decide) ht₀ hkp hbx h12 h14 hv0 hI hIa hw hsr hsfit hss hu₁ fun u₂ hu₂ => ?_
    refine lvstep hn ha1 ha hk1 hk (by decide) ht₀ hkp hbx h12 h14 hv0 hI hIa hw hsr hsfit hss hu₂ fun u₃ hu₃ => ?_
    have h := lvstep hn ha1 ha hk1 hk (by decide) ht₀ hkp hbx h12 h14 hv0 hI hIa hw hsr hsfit hss hu₃
      (is := []) (Q := LvInv p S sig kp t₀ I s 4) fun u hu => WP.block_nil hu
    rwa [List.append_nil] at h
  have hbu : u.gpr .rbx = S := by rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hspu : u.gpr .rsp = s.gpr .rsp := hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hFu : Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem u.mem := hu.frame.sub fun r hr => by
    simp only [laneR, List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_cons_self ..⟩))),
      Offset.sub S (by omega) (by simp only [Layout.strideA]; rw [eA]; omega)⟩
  have henvu := Env.of_frame hn32 henv hFu hstk
  have hwu : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hu.wr]; exact hw
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  rw [ht]
  refine lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
    (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by simp only [Layout.strideA]; omega) hbu hwu hS
    (by rw [hspu]; exact hstk) henvu.rc fun s' r' w' g' o' _ F' => ?_
  rw [hspu] at F'
  refine k s' (fun r hr => by
      rw [g' r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [r', hu.rd]) (by rw [w', hu.wr]) (fun j hj => ?_) ?_
  · have d := hu.done j hj
    -- the fields, which the call leaves
    have hfl : bytesAt s'.mem (at' S (Layout.laneA j + p.n + 16)) 16 = bytesAt u.mem (at' S (Layout.laneA j + p.n + 16)) 16 :=
      bytesAt_frame F' (fun r hr => by
        simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
        · have e : Layout.oA + Layout.strideA * c + p.n + 32 = Layout.laneA c + p.n + 32 := rfl
          rw [e, eA, eA]
          rcases Nat.lt_or_ge c j with h' | h'
          · exact Offset.disjoint S (by omega) (by omega) (by omega)
          · exact Offset.disjoint S (by omega) (by omega) (by omega)
        · rw [eA]; exact Offset.disjoint_base S (by omega) (by omega)
        · rw [eA]; exact Offset.disjoint S (by omega) (by omega) (by omega)
        · exact (hstk.sub_right (Offset.sub_base S (by rw [eA]; omega))).symm) (by decide)
    refine ⟨by rw [hfl]; exact d.fields, ?_⟩
    have o₀ := o' j hj
    rw [show Layout.oA + Layout.strideA * j + p.n + 32 = Layout.laneA j + p.n + 32 from rfl] at o₀
    rw [o₀, show 2 * p.n + 32 = p.n + 32 + p.n by omega, lane_msg henvu hj p.n d.fields, d.value, F_shake hfam]
  · refine (hu.frame.sub fun r hr => ?_).trans (F'.sub fun r hr => ?_)
    · simp only [laneR, List.mem_map, List.mem_range] at hr
      obtain ⟨c, hc, rfl⟩ := hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
        Offset.sub S (by omega) (by simp only [Layout.strideA]; rw [eA]; omega)⟩
    · simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
          Offset.sub S (by simp only [Layout.laneA]; omega) (by simp only [Layout.laneA, Layout.strideA, Layout.oA]; omega)⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩

/-! ## The heights -/

/-- The last block of `forsUpLane`: lane `k`'s height `z + 1` and tree index
`⌊L / 2^(z+1)⌋` (`L` in `r11`, `z` in variable 1). -/
theorem upFields_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {k' z L : Nat} (hk' : k' < 4)
    (hL : L < 2 ^ 32) (hz : z + 1 < 64)
    {s : State} {S : Addr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h11 : s.gpr .r11 = BitVec.ofNat 64 L)
    (hv1 : s.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 24)) 8 = toByte (z + 1) 4 ++ toByte (L / 2 ^ (z + 1)) 4 →
      Frame [⟨at' S (Layout.laneA k' + p.n + 24), 8⟩] s.mem s'.mem → Q s') :
    WP isa (.block (([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Fors.var 1)), .alu .add .r10 (.imm 1)] : List Instr) ++
        setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .shiftCl .shr .r11] : List Instr) ++
        setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hla' : 3296 ≤ Layout.laneA k' := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneA k' + p.n := ⟨_, rfl⟩
  rw [← hA]
  have e24 : Layout.laneA k' + p.n + 24 = A + 24 := by omega
  rw [e24] at k
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hbx])
    (by rw [oVar21]; exact in_scr' hw (by omega)) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => ?_
  have hr10 : s₂.gpr .r10 = BitVec.ofNat 64 (z + 1) := by
    rw [u₂.gpr, u₁.gpr, hv1, sx1']; exact (BitVec.ofNat_add z 1).symm
  have hz1 : (BitVec.ofNat 64 (z + 1)).toNat = z + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb₂ : s₂.gpr .rbx = S := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  refine setFieldR_ok (by decide) (by rw [hr10, hz1]; omega)
    (by rw [hb₂, u₂.wr, u₁.wr]; exact in_scr hw (by omega)) fun s₃ f₃ => ?_
  rw [hb₂, hr10, hz1] at f₃
  refine wp_mov fun s₄ u₄ => Levels.wp_shrcl fun s₅ u₅ => ?_
  have hq : L / 2 ^ (z + 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hL
  have hr11 : s₅.gpr .r11 = BitVec.ofNat 64 (L / 2 ^ (z + 1)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), f₃.gpr _ (by decide), f₃.gpr _ (by decide), hr10,
      u₂.other _ (by decide), u₁.other _ (by decide), h11, shr_nat _ _ (by omega) hz]
  have hb₅ : s₅.gpr .rbx = S := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr _ (by decide), hb₂]
  have hq' : (BitVec.ofNat 64 (L / 2 ^ (z + 1))).toNat = L / 2 ^ (z + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, f₃.wr, u₂.wr, u₁.wr]
  refine setFieldR_ok (by decide) (by rw [hr11, hq']; omega) (by rw [hb₅, hw₅]; exact in_scr hw (by omega))
    fun s₆ f₆ => WP.block_nil ?_
  rw [hb₅, hr11, hq'] at f₆
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  refine k s₆ (fun g h₁ h₂ h₃ h₄ => ?_) (by rw [f₆.rd, u₅.rd, u₄.rd, f₃.rd, u₂.rd, u₁.rd]) (by rw [f₆.wr, hw₅]) ?_ ?_
  · rw [f₆.gpr _ h₁, u₅.other _ h₄, u₄.other _ h₂, f₃.gpr _ h₁, u₂.other _ h₃, u₁.other _ h₃]
  · have e₃ : bytesAt s₆.mem (S + BitVec.ofNat 64 (A + 24)) 4 = toByte (z + 1) 4 := by
      rw [bytesAt_frame f₆.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by decide), hm₅, f₃.bytes]
    rw [show (8 : Nat) = 4 + 4 from rfl, at', bytesAt_split2, e₃, f₆.bytes]
  · have F₃ : Frame [⟨at' S (A + 24), 8⟩] s.mem s₃.mem := by
      rw [show s.mem = s₂.mem by rw [u₂.mem, u₁.mem]]
      exact f₃.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
    rw [← hm₅] at F₃
    exact F₃.trans (f₆.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩)

/-- The authentication path's node `z` of lane `k`'s tree, at
`sig + n·(t·(a + 1) + 1) + z·n`. -/
abbrev authOf (p : Params) (m : Mem) (sig : Addr) (t₀ k' z : Nat) : List Byte :=
  bytesAt m (sig + BitVec.ofNat 64 (p.n * (tOf p t₀ k' * (p.a + 1) + 1) + z * p.n)) p.n

/-- Lane `k`'s message at height `z` (`forsUpLane`): its node and the
authentication path's node `z`, in the order bit `z` of its leaf says; and
its address's height `z + 1` and tree index `⌊L / 2^(z+1)⌋`. -/
theorem upLane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {k' t₀ z : Nat} (hk' : k' < 4) (ht₀ : t₀ + 4 < 2 ^ 31) (hz : z < p.a)
    {s : State} {S sig : Addr} {I : Nat → Nat} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hv1 : s.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 32)) (2 * p.n) =
        (if lOf p I t₀ k' / 2 ^ z % 2 = 0 then
          bytesAt s.mem (at' S (Layout.laneA k' + p.n + 32)) p.n ++ authOf p s.mem sig t₀ k' z
        else authOf p s.mem sig t₀ k' z ++ bytesAt s.mem (at' S (Layout.laneA k' + p.n + 32)) p.n) →
      bytesAt s'.mem (at' S (Layout.laneA k' + p.n + 24)) 8 =
        toByte (z + 1) 4 ++ toByte (lOf p I t₀ k' / 2 ^ (z + 1)) 4 →
      Frame [⟨at' S (Layout.laneA k' + p.n + 24), 8⟩, ⟨at' S (Layout.laneA k' + p.n + 32), 2 * p.n⟩] s.mem s'.mem →
      Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsUpLane p k') s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have hla : Layout.laneA k' + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  have hla' : 3296 ≤ Layout.laneA k' := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega
  obtain ⟨t, ht⟩ : ∃ t, t = min (t₀ + k') (p.k - 1) := ⟨_, rfl⟩
  have htk : t < p.k := by omega
  obtain ⟨L, hL⟩ : ∃ L, L = lOf p I t₀ k' := ⟨_, rfl⟩
  rw [← hL] at k
  have hIt := hIa t htk
  have hL32 : L < 2 ^ 32 := by
    have : (t + 1) * 2 ^ p.a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) ha)
    rw [Nat.succ_mul] at this; rw [hL, lOf, tOf, ← ht]; omega
  obtain ⟨au, hau⟩ : ∃ au, au = sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1) + 1) + z * p.n) := ⟨_, rfl⟩
  have hsl := forsSig_le htk (j := z + 1) (by omega)
  have e1 : p.n * (t * (p.a + 1) + 1) = p.n * (t * (p.a + 1)) + p.n := Nat.mul_succ _ _
  have e2 : p.n * (z + 1) = p.n * z + p.n := Nat.mul_succ _ _
  have e3 : z * p.n = p.n * z := Nat.mul_comm _ _
  have hauo : p.n * (t * (p.a + 1) + 1) + z * p.n + p.n ≤ p.forsSigLen := by omega
  have hauk : authOf p s.mem sig t₀ k' z = bytesAt s.mem au p.n := by rw [hau, authOf, tOf, ← ht]
  rw [hauk] at k
  have hdis : Region.Disjoint ⟨au, p.n⟩ ⟨S, 2 ^ 16⟩ := by rw [hau]; exact hss.sub_left (Offset.sub_base sig hauo)
  have hsig : ∀ j < p.n / 8, InRegions (s.rd ++ s.wr) (au + BitVec.ofNat 64 (8 * j)) 8 := fun j hj =>
    ⟨_, List.mem_append_left _ hsr, by
      rw [hau, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by omega) (by omega)⟩
  unfold Impl.SlhDsa.X86_64.Verify.forsUpLane
  rw [hmsg]
  refine WP.seq ?_
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine treeOf_ok hn ha1 ha hk1 hk (by omega) hbx h14 hv0 hI hIa hw fun s₁ g₁ m₁ r₁ w₁ h10₁ h11₁ hsi₁ => ?_
  rw [← ht] at h10₁ h11₁ hsi₁
  have h11 : s₁.gpr .r11 = BitVec.ofNat 64 L := by rw [h11₁, hL, lOf, tOf, ← ht]
  have hb₁ : s₁.gpr .rbx = S := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  refine wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hb₁])
    (by rw [r₁, w₁, oVar21]; exact in_scr' hw (by omega)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => Levels.wp_shrcl fun s₄ u₄ => ?_
  refine wp_movm (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hb₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, r₁, w₁, oVar21]; exact in_scr' hw (by omega)) fun s₅ u₅ => ?_
  refine Levels.mulN_ok hn (r := .rdx) (tmp := .rcx) (by decide) fun s₆ h₆ g₆ m₆ r₆ w₆ => ?_
  refine wp_add fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_andi_zf fun s₉ u₉ z₉ => WP.block_nil ?_
  have hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hrd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, r₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, r₁]
  have hwr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, w₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, w₁]
  have hmz : s₄.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z := by
    rw [u₄.mem, u₃.mem, u₂.mem, m₁, hv1]
  have hrsi : s₉.gpr .rsi = au := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, g₆ _ (by decide) (by decide), h₆, u₅.gpr, hmz,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hsi₁,
      sx_ofNat (by omega), hau, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
    congr 2
    omega
  have hrax : s₉.gpr .rax = BitVec.ofNat 64 (L / 2 ^ z % 2) := by
    rw [u₉.gpr, u₈.other .rax (by decide), u₇.other .rax (by decide), g₆ .rax (by decide) (by decide),
      u₅.other .rax (by decide), u₄.gpr, u₃.gpr, u₃.other .rcx (by decide), u₂.gpr, u₂.other .r11 (by decide), h11, m₁,
      hv1, shr_nat _ _ (by omega) (by omega), sx1', and1_nat _ (by have := Nat.div_le_self L (2 ^ z); omega)]
  have hzf : s₉.zf = some (decide (L / 2 ^ z % 2 = 0)) := by
    rw [z₉, ← u₉.gpr, hrax, beq_bit]
  have hg₉ : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s₉.gpr g = s.gpr g :=
    fun g h1 h2 h3 h4 h5 h6 => by
      rw [u₉.other _ h1, u₈.other _ h4, u₇.other _ h4, g₆ _ h3 h2, u₅.other _ h3, u₄.other _ h1, u₃.other _ h1,
        u₂.other _ h2, g₁ _ h1 h2 h3 h4 h5 h6]
  have hbx₉ : s₉.gpr .rbx = S := by rw [hg₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have h11₉ : s₉.gpr .r11 = BitVec.ofNat 64 L := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h11]
  -- the copies
  obtain ⟨M, hM⟩ : ∃ M, M = Layout.laneA k' + p.n + 32 := ⟨_, rfl⟩
  have eM1 : Layout.laneA k' + (p.n + 32) = M := by omega
  have eM2 : Layout.laneA k' + (p.n + 32) + p.n = M + p.n := by omega
  rw [eM1]
  rw [← hM] at k
  have hMn : M + 2 * p.n ≤ Layout.laneA k' + 128 := by omega
  have hsep' : ∀ q, q + p.n ≤ 2 ^ 16 → Region.Disjoint ⟨S + BitVec.ofNat 64 q, p.n⟩ ⟨au, p.n⟩ := fun q hq =>
    (hdis.sub_right (Offset.sub_base S hq)).symm
  have hsep'' : ∀ i < p.n, Region.Disjoint ⟨au + BitVec.ofNat 64 i, 1⟩ ⟨S + BitVec.ofNat 64 (M + p.n), p.n⟩ :=
    fun i hi => (hdis.sub_left (Offset.sub_base au (by omega))).sub_right (Offset.sub_base S (by omega))
  have hfr : ∀ (o : Nat), o + p.n ≤ M + 2 * p.n → M ≤ o →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 o, p.n⟩ : Region)], ∃ r' ∈ [(⟨at' S M, 2 * p.n⟩ : Region)], Region.Sub r r' :=
    fun o h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₂ (by omega)⟩
  -- after the copies, the fields
  have post : ∀ s' : State, (∀ g, g ≠ .rax → s'.gpr g = s₉.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S M) (2 * p.n) =
        (if L / 2 ^ z % 2 = 0 then bytesAt s.mem (at' S M) p.n ++ bytesAt s.mem au p.n
        else bytesAt s.mem au p.n ++ bytesAt s.mem (at' S M) p.n) →
      Frame [⟨at' S M, 2 * p.n⟩] s.mem s'.mem →
      WP isa (.block (([.mov .r10 (.mem (Impl.SlhDsa.X86_64.Fors.var 1)), .alu .add .r10 (.imm 1)] : List Instr) ++
        setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) .r10 ++
        ([.mov .rcx (.reg .r10), .shiftCl .shr .r11] : List Instr) ++
        setFieldR .rbx (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) .r11)) s' Q := by
    intro s' g' r' w' hm' F'
    have hv1' : s'.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z := by
      rw [F'.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [oVar21]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), hv1]
    refine upFields_ok hn hk' hL32 (by omega) (by rw [g' _ (by decide), hbx₉]) (by rw [g' _ (by decide), h11₉]) hv1'
      (by rw [w']; exact hw) fun s'' g'' r'' w'' b'' F'' => k s'' (fun g h1 h2 h3 h4 h5 h6 => by
        rw [g'' _ h1 h2 h5 h6, g' _ h1, hg₉ _ h1 h2 h3 h4 h5 h6]) (by rw [r'', r']) (by rw [w'', w']) ?_ b'' ?_
    · rw [bytesAt_frame F'' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega), hm']
    · refine (F'.sub fun r hr => ?_).trans (F''.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [hM]; exact fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  refine WP.seq (WP.ite (decide (L / 2 ^ z % 2 = 0)) (by show s₉.zf = _; exact hzf) (fun hb => ?_) (fun hb => ?_))
  · -- bit 0: the node stays, the path's node after it
    have hb' : L / 2 ^ z % 2 = 0 := of_decide_eq_true hb
    refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
      (fun j hj => by rw [hwr₉, hbx₉]; exact in_scr hw (by omega))
      (fun j hj => by rw [hrsi, hrd₉, hwr₉, Nat.zero_add]; exact hsig j hj)
      (by rw [hbx₉, hrsi, BitVec.add_zero, e8]; exact hsep' (M + p.n) (by omega))
      (by omega) (by omega)) fun s' c => ?_
    rw [hbx₉, hrsi, BitVec.add_zero, e8] at c
    refine post s' (fun g h₁ => c.gpr _ h₁) (by rw [c.rd, hrd₉]) (by rw [c.wr, hwr₉]) ?_
      (by rw [← hm₉]; exact c.frame.sub (hfr _ (by omega) (by omega)))
    simp only [hb', ↓reduceIte]
    refine bytesAt_two (by simp [bytesAt_length']) (by simp [bytesAt_length']) (fun i hi => ?_) (fun i hi => ?_)
    · rw [frame_byte c.frame (by omega) (by omega) (by omega), hm₉, bytesAt_getD _ _ hi, ofNat_add']
    · rw [← ofNat_add', c.bytes i hi, hm₉, bytesAt_getD _ _ hi]
  · -- bit 1: the node moves after, the path's node first
    have hb' : ¬ (L / 2 ^ z % 2 = 0) := fun h => by simp [h] at hb
    refine WP.block_append (WP.mono (copyWords_ok (by decide) (by decide)
      (fun j hj => by rw [hwr₉, hbx₉]; exact in_scr hw (by omega))
      (fun j hj => by rw [hrd₉, hwr₉, hbx₉]; exact in_scr' hw (by omega))
      (by rw [hbx₉, e8]; exact Offset.disjoint S (by omega) (by omega) (by omega))
      (by omega) (by omega)) fun s₁₀ c₁₀ => ?_)
    rw [hbx₉, e8] at c₁₀
    have hbx₁₀ : s₁₀.gpr .rbx = S := by rw [c₁₀.gpr _ (by decide), hbx₉]
    have hsi₁₀ : s₁₀.gpr .rsi = au := by rw [c₁₀.gpr _ (by decide), hrsi]
    refine WP.mono (copyWords_ok (d₁ := 0) (by decide) (by decide)
      (fun j hj => by rw [c₁₀.wr, hwr₉, hbx₁₀]; exact in_scr hw (by omega))
      (fun j hj => by rw [hsi₁₀, c₁₀.rd, c₁₀.wr, hrd₉, hwr₉, Nat.zero_add]; exact hsig j hj)
      (by rw [hbx₁₀, hsi₁₀, BitVec.add_zero, e8]; exact hsep' M (by omega))
      (by omega) (by omega)) fun s' c => ?_
    rw [hbx₁₀, hsi₁₀, BitVec.add_zero, e8] at c
    refine post s' (fun g h₁ => by rw [c.gpr _ h₁, c₁₀.gpr _ h₁]) (by rw [c.rd, c₁₀.rd, hrd₉])
      (by rw [c.wr, c₁₀.wr, hwr₉]) ?_ ?_
    · simp only [hb', ↓reduceIte]
      refine bytesAt_two (by simp [bytesAt_length']) (by simp [bytesAt_length']) (fun i hi => ?_) (fun i hi => ?_)
      · rw [← ofNat_add', c.bytes i hi, frame_byte' c₁₀.frame (hsep'' i hi), hm₉, bytesAt_getD _ _ hi]
      · rw [frame_byte c.frame (by omega) (by omega) (by omega), ← ofNat_add', c₁₀.bytes i hi, hm₉,
          bytesAt_getD _ _ hi, ofNat_add']
    · rw [← hm₉]
      exact (c₁₀.frame.sub (hfr _ (by omega) (by omega))).trans (c.frame.sub (hfr _ (by omega) (by omega)))

end VG.Proof.SlhDsa.X86_64
