module

public import VerifiedGarbage.Proof.Rc2.RISCV64.KeySteps
public import VerifiedGarbage.Proof.Rc2.Expansion
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Rc2.Table
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Rc2.RISCV64.KeyLoop`, which only this module used -/

section

/-!
# RC2 on RISC-V: the loops of key expansion

Each loop keeps `KEnv` (the arguments, PITABLE in the working space and the
key) and builds `L` in the schedule (`Proof.Rc2.BytesPrefix`): `copy_loop`, `fill_loop`, `descend_loop`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- What the loops keep. -/
structure KEnv (K S W : Addr) (len bits : Nat) (key : List Byte) (s : State) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 len
  a2 : s.gpr .a2 = BitVec.ofNat 64 bits
  a3 : s.gpr .a3 = S
  pi : PiEnv W s
  rd : s.rd = [⟨K, len⟩]
  wr : s.wr = [⟨S, 128⟩, ⟨W, 512⟩]
  key : ∀ c < len, s.mem (K + BitVec.ofNat 64 c) = key.getD c 0

/-- The constant facts about the regions. -/
structure KRegions (K S W : Addr) (len : Nat) : Prop where
  hlen : 1 ≤ len ∧ len ≤ 128
  kS : (⟨K, len⟩ : Region).Disjoint ⟨S, 128⟩
  SW : (⟨S, 128⟩ : Region).Disjoint ⟨W, 512⟩

theorem KEnv.keep {K S W : Addr} {len bits : Nat} {key : List Byte} {s t : State}
    (E : KEnv K S W len bits key s) {rs : List Reg} (k : Keep rs s t)
    (h : Reg.a0 ∉ rs ∧ Reg.a1 ∉ rs ∧ Reg.a2 ∉ rs ∧ Reg.a3 ∉ rs ∧ Reg.a4 ∉ rs) (hm : t.mem = s.mem) :
    KEnv K S W len bits key t :=
  ⟨by rw [k.gpr h.1]; exact E.a0, by rw [k.gpr h.2.1]; exact E.a1, by rw [k.gpr h.2.2.1]; exact E.a2,
    by rw [k.gpr h.2.2.2.1]; exact E.a3, E.pi.keep k h.2.2.2.2 hm, by rw [k.2.1]; exact E.rd,
    by rw [k.2.2]; exact E.wr, by rw [hm]; exact E.key⟩

/-- After a step that writes byte `i` of `L`. -/
theorem KEnv.write {K S W : Addr} {len bits : Nat} {key : List Byte} {s t : State}
    (E : KEnv K S W len bits key s) (R : KRegions K S W len) (k : Keep keyTemps s t) {i : Nat} (hi : i < 128)
    {b : Byte} (hm : t.mem = s.mem.writeW (S + BitVec.ofNat 64 i) b) : KEnv K S W len bits key t := by
  have F : Frame [⟨S, 128⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨by rw [k.gpr (by decide)]; exact E.a0, by rw [k.gpr (by decide)]; exact E.a1,
    by rw [k.gpr (by decide)]; exact E.a2, by rw [k.gpr (by decide)]; exact E.a3,
    ⟨by rw [k.gpr (by decide)]; exact E.pi.a4, E.pi.al, fun j hj => by rw [k.2.1, k.2.2]; exact E.pi.rd j hj, fun j hj => ?_⟩,
    by rw [k.2.1]; exact E.rd, by rw [k.2.2]; exact E.wr, fun c hc => ?_⟩
  · rw [F.readW (r := ⟨W, 512⟩) (Offset.contains_base _ (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)
      (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)) (by simpa using R.SW.symm) (by decide)]
    exact E.pi.held j hj
  · rw [F.bytes (R := ⟨K, len⟩) (by simpa using R.kS) (by have := R.hlen; simp; omega_arith) hc]
    exact E.key c hc

theorem copy_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (s : State) (E : KEnv K S W len bits key s) (h8 : s.gpr .a5 = 0#64) :
    WP isa (.loop (.block copyKey) (.nonzero .a7)) s fun t =>
      KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 len ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) len := by
  have hl := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) i) len (fun i hi t ⟨E, h8, P⟩ => ?_) 0 (by omega_arith) s
    ⟨E, h8, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.mono (copy_run t (by rw [E.rd, E.wr, E.a0, h8]; exact ⟨⟨K, len⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [E.wr, E.a3, h8]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun t' ⟨a, b, m, k⟩ => ?_
  rw [E.a3, E.a0, h8, E.key i hi] at m
  refine ⟨⟨E.write R (k.mono (by simp)) (by omega_arith) m, by rw [a, h8, succ_ofNat], ?_⟩, ?_⟩
  · rw [m, ← Proof.Rc2.initial_set key i]
    exact P.extend (by omega_arith) _
  · rw [b, h8, E.a1, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

theorem fill_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hk : key.length = len) (hl : len < 128) (s : State) (E : KEnv K S W len bits key s)
    (h8 : s.gpr .a5 = BitVec.ofNat 64 len) (P : Proof.Rc2.BytesPrefix s.mem S (Proof.Rc2.fill key 0) len) :
    WP isa (.loop fillKey (.nonzero .a7)) s fun t =>
      KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 128 ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl1 := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (i - len)) i ∧ len ≤ i) 128
    (fun i hi t ⟨E, h8, P, hli⟩ => ?_) len hl s ⟨E, h8, by rw [Nat.sub_self]; exact P, Nat.le_refl _⟩
    |> fun h => WP.mono h fun t ⟨a, b, c, _⟩ => ⟨a, b, c⟩
  have lo : t.gpr .a3 + t.gpr .a5 - 1#64 = S + BitVec.ofNat 64 (i - 1) := by
    rw [E.a3, h8, Offset.add_ofNat_sub S (by omega_arith)]
  have hi' : t.gpr .a3 + (t.gpr .a5 - t.gpr .a1) = S + BitVec.ofNat 64 (i - len) := by
    rw [E.a3, h8, E.a1, Offset.ofNat_sub_ofNat hli]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (fill_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.a3, h8]; exact inS i hi)) fun t' ⟨a, b, m, k⟩ => ?_
  rw [lo, hi', E.a3, h8, P (i - 1) (by omega_arith), P (i - len) (by omega_arith)] at m
  refine ⟨⟨E.write R k hi m, by rw [a, h8, succ_ofNat], ?_, by omega_arith⟩, ?_⟩
  · have e : Proof.Rc2.fill key (i + 1 - len) = (Proof.Rc2.fill key (i - len)).set! i
        (Spec.Rc2.pi ((Proof.Rc2.fill key (i - len)).getD (i - 1) 0 +
          (Proof.Rc2.fill key (i - len)).getD (i - len) 0)) := by
      rw [show i + 1 - len = (i - len) + 1 by omega_arith, Proof.Rc2.fill_succ]
      simp only [Proof.Rc2.fillStep, hk]
      rw [show len + (i - len) = i by omega_arith]
    rw [m, e]
    exact P.extend (by omega_arith) _
  · rw [b, h8, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

theorem descend_loop {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) {t8 : Nat} (ht8 : 1 ≤ t8 ∧ t8 < 128) (l : Proof.Rc2.KeyBytes) (s : State)
    (E : KEnv K S W len bits key s) (h8 : s.gpr .a5 = BitVec.ofNat 64 (128 - t8))
    (h14 : s.gpr .t4 = BitVec.ofNat 64 t8) (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa (.loop descendKey (.nonzero .a5)) s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 (128 - t8)) 128 := by
  refine countLoop _ _ (fun j t => KEnv K S W len bits key t ∧ t.gpr .a5 = BitVec.ofNat 64 (128 - t8 - j) ∧
      t.gpr .t4 = BitVec.ofNat 64 t8 ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 j) 128) (128 - t8)
    (fun j hj t ⟨E, h8, h14, P⟩ => ?_) 0 (by omega_arith) s ⟨E, by rw [h8, Nat.sub_zero], h14, P⟩
    |> fun h => WP.mono h fun t ⟨a, _, _, c⟩ => ⟨a, c⟩
  have hd : t.gpr .a5 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [h8, Offset.ofNat_sub_ofNat (by omega_arith), show 128 - t8 - j - 1 = 127 - t8 - j by omega_arith]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have lo : t.gpr .a3 + (t.gpr .a5 - 1#64) + 1#64 = S + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [E.a3, hd, Offset.add_add]
  have hi' : t.gpr .a3 + (t.gpr .a5 - 1#64 + t.gpr .t4) = S + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [E.a3, hd, h14, BitVec.ofNat_add_ofNat]
  refine WP.mono (descend_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.a3, hd]; exact inS _ (by omega_arith))) fun t' ⟨a, m, k⟩ => ?_
  rw [lo, hi', E.a3, hd, P _ (by omega_arith), P _ (by omega_arith)] at m
  refine ⟨⟨E.write R k (by omega_arith) m, by rw [a, hd, show 128 - t8 - (j + 1) = 127 - t8 - j by omega_arith],
    by rw [k.gpr (by decide), h14], ?_⟩, ?_⟩
  · rw [m, Proof.Rc2.descend_succ]
    exact P.write (by decide) (by omega_arith) _
  · rw [a, hd, ofNat_bne_zero' (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.KeyInit`, which only this module used -/

section

/-!
# RC2 on RISC-V: the setup of key expansion

`piInit_run`: PITABLE's doublewords, from immediates, into the working space.
`maskCode_run`: `TM`, chosen by branches on the public `effective_bits mod 8`.
`reduceSetup_run`: `T8` and the index of the reduction.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64
open VG.Impl.Words.RISCV64 (li64)

theorem piInit_steps (u : State) {W : Addr} (hW : u.gpr .a4 = W) (hal : W.toNat % 8 = 0)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ n ≤ 32, WP isa (.block ((List.range n).flatMap fun k =>
        li64 .t0 .t1 (Impl.Rc2.piQuad k) ++ ([.store .d .t0 .a4 (8 * k)] : List Instr))) u fun t =>
      (∀ i < n, t.mem.readW (W + BitVec.ofNat 64 (8 * i)) 64 = Impl.Rc2.piQuad i) ∧
      Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.t0, .t1] u t := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun t ⟨held, F, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.t0, .t1] (ByteLoad.li64_ok (s := t) (by decide) (Impl.Rc2.piQuad n)) (by rfl) rfl)
      fun t₁ ⟨e₁, k₁⟩ => ?_
    have a₁ : t₁.gpr .t0 = Impl.Rc2.piQuad n := by rw [e₁]; exact RegUpd.gpr_write_self _ _ _
    have m₁ : t₁.mem = t.mem := by rw [e₁]; rfl
    have h7 : t₁.gpr .a4 = W := by rw [k₁.gpr (by decide), k.gpr (by decide), hW]
    refine WP.mono (WP.keep [] (c := .block [.store .d .t0 .a4 (8 * n)]) (Q := fun t₂ =>
        t₂.mem = t₁.mem.writeW (W + BitVec.ofNat 64 (8 * n)) (Impl.Rc2.piQuad n)) ?_
      (by rfl) rfl) fun t₂ ⟨m₂, k₂⟩ => ⟨fun i hi => ?_, ?_, ?_⟩
    · rrun [h7, a₁, show 8 * n < 2048 by omega_using [hn], Spill.al8 hal (show 8 * n % 8 = 0 by omega_using []),
        show InRegions t₁.wr (W + BitVec.ofNat 64 (8 * n)) 8 by rw [k₁.2.2, k.2.2]; exact hw n (by omega_using [hn])]
    · rw [m₂, m₁]
      by_cases e : i = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep W (by omega_using [e]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact held i (by omega_using [hi, e])
    · rw [m₂, m₁]; exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
    · exact ((k.trans k₁).trans k₂).mono (by simp)

theorem piInit_run (u : State) {W : Addr} (hW : u.gpr .a4 = W) (hal : W.toNat % 8 = 0)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block piInit) u fun t =>
      Proof.Rc2.PiHeld t.mem W ∧ Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.t0, .t1] u t :=
  WP.mono (piInit_steps u hW hal hw 32 (Nat.le_refl _)) fun _ ⟨held, F, k⟩ =>
    ⟨fun i hi => by rw [Proof.Rc2.piQuads_length] at hi; rw [held i hi, Proof.Rc2.piQuads_getD hi], F, k⟩

/-- `TM` for `c = effective_bits mod 8`. -/
def maskVal (c : Nat) : Nat := if c = 0 then 255 else 2 ^ c - 1

theorem sub_beq_zero {c k : Nat} (hc : c < 8) (hk : k < 8) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 k == (0 : BitVec 64)) = decide (c = k) := by
  by_cases h : c = k
  · subst h; simp
  · have : BitVec.ofNat 64 c - BitVec.ofNat 64 k ≠ (0 : BitVec 64) := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc]), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk])] at this
      omega_using [hc, hk, h, this]
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

theorem mask_loop {c₀ : Nat} (hc : c₀ < 8) : ∀ n k, k + n = 7 → ∀ u : State, u.gpr .a6 = BitVec.ofNat 64 c₀ →
    u.gpr .t2 = BitVec.ofNat 64 (if 1 ≤ c₀ ∧ c₀ ≤ k then 2 ^ c₀ - 1 else 255) →
    WP isa ((List.range' k n).foldr (fun c rest => .seq (.block [.addi .t0 .a6 (-((c + 1 : Nat) : Int))])
        (.seq (.ite (.zero .t0) (.block [.li .t2 ((2 ^ (c + 1) - 1 : Nat) : Int)]) (.block [])) rest)) (.block [])) u
      fun t => t.gpr .t2 = BitVec.ofNat 64 (maskVal c₀) ∧ t.mem = u.mem ∧ Keep [.t0, .t2] u t := by
  intro n
  induction n with
  | zero =>
    intro k hk u _ h12
    refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
    rw [h12]; unfold maskVal
    by_cases h : c₀ = 0
    · rw [ite_eq_right (by omega_using [h]), ite_eq_left h]
    · rw [ite_eq_left (by omega_using [hc, hk, h]), ite_eq_right h]
  | succ n ih =>
    intro k hk u h9 h12
    rw [List.range'_succ, List.foldr_cons]
    apply WP.seq
    refine WP.mono (WP.keep [.t0] (c := .block [.addi .t0 .a6 (-((k + 1 : Nat) : Int))]) (Q := fun t =>
        t.gpr .t0 = u.gpr .a6 - BitVec.ofNat 64 (k + 1) ∧ t.mem = u.mem)
      (by rrun [show k + 1 ≤ 2048 by omega_using [hk]]) (by rfl) rfl)
      fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    have hb : isa.eval (.zero .t0) t₁ = some (decide (c₀ = k + 1)) := by
      rw [Steps.eval_zero, a₁, h9, sub_beq_zero hc (by omega_using [hk])]
    refine WP.ite _ hb (fun ht => ?_) (fun hf => ?_)
    · have e : c₀ = k + 1 := of_decide_eq_true ht
      have hli : 2 ^ (k + 1) - 1 < 2048 := by
        have : 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
        omega_using [this]
      refine WP.mono (WP.keep [.t2] (c := .block [.li .t2 ((2 ^ (k + 1) - 1 : Nat) : Int)]) (Q := fun t =>
          t.gpr .t2 = BitVec.ofNat 64 (2 ^ (k + 1) - 1) ∧ t.mem = t₁.mem)
        (by rrun [hli])
        (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₂ (by rw [k₂.gpr (by decide), k₁.gpr (by decide), h9])
        (by rw [a₂, ite_eq_left (by omega_using [e]), e])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₂, m₁], ((k₁.trans k₂).trans kk).mono (by simp)⟩
    · have e : c₀ ≠ k + 1 := of_decide_eq_false hf
      refine WP.block_nil ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₁ (by rw [k₁.gpr (by decide), h9])
        (by
          rw [k₁.gpr (by decide), h12]
          by_cases h : 1 ≤ c₀ ∧ c₀ ≤ k
          · rw [ite_eq_left h, ite_eq_left (by omega_using [h])]
          · rw [ite_eq_right h, ite_eq_right (by omega_using [e, h])])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₁], (k₁.trans kk).mono (by simp)⟩

theorem low3 (bits : Nat) (hb : bits < 2 ^ 64) :
    (BitVec.ofNat 64 bits <<< 61) >>> 61 = BitVec.ofNat 64 (bits % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show bits % 8 < 2 ^ 64 by omega_using [])]
  omega_using []

theorem maskCode_run (u : State) {bits : Nat} (hb : bits < 2 ^ 64) (h5 : u.gpr .a2 = BitVec.ofNat 64 bits) :
    WP isa maskCode u fun t => t.gpr .t2 = BitVec.ofNat 64 (maskVal (bits % 8)) ∧ t.mem = u.mem ∧
      Keep [.a6, .t0, .t2] u t := by
  unfold maskCode
  apply WP.seq
  refine WP.mono (WP.keep [.a6, .t2] (c := .block [.shift .sll .d .a6 .a2 61, .shift .srl .d .a6 .a6 61, .li .t2 255])
      (Q := fun t => t.gpr .a6 = BitVec.ofNat 64 (bits % 8) ∧ t.gpr .t2 = BitVec.ofNat 64 255 ∧ t.mem = u.mem)
    (by rrun [h5]; exact low3 bits hb) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [List.range_eq_range']
  refine WP.mono (mask_loop (c₀ := bits % 8) (by omega_using []) 7 0 rfl t₁ a₁ (by rw [b₁, ite_eq_right (by omega_using [])]))
    fun t ⟨a, m, k⟩ => ⟨a, by rw [m, m₁], (k₁.trans k).mono (by simp)⟩

theorem maskVal_eq {bits : Nat} : maskVal (bits % 8) = 255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8)) := by
  unfold maskVal
  by_cases h : bits % 8 = 0
  · rw [ite_eq_left h, show 8 + bits - 8 * ((bits + 7) / 8) = 8 by omega_using [h]]
  · rw [ite_eq_right h, show 8 + bits - 8 * ((bits + 7) / 8) = bits % 8 by omega_using [h]]
    have : ∀ c < 8, c ≠ 0 → 2 ^ c - 1 = 255 % 2 ^ c := by decide
    exact this _ (Nat.mod_lt _ (by decide)) h

theorem reduceSetup_run (u : State) {bits : Nat} (hb : bits ≤ 1024) (h5 : u.gpr .a2 = BitVec.ofNat 64 bits) :
    WP isa (.block reduceSetup) u fun t => t.gpr .t4 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      t.gpr .a5 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ t.mem = u.mem ∧ Keep [.a5, .t4] u t := by
  refine WP.mono (WP.keep [.a5, .t4] (c := .block reduceSetup) (Q := fun t =>
      t.gpr .t4 = BitVec.ofNat 64 ((bits + 7) / 8) ∧ t.gpr .a5 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧
        t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  have e14 : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show bits < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (7 : Nat) < 2 ^ 64 by omega_using []),
      Nat.mod_eq_of_lt (show bits + 7 < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (bits + 7) / 8 < 2 ^ 64 by omega_using [hb])]
  have e8 : BitVec.ofNat 64 128 - BitVec.ofNat 64 ((bits + 7) / 8) = BitVec.ofNat 64 (128 - (bits + 7) / 8) :=
    Offset.ofNat_sub_ofNat (by omega_using [hb])
  unfold reduceSetup
  rrun [h5, e14, e8]

end VG.Proof.Rc2.RISCV64

end

end


/-!
# RC2 on RISC-V: key expansion

`expandKey_wp`: the schedule at `a3` becomes the expansion of the key at
`a0`, with PITABLE written to the working space at `a4`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem copyFill_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hk : key.length = len) (s : State) (E : KEnv K S W len bits key s)
    (h8 : s.gpr .a5 = 0#64) :
    WP isa expandCopyFill s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl := R.hlen
  unfold expandCopyFill
  apply WP.seq
  refine WP.mono (copy_loop R s E h8) fun t₁ ⟨E₁, a₁, P₁⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.keep [.a7] (c := .block [.li .a7 128, .sub .a7 .a5 .a7]) (Q := fun t =>
      t.gpr .a7 = BitVec.ofNat 64 len - BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) (by rrun [a₁])
    (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have hb : isa.eval (.zero .a7) t₂ = some (decide (len = 128)) := by
    rw [Steps.eval_zero, a₂]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith))
  refine WP.ite _ hb (fun ht => WP.block_nil ⟨E₂, ?_⟩) (fun hf => ?_)
  · have e : len = 128 := of_decide_eq_true ht
    rw [m₂, e, Nat.sub_self]; rw [e] at P₁; exact P₁
  · have e : len ≠ 128 := of_decide_eq_false hf
    exact WP.mono (fill_loop R hk (by omega_arith) t₂ E₂ (by rw [k₂.gpr (by decide), a₁]) (by rw [m₂]; exact P₁))
      fun _ ⟨a, _, c⟩ => ⟨a, c⟩

theorem setWidth_ofNat8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem reducePhase_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hb : 1 ≤ bits ∧ bits ≤ 1024) (s : State) (E : KEnv K S W len bits key s)
    {l : Proof.Rc2.KeyBytes} (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa expandReduce s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S
        (Proof.Rc2.descend (Proof.Rc2.reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128 := by
  let t8 := (bits + 7) / 8
  have ht8 : 1 ≤ t8 ∧ t8 ≤ 128 := ⟨by omega_arith, by omega_arith⟩
  unfold expandReduce
  apply WP.seq
  refine WP.mono (reduceSetup_run s hb.2 E.a2) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have E₁ := E.keep k₁ (by decide) m₁
  apply WP.seq
  refine WP.mono (maskCode_run t₁ (by omega_arith) E₁.a2) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have h8₂ : t₂.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₂.gpr (by decide), b₁]
  have at₂ : t₂.gpr .a3 + t₂.gpr .a5 = S + BitVec.ofNat 64 (128 - t8) := by rw [E₂.a3, h8₂]
  have inS : InRegions t₂.wr (S + BitVec.ofNat 64 (128 - t8)) 1 := by
    rw [E₂.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (reduce_run t₂ E₂.pi (by rw [at₂]; obtain ⟨r, hr, hc⟩ := inS; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [at₂]; exact inS)) fun t₃ ⟨m₃, k₃⟩ => ?_
  have P₂ : Proof.Rc2.BytesPrefix t₂.mem S l 128 := by rw [m₂, m₁]; exact P
  rw [at₂, a₂, setWidth_ofNat8, P₂ _ (by omega_arith), maskVal_eq] at m₃
  have E₃ := E₂.write R (k₃.mono (by simp)) (by omega_arith) m₃
  have P₃ : Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.reduce l bits) 128 := by
    rw [m₃]; exact P₂.write (by decide) (by omega_arith) _
  have h8₃ : t₃.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₃.gpr (by decide), h8₂]
  have hz : isa.eval (.zero .a5) t₃ = some (decide (128 - t8 = 0)) := by
    rw [Steps.eval_zero, h8₃, Steps.ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun ht => WP.block_nil ⟨E₃, ?_⟩) (fun hf => ?_)
  · have e : 128 - t8 = 0 := of_decide_eq_true ht
    show Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.descend (Proof.Rc2.reduce l bits) t8 (128 - t8)) 128
    rw [e]; exact P₃
  · have e : 128 - t8 ≠ 0 := of_decide_eq_false hf
    exact descend_loop R ⟨ht8.1, by omega_arith⟩ _ t₃ E₃ h8₃
      (by rw [k₃.gpr (by decide), k₂.gpr (by decide), a₁]) P₃

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : Spec.Rc2.validKey (s.gpr .a1).toNat (s.gpr .a2).toNat
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a3, 128⟩, ⟨s.gpr .a4, 512⟩]
  al : (s.gpr .a4).toNat % 8 = 0
  kS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 128⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩
  SW : (⟨s.gpr .a3, 128⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩

/-- What key expansion guarantees. -/
def KeyPost (s s' : State) : Prop :=
  Spec.Rc2.scheduleAt s'.mem (s.gpr .a3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let K := s.gpr .a0
  let len := (s.gpr .a1).toNat
  let bits := (s.gpr .a2).toNat
  let S := s.gpr .a3
  let W := s.gpr .a4
  let key := Spec.Rc2.bytesAt s.mem K len
  have hv := h.valid
  unfold Spec.Rc2.validKey at hv
  have R : KRegions K S W len := ⟨⟨hv.1, hv.2.1⟩, h.kS, h.SW⟩
  have wW : ∀ d, d + 8 ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega_arith)⟩
  unfold expandKey
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (piInit_run s rfl h.al fun k hk => wW _ (by omega_arith)) fun t₁ ⟨held, F₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.a5] (c := .block [.li .a5 0]) (Q := fun t => t.gpr .a5 = 0#64 ∧ t.mem = t₁.mem)
    (by rrun) (by rfl) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have k01 := k₁.trans k₀
  have E₀ : KEnv K S W len bits key t₀ := by
    refine ⟨k01.gpr (by decide), by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      k01.gpr (by decide), ⟨k01.gpr (by decide), h.al, fun j hj => ?_, by rw [m₀]; exact held⟩,
      by rw [k01.2.1]; exact h.rd, by rw [k01.2.2]; exact h.wr, fun c hc => ?_⟩
    · rw [k01.2.1, k01.2.2]
      obtain ⟨r, hr, hc⟩ := wW (8 * j) (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [m₀, F₁.bytes (R := ⟨K, len⟩) (by simpa using h.kW.sub_right (Region.sub_prefix (show 256 ≤ 512 by decide)))
        (by simp; omega_arith) hc]
      exact (Proof.Rc2.bytesAt_getD _ _ _ _ hc).symm
  have hk : key.length = len := bytesAt_length _ _ _
  apply WP.seq
  refine WP.mono (copyFill_run R hk t₀ E₀ a₀) fun t₂ ⟨E₂, P₂⟩ => ?_
  refine WP.mono (reducePhase_run R ⟨hv.2.2.1, hv.2.2.2⟩ t₂ E₂ P₂) fun t₃ ⟨_, P₃⟩ => ?_
  refine Proof.Rc2.scheduleAt_expanded ?_
  rw [Proof.Rc2.expandBytes_eq, hk]
  exact P₃

end VG.Proof.Rc2.RISCV64
