module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on x86-64: squeezes of three seeds and a fourth state

`Sample4.sampleH` (`Impl/MlKem/X86_64/SampleH.lean`) runs the code of
`vg_mlkem_sample_ntt4_avx2` on three seeds, its fourth Keccak state holding
another sponge's. `SqY w16 σ Y t n` is `SqTW w16 σ t n` (`S4SqT.lean`) for the first
three states (permuted `t + n` times, their buffers holding bytes `168 t` to
`168 (t + n)` of their seeds' output) with the fourth state `Y` (`L3`): a
squeeze permutes `Y` too (`sqY_ok`, `sqYs_ok`), and copies its output to the
fourth buffer, which nothing reads.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (xofByte)
open VG.Proof.Sha3.X86_64.X4 (la Lanes4 byte_of_lanes4 permute4_ok)

/-- The four states after `j` permutations of the first three seeds' padded
blocks, and the fourth `Y`. -/
def L3 (σ : State) (j : Nat) (Y : Spec.Sha3.State) (k : Nat) : Spec.Sha3.State :=
  if k < 3 then iterF j (A0 (B σ k)) else Y

theorem L3_lt {σ : State} {j : Nat} {Y : Spec.Sha3.State} {k : Nat} (hk : k < 3) :
    L3 σ j Y k = iterF j (A0 (B σ k)) := ite_eq_left hk

theorem L3_three (σ : State) (j : Nat) (Y : Spec.Sha3.State) : L3 σ j Y 3 = Y := ite_eq_right (by decide)

theorem L3_perm (σ : State) (j : Nat) (Y : Spec.Sha3.State) :
    (fun k => keccakF (L3 σ j Y k)) = L3 σ (j + 1) (keccakF Y) := by
  funext k
  unfold L3
  split <;> rfl

/-- After `n` squeezes, `t` blocks after the absorption, with the fourth state `Y`. -/
structure SqY (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (t n : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (L3 σ (t + n) Y)
  buf : ∀ k < 3, ∀ p < 168 * n, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)

/-- The permutation, after `n` squeezes. -/
theorem permY_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t n : Nat} (hn : n < 3) {s : State}
    (h : SqY w16 σ Y t n s) {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', EnvW w16 σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (L3 σ (t + n + 1) (keccakF Y)) ∧
      (∀ k < 3, ∀ p < 168 * n, s'.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)) ∧
      Frame [lowR σ] s.mem s'.mem ∧ s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 ∧
      (∀ g, g ≠ .rax → g ≠ .rdx → g ≠ .rdi → g ≠ .rsi → g ≠ .rcx → s'.gpr g = s.gpr g) → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq (Impl.Sha3.X86_64.X4.permute4 fast) rest)) s Q := by
  refine WP.seq (WP.mono (args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (fast := fast) (A := L3 σ (t + n) Y)
    (pre4 hp hrd hwr (by rw [hm]; exact h.rc)) hdi hsi hdx (by rw [hcx, at', at', Offset.add_add])
    (by rw [hm]; exact h.lanes)) fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨EnvW.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [← hm]; exact hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, hsub r hr⟩,
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)], by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)],
    fun g h₁ h₂ h₃ h₄ h₅ => by rw [hg g h₁ h₂, k₁.gpr (by simp [h₃, h₄, h₂, h₅])]⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · rw [← L3_perm]
    exact hl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016)
        (by simp only [oBuf]; omega) (by simp only [oBuf]; omega), Offset.disjoint (scr σ) (d := oBuf) (n := 2016)
          (e := 800) (k := 800) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf (by omega)
          (by omega), hm]
    exact h.buf k hk p hp'

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXY (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (m₀ : Mem) (t n K I : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (L3 σ (t + n + 1) Y)
  buf : ∀ k < 3, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)
  fr : Frame [lowR σ] m₀ s.mem
  rbp : s.gpr .rbp = at' σ (oBuf + 168 * n)

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem extY_step {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {m₀ : Mem} {t n K I : Nat} (hn : n < 3)
    (hK : K < 4) (hI : I < 21) {s : State} (h : EXY w16 σ Y m₀ t n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbp (504 * K + 8 * I)) .rax]) s (EXY w16 σ Y m₀ t n K (I + 1)) := by
  refine wp_movm (a := at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.rbp, at', at', Offset.add_add,
        show oBuf + 168 * n + (504 * K + 8 * I) = oBuf + 504 * K + 168 * n + 8 * I by omega])
      (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hsub : Region.Sub ⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩ (lowR σ) :=
    Offset.sub_base _ (by simp only [oBuf, oSave]; omega)
  have hf : Frame [⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨EnvW.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_,
    h.fr.trans (hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), by rw [g₂, u₁.other _ (by decide), h.rbp]⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hK (by omega), L3_lt hk, show t + n + 1 = (t + n) + 1 from rfl,
        ← xofByte_A0 (B_length σ k) (by omega),
        show 168 * (t + n) + (8 * I + (p - 168 * n - 8 * I)) = 168 * t + p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

/-- Block `n` of each state's output. -/
theorem extractY_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {m₀ : Mem} {t n : Nat} (hn : n < 3) {s : State}
    (h : EXY w16 σ Y m₀ t n 0 0 s) :
    WP isa (.block extract) s fun s' => SqY w16 σ Y t (n + 1) s' ∧ Frame [lowR σ] m₀ s'.mem := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXY w16 σ Y m₀ t n K 0 s) (fun K s hK h => ?_) 4
    (Nat.le_refl _) s h) fun s' h' =>
      ⟨⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩, h'.fr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXY w16 σ Y m₀ t n K I s)
    (fun I s hI h => extY_step hp hn hK hI h) 21 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega), h'.fr, h'.rbp⟩

/-- `squeeze`, to block `n`: after `n + 1` squeezes, with `rbp`, `r10` and
`r8` kept; it writes only below the saved registers. -/
theorem sqY_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t n : Nat} (hn : n < 3) {s : State}
    (h : SqY w16 σ Y t n s) (hbp : s.gpr .rbp = at' σ (oBuf + 168 * n)) :
    WP isa (squeeze fast) s fun s' => (SqY w16 σ (keccakF Y) t (n + 1) s' ∧ Frame [lowR σ] s.mem s'.mem) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r8 = s.gpr .r8 := by
  unfold squeeze
  exact permY_ok (fast := fast) hp hn h fun s' ⟨he, h14, hrc, hl, hb, hf, h₁, h₂, hg⟩ =>
    WP.mono (WP.keep [.rax] (extractY_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega), hf,
      by rw [h₁, hbp]⟩) (by decide)) fun s'' ⟨h', k⟩ =>
        ⟨h', by rw [k.gpr (by decide), h₁], by rw [k.gpr (by decide), h₂],
          by rw [k.gpr (by decide), hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]⟩

/-- `SqY` does not depend on `rbp`, `r10` or the flags. -/
theorem SqY.frame {σ : State} {Y : Spec.Sha3.State} {t n : Nat} {s s' : State} (h : SqY w16 σ Y t n s)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) : SqY w16 σ Y t n s' := by
  have k : Keep [.rbp, .r10] s s' := ⟨fun r hr => hg r (fun e => hr (by simp [e])) (fun e => hr (by simp [e])), hrd, hwr⟩
  exact ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14], by rw [hm]; exact h.rc,
    by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩

/-- `squeezes b n`: after `b + n` squeezes; it writes only below the saved
registers. -/
theorem sqYs_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t b n : Nat} (hn : 0 < n)
    (hbn : b + n ≤ 3) {s : State} (h : SqY w16 σ Y t b s) :
    WP isa (squeezes b n fast) s fun s' => SqY w16 σ (iterF n Y) t (b + n) s' ∧ Frame [lowR σ] s.mem s'.mem := by
  unfold squeezes
  refine WP.mono (blocks_ok (b := b) (P := fun i s' => SqY w16 σ (iterF (i - b) Y) t i s' ∧ Frame [lowR σ] s.mem s'.mem) hn
    (by omega) (by simp only [oBuf]; omega) (by decide)
    (fun _ _ _ ⟨h', hf⟩ hm hrd hwr hg => ⟨h'.frame hm hrd hwr hg, by rw [hm]; exact hf⟩)
    (fun i u hb hi ⟨hi', hf⟩ hbp => WP.mono (sqY_ok (fast := fast) hp (by omega) hi' ?_)
      fun _ ⟨⟨h', hf'⟩, k⟩ => ⟨⟨?_, hf.trans hf'⟩, k.1, k.2.1⟩) ⟨by rw [Nat.sub_self]; exact h, Frame.refl _ _⟩)
    fun s' h' => by rwa [Nat.add_sub_cancel_left] at h'
  · rw [hbp, h.env.rbx, Offset.add_add, at', show oBuf + 168 * b + 168 * (i - b) = oBuf + 168 * i by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hb]]
  · rwa [show i + 1 - b = (i - b) + 1 by omega, iterF_succ]

/-- `SqY` after writes apart from the low scratch space and the saved registers. -/
theorem SqY.apart {σ : State} {Y : Spec.Sha3.State} {t n : Nat} (hn : n ≤ 3) {s s' : State} (h : SqY w16 σ Y t n s)
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hlow : ∀ r ∈ rs, (lowR σ).Disjoint r)
    (hsv : ∀ r ∈ rs, (⟨at' σ oSave, 40⟩ : Region).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [aRW w16 σ, scrR σ, stkR σ], Region.Sub r R) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r) : SqY w16 σ Y t n s' := by
  refine ⟨h.env.apart hf hsv hsub hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hg .r14 (by simp), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * (50 + r) + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.rc r hr k hk
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * i + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.lanes i hi k hk
  · rw [hf (at' σ (oBuf + 504 * k + p)) fun r' hr' hc => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := oBuf + 504 * k + p) (n := 1) (by simp only [oBuf, oSave]; omega)) _
      (Region.contains_self _ _) hc]
    exact h.buf k hk p (by omega)

end VG.Proof.MlKem.X86_64.SH
