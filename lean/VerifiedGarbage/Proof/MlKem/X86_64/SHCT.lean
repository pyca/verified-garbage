module

public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
public import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.MlKem.X86_64.SampleH
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
public import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.MlKem.X86_64.SampleH
meta import VerifiedGarbage.Proof.Sha3.X86_64.Permute
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Run
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop

/-! ### `MlKem.X86_64.SHTop`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.SHRun`, which only this module used -/

section

/-! ### `MlKem.X86_64.SHAbs`, which only this module used -/

section

/-! ### `MlKem.X86_64.SHSq`, which only this module used -/

section

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
  obtain hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  obtain hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (fast := fast) (A := L3 σ (t + n) Y)
    (pre4 hp hrd hwr (by rw [hm]; exact h.rc)) hdi hsi hdx (by rw [hcx, at', at', Offset.add_add])
    (by rw [hm]; exact h.lanes)) fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  obtain hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega_arith)
    · exact Offset.sub_base _ (by simp only [oSave]; omega_arith)
  refine ⟨EnvW.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [← hm]; exact hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, hsub r hr⟩,
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)], by rw [hg _ (by decide) (by decide), k₁.gpr (by decide)],
    fun g h₁ h₂ h₃ h₄ h₅ => by rw [hg g h₁ h₂, k₁.gpr (by simp [h₃, h₄, h₂, h₅])]⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega_arith) (by omega_arith),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega_arith) (by omega_arith)
            (by omega_arith)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · rw [← L3_perm]
    exact hl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016)
        (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith), Offset.disjoint (scr σ) (d := oBuf) (n := 2016)
          (e := 800) (k := 800) (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith) (by omega_arith)⟩) hf (by omega_arith)
          (by omega_arith), hm]
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
    (in_scr' hp h.env.rd h.env.wr (by omega_arith)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.rbp, at', at', Offset.add_add,
        show oBuf + 168 * n + (504 * K + 8 * I) = oBuf + 504 * K + 168 * n + 8 * I by omega_arith])
      (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega_arith))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  obtain hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  obtain hsub : Region.Sub ⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩ (lowR σ) :=
    Offset.sub_base _ (by simp only [oBuf, oSave]; omega_arith)
  obtain hf : Frame [⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
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
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega_arith) (by simp only [oBuf]; omega_arith)
      (by simp only [oBuf]; omega_arith)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega_arith) (by simp only [oBuf]; omega_arith)
      (by simp only [oBuf]; omega_arith)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega_arith) (by simp only [oBuf]; omega_arith) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega_arith,
        byte_readW _ _ (by omega_arith), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega_arith,
        byte_of_lanes4 h.lanes hK (by omega_arith), L3_lt hk, show t + n + 1 = (t + n) + 1 from rfl,
        ← xofByte_A0 (B_length σ k) (by omega_arith),
        show 168 * (t + n) + (8 * I + (p - 168 * n - 8 * I)) = 168 * t + p by omega_arith]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith)]
      exact h.buf k hk p hp' (by omega_arith)

/-- Block `n` of each state's output. -/
theorem extractY_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {m₀ : Mem} {t n : Nat} (hn : n < 3) {s : State}
    (h : EXY w16 σ Y m₀ t n 0 0 s) :
    WP isa (.block extract) s fun s' => SqY w16 σ Y t (n + 1) s' ∧ Frame [lowR σ] m₀ s'.mem := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXY w16 σ Y m₀ t n K 0 s) (fun K s hK h => ?_) 4
    (Nat.le_refl _) s h) fun s' h' =>
      ⟨⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega_arith) (by omega_arith)⟩, h'.fr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXY w16 σ Y m₀ t n K I s)
    (fun I s hI h => extY_step hp hn hK hI h) 21 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega_arith), h'.fr, h'.rbp⟩

/-- `squeeze`, to block `n`: after `n + 1` squeezes, with `rbp`, `r10` and
`r8` kept; it writes only below the saved registers. -/
theorem sqY_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t n : Nat} (hn : n < 3) {s : State}
    (h : SqY w16 σ Y t n s) (hbp : s.gpr .rbp = at' σ (oBuf + 168 * n)) :
    WP isa (squeeze fast) s fun s' => (SqY w16 σ (keccakF Y) t (n + 1) s' ∧ Frame [lowR σ] s.mem s'.mem) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r8 = s.gpr .r8 := by
  unfold squeeze
  exact permY_ok (fast := fast) hp hn h fun s' ⟨he, h14, hrc, hl, hb, hf, h₁, h₂, hg⟩ =>
    WP.mono (WP.keep [.rax] (extractY_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega_arith), hf,
      by rw [h₁, hbp]⟩) (by decide)) fun s'' ⟨h', k⟩ =>
        ⟨h', by rw [k.gpr (by decide), h₁], by rw [k.gpr (by decide), h₂],
          by rw [k.gpr (by decide), hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]⟩

/-- `SqY` does not depend on `rbp`, `r10` or the flags. -/
theorem SqY.frame {σ : State} {Y : Spec.Sha3.State} {t n : Nat} {s s' : State} (h : SqY w16 σ Y t n s)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) : SqY w16 σ Y t n s' := by
  obtain k : Keep [.rbp, .r10] s s' := ⟨fun r hr => hg r (fun e => hr (by simp [e])) (fun e => hr (by simp [e])), hrd, hwr⟩
  exact ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14], by rw [hm]; exact h.rc,
    by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩

/-- `squeezes b n`: after `b + n` squeezes; it writes only below the saved
registers. -/
theorem sqYs_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {t b n : Nat} (hn : 0 < n)
    (hbn : b + n ≤ 3) {s : State} (h : SqY w16 σ Y t b s) :
    WP isa (squeezes b n fast) s fun s' => SqY w16 σ (iterF n Y) t (b + n) s' ∧ Frame [lowR σ] s.mem s'.mem := by
  unfold squeezes
  refine WP.mono (blocks_ok (b := b) (P := fun i s' => SqY w16 σ (iterF (i - b) Y) t i s' ∧ Frame [lowR σ] s.mem s'.mem) hn
    (by omega_arith) (by simp only [oBuf]; omega_arith) (by decide)
    (fun _ _ _ ⟨h', hf⟩ hm hrd hwr hg => ⟨h'.frame hm hrd hwr hg, by rw [hm]; exact hf⟩)
    (fun i u hb hi ⟨hi', hf⟩ hbp => WP.mono (sqY_ok (fast := fast) hp (by omega_arith) hi' ?_)
      fun _ ⟨⟨h', hf'⟩, k⟩ => ⟨⟨?_, hf.trans hf'⟩, k.1, k.2.1⟩) ⟨by rw [Nat.sub_self]; exact h, Frame.refl _ _⟩)
    fun s' h' => by rwa [Nat.add_sub_cancel_left] at h'
  · rw [hbp, h.env.rbx, Offset.add_add, at', show oBuf + 168 * b + 168 * (i - b) = oBuf + 168 * i by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' hb]]
  · rwa [show i + 1 - b = (i - b) + 1 by omega_arith, iterF_succ]

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
      (Offset.sub_base (scr σ) (d := 32 * (50 + r) + 8 * k) (by simp only [oSave]; omega_arith))) (by decide)]
    exact h.rc r hr k hk
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * i + 8 * k) (by simp only [oSave]; omega_arith))) (by decide)]
    exact h.lanes i hi k hk
  · rw [hf (at' σ (oBuf + 504 * k + p)) fun r' hr' hc => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := oBuf + 504 * k + p) (n := 1) (by simp only [oBuf, oSave]; omega_arith)) _
      (Region.contains_self _ _) hc]
    exact h.buf k hk p (by omega_arith)

end VG.Proof.MlKem.X86_64.SH

end

end


/-!
# ML-KEM on x86-64: `Sample4.sampleH`, the sponge of `H` in the fourth state

From the entry state `σ` of `Sample4.sampleH` (with `vg_mlkem_sample_ntt4`'s
precondition, `S4.Pre`): the prologue, the round constants and the padded
seeds (`S4.start_ok`) write only the low scratch space and the saved
registers, apart from the sponge's state and blocks (`hR`, from
`scratch + 6720`), which therefore hold their values at entry (`HR`). The
fourth state is then overwritten with the sponge's (`hload_ok`), each of the
three squeezes first XORs the next block into it (`hxor_ok`), so that it is
the sponge's state after absorbing the three blocks (`habs`), which is
stored back (`hsave_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.Sha3 (keccakF RC stateAt bytesAt)
open VG.Proof.Sha3 (byteOf iterF xorAt byteOf_xorAt byteOf_eq)
open VG.Proof.Sha3.X86_64.X4 (la Lanes4 lane_ext)

/-! ## The sponge -/

/-- The sponge's state, and its block `i`. -/
abbrev hsA (σ : State) : Addr := at' σ oHS
abbrev hbA (σ : State) (i : Nat) : Addr := at' σ (oHB + 136 * i)

/-- The state after absorbing `n` of the blocks `bs` (each of 136 bytes) into `H`. -/
def habs (H : Spec.Sha3.State) (bs : Nat → List Byte) : Nat → Spec.Sha3.State
  | 0 => H
  | n + 1 => keccakF (xorAt (habs H bs n) 0 (bs n))

/-- The sponge's blocks at entry, and its state after absorbing `n` of them. -/
abbrev hblk (σ : State) (i : Nat) : List Byte := bytesAt σ.mem (hbA σ i) 136
abbrev hst (σ : State) (n : Nat) : Spec.Sha3.State := habs (stateAt σ.mem (hsA σ)) (hblk σ) n

/-- The sponge's state and blocks. -/
abbrev hR (σ : State) : Region := ⟨hsA σ, 608⟩

/-- The sponge's state and blocks hold their values at entry. -/
def HR (σ : State) (m : Mem) : Prop := ∀ i < 608, m (at' σ (oHS + i)) = σ.mem (at' σ (oHS + i))

theorem HR.refl (σ : State) : HR σ σ.mem := fun _ _ => rfl

theorem HR.frame {σ : State} {m m' : Mem} (h : HR σ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hR σ).Disjoint r) : HR σ m' := fun i hi => by
  rw [← h i hi, at', ← Offset.add_add]
  exact hf.bytes (R := hR σ) hd (show 608 ≤ 2 ^ 64 by decide) hi

theorem HR.word {σ : State} {m : Mem} (h : HR σ m) {d : Nat} (hd : d + 8 ≤ 608) :
    m.readW (at' σ (oHS + d)) 64 = σ.mem.readW (at' σ (oHS + d)) 64 :=
  Mem.readW_congr fun i hi => by
    show m (at' σ (oHS + d) + BitVec.ofNat 64 i) = σ.mem (at' σ (oHS + d) + BitVec.ofNat 64 i)
    rw [at', Offset.add_add, Nat.add_assoc]
    exact h _ (by omega_arith)

/-- The low scratch space is apart from the sponge's. -/
theorem low_hR (σ : State) : (lowR σ).Disjoint (hR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oHS]; omega_arith) (by simp only [oHS]; omega_arith)

theorem HR.low {σ : State} {m m' : Mem} (h : HR σ m) (hf : Frame [lowR σ] m m') : HR σ m' :=
  h.frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_hR σ).symm

/-- Lane `i` of a state in memory. -/
theorem stateAt_lane (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (stateAt m p)[i]! = m.readW (p + BitVec.ofNat 64 (8 * i)) 64 := by
  simp [stateAt, hi]

/-- A state in memory, lane by lane. -/
theorem stateAt_of_lanes {m : Mem} {p : Addr} {Y : Spec.Sha3.State}
    (h : ∀ i < 25, m.readW (p + BitVec.ofNat 64 (8 * i)) 64 = Y[i]!) : stateAt m p = Y := by
  apply Vector.ext
  intro i hi
  have := h i hi
  rw [VG.Proof.Sha3.getElem!_eq _ hi] at this
  simpa [stateAt] using this

/-- Lane `j` of a state with 136 bytes XORed into it. -/
theorem xorAt_lane (Y : Spec.Sha3.State) (m : Mem) (p : Addr) {j : Nat} (hj : j < 25) :
    (xorAt Y 0 (bytesAt m p 136))[j]! =
      if j < 17 then Y[j]! ^^^ m.readW (p + BitVec.ofNat 64 (8 * j)) 64 else Y[j]! := by
  refine lane_ext fun b hb => ?_
  obtain e := byteOf_eq (xorAt Y 0 (bytesAt m p 136)) hj hb
  obtain e2 := byteOf_eq Y hj hb
  rw [byteOf_xorAt _ _ _ (by omega_arith), VG.Proof.MlKem.bytesAt_length, e2] at e
  rw [VG.Proof.Sha3.getElem!_eq _ hj, ← e, VG.Proof.Sha3.getElem!_eq _ hj]
  split
  · rw [ite_eq_left (by omega_arith), BitVec.extractLsb'_xor, byte_readW _ _ (by omega_arith), Offset.add_add, Nat.sub_zero]
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 8 * j + b < 136 by omega_arith),
      Option.map_some, Option.getD_some]
  · rw [ite_eq_right (by omega_arith)]

/-! ## The start, apart from the sponge -/

/-- The prologue writes only the saved registers. -/
theorem proF_ok {σ : State} (hp : PreW w16 σ) :
    WP isa (.block pro) σ fun s => I0W w16 σ s ∧ Frame [⟨at' σ oSave, 40⟩] σ.mem s.mem := by
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (at' σ 4384) (σ.gpr .rbx)).writeW (at' σ 4392) (σ.gpr .rbp)).writeW (at' σ 4400)
          (σ.gpr .r12)).writeW (at' σ 4408) (σ.gpr .r13)).writeW (at' σ 4416) (σ.gpr .r14) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .r12 = sd σ ∧ s.gpr .r13 = aP σ ∧ s.gpr .r14 = 1)
    (by xrun [in_scr hp rfl (a := 4384) (n := 8) (by omega_arith), in_scr hp rfl (a := 4392) (n := 8) (by omega_arith),
      in_scr hp rfl (a := 4400) (n := 8) (by omega_arith), in_scr hp rfl (a := 4408) (n := 8) (by omega_arith),
      in_scr hp rfl (a := 4416) (n := 8) (by omega_arith)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨⟨⟨k1.2.1, k1.2.2, hbx, h12, h13,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩, h14⟩, ?_⟩
  · rw [hm1]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega_arith) only [oSave, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    obtain hin : ∀ a, a + 8 ≤ 8192 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 4384 (by omega_arith))).writeW (by simp) _
      (hin 4392 (by omega_arith))).writeW (by simp) _ (hin 4400 (by omega_arith))).writeW (by simp) _
      (hin 4408 (by omega_arith))).writeW (by simp) _ (hin 4416 (by omega_arith)))
  · rw [hm1]
    obtain hin : ∀ a, 4384 ≤ a → a + 8 ≤ 4424 → (⟨at' σ oSave, 40⟩ : Region).Contains (at' σ a) (64 / 8) :=
      fun a h₁ h₂ => Offset.contains _ (by simp only [oSave]; omega_arith) (by simp only [oSave]; omega_arith)
        (by simp only [oSave]; omega_arith)
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hin 4384 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (hin 4392 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (hin 4400 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (hin 4408 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (hin 4416 (by omega_arith) (by omega_arith)))

/-- The prologue, the round constants and the padded seeds, apart from the sponge. -/
theorem startF_ok {σ : State} (hp : PreW w16 σ) :
    WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ
      fun s => SqInvW w16 σ 0 s ∧ HR σ s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (proF_ok hp) fun s₁ ⟨h₁, f₁⟩ => WP.mono (rc_ok hp h₁.env) fun s₂ h₂ => ?_
  obtain he₂ : EnvW w16 σ s₂ := EnvW.low h₁.env (rs := [⟨at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega_arith))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain r₂ : HR σ s₂.mem := ((HR.refl σ).frame f₁ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oSave, oHS]; omega_arith)) (by simp only [oHS]; omega_arith)
        (by simp only [oSave]; omega_arith)).frame h₂.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [oRc, oHS]; omega_arith)) (by simp only [oHS]; omega_arith)
      (by simp only [oRc]; omega_arith)
  refine WP.mono (absorb_ok hp (m₁ := s₂.mem) ⟨he₂, by rw [h₂.keep.gpr (by decide), h₁.r14], Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨⟨a₃.env, a₃.r14, fun r hr k hk => ?_, lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega_arith)⟩,
      r₂.frame a₃.frame fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by simp only [oHS]; omega_arith) (by simp only [oHS]; omega_arith)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega_arith) (by omega_arith))
    (by decide)]
  exact h₂.rc r hr k hk

/-! ## The sponge's state to the fourth state -/

/-- After the first `i` lanes of the fourth state are the sponge's. -/
structure HLI (w16 : Bool) (σ : State) (i : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  w : ∀ j < 25, ∀ k < 4, s.mem.readW (la (scr σ) j k) 64 =
    if k = 3 ∧ j < i then (stateAt σ.mem (hsA σ))[j]! else (A0 (B σ k))[j]!
  hr : HR σ s.mem

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem hload_step {σ : State} (hp : PreW w16 σ) {i : Nat} (hi : i < 25) {s : State} (h : HLI w16 σ i s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (oHS + 8 * i))), .store (at_ .rbx (32 * i + 24)) .rax]) s
      (HLI w16 σ (i + 1)) := by
  refine wp_movm (a := at' σ (oHS + 8 * i)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by simp only [oHS]; omega_arith)) fun s₁ u₁ => wp_store (a := at' σ (32 * i + 24))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact in_scr hp h.env.wr (by omega_arith))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  obtain hv : s.mem.readW (at' σ (oHS + 8 * i)) 64 = (stateAt σ.mem (hsA σ))[i]! := by
    rw [h.hr.word (by omega_arith), stateAt_lane _ _ hi, hsA, at', at', Offset.add_add]
  obtain hm : s₂.mem = s.mem.writeW (at' σ (32 * i + 24)) ((stateAt σ.mem (hsA σ))[i]!) := by
    rw [m₂, u₁.mem, u₁.gpr, hv]
  obtain hsub : Region.Sub ⟨at' σ (32 * i + 24), 8⟩ (lowR σ) := Offset.sub_base _ (by simp only [oSave]; omega_arith)
  obtain hf : Frame [⟨at' σ (32 * i + 24), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨EnvW.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₂.trans u₁.rd) (w₂.trans u₁.wr) fun r hr => by
        rw [g₂, u₁.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun j hj k hk => ?_,
    h.hr.frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oHS]; omega_arith)) (by simp only [oHS]; omega_arith) (by omega_arith)⟩
  · have e := readW_writeW_off s.mem (scr σ) ((stateAt σ.mem (hsA σ))[i]!) (d := 32 * (50 + r) + 8 * k)
      (e := 32 * i + 24) (n := 8) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · rw [hm]
    by_cases e : j = i ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := e
      rw [show la (scr σ) j 3 = at' σ (32 * j + 24) from rfl, Mem.readW_writeW_self64, ite_eq_left ⟨rfl, by omega_arith⟩]
    · have e' := readW_writeW_off s.mem (scr σ) ((stateAt σ.mem (hsA σ))[i]!) (d := 32 * j + 8 * k)
        (e := 32 * i + 24) (n := 8) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [show la (scr σ) j k = scr σ + BitVec.ofNat 64 (32 * j + 8 * k) from rfl, e', ← la, h.w j hj k hk]
      by_cases c : k = 3 ∧ j < i
      · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega_arith⟩]
      · rw [ite_eq_right c, ite_eq_right (by omega_arith)]

theorem hload_eq : hload = (List.range 25).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (oHS + 8 * i))), .store (at_ .rbx (32 * i + 24)) .rax] := rfl

/-- The sponge's state to the fourth state. -/
theorem hload_ok {σ : State} (hp : PreW w16 σ) {s : State} (h : SqInvW w16 σ 0 s) (hr : HR σ s.mem) :
    WP isa (.block hload) s fun s' => SqY w16 σ (hst σ 0) 0 0 s' ∧ HR σ s'.mem := by
  rw [hload_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (HLI w16 σ) (fun i s hi h => hload_step hp hi h) 25 (Nat.le_refl _) s
    ⟨h.env, h.r14, h.rc, fun j hj k hk => ?_, hr⟩) fun s' h' =>
      ⟨⟨h'.env, h'.r14, h'.rc, fun j hj k hk => ?_, fun _ _ p hp' => absurd hp' (by omega_arith)⟩, h'.hr⟩
  · rw [h.lanes j hj k hk, ite_eq_right (by omega_arith)]; rfl
  · rw [h'.w j hj k hk]
    by_cases e : k = 3
    · subst e; rw [ite_eq_left ⟨rfl, hj⟩, L3_three]; rfl
    · rw [ite_eq_right (by omega_arith), L3_lt (by omega_arith)]; rfl

/-! ## The squeezes, each absorbing a block -/

/-- During the XOR of block `i` into the fourth state `Y`: its first `J` lanes. -/
structure HXI (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (i J : Nat) (s₀ s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  w : ∀ j < 25, ∀ k < 4, s.mem.readW (la (scr σ) j k) 64 =
    if k = 3 ∧ j < J then (xorAt Y 0 (hblk σ i))[j]! else (L3 σ i Y k)[j]!
  buf : ∀ k < 3, ∀ p < 168 * i, s.mem (at' σ (oBuf + 504 * k + p)) = VG.Proof.MlKem.xofByte (B σ k) p
  hr : HR σ s.mem
  r8 : s.gpr .r8 = hbA σ i
  keep : s.gpr .rbp = s₀.gpr .rbp ∧ s.gpr .r10 = s₀.gpr .r10
  fr : Frame [lowR σ] s₀.mem s.mem

open VG.Proof.Sha3.X86_64 (wp_movm wp_xorm wp_store wp_nil) in
theorem hxor_step {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {i J : Nat} (hi : i < 3) (hJ : J < 17)
    {s₀ s : State} (h : HXI w16 σ Y i J s₀ s) :
    WP isa (.block [.mov .rax (.mem (at_ .r8 (8 * J))), .alu .xor .rax (.mem (at_ .rbx (32 * J + 24))),
      .store (at_ .rbx (32 * J + 24)) .rax]) s (HXI w16 σ Y i (J + 1) s₀) := by
  obtain hb : hbA σ i + BitVec.ofNat 64 (8 * J) = at' σ (oHS + (200 + 136 * i + 8 * J)) := by
    rw [hbA, at', at', Offset.add_add, show oHB + 136 * i + 8 * J = oHS + (200 + 136 * i + 8 * J) by
      simp only [oHB, oHS]; omega_arith]
  refine wp_movm (a := hbA σ i + BitVec.ofNat 64 (8 * J)) (by rw [ea_at, h.r8])
    (by rw [hb]; exact in_scr' hp h.env.rd h.env.wr (by simp only [oHS]; omega_arith)) fun s₁ u₁ =>
    wp_xorm (a := at' σ (32 * J + 24)) (by rw [ea_at, u₁.other _ (by decide), h.env.rbx])
      (by rw [u₁.rd, u₁.wr]; exact in_scr' hp h.env.rd h.env.wr (by omega_arith)) fun s₂ u₂ =>
    wp_store (a := at' σ (32 * J + 24)) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.env.rbx])
      (by rw [u₂.wr, u₁.wr]; exact in_scr hp h.env.wr (by omega_arith)) fun s₃ g₃ m₃ r₃ w₃ => wp_nil ?_
  obtain hv : s₂.gpr .rax = (xorAt Y 0 (hblk σ i))[J]! := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hb, h.hr.word (by omega_arith), ← hb, show at' σ (32 * J + 24) = la (scr σ) J 3 from rfl,
      h.w J (by omega_arith) 3 (by decide), ite_eq_right (by omega_arith), L3_three, xorAt_lane _ _ _ (by omega_arith),
      ite_eq_left hJ, BitVec.xor_comm]
  obtain hm : s₃.mem = s.mem.writeW (at' σ (32 * J + 24)) ((xorAt Y 0 (hblk σ i))[J]!) := by
    rw [m₃, u₂.mem, u₁.mem, hv]
  obtain hsub : Region.Sub ⟨at' σ (32 * J + 24), 8⟩ (lowR σ) := Offset.sub_base _ (by simp only [oSave]; omega_arith)
  obtain hf : Frame [⟨at' σ (32 * J + 24), 8⟩] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hg : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r hr => by rw [g₃, u₂.other r hr, u₁.other r hr]
  refine ⟨EnvW.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₃.trans (u₂.rd.trans u₁.rd)) (w₃.trans (u₂.wr.trans u₁.wr)) fun r hr => hg r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide), h.r14], fun r hr k hk => ?_, fun j hj k hk => ?_, fun k hk p hp' => ?_,
    h.hr.frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oHS]; omega_arith)) (by simp only [oHS]; omega_arith) (by omega_arith),
    by rw [hg _ (by decide), h.r8], by rw [hg _ (by decide), hg _ (by decide)]; exact h.keep,
    h.fr.trans (hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩)⟩
  · have e := readW_writeW_off s.mem (scr σ) ((xorAt Y 0 (hblk σ i))[J]!) (d := 32 * (50 + r) + 8 * k)
      (e := 32 * J + 24) (n := 8) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · rw [hm]
    by_cases e : j = J ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := e
      rw [show la (scr σ) j 3 = at' σ (32 * j + 24) from rfl, Mem.readW_writeW_self64, ite_eq_left ⟨rfl, by omega_arith⟩]
    · have e' := readW_writeW_off s.mem (scr σ) ((xorAt Y 0 (hblk σ i))[J]!) (d := 32 * j + 8 * k)
        (e := 32 * J + 24) (n := 8) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [show la (scr σ) j k = scr σ + BitVec.ofNat 64 (32 * j + 8 * k) from rfl, e', ← la, h.w j hj k hk]
      by_cases c : k = 3 ∧ j < J
      · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega_arith⟩]
      · rw [ite_eq_right c, ite_eq_right (by omega_arith)]
  · rw [hm, wb_out _ _ _ (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith) (by omega_arith)]
    exact h.buf k hk p hp'

theorem hxor_eq : hxor = (List.range 17).flatMap (fun i => [.mov .rax (.mem (at_ .r8 (8 * i))),
    .alu .xor .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (32 * i + 24)) .rax]) ++
    ([.alu .add .r8 (.imm 136)] : List Instr) := rfl

open VG.Proof.Sha3.X86_64 (wp_addi wp_nil) in
/-- Block `i` XORed into the fourth state, and `r8` to the next. -/
theorem hxor_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {i : Nat} (hi : i < 3) {s : State}
    (h : SqY w16 σ Y 0 i s) (hr : HR σ s.mem) (h8 : s.gpr .r8 = hbA σ i) :
    WP isa (.block hxor) s fun s' => (SqY w16 σ (xorAt Y 0 (hblk σ i)) 0 i s' ∧ HR σ s'.mem ∧
      s'.gpr .r8 = hbA σ (i + 1) ∧ Frame [lowR σ] s.mem s'.mem) ∧
      s'.gpr .rbp = s.gpr .rbp ∧ s'.gpr .r10 = s.gpr .r10 := by
  rw [hxor_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun J t => HXI w16 σ Y i J s t) (fun J t hJ ht => hxor_step hp hi hJ ht)
    17 (Nat.le_refl _) s ⟨h.env, h.r14, h.rc, fun j hj k hk => ?_, fun k hk p hp' => ?_, hr, h8, ⟨rfl, rfl⟩,
      Frame.refl _ _⟩) fun t ht => wp_addi fun t₁ u₁ => wp_nil ?_
  · rw [h.lanes j hj k hk, ite_eq_right (by omega_arith), Nat.zero_add]
  · rw [h.buf k hk p hp', Nat.mul_zero, Nat.zero_add]
  · refine ⟨⟨⟨ht.env.keep (rs := [.r8]) u₁.mem ⟨fun r hr => u₁.other r (by simpa using hr), u₁.rd, u₁.wr⟩ (by decide),
        by rw [u₁.other _ (by decide), ht.r14], by rw [u₁.mem]; exact ht.rc, fun j hj k hk => ?_,
        fun k hk p hp' => by rw [u₁.mem, ht.buf k hk p hp', Nat.mul_zero, Nat.zero_add]⟩, by rw [u₁.mem]; exact ht.hr,
      ?_, by rw [u₁.mem]; exact ht.fr⟩, by rw [u₁.other _ (by decide)]; exact ht.keep.1,
      by rw [u₁.other _ (by decide)]; exact ht.keep.2⟩
    · rw [u₁.mem, ht.w j hj k hk, Nat.zero_add]
      by_cases e : k = 3
      · subst e
        rw [L3_three]
        by_cases c : j < 17
        · rw [ite_eq_left ⟨rfl, c⟩, L3_three]
        · rw [ite_eq_right (by omega_arith), L3_three, xorAt_lane _ _ _ hj, ite_eq_right c]
      · rw [ite_eq_right (by omega_arith), L3_lt (by omega_arith), L3_lt (by omega_arith)]
    · rw [u₁.gpr, ht.r8, hbA, hbA, at', at', show (136 : BitVec 32).signExtend 64 = BitVec.ofNat 64 136 from rfl, Offset.add_add,
        show oHB + 136 * i + 136 = oHB + 136 * (i + 1) by omega_arith]

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_nil) in
/-- The first `m` squeezes, each after XORing the next block into the fourth state. -/
theorem squeezesH'_ok {fast : Bool} {m : Nat} (hm0 : 0 < m) (hm3 : m ≤ 3) {σ : State} (hp : PreW w16 σ) {s : State}
    (h : SqY w16 σ (hst σ 0) 0 0 s) (hr : HR σ s.mem) :
    WP isa (squeezesHM.squeezesH' fast m) s fun s' => SqY w16 σ (hst σ m) 0 m s' ∧ HR σ s'.mem := by
  unfold squeezesHM.squeezesH'
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_nil ?_)
  obtain k : Keep [.r8] s s₂ := ⟨fun r hr => by
      rw [u₂.other r (by simpa using hr), u₁.other r (by simpa using hr)], u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  obtain hm : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  obtain h₂ : SqY w16 σ (hst σ 0) 0 0 s₂ := ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14],
    by rw [hm]; exact h.rc, by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩
  obtain r₂ : HR σ s₂.mem := by rw [hm]; exact hr
  obtain ebx : s₂.gpr .rbx = scr σ := by rw [k.gpr (by decide), h.env.rbx]
  obtain e₈ : s₂.gpr .r8 = hbA σ 0 := by
    rw [u₂.gpr, u₁.gpr, h.env.rbx, hbA, at', sx_ofNat (by simp only [oHB]; omega_arith), Nat.mul_zero, Nat.add_zero]
  refine WP.mono (blocks_ok (b := 0) (P := fun i t => SqY w16 σ (hst σ i) 0 i t ∧ HR σ t.mem ∧ t.gpr .r8 = hbA σ i)
    hm0 (by omega_arith) (by simp only [oBuf]; omega_arith) (by decide)
    (fun _ _ _ ⟨h', r', e'⟩ hm hrd hwr hg => ⟨h'.frame hm hrd hwr hg, by rw [hm]; exact r',
      by rw [hg _ (by decide) (by decide)]; exact e'⟩)
    (fun i t _ hi ⟨hi', ri, ei⟩ hbp => ?_) ⟨h₂, r₂, e₈⟩) fun t ⟨ht, rt, _⟩ => by rw [Nat.zero_add] at ht; exact ⟨ht, rt⟩
  unfold squeezeH
  refine WP.seq (WP.mono (hxor_ok hp (by omega_arith) hi' ri ei) fun t₁ ⟨⟨h₁, r₁, e₁, _⟩, bp₁, r10₁⟩ => ?_)
  refine WP.mono (sqY_ok (fast := fast) hp (by omega_arith) h₁ ?_) fun t₂ ⟨⟨h₃, f₃⟩, bp₃, r10₃, e₃⟩ =>
    ⟨⟨h₃, r₁.low f₃, by rw [e₃, e₁]⟩, by rw [bp₃, bp₁], by rw [r10₃, r10₁]⟩
  rw [bp₁, hbp, ebx, at', Offset.add_add, Nat.sub_zero]

/-- The three squeezes, each after XORing the next block into the fourth state. -/
theorem squeezesH_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {s : State} (h : SqY w16 σ (hst σ 0) 0 0 s)
    (hr : HR σ s.mem) : WP isa (squeezesH fast) s fun s' => SqY w16 σ (hst σ 3) 0 3 s' ∧ HR σ s'.mem :=
  squeezesH'_ok (by decide) (by decide) hp h hr

/-! ## The fourth state back to the sponge's -/

/-- During the copy of the fourth state: its first `i` lanes. -/
structure HSI (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (n i : Nat) (s : State) : Prop where
  sq : SqY w16 σ Y 0 n s
  w : ∀ j < i, s.mem.readW (at' σ (oHS + 8 * j)) 64 = Y[j]!

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem hsave_step {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {n i : Nat} (hn : n ≤ 3) (hi : i < 25)
    {s : State} (h : HSI w16 σ Y n i s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax]) s
      (HSI w16 σ Y n (i + 1)) := by
  refine wp_movm (a := at' σ (32 * i + 24)) (by rw [ea_at, h.sq.env.rbx])
    (in_scr' hp h.sq.env.rd h.sq.env.wr (by omega_arith)) fun s₁ u₁ => wp_store (a := at' σ (oHS + 8 * i))
      (by rw [ea_at, u₁.other _ (by decide), h.sq.env.rbx])
      (by rw [u₁.wr]; exact in_scr hp h.sq.env.wr (by simp only [oHS]; omega_arith)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  obtain hv : s.mem.readW (at' σ (32 * i + 24)) 64 = Y[i]! := by
    rw [show at' σ (32 * i + 24) = la (scr σ) i 3 from rfl, h.sq.lanes i hi 3 (by decide), L3_three]
  obtain hm : s₂.mem = s.mem.writeW (at' σ (oHS + 8 * i)) (Y[i]!) := by rw [m₂, u₁.mem, u₁.gpr, hv]
  obtain hf : Frame [⟨at' σ (oHS + 8 * i), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.sq.apart hn hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.base_disjoint _ (by simp only [oSave, oHS]; omega_arith) (by simp only [oHS]; omega_arith))
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by simp only [oSave, oHS]; omega_arith)) (by simp only [oSave]; omega_arith)
        (by simp only [oHS]; omega_arith))
    (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oHS]; omega_arith)⟩)
    (r₂.trans u₁.rd) (w₂.trans u₁.wr) fun r hr => by
      rw [g₂, u₁.other r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)], fun j hj => ?_⟩
  rw [hm]
  by_cases e : j = i
  · subst e; exact Mem.readW_writeW_self64 _ _ _
  · rw [rd64_off (by simp only [oHS]; omega_arith) (by simp only [oHS]; omega_arith) (by omega_arith)]
    exact h.w j (by omega_arith)

theorem hsave_eq : hsave = (List.range 25).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax] := rfl

/-- The fourth state to the sponge's, after `n` squeezes. -/
theorem hsave_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {n : Nat} {s : State} (h : SqY w16 σ Y 0 n s)
    (hn : n ≤ 3 := by decide) :
    WP isa (.block hsave) s fun s' => SqY w16 σ Y 0 n s' ∧ stateAt s'.mem (hsA σ) = Y := by
  rw [hsave_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (HSI w16 σ Y n) (fun i s hi h => hsave_step hp hn hi h) 25 (Nat.le_refl _) s
    ⟨h, fun _ h => absurd h (by omega_arith)⟩) fun s' h' => ⟨h'.sq, stateAt_of_lanes fun i hi => ?_⟩
  rw [hsA, at', Offset.add_add]
  exact h'.w i hi

end VG.Proof.MlKem.X86_64.SH

end

end


/-!
# ML-KEM on x86-64: `Sample4.sampleH`, the runs of the loop on three seeds

After the squeezes and the sponge's state stored back, the code runs
`vg_mlkem_sample_ntt4_avx2`'s loops (`S4Run.lean`) on the first three seeds
(`Q1`, `Q2`, `Done3`), keeping the sponge's state (`HS`): if one of them has
fewer than 256 coefficients after 168 iterations, the two more squeezes
permute all four states, the fourth no longer the sponge's.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)
open VG.Proof.MlKem (xofByte sampleAfter sampleAfter_full sampleNTT_eq)
open VG.Proof.Sha3 (iterF)

/-- The sponge's state is `Hf`. -/
def HS (σ : State) (Hf : Spec.Sha3.State) (m : Mem) : Prop := stateAt m (hsA σ) = Hf

/-- The scratch space from the sponge's state on, which the runs keep. -/
abbrev hkR (σ : State) : Region := ⟨hsA σ, 1472⟩

/-- `H` holds after writes apart from `hkR σ`. -/
def Stab (σ : State) (H : Mem → Prop) : Prop :=
  ∀ {m m' : Mem} {rs : List Region}, H m → Frame rs m m' → (∀ r ∈ rs, (hkR σ).Disjoint r) → H m'

theorem HS.stab (σ : State) (Hf : Spec.Sha3.State) : Stab σ (HS σ Hf) := fun {m m' rs} h hf hd => by
  unfold HS
  rw [VG.Proof.Sha3.stateAt_congr fun i hi => hf.bytes (R := hkR σ) hd (show 1472 ≤ 2 ^ 64 by decide) (show i < 1472 by omega_using [hi])]
  exact h

theorem low_hs (σ : State) : (lowR σ).Disjoint (hkR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oHS]; omega_using []) (by simp only [oHS]; omega_using [])

theorem cnt_hs (σ : State) : (cntR σ).Disjoint (hkR σ) :=
  Offset.disjoint (scr σ) (.inl (by simp only [oCnt, oHS]; omega_using [])) (by simp only [oCnt]; omega_using [])
    (by simp only [oHS]; omega_using [])

theorem poly_hs {σ : State} (hp : PreW w16 σ) {K : Nat} (hK : K < 4) : (cRegion w16 (poly4W w16 (aP σ) K)).Disjoint (hkR σ) :=
  (scr_poly hp hK (a := oHS) (n := 1472) (by simp only [oHS]; omega_using [])).symm

/-- After the first 168 iterations on the seeds before `K`. -/
structure Q1 (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (H : Mem → Prop) (K : Nat) (s : State) : Prop where
  sq : SqY w16 σ Y 0 3 s
  tab : TabOK s
  j : ∀ k < K, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < K, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)
  hs : H s.mem
  stab : Stab σ H

/-- After the two more squeezes, before the static's address. -/
structure R2 (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (H : Mem → Prop) (s : State) : Prop where
  sq : SqY w16 σ (iterF 2 Y) 3 2 s
  j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < 0 then 280 else 168)).length
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k (if k < 0 then 280 else 168))
  hs : H s.mem
  stab : Stab σ H

/-- After the 112 more iterations on the seeds before `K`. -/
structure Q2 (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (H : Mem → Prop) (K : Nat) (s : State) : Prop where
  sq : SqY w16 σ (iterF 2 Y) 3 2 s
  tab : TabOK s
  j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < K then 280 else 168)).length
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k (if k < K then 280 else 168))
  hs : H s.mem
  stab : Stab σ H

/-- The coefficients of each of the three seeds after 280 iterations, and whether they are 256. -/
structure Done3 (w16 : Bool) (σ : State) (H : Mem → Prop) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 3)
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 280)
  hs : H s.mem

/-- Whether each of the three seeds has 256 coefficients after `t` iterations. -/
def allFull3 (σ : State) (t : Nat) : Bool := (List.range 3).all fun k => (Lt σ k t).length == 256

theorem okN_full3 (σ : State) : okN σ 3 = if allFull3 σ 280 then 1 else 0 := by
  obtain e : ((List.range 3).all fun k => (sampleNTT minIterations (B σ k)).isSome) = allFull3 σ 280 := by
    simp only [allFull3, isSome_iff]
  unfold okN
  rw [e]

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-! ## The first runs -/

omit hp in
/-- `SqY` after the static's address. -/
theorem SqY.tab {Y : Spec.Sha3.State} {t n : Nat} {s s' : State} (h : SqY w16 σ Y t n s) (hm : s'.mem = s.mem)
    (k : Keep [.r11] s s') : SqY w16 σ Y t n s' :=
  ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14], by rw [hm]; exact h.rc, by rw [hm]; exact h.lanes,
    by rw [hm]; exact h.buf⟩

omit hp in
/-- The static's address, after the squeezes. -/
theorem tabY_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : SqY w16 σ Y 0 3 s) (hs : H s.mem) (hH : Stab σ H) :
    WP isa (.block tabAddr) s (Q1 w16 σ Y H 0) :=
  WP.mono (tabAddr_ok s) fun _ ⟨hm, k, ht⟩ => ⟨h.tab hm k, ht, fun _ hk => absurd hk (by omega_using []),
    fun _ hk => absurd hk (by omega_using []), by rw [hm]; exact hs, hH⟩

omit hp in
theorem lbY1 {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {s : State} (h : Q1 w16 σ Y H K s) : LBW w16 σ s K 0 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' _ => by simpa using h.sq.buf K hK p (by omega_using [hp']), Frame.refl _ _⟩

/-- The count of seed `K` kept, after its first 168 iterations. -/
theorem run1EndY_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {s s₂ : State} (h : Q1 w16 σ Y H K s)
    (h₂ : LAtW w16 σ s K 0 168 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (Q1 w16 σ Y H (K + 1)) := by
  refine WP.mono_syms (keepCnt_ok hp (by omega_using [hK]) h₂) fun s₃ ⟨hm, k⟩ sy => ?_
  obtain hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write (by omega_using [hK]) _
  obtain g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  obtain g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  obtain hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp (by omega_using [hK]))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp (by omega_using [hK]) (a := oSave) (n := 40) (by simp only [oSave]; omega_using [])) (sub_polyR (by omega_using [hK]))
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    h₂.lb.tab.of (k.gpr (by simp)) sy, fun k hk => ?_, fun k hk => ?_,
    h.stab (h.stab h.hs h₂.lb.fr fun r hr => by rw [List.mem_singleton.mp hr]; exact (poly_hs hp (by omega_using [hK])).symm) hf₃
      fun r hr => by rw [List.mem_singleton.mp hr]; exact (cnt_hs σ).symm, h.stab⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [rd64_off (by simp only [oCnt]; omega_using [hK, hk]) (by simp only [oCnt]; omega_using [hK]) (by omega_using [e]),
        cnt_poly hp (by omega_using [hK]) h₂.lb.fr (by omega_using [hK, hk]), h.j k (by omega_using [hk, e])]
  · refine st_cnt hp (by omega_using [hK, hk]) hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; exact h₂.stored
    · exact st_poly (by omega_using [hK]) (by omega_using [hK, hk]) e h₂.lb.fr (h.st k (by omega_using [hk, e])) (hL _ _)

/-- The first 168 iterations on seed `K`, and its count kept. -/
theorem run1Y_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {z : Bool} {s : State}
    (h : Q1 w16 σ Y H K s) : WP isa (run1 K w16 z) s (Q1 w16 σ Y H (K + 1)) := by
  unfold run1
  split
  · rename_i hz
    exact WP.seq (WP.mono (setupZ_ok hp (by omega_using [hK]) (lbY1 hK h)) fun s₁ ⟨h₁, h10⟩ =>
      WP.seq (WP.mono (zloop_ok hp hz.2 (by omega_using [hK]) (N := 10) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
        WP.seq (WP.mono (vgrp_ok hp (by omega_using [hK]) (by decide) (by decide) h₂.lv) fun _ ⟨h₃, _⟩ =>
          run1EndY_ok hp hK h h₃.lat)))
  · exact WP.seq (WP.mono (setup_ok hp (by omega_using [hK]) (lbY1 hK h)) fun s₁ ⟨h₁, h10⟩ =>
      WP.seq (WP.mono (loop_ok hp (by omega_using [hK]) (N := 21) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
        run1EndY_ok hp hK h h₂))

/-! ## The check -/

/-- After the counts' check. -/
structure Checked3 (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (H : Mem → Prop) (s : State) : Prop where
  prior : ∃ s₀, Q1 w16 σ Y H 3 s₀ ∧ s.mem = s₀.mem ∧ Keep [.rax, .r14] s₀ s
  r14 : s.gpr .r14 = if allFull3 σ 168 then 1 else 0
  zf : s.zf = some (!allFull3 σ 168)

theorem cntFlags3_ok {t : Nat} {s : State} (env : EnvW w16 σ s)
    (j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k t).length) :
    WP isa (.block cntFlags3) s fun s' =>
      (s'.gpr .r14 = (if allFull3 σ t then 1 else 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  obtain hin : ∀ k < 3, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oCnt + 8 * k)) 8 :=
    fun k hk => in_scr' hp env.rd env.wr (by simp only [oCnt]; omega_using [hk])
  obtain h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  obtain j0 := j 0 (by decide); have j1 := j 1 (by decide); have j2 := j 2 (by decide)
  simp only [oCnt, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 j0 j1 j2
  refine WP.keep _ ?_ (writesOnly_of (by decide))
  change WP isa (.block ([.mov32 .r14 (.imm 1),
    .mov .rax (.mem (at_ .rbx 4424)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4432)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax),
    .mov .rax (.mem (at_ .rbx 4440)), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])) s _
  xrun [env.rbx, h0, h1, h2, j0, j1, j2]
  simp only [cnt_bit (Lt_le σ _ _)]
  unfold allFull3
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  cases (Lt σ 0 t).length == 256 <;> cases (Lt σ 1 t).length == 256 <;> cases (Lt σ 2 t).length == 256 <;> rfl

/-- The counts' check, after the first runs. -/
theorem check3_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Q1 w16 σ Y H 3 s) :
    WP isa (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (Checked3 w16 σ Y H) := by
  apply WP.block_append
  refine WP.mono (cntFlags3_ok hp h.sq.env h.j) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull3 σ 168 <;> rfl

omit hp in
/-- Each of the three seeds has 256 coefficients after the first runs. -/
theorem Done3.of_full {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Checked3 w16 σ Y H s) (hf : allFull3 σ 168 = true) :
    Done3 w16 σ H s := by
  obtain ⟨s₀, h₀, hm, hk⟩ := h.prior
  obtain hfull : ∀ k < 3, (Lt σ k 168).length = 256 := by
    simpa only [allFull3, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  obtain he : ∀ k < 3, Lt σ k 280 = Lt σ k 168 := fun k hk =>
    sampleAfter_full (by rw [n_eq]; exact hfull k hk) 280 (by decide)
  refine ⟨h₀.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_, by rw [hm]; exact h₀.hs⟩
  · have hf' : allFull3 σ 280 = true := by
      simp only [allFull3, List.all_eq_true, List.mem_range, beq_iff_eq] at hf ⊢
      intro k hk; rw [he k hk]; exact hf k hk
    rw [h.r14, okN_full3, hf, hf']; rfl
  · rw [hm, he k hk']; exact h₀.st k hk'

/-! ## The second runs -/

/-- Before the two more squeezes: the counts and coefficients of the first runs. -/
structure M3 (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (H : Mem → Prop) (s : State) : Prop where
  sq : SqY w16 σ Y 3 0 s
  j : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 3, Stored w16 s.mem (poly4W w16 (aP σ) k) (Lt σ k 168)
  hs : H s.mem
  stab : Stab σ H

omit hp in
/-- `r14 ← 1`, after the check. -/
theorem reset3_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Checked3 w16 σ Y H s) :
    WP isa (.block [.mov32 .r14 (.imm 1)]) s (M3 w16 σ Y H) := by
  obtain ⟨s₀, h₀, hm₀, hk₀⟩ := h.prior
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s₁ ⟨⟨hm, hr⟩, hk⟩ => ?_
  obtain hm₁ : s₁.mem = s₀.mem := hm.trans hm₀
  obtain hk₁ : Keep [.rax, .r14] s₀ s₁ := (hk₀.trans hk).mono (by simp)
  exact ⟨⟨h₀.sq.env.keep hm₁ hk₁ (by simp), hr, by rw [hm₁]; exact h₀.sq.rc, by rw [hm₁]; exact h₀.sq.lanes,
    fun _ _ p hp' => absurd hp' (by omega_using [])⟩, by rw [hm₁]; exact h₀.j,
    by rw [hm₁]; exact h₀.st, by rw [hm₁]; exact h₀.hs, h₀.stab⟩

/-- The two more squeezes. -/
theorem sqM3_ok {fast : Bool} {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : M3 w16 σ Y H s) :
    WP isa (squeezes 0 2 fast) s (R2 w16 σ Y H) := by
  refine WP.mono (sqYs_ok (fast := fast) hp (by decide) (by decide) h.sq) fun s₂ ⟨q₂, hf⟩ =>
    ⟨q₂, fun k hk => ?_, fun k hk => ?_, h.stab h.hs hf fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_hs σ).symm, h.stab⟩
  · rw [ite_eq_right (by omega_using []), hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oCnt + 8 * k) (n := 8) (by simp only [oSave, oCnt]; omega_using [])
        (by simp only [oCnt]; omega_using [hk])).symm) (by decide), h.j k hk]
  · rw [ite_eq_right (by omega_using [])]
    exact stored_apart hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp (by omega_using [hk])).symm)
      (Lt_le σ k _) (h.st k hk)

omit hp in
/-- The static's address, after the two more squeezes. -/
theorem tabY2_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : R2 w16 σ Y H s) : WP isa (.block tabAddr) s (Q2 w16 σ Y H 0) :=
  WP.mono (tabAddr_ok s) fun _ ⟨hm, k, ht⟩ => ⟨h.sq.tab hm k, ht, by rw [hm]; exact h.j, by rw [hm]; exact h.st,
    by rw [hm]; exact h.hs, h.stab⟩

omit hp in
theorem lbY2 {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {s : State} (h : Q2 w16 σ Y H K s) : LBW w16 σ s K 168 s :=
  ⟨h.sq.env, rfl, h.tab, fun p hp' hb => by
    rw [h.sq.buf K hK p (by omega_using [hb])], Frame.refl _ _⟩

/-- The count of seed `K` kept, after its 112 more iterations. -/
theorem run2EndY_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {s s₂ : State} (h : Q2 w16 σ Y H K s)
    (h₂ : LAtW w16 σ s K 168 112 s₂) :
    WP isa (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) s₂ (Q2 w16 σ Y H (K + 1)) := by
  refine WP.mono_syms (keepCnt_ok hp (by omega_using [hK]) h₂) fun s₃ ⟨hm, k⟩ sy => ?_
  obtain hf₃ : Frame [cntR σ] s₂.mem s₃.mem := by rw [hm]; exact cnt_write (by omega_using [hK]) _
  obtain g₂ := env_regs h.sq.env h₂.lb.env h₂.lb.r14
  obtain g₃ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₃.gpr r = s₂.gpr r := fun r _ => k.gpr (by simp)
  obtain hL : ∀ k t, (Lt σ k t).length ≤ 256 := fun k t => Lt_le σ k t
  refine ⟨(h.sq.apart (by decide) h₂.lb.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp (by omega_using [hK]))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact scr_poly hp (by omega_using [hK]) (a := oSave) (n := 40) (by simp only [oSave]; omega_using [])) (sub_polyR (by omega_using [hK]))
      (h₂.lb.env.rd.trans h.sq.env.rd.symm) (h₂.lb.env.wr.trans h.sq.env.wr.symm) g₂).apart (by decide) hf₃
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_cnt) (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_cnt)
      sub_cntR k.2.1 k.2.2 g₃,
    h₂.lb.tab.of (k.gpr (by simp)) sy, fun k hk => ?_, fun k hk => ?_,
    h.stab (h.stab h.hs h₂.lb.fr fun r hr => by rw [List.mem_singleton.mp hr]; exact (poly_hs hp (by omega_using [hK])).symm) hf₃
      fun r hr => by rw [List.mem_singleton.mp hr]; exact (cnt_hs σ).symm, h.stab⟩
  · rw [hm]
    by_cases e : k = K
    · subst e; rw [Mem.readW_writeW_self64, ite_eq_left (by omega_using [])]
    · rw [rd64_off (by simp only [oCnt]; omega_using [hk]) (by simp only [oCnt]; omega_using [hK]) (by omega_using [e]),
        cnt_poly hp (by omega_using [hK]) h₂.lb.fr (by omega_using [hk]), h.j k hk]
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk', ite_eq_right (by omega_using [e, hk'])]
  · refine st_cnt hp (by omega_using [hk]) hf₃ ?_ (hL _ _)
    by_cases e : k = K
    · subst e; rw [ite_eq_left (by omega_using [])]; exact h₂.stored
    · have := st_poly (by omega_using [hK]) (by omega_using [hk]) e h₂.lb.fr (h.st k hk) (hL _ _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega_using [hk'])]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega_using [e, hk'])]

/-- 112 more iterations on seed `K`, and its count kept. -/
theorem run2Y_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {K : Nat} (hK : K < 3) {z : Bool} {s : State}
    (h : Q2 w16 σ Y H K s) : WP isa (run2 K w16 z) s (Q2 w16 σ Y H (K + 1)) := by
  obtain hj : s.mem.readW (at' σ (oCnt + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K 168).length := by
    rw [h.j K hK, ite_eq_right (by omega_using [])]
  obtain hst : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K 168) := by
    have := h.st K hK; rwa [ite_eq_right (by omega_using [])] at this
  unfold run2
  split
  · rename_i hz
    exact WP.seq (WP.mono (contSetupZ_ok hp (by omega_using [hK]) (lbY2 hK h) hj hst) fun s₁ ⟨h₁, h10⟩ =>
      WP.seq (WP.mono (zloop_ok hp hz.2 (by omega_using [hK]) (N := 7) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
        run2EndY_ok hp hK h h₂.lv.lat))
  · exact WP.seq (WP.mono (contSetup_ok hp (by omega_using [hK]) (lbY2 hK h) hj hst) fun s₁ ⟨h₁, h10⟩ =>
      WP.seq (WP.mono (loop_ok hp (by omega_using [hK]) (N := 14) (by decide) (by decide) (by decide) h₁ h10) fun _ h₂ =>
        run2EndY_ok hp hK h h₂))

/-- The counts' AND, after the second runs. -/
theorem last3_ok {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Q2 w16 σ Y H 3 s) : WP isa (.block cntFlags3) s (Done3 w16 σ H) := by
  obtain hj : ∀ k < 3, s.mem.readW (at' σ (oCnt + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (cntFlags3_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), by rw [hr, okN_full3]; split <;> rfl, fun k hk' => ?_,
      by rw [hm]; exact h.hs⟩
  rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

/-- The two more squeezes and the second runs, after the check. -/
theorem more3_ok {fast : Bool} {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Checked3 w16 σ Y H s) :
    WP isa (more3 fast w16) s (Done3 w16 σ H) := by
  unfold more3
  exact WP.seq (WP.mono (reset3_ok h) fun _ m => WP.seq (WP.mono (sqM3_ok hp m) fun _ q =>
    WP.seq (WP.mono (tabY2_ok q) fun _ q₀ => WP.seq (WP.mono (run2Y_ok hp (by decide) q₀) fun _ q₁ =>
    WP.seq (WP.mono (run2Y_ok hp (by decide) q₁) fun _ q₂ =>
      WP.seq (WP.mono (run2Y_ok hp (by decide) q₂) fun _ q₃ => last3_ok hp q₃))))))

/-- The branch on the check. -/
theorem branch3_ok {fast : Bool} {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : Checked3 w16 σ Y H s) :
    WP isa (.ite .e (more3 fast w16) (.block [])) s (Done3 w16 σ H) := by
  cases hf : allFull3 σ 168 with
  | false =>
    obtain hz : s.zf = some true := by rw [h.zf, hf]; rfl
    exact WP.ite true hz (fun _ => more3_ok hp h) (fun hb => absurd hb (by decide))
  | true =>
    obtain hz : s.zf = some false := by rw [h.zf, hf]; rfl
    exact WP.ite false hz (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil (Done3.of_full h hf))

end

end VG.Proof.MlKem.X86_64.SH

end

end


/-!
# ML-KEM on x86-64: `Sample4.sampleH`, correctness

The fragment's contract (`sampleHKW w16`): `vg_mlkem_sample_ntt4`'s precondition
and public data (`sample4K`), and as postcondition its result and
polynomials for the first three seeds, and the sponge's state at
`scratch + 6720` after absorbing the three blocks from `scratch + 6920`
(`habs`). The pieces in order (`correct`): the prologue, the round constants
and the padded seeds (`startF_ok`); the sponge's state to the fourth state
(`hload_ok`); the three squeezes absorbing the blocks (`squeezesH_ok`); the
fourth state back (`hsave_ok`); the table and the runs on the three seeds,
with the two more squeezes if one needs them (`SHRun.lean`); and the
epilogue (`end3_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt bytesAt)

/-- The contract of `Sample4.sampleH`: `vg_mlkem_sample_ntt4`'s on the first
three seeds, and the sponge of `H` at `scratch + 6720` absorbing the three
blocks at `scratch + 6920`; with 32-bit coefficients or, if `w16`, 16-bit
ones. -/
def sampleHKW (w16 : Bool) : Contract isa where
  pre := (sample4KW w16).pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 3).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
          then 1 else 0) ∧
      (∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
        PolyIsW (cw w16) s'.mem (poly4W w16 (s.gpr .rsi) k) f) ∧
      stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS) =
        SH.habs (stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS))
          (fun i => bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (Impl.MlKem.X86_64.Sample4.oHB + 136 * i)) 136) 3
  pub := sample4K.pub

/-- The contract of `Sample4.sampleHM m`: as `sampleHKW`, with the sponge
absorbing the first `m` blocks. -/
def sampleHMKW (w16 : Bool) (m : Nat) : Contract isa where
  pre := (sample4KW w16).pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 3).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
          then 1 else 0) ∧
      (∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
        PolyIsW (cw w16) s'.mem (poly4W w16 (s.gpr .rsi) k) f) ∧
      stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS) =
        SH.habs (stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 Impl.MlKem.X86_64.Sample4.oHS))
          (fun i => bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (Impl.MlKem.X86_64.Sample4.oHB + 136 * i)) 136) m
  pub := sample4K.pub

theorem sampleHKW_eq (w16 : Bool) : sampleHKW w16 = sampleHMKW w16 3 := rfl

namespace SH

variable {w16 : Bool}

open VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4

section
variable {σ : State} (hp : PreW w16 σ)
include hp

/-- The return value and the first three polynomials of `Sample4.sampleH`'s contracts. -/
def Post3 (w16 : Bool) (s s' : State) : Prop :=
  (s'.gpr .rax).setWidth 32 =
      (if (List.range 3).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
        then 1 else 0) ∧
    ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
      PolyIsW (cw w16) s'.mem (poly4W w16 (s.gpr .rsi) k) f

/-- The return value, and the callee-saved registers restored. -/
theorem end3G_ok {H : Mem → Prop} {s : State} (h : Done3 w16 σ H s) :
    WP isa (.block epi) s fun s' => Post3 w16 σ s' ∧ H s'.mem ∧ gprPreserved σ s' := by
  obtain hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      obtain h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      obtain h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk f e => ?_⟩, by rw [hm]; exact h.hs, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    split <;> rfl
  · rw [hm]; exact polyIs_of (h.st k hk) f e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega_using [])⟩)
      (by decide)

/-- The runs after the squeezes, keeping `H`. -/
theorem run3G_ok {fast : Bool} {Y : Spec.Sha3.State} {H : Mem → Prop} {s : State} (h : SqY w16 σ Y 0 3 s)
    (hs : H s.mem) (hH : Stab σ H) :
    WP isa (.seq (.block tabAddr) (.seq (run1 0 w16 fast) (.seq (run1 1 w16 fast) (.seq (run1 2 w16 fast) (tail3 fast w16))))) s fun s' =>
      Post3 w16 σ s' ∧ H s'.mem ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (tabY_ok h hs hH) fun _ p₀ => ?_)
  refine WP.seq (WP.mono (run1Y_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (run1Y_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (run1Y_ok hp (by decide) p₂) fun _ p₃ => ?_)))
  unfold tail3
  refine WP.seq (WP.mono (check3_ok hp p₃) fun _ c => WP.seq (WP.mono (branch3_ok hp c) fun s₅ d => ?_))
  exact WP.block_append (WP.mono (vz_ok s₅) fun _ ⟨hm, hk⟩ => end3G_ok hp
    ⟨d.env.keep hm hk (by decide), by rw [hk.gpr (by decide), d.r14], by rw [hm]; exact d.st,
      by rw [hm]; exact d.hs⟩)

/-- After the squeezes, with the sponge's state stored back. -/
theorem run3_ok {fast : Bool} {m : Nat} {Y : Spec.Sha3.State} {s : State} (h : SqY w16 σ Y 0 3 s)
    (hs : HS σ (hst σ m) s.mem) :
    WP isa (.seq (.block tabAddr) (.seq (run1 0 w16 fast) (.seq (run1 1 w16 fast) (.seq (run1 2 w16 fast) (tail3 fast w16))))) s fun s' =>
      (sampleHMKW w16 m).post σ s' ∧ gprPreserved σ s' :=
  WP.mono (run3G_ok (fast := fast) hp h hs (HS.stab σ _)) fun _ ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, b, c⟩, d⟩

end

theorem correctW {fast : Bool} (σ : State) (hs : (sampleHKW w16).pre σ) :
    ∃ t s', Exec isa (sampleH fast w16) σ t s' ∧ abiPreserved σ s' ∧ (sampleHKW w16).post σ s' := by
  rw [sampleHKW_eq] at hs ⊢
  obtain hp := preW_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (startF_ok hp) fun s₁ ⟨h₁, r₁⟩ =>
    WP.seq (WP.mono (hload_ok hp h₁ r₁) fun s₂ ⟨h₂, r₂⟩ =>
      WP.seq (WP.mono (squeezesH_ok (fast := fast) hp h₂ r₂) fun s₃ ⟨h₃, _⟩ =>
        WP.seq (WP.mono (hsave_ok hp h₃) fun s₄ ⟨h₄, e₄⟩ => run3_ok (fast := fast) hp h₄ e₄))))
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> cases w16 <;> decide +kernel) he hF.2, hF.1⟩

end SH

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: `Sample4.sampleH`, constant time but for the seeds

As `vg_mlkem_sample_ntt4_avx2` (`S4CT.lean`): two runs whose seeds and
pointers agree leak the same. The code but for the loops and the checks of
the counts is proven by the taint analysis from the pointers, with every
byte of the states secret: the sponge's state and blocks, which the fourth
state absorbs, flow only into the states, the fourth buffer and the
sponge's state, at fixed addresses. The loops of both runs read the same
output of the first three seeds (`S4.run_ct`), and the checks give both the
same flags (`branch3_ct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.SH

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem

theorem startH_ct : RelCT isa (S4.R4W w16 fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4))
    (S4.R4W w16 fun σ s => SqInvW w16 σ 0 s ∧ HR σ s.mem) :=
  relInv (fun σ s hp h => by subst h; exact startF_ok (preW_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))

theorem hload_ct : RelCT isa (S4.R4W w16 fun σ s => SqInvW w16 σ 0 s ∧ HR σ s.mem) (.block hload)
    (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 0) 0 0 s ∧ HR σ s.mem) :=
  relInv (fun σ s hp h => hload_ok (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

theorem squeezesH_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 0) 0 0 s ∧ HR σ s.mem)
    (squeezesH fast) (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HR σ s.mem) := by
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezesH fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, c⟩ := hsq
  exact relInv (fun σ s hp h => squeezesH_ok (fast := fast) (preW_of hp) h.1 h.2)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) c)

theorem hsave_ct : RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HR σ s.mem) (.block hsave)
    (S4.R4W w16 fun σ s => SqY w16 σ (hst σ 3) 0 3 s ∧ HS σ (hst σ 3) s.mem) :=
  relInv (fun σ s hp h => hsave_ok (preW_of hp) h.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

section
variable {Y : State → Spec.Sha3.State} {H : State → Mem → Prop}

theorem tabY_ct (hH : ∀ σ, Stab σ (H σ)) :
    RelCT isa (S4.R4W w16 fun σ s => SqY w16 σ (Y σ) 0 3 s ∧ H σ s.mem) (.block tabAddr)
      (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (H σ) 0 s) :=
  relInv (fun σ s _ h => tabY_ok h.1 h.2 (hH σ))
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.1.env h₂.1.env) (by taint_decide))

theorem run1Y_ct {K : Nat} (hK : K < 3) {z : Bool} {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (H σ) K s) (run1 K w16 z)
      (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (H σ) (K + 1) s) := by
  unfold run1
  split
  · rename_i hz
    exact run1Z_ct hz.2 (by omega_using [hK]) (fun σ s _ h => ⟨h.sq.env, lbY1 hK h⟩)
      (fun σ s₀ s hp h₀ hA => run1EndY_ok (preW_of hp) hK h₀ hA) c₂
  · obtain ⟨⟨_, c₁⟩, _⟩ := setup_taint (by omega_using [hK] : K < 4) w16
    exact run_ct (N := 21) (by omega_using [hK]) (by decide) (by decide) (by decide)
      (fun σ s hp h => ⟨h.sq.env, setup_ok (preW_of hp) (by omega_using [hK]) (lbY1 hK h)⟩)
      (fun σ s₀ s hp h₀ hA => run1EndY_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem run2Y_ct {K : Nat} (hK : K < 3) {z : Bool} {h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oCnt + 8 * K)) .rdi]) h₂).isSome = true) :
    RelCT isa (S4.R4W w16 fun σ s => Q2 w16 σ (Y σ) (H σ) K s) (run2 K w16 z)
      (S4.R4W w16 fun σ s => Q2 w16 σ (Y σ) (H σ) (K + 1) s) := by
  unfold run2
  split
  · rename_i hz
    exact run2Z_ct hz.2 (by omega_using [hK]) (fun σ s _ h => ⟨h.sq.env, lbY2 hK h, by rw [h.j K hK, ite_eq_right (by omega_using [])],
        by have := h.st K hK; rwa [ite_eq_right (by omega_using [])] at this⟩)
      (fun σ s₀ s hp h₀ hA => run2EndY_ok (preW_of hp) hK h₀ hA) c₂
  · obtain ⟨_, ⟨_, c₁⟩⟩ := setup_taint (by omega_using [hK] : K < 4) w16
    exact run_ct (N := 14) (by omega_using [hK]) (by decide) (by decide) (by decide)
      (fun σ s hp h => ⟨h.sq.env, contSetup_ok (preW_of hp) (by omega_using [hK]) (lbY2 hK h)
        (by rw [h.j K hK, ite_eq_right (by omega_using [])]) (by have := h.st K hK; rwa [ite_eq_right (by omega_using [])] at this)⟩)
      (fun σ s₀ s hp h₀ hA => run2EndY_ok (preW_of hp) hK h₀ hA) c₁ c₂

theorem pub_allFull3 {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (t : Nat) : allFull3 σ₁ t = allFull3 σ₂ t := by
  simp only [allFull3, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt hq (K := 0) (by decide), pub_Lt hq (K := 1) (by decide), pub_Lt hq (K := 2) (by decide)]

theorem check3_ct : RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (H σ) 3 s)
    (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (H σ) s) :=
  relInv (fun σ s hp h => check3_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem more3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (H σ) s) (more3 fast w16)
    (S4.R4W w16 fun σ s => Done3 w16 σ (H σ) s) := by
  unfold more3
  refine RelCT.seq (relInv (fun σ s _ h => reset3_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))) ?_
  have hsq : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
      (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes 0 2 fast) hc).isSome = true := by
    cases fast
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, csq⟩ := hsq
  refine RelCT.seq (relInv (fun σ s hp h => sqM3_ok (fast := fast) (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) csq)) ?_
  refine RelCT.seq (relInv (fun σ s _ h => tabY2_ok h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))) ?_
  refine RelCT.seq (run2Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run2Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact relInv (fun σ s hp h => last3_ok (preW_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem branch3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (H σ) s)
    (.ite .e (more3 fast w16) (.block [])) (S4.R4W w16 fun σ s => Done3 w16 σ (H σ) s) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull3 hq])
    (RelCT.mono more3_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (S4.R4W w16 fun σ s => Checked3 w16 σ (Y σ) (H σ) s ∧ allFull3 σ 168 = true) (.block [])
      (S4.R4W w16 fun σ s => Done3 w16 σ (H σ) s) :=
    relInv (fun σ s _ ⟨h, hf⟩ => WP.block_nil (Done3.of_full h hf)) (taintRel [] SampleNtt.nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull3 σ₁ 168 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull3 hq]; exact hf⟩⟩

theorem tail3_ct {fast : Bool} : RelCT isa (S4.R4W w16 fun σ s => Q1 w16 σ (Y σ) (H σ) 3 s) (tail3 fast w16)
    (fun _ _ => True) := by
  unfold tail3
  exact RelCT.seq check3_ct (RelCT.seq branch3_ct
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

end

theorem ctW {fast : Bool} : ConstantTime isa (sampleHKW w16).pre (sampleHKW w16).pub (sampleH fast w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq startH_ct (RelCT.seq hload_ct
    (RelCT.seq (squeezesH_ct (fast := fast)) (RelCT.seq hsave_ct
      (RelCT.seq (tabY_ct (Y := fun σ => hst σ 3) (H := fun σ => HS σ (hst σ 3)) fun σ => HS.stab σ _) ?_)))))
  refine RelCT.seq (run1Y_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (run1Y_ct (K := 2) (by decide) (by taint_decide)) ?_
  exact tail3_ct

end VG.Proof.MlKem.X86_64.SH
