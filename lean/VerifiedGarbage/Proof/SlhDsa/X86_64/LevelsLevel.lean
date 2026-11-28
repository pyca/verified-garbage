module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsLane
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, a group of four nodes

`levelLanes`: the lanes `A` set up for the nodes `j` to `j + 3` of height
`z + 1`, each lane `PK.seed ‖ ADRS ‖ node 2(j+k) ‖ node 2(j+k)+1` (`lanes_ok`,
`laneBytes`).
-/

-- separate module: the lanes and outputs of a group, built in parallel with `LevelsScan`.

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Tree
open VG.Proof.Sha3.X86_64 (Upd ea_at wp_mov wp_movm wp_addi)

/-- What `levelLanes` does: lane `k` gets the fields `ty`, `kp`, `z` and
`x + k` and the `2n` bytes from `b + 2nk`. -/
structure LanesPost (n : Nat) (S : Addr) (s s' : State) (b ty kp z x : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  ty : ∀ k < 4, ∀ i < 4, s'.mem (at' S (Layout.laneA k + n + 16 + i)) = (toByte ty 4).getD i 0
  kp : ∀ k < 4, ∀ i < 4, s'.mem (at' S (Layout.laneA k + n + 20 + i)) = (toByte kp 4).getD i 0
  z : ∀ k < 4, ∀ i < 4, s'.mem (at' S (Layout.laneA k + n + 24 + i)) = (toByte z 4).getD i 0
  x : ∀ k < 4, ∀ i < 4, s'.mem (at' S (Layout.laneA k + n + 28 + i)) = (toByte (x + k) 4).getD i 0
  msg : ∀ k < 4, ∀ i < 2 * n, s'.mem (at' S (Layout.laneA k + n + 32 + i)) = s.mem (at' S (b + 2 * n * k + i))
  frame : Frame ((List.range 4).map fun k => (⟨at' S (Layout.laneA k + n + 16), 16 + 2 * n⟩ : Region)) s.mem s'.mem

theorem laneA_le (k : Nat) (hk : k < 4) : 3296 ≤ Layout.laneA k ∧ Layout.laneA k + 128 ≤ 3808 := by
  simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hk]

/-- The four lanes, from `r10 = z`, `r9 = x` and `rsi = S + b`. -/
theorem lanes_four {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {z x b : Nat} {V7 V8 : BitVec 64}
    {s : State} (hbx : s.gpr .rbx = S) (h10 : s.gpr .r10 = BitVec.ofNat 64 z) (hz : z < 2 ^ 32)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 x) (hx : x + 3 < 2 ^ 32) (hsi : s.gpr .rsi = at' S b)
    (hb : 3808 ≤ b) (hb' : b + 8 * p.n ≤ 2 ^ 16)
    (h7 : s.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7) (h8 : s.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (nodeLane ⟨p.n, p.len⟩ 0 ++ (nodeLane ⟨p.n, p.len⟩ 1 ++ (nodeLane ⟨p.n, p.len⟩ 2 ++
      nodeLane ⟨p.n, p.len⟩ 3)))) s fun s' => LanesPost p.n S s s' b V7.toNat V8.toNat z x := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  -- each lane keeps the registers the next needs and the bytes outside it
  have keepV : ∀ {s s' : State} {k : Nat}, k < 4 → LanePost p.n S s s' (Layout.laneA k) (b + 2 * p.n * k)
      V7.toNat V8.toNat z (x + k) →
      ∀ o, o + 8 ≤ 3296 → s'.mem.readW (at' S o) 64 = s.mem.readW (at' S o) 64 := fun {s s' k} hk hl o ho => by
    have hla := laneA_le k hk
    refine hl.frame.readW (r := ⟨at' S o, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_scr S (.inl (by omega_using [ho, hla])) (by omega_using [ho]) (by omega_using [hla, hn32])
    · exact disj_scr S (.inl (by omega_using [ho, hla])) (by omega_using [ho]) (by omega_using [hla, hn32])
  have keepB : ∀ {s s' : State} {k : Nat}, k < 4 → LanePost p.n S s s' (Layout.laneA k) (b + 2 * p.n * k)
      V7.toNat V8.toNat z (x + k) →
      ∀ q, (q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + 128 ≤ q) → q < 2 ^ 16 →
        s'.mem (at' S q) = s.mem (at' S q) := fun {s s' k} hk hl q hq hq' => by
    have hla := laneA_le k hk
    have e := hl.frame.bytes (R := ⟨at' S q, 1⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact disj_scr S (by omega_using [hq, hn32]) (by omega_using [hq']) (by omega_using [hla, hn32])
      · exact disj_scr S (by omega_using [hq, hn32]) (by omega_using [hq']) (by omega_using [hla, hn32]))
      (by show 1 ≤ 2 ^ 64; decide) (show 0 < 1 by decide)
    simpa using e
  have v7 : Layout.oVar 4 7 + 8 ≤ 3296 := by decide
  have v8 : Layout.oVar 4 8 + 8 ≤ 3296 := by decide
  refine WP.block_append (WP.mono (lane_ok hn (k := 0) (by decide) hbx h10 hz h9 (by omega_using [hx])
    hsi hb (by omega_using [hb']) h7 h8 hw) fun s₁ l₀ => ?_)
  have g₁ : ∀ g, g ≠ .rax → g ≠ .rdx → g ≠ .r11 → s₁.gpr g = s.gpr g := l₀.gpr
  refine WP.block_append (WP.mono (lane_ok hn (k := 1) (by decide) (by rw [g₁ _ (by decide) (by decide) (by decide), hbx])
    (by rw [g₁ _ (by decide) (by decide) (by decide), h10]) hz
    (by rw [g₁ _ (by decide) (by decide) (by decide), h9]) (by omega_using [hx])
    (by rw [g₁ _ (by decide) (by decide) (by decide), hsi]) hb (by omega_using [hb'])
    (by rw [keepV (k := 0) (by decide) l₀ _ v7, h7]) (by rw [keepV (k := 0) (by decide) l₀ _ v8, h8])
    (by rw [l₀.wr]; exact hw)) fun s₂ l₁ => ?_)
  have g₂ : ∀ g, g ≠ .rax → g ≠ .rdx → g ≠ .r11 → s₂.gpr g = s.gpr g := fun g h1 h2 h3 => by
    rw [l₁.gpr _ h1 h2 h3, g₁ _ h1 h2 h3]
  refine WP.block_append (WP.mono (lane_ok hn (k := 2) (by decide) (by rw [g₂ _ (by decide) (by decide) (by decide), hbx])
    (by rw [g₂ _ (by decide) (by decide) (by decide), h10]) hz
    (by rw [g₂ _ (by decide) (by decide) (by decide), h9]) (by omega_using [hx])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hsi]) hb (by omega_using [hb'])
    (by rw [keepV (k := 1) (by decide) l₁ _ v7, keepV (k := 0) (by decide) l₀ _ v7, h7])
    (by rw [keepV (k := 1) (by decide) l₁ _ v8, keepV (k := 0) (by decide) l₀ _ v8, h8])
    (by rw [l₁.wr, l₀.wr]; exact hw)) fun s₃ l₂ => ?_)
  have g₃ : ∀ g, g ≠ .rax → g ≠ .rdx → g ≠ .r11 → s₃.gpr g = s.gpr g := fun g h1 h2 h3 => by
    rw [l₂.gpr _ h1 h2 h3, g₂ _ h1 h2 h3]
  refine WP.mono (lane_ok hn (k := 3) (by decide) (by rw [g₃ _ (by decide) (by decide) (by decide), hbx])
    (by rw [g₃ _ (by decide) (by decide) (by decide), h10]) hz
    (by rw [g₃ _ (by decide) (by decide) (by decide), h9]) (by omega_using [hx])
    (by rw [g₃ _ (by decide) (by decide) (by decide), hsi]) hb (by omega_using [hb'])
    (by rw [keepV (k := 2) (by decide) l₂ _ v7, keepV (k := 1) (by decide) l₁ _ v7,
      keepV (k := 0) (by decide) l₀ _ v7, h7])
    (by rw [keepV (k := 2) (by decide) l₂ _ v8, keepV (k := 1) (by decide) l₁ _ v8,
      keepV (k := 0) (by decide) l₀ _ v8, h8])
    (by rw [l₂.wr, l₁.wr, l₀.wr]; exact hw)) fun t' l3 => ?_
  -- bytes of the later lanes' outsides
  have kb3 : ∀ q, (q < 3680 + p.n + 16 ∨ 3808 ≤ q) → q < 2 ^ 16 → t'.mem (at' S q) = s₃.mem (at' S q) :=
    fun q hq hq' => keepB (k := 3) (by decide) l3 q hq hq'
  have kb2 : ∀ q, (q < 3552 + p.n + 16 ∨ 3680 ≤ q) → q < 2 ^ 16 → s₃.mem (at' S q) = s₂.mem (at' S q) :=
    fun q hq hq' => keepB (k := 2) (by decide) l₂ q hq hq'
  have kb1 : ∀ q, (q < 3424 + p.n + 16 ∨ 3552 ≤ q) → q < 2 ^ 16 → s₂.mem (at' S q) = s₁.mem (at' S q) :=
    fun q hq hq' => keepB (k := 1) (by decide) l₁ q hq hq'
  have kb0 : ∀ q, (q < 3296 + p.n + 16 ∨ 3424 ≤ q) → q < 2 ^ 16 → s₁.mem (at' S q) = s.mem (at' S q) :=
    fun q hq hq' => keepB (k := 0) (by decide) l₀ q hq hq'
  have fin0 : ∀ q, 3296 ≤ q → q < 3424 → t'.mem (at' S q) = s₁.mem (at' S q) := fun q h1 h2 => by
    rw [kb3 q (.inl (by omega_using [h2])) (by omega_using [h2]), kb2 q (.inl (by omega_using [h2])) (by omega_using [h2]),
      kb1 q (.inl (by omega_using [h2])) (by omega_using [h2])]
  have fin1 : ∀ q, 3424 ≤ q → q < 3552 → t'.mem (at' S q) = s₂.mem (at' S q) := fun q h1 h2 => by
    rw [kb3 q (.inl (by omega_using [h2])) (by omega_using [h2]), kb2 q (.inl (by omega_using [h2])) (by omega_using [h2])]
  have fin2 : ∀ q, 3552 ≤ q → q < 3680 → t'.mem (at' S q) = s₃.mem (at' S q) := fun q h1 h2 => by
    rw [kb3 q (.inl (by omega_using [h2])) (by omega_using [h2])]
  have src0 : ∀ q, 3808 ≤ q → q < 2 ^ 16 → s₁.mem (at' S q) = s.mem (at' S q) := fun q h1 h2 =>
    kb0 q (.inr (by omega_using [h1])) h2
  have src1 : ∀ q, 3808 ≤ q → q < 2 ^ 16 → s₂.mem (at' S q) = s.mem (at' S q) := fun q h1 h2 => by
    rw [kb1 q (.inr (by omega_using [h1])) h2, src0 q h1 h2]
  have src2 : ∀ q, 3808 ≤ q → q < 2 ^ 16 → s₃.mem (at' S q) = s.mem (at' S q) := fun q h1 h2 => by
    rw [kb2 q (.inr (by omega_using [h1])) h2, src1 q h1 h2]
  refine ⟨fun g h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [l3.rd, l₂.rd, l₁.rd, l₀.rd],
    by rw [l3.wr, l₂.wr, l₁.wr, l₀.wr], fun k hk i hi => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_,
    fun k hk i hi => ?_, fun k hk i hi => ?_, ?_⟩
  · rw [l3.gpr _ h1 h3 h7, g₃ _ h1 h3 h7]
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fin0 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₀.ty i hi
    · rw [fin1 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₁.ty i hi
    · rw [fin2 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₂.ty i hi
    · exact l3.ty i hi
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fin0 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₀.kp i hi
    · rw [fin1 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₁.kp i hi
    · rw [fin2 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₂.kp i hi
    · exact l3.kp i hi
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fin0 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₀.z i hi
    · rw [fin1 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₁.z i hi
    · rw [fin2 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₂.z i hi
    · exact l3.z i hi
  · rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fin0 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₀.x i hi
    · rw [fin1 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₁.x i hi
    · rw [fin2 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi])]; exact l₂.x i hi
    · exact l3.x i hi
  · have hsb : ∀ k < 4, 3808 ≤ b + 2 * p.n * k + i ∧ b + 2 * p.n * k + i < 2 ^ 16 := fun k hk => by
      rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        exact ⟨by omega_using [hb], by omega_using [hb', hi]⟩
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fin0 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]), l₀.msg i hi]
    · rw [fin1 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]), l₁.msg i hi, src0 _ (hsb 1 (by decide)).1 (hsb 1 (by decide)).2]
    · rw [fin2 _ (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]) (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hn32, hi]), l₂.msg i hi, src1 _ (hsb 2 (by decide)).1 (hsb 2 (by decide)).2]
    · rw [l3.msg i hi, src2 _ (hsb 3 (by decide)).1 (hsb 3 (by decide)).2]
  -- the frame
  · have sub2 : ∀ k < 4, ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + 16), 16⟩ : Region), ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩],
        ∃ r' ∈ ((List.range 4).map fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)), Region.Sub r r' :=
      fun k hk r hr => by
        refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.sub S (d := Layout.laneA k + p.n + 16) (e := Layout.laneA k + p.n + 16) (Nat.le_refl _)
            (by omega_using [])
        · exact Offset.sub S (d := Layout.laneA k + p.n + 32) (e := Layout.laneA k + p.n + 16) (by omega_using [])
            (by omega_using [])
    exact (l₀.frame.sub (sub2 0 (by decide))).trans ((l₁.frame.sub (sub2 1 (by decide))).trans
      ((l₂.frame.sub (sub2 2 (by decide))).trans (l3.frame.sub (sub2 3 (by decide)))))

/-- `levelLanes`' setup: `r10 = z + 1`, `r9 = ⌊V6 / 2^(z+1)⌋ + j`,
`rsi = S + no + 2jn`, before the four lanes. -/
theorem lanes_setup {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {no z j : Nat} {V6 : BitVec 64}
    {t : State} {Q : State → Prop} (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 z) (hbp : t.gpr .rbp = BitVec.ofNat 64 j) (hz : z < 14)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (k : ∀ s, s.mem = t.mem → s.rd = t.rd → s.wr = t.wr →
      (∀ g, g ≠ .rcx → g ≠ .rsi → g ≠ .r9 → g ≠ .r10 → s.gpr g = t.gpr g) →
      s.gpr .r10 = BitVec.ofNat 64 (z + 1) → s.gpr .r9 = BitVec.ofNat 64 (V6.toNat / 2 ^ (z + 1) + j) →
      s.gpr .rsi = at' S (no + 2 * j * p.n) →
      WP isa (.block (nodeLane ⟨p.n, p.len⟩ 0 ++ (nodeLane ⟨p.n, p.len⟩ 1 ++ (nodeLane ⟨p.n, p.len⟩ 2 ++
        nodeLane ⟨p.n, p.len⟩ 3)))) s Q) :
    WP isa (.block (levelLanes ⟨p.n, p.len⟩)) t Q := by
  have e : levelLanes ⟨p.n, p.len⟩ =
      [.mov .r10 (.reg .r14), .alu .add .r10 (.imm 1), .mov .r9 (.mem (var 6)), .mov .rcx (.reg .r10),
        .shiftCl .shr .r9, .alu .add .r9 (.reg .rbp), .mov .rsi (.reg .rbp)] ++
      (Impl.SlhDsa.X86_64.Wots.mulN p.n .rsi .rcx ++
        (.alu .add .rsi (.reg .rsi) :: .alu .add .rsi (.reg .r12) ::
          (nodeLane ⟨p.n, p.len⟩ 0 ++ (nodeLane ⟨p.n, p.len⟩ 1 ++ (nodeLane ⟨p.n, p.len⟩ 2 ++ nodeLane ⟨p.n, p.len⟩ 3))))) := by
    simp only [levelLanes, show List.range 4 = [0, 1, 2, 3] from rfl, List.append_assoc, List.nil_append,
      List.cons_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [e]
  refine WP.block_append (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ =>
    wp_movm (a := at' S (Layout.oVar 4 6)) (by rw [var, ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
      (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_scr' hw (by decide)) fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => wp_shrcl fun s₅ u₅ => wp_add fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_)
  refine mulN_ok hn (by decide) fun s₈ g₈ o₈ m₈ r₈ w₈ => wp_add fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => ?_
  have hgo : ∀ g, g ≠ .rcx → g ≠ .rsi → g ≠ .r9 → g ≠ .r10 → s₁₀.gpr g = t.gpr g := fun g h1 h2 h3 h4 => by
    rw [u₁₀.other _ h2, u₉.other _ h2, o₈ _ h2 h1, u₇.other _ h2, u₆.other _ h3, u₅.other _ h3, u₄.other _ h1,
      u₃.other _ h3, u₂.other _ h4, u₁.other _ h4]
  have a2 : s₂.gpr .r10 = BitVec.ofNat 64 z + 1 := by
    rw [u₂.gpr, u₁.gpr, h14]; rfl
  have a3 : s₃.gpr .r9 = V6 := by rw [u₃.gpr, u₂.mem, u₁.mem, h6]
  have a4 : s₄.gpr .rcx = BitVec.ofNat 64 z + 1 := by rw [u₄.gpr, u₃.other _ (by decide), a2]
  have a4' : s₄.gpr .r9 = V6 := by rw [u₄.other _ (by decide), a3]
  have h9 : s₁₀.gpr .r9 = BitVec.ofNat 64 (V6.toNat / 2 ^ (z + 1) + j) := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), o₈ _ (by decide) (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅.gpr, a4', a4, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbp]
    have hz1 : (BitVec.ofNat 64 z + 1).toNat % 64 = z + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega_using [hz]
    have hsh : V6 >>> (z + 1) = BitVec.ofNat 64 (V6.toNat / 2 ^ (z + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) V6.isLt)]
    rw [hz1, hsh, BitVec.ofNat_add]
  have r12₉ : s₉.gpr .r12 = at' S no := by
    rw [← u₁₀.other _ (by decide), hgo _ (by decide) (by decide) (by decide) (by decide), h12]
  have hsi : s₁₀.gpr .rsi = at' S (no + 2 * j * p.n) := by
    rw [u₁₀.gpr, r12₉, u₉.gpr, g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbp, ← BitVec.ofNat_mul,
      ← BitVec.ofNat_add, at', at', show no + 2 * j * p.n = (j * p.n + j * p.n) + no by
        rw [Nat.mul_assoc]; omega_using [], BitVec.ofNat_add (j * p.n + j * p.n) no]
    ac_rfl
  have h10 : s₁₀.gpr .r10 = BitVec.ofNat 64 (z + 1) := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), o₈ _ (by decide) (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), a2,
      BitVec.ofNat_add]; rfl
  exact k s₁₀ (by rw [u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₁₀.rd, u₉.rd, r₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₁₀.wr, u₉.wr, w₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) hgo h10 h9 hsi

/-- `levelLanes` from the group's `j` (`rbp`), at height `z` (`r14`), with the
nodes at `S + no` (`r12`) and the parameters `V6`, `V7`, `V8` in frame 4. -/
theorem lanes_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {no z j : Nat} {V6 V7 V8 : BitVec 64}
    {t : State} (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (h14 : t.gpr .r14 = BitVec.ofNat 64 z)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 j) (hz : z < 14) (hj : j < 2 ^ 14) (hno : 3808 ≤ no)
    (hno' : no + 2 * j * p.n + 8 * p.n ≤ 2 ^ 16)
    (h6 : t.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6) (h7 : t.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7)
    (h8 : t.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8) (hV6 : V6.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) :
    WP isa (.block (levelLanes ⟨p.n, p.len⟩)) t fun t' =>
      LanesPost p.n S t t' (no + 2 * j * p.n) V7.toNat V8.toNat (z + 1) (V6.toNat / 2 ^ (z + 1) + j) := by
  refine lanes_setup hn hbx h12 h14 hbp hz h6 hw fun s hm hrd hwr hgo h10 h9 hsi => ?_
  have hx : V6.toNat / 2 ^ (z + 1) + j + 3 < 2 ^ 32 := by
    have : V6.toNat / 2 ^ (z + 1) ≤ V6.toNat / 2 := Nat.div_le_div_left (a := V6.toNat)
      (Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega_using []))) (by decide : 0 < 2)
    omega_using [this, hV6, hj]
  refine WP.mono (lanes_four hn (V7 := V7) (V8 := V8) (by rw [hgo _ (by decide) (by decide) (by decide) (by decide), hbx])
    h10 (by omega_using [hz]) h9 hx hsi (by omega_using [hno]) hno' (by rw [hm, h7]) (by rw [hm, h8])
    (by rw [hwr]; exact hw)) fun t' l => ?_
  exact ⟨fun g h1 h2 h3 h4 h5 h6 h7 => by rw [l.gpr g h1 h2 h3 h4 h5 h6 h7, hgo g h2 h4 h5 h6],
    by rw [l.rd, hrd], by rw [l.wr, hwr], l.ty, l.kp, l.z, l.x, fun k hk i hi => by rw [l.msg k hk i hi, hm],
    by rw [← hm]; exact l.frame⟩

/-! ## The outputs -/

/-- A byte of `scratch` outside the one region a frame changes. -/
theorem frame_byte {S : Addr} {o l q : Nat} {m m' : Mem} (hf : Frame [⟨at' S o, l⟩] m m')
    (hq : q < o ∨ o + l ≤ q) (h₁ : o + l ≤ 2 ^ 16) (h₂ : q < 2 ^ 16) : m' (at' S q) = m (at' S q) := by
  have e := hf.bytes (R := ⟨at' S q, 1⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega_using [hq]) (by omega_using [h₂]) h₁)
    (by show 1 ≤ 2 ^ 64; decide) (show 0 < 1 by decide)
  simpa using e

/-- What `levelOut` does: the four outputs copied to the nodes `j` to `j + 3`
at `S + no`, `rbp` advanced by 4 and compared with the count `P` (`r15`). -/
structure OutPost (n : Nat) (S : Addr) (s s' : State) (no j P : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rbp → s'.gpr g = s.gpr g
  bp : s'.gpr .rbp = BitVec.ofNat 64 (j + 4)
  cf : s'.cf = some (decide (j + 4 < P))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ k < 4, ∀ i < n, s'.mem (at' S (no + (j + k) * n + i)) = s.mem (at' S (Layout.laneA k + n + 32 + i))
  frame : Frame [⟨at' S (no + j * n), 4 * n⟩] s.mem s'.mem

theorem out_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {no j P : Nat} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = at' S no) (hbp : t.gpr .rbp = BitVec.ofNat 64 j)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 P) (hj : j < 2 ^ 16) (hP : P < 2 ^ 64) (hno : 3808 ≤ no)
    (hno' : no + (j + 4) * p.n ≤ 2 ^ 16) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) :
    WP isa (.block (levelOut ⟨p.n, p.len⟩)) t fun t' => OutPost p.n S t t' no j P := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have h8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hjn : no + j * p.n + 4 * p.n ≤ 2 ^ 16 := by rw [Nat.add_mul] at hno'; omega_using [hno']
  simp only [levelOut, show List.range 4 = [0, 1, 2, 3] from rfl, List.append_assoc, List.nil_append,
    List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Layout.msgOff]
  refine wp_mov fun s₁ u₁ => mulN_ok hn (by decide) fun s₂ g₂ o₂ m₂ r₂ w₂ => wp_add fun s₃ u₃ => ?_
  have hd : s₃.gpr .rdx = at' S (no + j * p.n) := by
    rw [u₃.gpr, o₂ .r12 (by decide) (by decide), u₁.other .r12 (by decide), h12, g₂, u₁.gpr, hbp,
      ← BitVec.ofNat_mul, at', at', Nat.add_comm no, BitVec.ofNat_add (j * p.n) no]
    ac_rfl
  have g₃ : ∀ g, g ≠ .rcx → g ≠ .rdx → s₃.gpr g = t.gpr g := fun g h1 h2 => by
    rw [u₃.other _ h2, o₂ _ h2 h1, u₁.other _ h2]
  have hm₃ : s₃.mem = t.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hb₃ : s₃.gpr .rbx = S + BitVec.ofNat 64 0 := by rw [g₃ _ (by decide) (by decide), hbx]; exact scr0 S
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₃.wr := by rw [u₃.wr, w₂, u₁.wr]; exact hw
  have hla : ∀ k < 4, 0 + (Layout.laneA k + (p.n + 32)) + 8 * (p.n / 8) ≤ 3808 := fun k hk => by
    have := laneA_le k hk; omega_using [this, h8, hn32]
  have hdst : ∀ k < 4, no + j * p.n + p.n * k + 8 * (p.n / 8) ≤ 2 ^ 16 := fun k hk => by
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      omega_using [hjn, h8]
  refine WP.block_append (WP.mono (copy_ok (by decide) (by decide) _ s₃ hd hb₃ hw₃
    (by omega_using [hla 0 (by decide)]) (hdst 0 (by decide)) (.inl (by omega_using [hla 0 (by decide), hno])))
    fun s₄ h₄ => ?_)
  obtain ⟨g₄, r₄, w₄, c₄, f₄⟩ := h₄
  refine WP.block_append (WP.mono (copy_ok (by decide) (by decide) _ s₄ (by rw [g₄ _ (by decide), hd])
    (by rw [g₄ _ (by decide), hb₃]) (by rw [w₄]; exact hw₃)
    (by omega_using [hla 1 (by decide)]) (hdst 1 (by decide)) (.inl (by omega_using [hla 1 (by decide), hno])))
    fun s₅ h₅ => ?_)
  obtain ⟨g₅, r₅, w₅, c₅, f₅⟩ := h₅
  refine WP.block_append (WP.mono (copy_ok (by decide) (by decide) _ s₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), hd]) (by rw [g₅ _ (by decide), g₄ _ (by decide), hb₃])
    (by rw [w₅, w₄]; exact hw₃)
    (by omega_using [hla 2 (by decide)]) (hdst 2 (by decide)) (.inl (by omega_using [hla 2 (by decide), hno])))
    fun s₆ h₆ => ?_)
  obtain ⟨g₆, r₆, w₆, c₆, f₆⟩ := h₆
  refine WP.block_append (WP.mono (copy_ok (by decide) (by decide) _ s₆
    (by rw [g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide), hd])
    (by rw [g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide), hb₃]) (by rw [w₆, w₅, w₄]; exact hw₃)
    (by omega_using [hla 3 (by decide)]) (hdst 3 (by decide)) (.inl (by omega_using [hla 3 (by decide), hno])))
    fun s₇ h₇ => ?_)
  obtain ⟨g₇, r₇, w₇, c₇, f₇⟩ := h₇
  refine wp_addi fun s₈ u₈ => wp_cmpr fun s₉ g₉ m₉ r₉ w₉ _ cf₉ => WP.block_nil ?_
  have g₇' : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → s₇.gpr g = t.gpr g := fun g h1 h2 h3 => by
    rw [g₇ _ h1, g₆ _ h1, g₅ _ h1, g₄ _ h1, g₃ _ h2 h3]
  have hbp₈ : s₈.gpr .rbp = BitVec.ofNat 64 (j + 4) := by
    rw [u₈.gpr, g₇' _ (by decide) (by decide) (by decide), hbp, BitVec.ofNat_add]; rfl
  have hm₉ : s₉.mem = s₇.mem := by rw [m₉, u₈.mem]
  -- the bytes each copy wrote
  have hidx : ∀ k < 4, ∀ i < p.n, no + (j + k) * p.n + i = no + j * p.n + p.n * k + i := fun k _ i _ => by
    rw [Nat.add_mul, Nat.mul_comm k]; omega_using []
  refine ⟨fun g h1 h2 h3 h4 => ?_, by rw [g₉, hbp₈], ?_, by rw [r₉, u₈.rd, r₇, r₆, r₅, r₄, u₃.rd, r₂, u₁.rd],
    by rw [w₉, u₈.wr, w₇, w₆, w₅, w₄, u₃.wr, w₂, u₁.wr], fun k hk i hi => ?_, ?_⟩
  · rw [g₉, u₈.other _ h4, g₇' _ h1 h2 h3]
  · rw [cf₉, hbp₈, u₈.other _ (by decide), g₇' _ (by decide) (by decide) (by decide), h15, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj]), Nat.mod_eq_of_lt hP]
  · rw [hm₉, hidx k hk i hi]
    -- the lanes, as the copies leave them
    have src : ∀ q, q < 3808 → s₆.mem (at' S q) = t.mem (at' S q) ∧ s₅.mem (at' S q) = t.mem (at' S q) ∧
        s₄.mem (at' S q) = t.mem (at' S q) := fun q hq => by
      have e4 := frame_byte f₄ (q := q) (.inl (by omega_using [hq, hno])) (hdst 0 (by decide)) (by omega_using [hq])
      have e5 := frame_byte f₅ (q := q) (.inl (by omega_using [hq, hno])) (hdst 1 (by decide)) (by omega_using [hq])
      have e6 := frame_byte f₆ (q := q) (.inl (by omega_using [hq, hno])) (hdst 2 (by decide)) (by omega_using [hq])
      rw [hm₃] at e4
      exact ⟨by rw [e6, e5, e4], by rw [e5, e4], e4⟩
    have hq : ∀ k < 4, 0 + (Layout.laneA k + (p.n + 32)) + i < 3808 := fun k hk => by
      have := hla k hk; omega_using [this, hi, h8]
    have hlane : Layout.laneA k + p.n + 32 + i = 0 + (Layout.laneA k + (p.n + 32)) + i := by omega_using []
    rw [hlane]
    have hi8 : i < 8 * (p.n / 8) := by omega_using [hi, h8]
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [frame_byte f₇ (.inl (by omega_using [hi])) (hdst 3 (by decide)) (by omega_using [hi, h8, hdst 0 (by decide)]),
        frame_byte f₆ (.inl (by omega_using [hi])) (hdst 2 (by decide)) (by omega_using [hi, h8, hdst 0 (by decide)]),
        frame_byte f₅ (.inl (by omega_using [hi])) (hdst 1 (by decide)) (by omega_using [hi, h8, hdst 0 (by decide)]),
        c₄ i hi8, hm₃]
    · rw [frame_byte f₇ (.inl (by omega_using [hi])) (hdst 3 (by decide)) (by omega_using [hi, h8, hdst 1 (by decide)]),
        frame_byte f₆ (.inl (by omega_using [hi])) (hdst 2 (by decide)) (by omega_using [hi, h8, hdst 1 (by decide)]),
        c₅ i hi8, (src _ (hq 1 (by decide))).2.2]
    · rw [frame_byte f₇ (.inl (by omega_using [hi])) (hdst 3 (by decide)) (by omega_using [hi, h8, hdst 2 (by decide)]),
        c₆ i hi8, (src _ (hq 2 (by decide))).2.1]
    · rw [c₇ i hi8, (src _ (hq 3 (by decide))).1]
  · rw [hm₉, ← hm₃]
    have sub1 : ∀ k < 4, ∀ r ∈ [(⟨S + BitVec.ofNat 64 (no + j * p.n + p.n * k), 8 * (p.n / 8)⟩ : Region)],
        ∃ r' ∈ [(⟨at' S (no + j * p.n), 4 * p.n⟩ : Region)], Region.Sub r r' := fun k hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, Offset.sub S (d := no + j * p.n + p.n * k) (e := no + j * p.n)
        (by omega_using []) ?_⟩
      rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> omega_using [h8]
    exact (f₄.sub (sub1 0 (by decide))).trans ((f₅.sub (sub1 1 (by decide))).trans
      ((f₆.sub (sub1 2 (by decide))).trans (f₇.sub (sub1 3 (by decide)))))

/-! ## A lane's message -/

/-- Lane `k` after `levelLanes`: `PK.seed ‖ ADRS ‖` the `2n` bytes from `b + 2nk`. -/
theorem lane_bytes {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {t t₁ : State}
    {pkSeed a16 : List Byte} {b ty kp z x k : Nat} (hE : Env p t.mem S pkSeed a16) (ha : a16.length = 16)
    (l : LanesPost p.n S t t₁ b ty kp z x) (hk : k < 4) :
    bytesAt t₁.mem (at' S (Layout.laneA k)) (3 * p.n + 32) =
      pkSeed ++ nodeAdrs a16 ty kp z (x + k) ++ bytesAt t.mem (at' S (b + 2 * p.n * k)) (2 * p.n) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hl : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hpk : pkSeed.length = p.n := by rw [← hE.seedA k hk]; simp [bytesAt]
  have hkeep : ∀ i < p.n + 16, t₁.mem (at' S (Layout.laneA k + i)) = t.mem (at' S (Layout.laneA k + i)) :=
    fun i hi => by
      have e := l.frame.bytes (R := ⟨at' S (Layout.laneA k + i), 1⟩) (fun r hr => by
          simp only [List.mem_map, List.mem_range] at hr
          obtain ⟨k', hk', rfl⟩ := hr
          refine disj_scr S ?_ (by rw [hl]; omega_using [hk, hi, hn32]) (by rw [hl]; omega_using [hk', hn32])
          rw [hl, hl]
          rcases Nat.lt_trichotomy k k' with h | h | h
          · exact .inl (by omega_using [h, hi, hn32])
          · exact .inl (by omega_using [h, hi])
          · exact .inr (by omega_using [h, hn32]))
        (by show 1 ≤ 2 ^ 64; decide) (show 0 < 1 by decide)
      simpa using e
  have ad : ∀ i c, Layout.laneA k + i = c → at' S (Layout.laneA k) + BitVec.ofNat 64 i = at' S c := fun i c h => by
    rw [add_add, h]
  refine bytesAt_eq (by simp only [List.length_append, hpk, length_nodeAdrs ha, bytesAt, List.length_map,
    List.length_range]; omega_using []) fun i hi => ?_
  rw [Proof.SlhDsa.getD_append, Proof.SlhDsa.getD_append]
  simp only [List.length_append, hpk, length_nodeAdrs ha]
  by_cases h1 : i < p.n
  · rw [ite_eq_left (by omega_using [h1]), ite_eq_left h1, ← hE.seedA k hk, getD_bytesAt _ _ h1, ad i _ rfl,
      hkeep i (by omega_using [h1]), at']
  rw [ite_eq_right h1]
  by_cases h2 : i < p.n + 32
  · rw [ite_eq_left h2, getD_nodeAdrs ha _ _ _ _ _ (by omega_using [h2])]
    by_cases h3 : i - p.n < 16
    · rw [ite_eq_left h3, ← hE.adrsA k hk, getD_bytesAt _ _ h3, ad i _ rfl, hkeep i (by omega_using [h3]), add_add,
        show Layout.laneA k + p.n + (i - p.n) = Layout.laneA k + i by omega_using [h1]]
    rw [ite_eq_right h3]
    by_cases h4 : i - p.n < 20
    · rw [ite_eq_left h4, ad i (Layout.laneA k + p.n + 16 + (i - p.n - 16)) (by omega_using [h1, h3]),
        l.ty k hk _ (by omega_using [h3, h4])]
    rw [ite_eq_right h4]
    by_cases h5 : i - p.n < 24
    · rw [ite_eq_left h5, ad i (Layout.laneA k + p.n + 20 + (i - p.n - 20)) (by omega_using [h1, h4]),
        l.kp k hk _ (by omega_using [h4, h5])]
    rw [ite_eq_right h5]
    by_cases h6 : i - p.n < 28
    · rw [ite_eq_left h6, ad i (Layout.laneA k + p.n + 24 + (i - p.n - 24)) (by omega_using [h1, h5]),
        l.z k hk _ (by omega_using [h5, h6])]
    rw [ite_eq_right h6, ad i (Layout.laneA k + p.n + 28 + (i - p.n - 28)) (by omega_using [h1, h6]),
      l.x k hk _ (by omega_using [h6, h2])]
  · rw [ite_eq_right h2, getD_bytesAt _ _ (by omega_using [hi, h2]), ad i (Layout.laneA k + p.n + 32 + (i - (p.n + 32)))
      (by omega_using [h1, h2]), l.msg k hk _ (by omega_using [hi, h2]), add_add]

end VG.Proof.SlhDsa.X86_64.Levels
