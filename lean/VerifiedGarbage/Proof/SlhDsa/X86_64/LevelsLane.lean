module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, a lane of a group

`nodeLane k`: lane `k` of the lanes `A` set up for node `j + k` of height
`z + 1`: its address's type, key pair, height and index, and its message,
the two nodes below it (`lane_ok`).
-/

-- separate module: the lanes' fields, built in parallel with `LevelsCorrect` and `LevelsScan`.

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Tree

/-- A byte of `scratch` outside a frame's one region. -/
theorem frame_at {m m' : Mem} {S : Addr} {o l q : Nat} (f : Frame [⟨at' S o, l⟩] m m') (h : q + 1 ≤ o ∨ o + l ≤ q)
    (hq : q + 1 ≤ 2 ^ 16) (ho : o + l ≤ 2 ^ 16) : m' (at' S q) = m (at' S q) := by
  have e := f.bytes (R := ⟨at' S q, 1⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S h (by omega_using [hq]) (by omega_using [ho])) (show 1 ≤ 2 ^ 64 by decide) (i := 0) (show 0 < 1 by decide)
  simpa using e

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `setFieldR rbx o r`: the field at `S + o` set to `r`, below `2³²`. -/
theorem setF_ok {S : Addr} {o : Nat} {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (ho : o + 4 ≤ 2 ^ 16)
    (k : ∀ s', (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      (∀ j < 4, s'.mem (at' S (o + j)) = (toByte (s.gpr r).toNat 4).getD j 0) →
      Frame [⟨at' S o, 4⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.setFieldR .rbx o r ++ is)) s Q := by
  simp only [Impl.SlhDsa.X86_64.setFieldR, List.cons_append, List.nil_append]
  refine wp_mov32r fun s₁ u₁ => wp_bswap32 fun s₂ u₂ => wp_store32 (a := at' S o)
    (by rw [Proof.Sha3.X86_64.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (by rw [u₂.wr, u₁.wr]; exact in_scr hw ho) fun s₃ g₃ m₃ r₃ w₃ => k s₃
      (fun g h => by rw [g₃, u₂.other _ h, u₁.other _ h]) (by rw [r₃, u₂.rd, u₁.rd]) (by rw [w₃, u₂.wr, u₁.wr])
      (fun j hj => ?_) ?_
  · rw [m₃, u₂.gpr, u₁.gpr, sw32, sw32, u₂.mem, u₁.mem, field_bytes _ _ _ _ hj]
  · rw [m₃, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- What `nodeLane k` does to lane `k`, at `la = laneA k` in `scratch`, its
message from `src`. -/
structure LanePost (n : Nat) (S : Addr) (s s' : State) (la src : Nat) (ty kp z x : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rdx → g ≠ .r11 → s'.gpr g = s.gpr g
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  ty : ∀ j < 4, s'.mem (at' S (la + n + 16 + j)) = (toByte ty 4).getD j 0
  kp : ∀ j < 4, s'.mem (at' S (la + n + 20 + j)) = (toByte kp 4).getD j 0
  z : ∀ j < 4, s'.mem (at' S (la + n + 24 + j)) = (toByte z 4).getD j 0
  x : ∀ j < 4, s'.mem (at' S (la + n + 28 + j)) = (toByte x 4).getD j 0
  msg : ∀ i < 2 * n, s'.mem (at' S (la + n + 32 + i)) = s.mem (at' S (src + i))
  frame : Frame [⟨at' S (la + n + 16), 16⟩, ⟨at' S (la + n + 32), 2 * n⟩] s.mem s'.mem

/-- Lane `k` for the node `x + k` of height `z` (`r10`; `x` in `r9`), its
message the `2n` bytes at `rsi + 2nk`, `rsi = S + b` above the lanes `A`. -/
theorem lane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {k z x b : Nat} {V7 V8 : BitVec 64}
    {s : State} (hk : k < 4) (hbx : s.gpr .rbx = S) (h10 : s.gpr .r10 = BitVec.ofNat 64 z) (hz : z < 2 ^ 32)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 x) (hx : x + k < 2 ^ 32) (hsi : s.gpr .rsi = at' S b)
    (hb : 3808 ≤ b) (hb' : b + 2 * p.n * k + 2 * p.n ≤ 2 ^ 16)
    (h7 : s.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7) (h8 : s.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (nodeLane ⟨p.n, p.len⟩ k)) s fun s' =>
      LanePost p.n S s s' (Layout.laneA k) (b + 2 * p.n * k) V7.toNat V8.toNat z (x + k) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (2 * p.n / 8) = 2 * p.n := by omega_using [hn]
  have hla : Layout.laneA k + 128 ≤ 3808 := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using [hk]
  have v7 : Layout.oVar 4 7 = 3016 := rfl
  have v8 : Layout.oVar 4 8 = 3024 := rfl
  have hla0 : 3296 ≤ Layout.laneA k := by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega_using []
  simp only [nodeLane, Layout.adrsOff, Layout.msgOff, var, List.cons_append, List.nil_append, List.append_assoc]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 4 7)) (by rw [Proof.Sha3.X86_64.ea_at, hbx])
    (by rw [v7]; exact in_scr' hw (by omega_using [])) fun s₁ u₁ => ?_
  refine setF_ok (by rw [u₁.other _ (by decide), hbx]) (by rw [u₁.wr]; exact hw) (by omega_using [hla, hn32])
    fun s₂ g₂ r₂ w₂ b₂ f₂ => ?_
  have hm₂ : s₂.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8 := by
    rw [← h8, ← u₁.mem]
    refine f₂.readW (r := ⟨at' S (Layout.oVar 4 8), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint S (d := Layout.oVar 4 8) (n := 8) (e := Layout.laneA k + p.n + 16) (k := 4)
      (by rw [v8]; omega_using [hla0]) (by rw [v8]; omega_using []) (by omega_using [hla, hn32])
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 4 8))
    (by rw [Proof.Sha3.X86_64.ea_at, g₂ _ (by decide), u₁.other _ (by decide), hbx])
    (by rw [r₂, w₂, u₁.rd, u₁.wr, v8]; exact in_scr' hw (by omega_using [])) fun s₃ u₃ => ?_
  have hb₃ : s₃.gpr .rbx = S := by rw [u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide), hbx]
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₃.wr := by rw [u₃.wr, w₂, u₁.wr]; exact hw
  refine setF_ok hb₃ hw₃ (by omega_using [hla, hn32]) fun s₄ g₄ r₄ w₄ b₄ f₄ => ?_
  have hb₄ : s₄.gpr .rbx = S := by rw [g₄ _ (by decide), hb₃]
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₄.wr := by rw [w₄]; exact hw₃
  refine setF_ok hb₄ hw₄ (by omega_using [hla, hn32]) fun s₅ g₅ r₅ w₅ b₅ f₅ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun s₆ u₆ => Proof.Sha3.X86_64.wp_addi fun s₇ u₇ => ?_
  have hb₇ : s₇.gpr .rbx = S := by rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), hb₄]
  have hw₇ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₇.wr := by rw [u₇.wr, u₆.wr, w₅]; exact hw₄
  refine setF_ok hb₇ hw₇ (by omega_using [hla, hn32]) fun s₈ g₈ r₈ w₈ b₈ f₈ => ?_
  have hsi₈ : s₈.gpr .rsi = at' S b := by
    rw [g₈ _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide), hsi]
  refine WP.mono (copy_ok (S := S) (a := 0) (b := b) (d₁ := 2 * p.n * k) (d₂ := Layout.laneA k + p.n + 32)
    (by decide) (by decide) (2 * p.n / 8) s₈ (by rw [g₈ _ (by decide), hb₇]; exact (BitVec.add_zero S).symm) hsi₈
    (by rw [w₈]; exact hw₇) (by omega_using [e8, hb']) (by omega_using [e8, hla, hn32])
    (by omega_using [e8, hla, hn32, hb])) fun s' ⟨g', r', w', c', f'⟩ => ?_
  rw [e8, Nat.zero_add] at c' f'
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  have hm₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- the four fields and the message, as the later writes leave them
  have F1 : Layout.laneA k + p.n + 16 + 4 ≤ 2 ^ 16 := by omega_using [hla, hn32]
  have M1 : Layout.laneA k + p.n + 32 + 2 * p.n ≤ 2 ^ 16 := by omega_using [hla, hn32]
  have keep8 : ∀ q, q + 1 ≤ Layout.laneA k + p.n + 32 → s'.mem (at' S q) = s₈.mem (at' S q) := fun q hq =>
    frame_at f' (.inl hq) (by omega_using [hq, M1, hla, hn32]) M1
  have keep7 : ∀ q, q + 1 ≤ Layout.laneA k + p.n + 28 → s'.mem (at' S q) = s₅.mem (at' S q) := fun q hq => by
    rw [keep8 q (by omega_using [hq, hla, hn32]), frame_at f₈ (.inl hq) (by omega_using [hq, F1, hla, hn32]) (by omega_using [F1, hla, hn32]), hm₇]
  have keep5 : ∀ q, q + 1 ≤ Layout.laneA k + p.n + 24 → s'.mem (at' S q) = s₄.mem (at' S q) := fun q hq => by
    rw [keep7 q (by omega_using [hq, hla, hn32]), frame_at f₅ (.inl hq) (by omega_using [hq, F1, hla, hn32]) (by omega_using [F1, hla, hn32])]
  have keep4 : ∀ q, q + 1 ≤ Layout.laneA k + p.n + 20 → s'.mem (at' S q) = s₂.mem (at' S q) := fun q hq => by
    rw [keep5 q (by omega_using [hq, hla, hn32]), frame_at f₄ (.inl hq) (by omega_using [hq, F1, hla, hn32]) (by omega_using [F1, hla, hn32]), hm₃]
  have hsrc : ∀ i < 2 * p.n, s₈.mem (at' S (b + 2 * p.n * k + i)) = s.mem (at' S (b + 2 * p.n * k + i)) :=
    fun i hi => by
      have h1 : Layout.laneA k + p.n + 32 ≤ b + 2 * p.n * k + i := by omega_using [hla, hn32, hb]
      have h2 : b + 2 * p.n * k + i + 1 ≤ 2 ^ 16 := by omega_using [hb', hi]
      rw [frame_at f₈ (.inr (by omega_using [h1])) h2 (by omega_using [F1, hla, hn32]), hm₇,
        frame_at f₅ (.inr (by omega_using [h1])) h2 (by omega_using [F1, hla, hn32]),
        frame_at f₄ (.inr (by omega_using [h1])) h2 (by omega_using [F1, hla, hn32]), hm₃,
        frame_at f₂ (.inr (by omega_using [h1])) h2 (by omega_using [F1, hla, hn32]), u₁.mem]
  have v1 : (s₁.gpr .rdx).toNat = V7.toNat := by rw [u₁.gpr, h7]
  have v3 : (s₃.gpr .rdx).toNat = V8.toNat := by rw [u₃.gpr, hm₂]
  have v4 : (s₄.gpr .r10).toNat = z := by
    rw [g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide), h10,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hz])]
  have v7' : (s₇.gpr .r11).toNat = x + k := by
    rw [u₇.gpr, u₆.gpr, g₅ _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide),
      u₁.other _ (by decide), h9, sx_ofNat (by omega_using [hk]), BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hx])]
  have sub16 : ∀ o, o + 4 ≤ 16 →
      Region.Sub ⟨at' S (Layout.laneA k + p.n + 16 + o), 4⟩ ⟨at' S (Layout.laneA k + p.n + 16), 16⟩ := fun o ho => by
    rw [show at' S (Layout.laneA k + p.n + 16 + o) = at' S (Layout.laneA k + p.n + 16) + BitVec.ofNat 64 o from
      (add_add S _ o).symm]
    exact Offset.sub_base _ ho
  refine ⟨fun g h1 h2 h3 => ?_, by rw [r', r₈, u₇.rd, u₆.rd, r₅, r₄, u₃.rd, r₂, u₁.rd],
    by rw [w', w₈, u₇.wr, u₆.wr, w₅, w₄, u₃.wr, w₂, u₁.wr], fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun i hi => ?_, ?_⟩
  · rw [g' _ h1, g₈ _ h1, u₇.other _ h3, u₆.other _ h3, g₅ _ h1, g₄ _ h1, u₃.other _ h2, g₂ _ h1, u₁.other _ h2]
  · rw [keep4 _ (by omega_using [hj, hla, hn32]), b₂ j hj, v1]
  · rw [keep5 _ (by omega_using [hj, hla, hn32]), show Layout.laneA k + p.n + 20 + j = Layout.laneA k + p.n + 20 + j from rfl,
      b₄ j hj, v3]
  · rw [keep7 _ (by omega_using [hj, hla, hn32]), b₅ j hj, v4]
  · rw [keep8 _ (by omega_using [hj, hla, hn32]), b₈ j hj, v7']
  · rw [c' i hi, hsrc i hi]
  · have t1 : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16⟩, ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩]
        s.mem s₂.mem := (u₁.mem ▸ f₂).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., by simpa using sub16 0 (by decide)⟩
    have t2 : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16⟩, ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩]
        s₂.mem s₄.mem := (hm₃ ▸ f₄).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., sub16 4 (by decide)⟩
    have t3 : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16⟩, ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩]
        s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., by
        rw [show Layout.laneA k + p.n + 24 = Layout.laneA k + p.n + 16 + 8 by omega_using []]; exact sub16 8 (by decide)⟩
    have t4 : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16⟩, ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩]
        s₅.mem s₈.mem := (hm₇ ▸ f₈).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., by
        rw [show Layout.laneA k + p.n + 28 = Layout.laneA k + p.n + 16 + 12 by omega_using []]; exact sub16 12 (by decide)⟩
    have t5 : Frame [⟨at' S (Layout.laneA k + p.n + 16), 16⟩, ⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩]
        s₈.mem s'.mem := f'.mono fun r hr => by simp at hr; simp [hr]
    exact t1.trans (t2.trans (t3.trans (t4.trans t5)))

end VG.Proof.SlhDsa.X86_64.Levels
