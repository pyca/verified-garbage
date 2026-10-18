module

public import VerifiedGarbage.Proof.MlKem.X86_64.SHSq
public import VerifiedGarbage.Impl.MlKem.X86_64.SampleH
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes

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
    exact h _ (by omega)

theorem HR.blk {σ : State} {m : Mem} (h : HR σ m) {i : Nat} (hi : i < 3) : bytesAt m (hbA σ i) 136 = hblk σ i :=
  VG.Proof.MlKem.bytesAt_congr fun j hj => by
    rw [hbA, at', Offset.add_add, ← at', show oHB + 136 * i + j = oHS + (200 + 136 * i + j) by simp only [oHB, oHS]; omega]
    exact h _ (by omega)

/-- The low scratch space is apart from the sponge's. -/
theorem low_hR (σ : State) : (lowR σ).Disjoint (hR σ) :=
  Offset.base_disjoint (scr σ) (by simp only [oSave, oHS]; omega) (by simp only [oHS]; omega)

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
  have e := byteOf_eq (xorAt Y 0 (bytesAt m p 136)) hj hb
  have e2 := byteOf_eq Y hj hb
  rw [byteOf_xorAt _ _ _ (by omega), VG.Proof.MlKem.bytesAt_length, e2] at e
  rw [VG.Proof.Sha3.getElem!_eq _ hj, ← e, VG.Proof.Sha3.getElem!_eq _ hj]
  split
  · rw [ite_eq_left (by omega), BitVec.extractLsb'_xor, byte_readW _ _ (by omega), Offset.add_add, Nat.sub_zero]
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 8 * j + b < 136 by omega),
      Option.map_some, Option.getD_some]
  · rw [ite_eq_right (by omega)]

/-! ## The start, apart from the sponge -/

/-- The prologue writes only the saved registers. -/
theorem proF_ok {σ : State} (hp : PreW w16 σ) :
    WP isa (.block pro) σ fun s => I0W w16 σ s ∧ Frame [⟨at' σ oSave, 40⟩] σ.mem s.mem := by
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (at' σ 4384) (σ.gpr .rbx)).writeW (at' σ 4392) (σ.gpr .rbp)).writeW (at' σ 4400)
          (σ.gpr .r12)).writeW (at' σ 4408) (σ.gpr .r13)).writeW (at' σ 4416) (σ.gpr .r14) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .r12 = sd σ ∧ s.gpr .r13 = aP σ ∧ s.gpr .r14 = 1)
    (by xrun [in_scr hp rfl (a := 4384) (n := 8) (by omega), in_scr hp rfl (a := 4392) (n := 8) (by omega),
      in_scr hp rfl (a := 4400) (n := 8) (by omega), in_scr hp rfl (a := 4408) (n := 8) (by omega),
      in_scr hp rfl (a := 4416) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨⟨⟨k1.2.1, k1.2.2, hbx, h12, h13,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩, h14⟩, ?_⟩
  · rw [hm1]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oSave, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega) (by omega)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 4384 (by omega))).writeW (by simp) _
      (hin 4392 (by omega))).writeW (by simp) _ (hin 4400 (by omega))).writeW (by simp) _
      (hin 4408 (by omega))).writeW (by simp) _ (hin 4416 (by omega)))
  · rw [hm1]
    have hin : ∀ a, 4384 ≤ a → a + 8 ≤ 4424 → (⟨at' σ oSave, 40⟩ : Region).Contains (at' σ a) (64 / 8) :=
      fun a h₁ h₂ => Offset.contains _ (by simp only [oSave]; omega) (by simp only [oSave]; omega)
        (by simp only [oSave]; omega)
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hin 4384 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (hin 4392 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (hin 4400 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (hin 4408 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (hin 4416 (by omega) (by omega)))

/-- The prologue, the round constants and the padded seeds, apart from the sponge. -/
theorem startF_ok {σ : State} (hp : PreW w16 σ) :
    WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ
      fun s => SqInvW w16 σ 0 s ∧ HR σ s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (proF_ok hp) fun s₁ ⟨h₁, f₁⟩ => WP.mono (rc_ok hp h₁.env) fun s₂ h₂ => ?_
  have he₂ : EnvW w16 σ s₂ := EnvW.low h₁.env (rs := [⟨at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have r₂ : HR σ s₂.mem := ((HR.refl σ).frame f₁ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oSave, oHS]; omega)) (by simp only [oHS]; omega)
        (by simp only [oSave]; omega)).frame h₂.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [oRc, oHS]; omega)) (by simp only [oHS]; omega)
      (by simp only [oRc]; omega)
  refine WP.mono (absorb_ok hp (m₁ := s₂.mem) ⟨he₂, by rw [h₂.keep.gpr (by decide), h₁.r14], Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨⟨a₃.env, a₃.r14, fun r hr k hk => ?_, lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega)⟩,
      r₂.frame a₃.frame fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by simp only [oHS]; omega) (by simp only [oHS]; omega)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega))
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
    (in_scr' hp h.env.rd h.env.wr (by simp only [oHS]; omega)) fun s₁ u₁ => wp_store (a := at' σ (32 * i + 24))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact in_scr hp h.env.wr (by omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hv : s.mem.readW (at' σ (oHS + 8 * i)) 64 = (stateAt σ.mem (hsA σ))[i]! := by
    rw [h.hr.word (by omega), stateAt_lane _ _ hi, hsA, at', at', Offset.add_add]
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * i + 24)) ((stateAt σ.mem (hsA σ))[i]!) := by
    rw [m₂, u₁.mem, u₁.gpr, hv]
  have hsub : Region.Sub ⟨at' σ (32 * i + 24), 8⟩ (lowR σ) := Offset.sub_base _ (by simp only [oSave]; omega)
  have hf : Frame [⟨at' σ (32 * i + 24), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨EnvW.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₂.trans u₁.rd) (w₂.trans u₁.wr) fun r hr => by
        rw [g₂, u₁.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun j hj k hk => ?_,
    h.hr.frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oHS]; omega)) (by simp only [oHS]; omega) (by omega)⟩
  · have e := readW_writeW_off s.mem (scr σ) ((stateAt σ.mem (hsA σ))[i]!) (d := 32 * (50 + r) + 8 * k)
      (e := 32 * i + 24) (n := 8) (by omega) (by omega) (by omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · rw [hm]
    by_cases e : j = i ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := e
      rw [show la (scr σ) j 3 = at' σ (32 * j + 24) from rfl, Mem.readW_writeW_self64, ite_eq_left ⟨rfl, by omega⟩]
    · have e' := readW_writeW_off s.mem (scr σ) ((stateAt σ.mem (hsA σ))[i]!) (d := 32 * j + 8 * k)
        (e := 32 * i + 24) (n := 8) (by omega) (by omega) (by omega)
      rw [show la (scr σ) j k = scr σ + BitVec.ofNat 64 (32 * j + 8 * k) from rfl, e', ← la, h.w j hj k hk]
      by_cases c : k = 3 ∧ j < i
      · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega⟩]
      · rw [ite_eq_right c, ite_eq_right (by omega)]

theorem hload_eq : hload = (List.range 25).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (oHS + 8 * i))), .store (at_ .rbx (32 * i + 24)) .rax] := rfl

/-- The sponge's state to the fourth state. -/
theorem hload_ok {σ : State} (hp : PreW w16 σ) {s : State} (h : SqInvW w16 σ 0 s) (hr : HR σ s.mem) :
    WP isa (.block hload) s fun s' => SqY w16 σ (hst σ 0) 0 0 s' ∧ HR σ s'.mem := by
  rw [hload_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (HLI w16 σ) (fun i s hi h => hload_step hp hi h) 25 (Nat.le_refl _) s
    ⟨h.env, h.r14, h.rc, fun j hj k hk => ?_, hr⟩) fun s' h' =>
      ⟨⟨h'.env, h'.r14, h'.rc, fun j hj k hk => ?_, fun _ _ p hp' => absurd hp' (by omega)⟩, h'.hr⟩
  · rw [h.lanes j hj k hk, ite_eq_right (by omega)]; rfl
  · rw [h'.w j hj k hk]
    by_cases e : k = 3
    · subst e; rw [ite_eq_left ⟨rfl, hj⟩, L3_three]; rfl
    · rw [ite_eq_right (by omega), L3_lt (by omega)]; rfl

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
  have hb : hbA σ i + BitVec.ofNat 64 (8 * J) = at' σ (oHS + (200 + 136 * i + 8 * J)) := by
    rw [hbA, at', at', Offset.add_add, show oHB + 136 * i + 8 * J = oHS + (200 + 136 * i + 8 * J) by
      simp only [oHB, oHS]; omega]
  refine wp_movm (a := hbA σ i + BitVec.ofNat 64 (8 * J)) (by rw [ea_at, h.r8])
    (by rw [hb]; exact in_scr' hp h.env.rd h.env.wr (by simp only [oHS]; omega)) fun s₁ u₁ =>
    wp_xorm (a := at' σ (32 * J + 24)) (by rw [ea_at, u₁.other _ (by decide), h.env.rbx])
      (by rw [u₁.rd, u₁.wr]; exact in_scr' hp h.env.rd h.env.wr (by omega)) fun s₂ u₂ =>
    wp_store (a := at' σ (32 * J + 24)) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.env.rbx])
      (by rw [u₂.wr, u₁.wr]; exact in_scr hp h.env.wr (by omega)) fun s₃ g₃ m₃ r₃ w₃ => wp_nil ?_
  have hv : s₂.gpr .rax = (xorAt Y 0 (hblk σ i))[J]! := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hb, h.hr.word (by omega), ← hb, show at' σ (32 * J + 24) = la (scr σ) J 3 from rfl,
      h.w J (by omega) 3 (by decide), ite_eq_right (by omega), L3_three, xorAt_lane _ _ _ (by omega),
      ite_eq_left hJ, BitVec.xor_comm]
  have hm : s₃.mem = s.mem.writeW (at' σ (32 * J + 24)) ((xorAt Y 0 (hblk σ i))[J]!) := by
    rw [m₃, u₂.mem, u₁.mem, hv]
  have hsub : Region.Sub ⟨at' σ (32 * J + 24), 8⟩ (lowR σ) := Offset.sub_base _ (by simp only [oSave]; omega)
  have hf : Frame [⟨at' σ (32 * J + 24), 8⟩] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hg : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r hr => by rw [g₃, u₂.other r hr, u₁.other r hr]
  refine ⟨EnvW.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₃.trans (u₂.rd.trans u₁.rd)) (w₃.trans (u₂.wr.trans u₁.wr)) fun r hr => hg r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide), h.r14], fun r hr k hk => ?_, fun j hj k hk => ?_, fun k hk p hp' => ?_,
    h.hr.frame hf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by simp only [oHS]; omega)) (by simp only [oHS]; omega) (by omega),
    by rw [hg _ (by decide), h.r8], by rw [hg _ (by decide), hg _ (by decide)]; exact h.keep,
    h.fr.trans (hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩)⟩
  · have e := readW_writeW_off s.mem (scr σ) ((xorAt Y 0 (hblk σ i))[J]!) (d := 32 * (50 + r) + 8 * k)
      (e := 32 * J + 24) (n := 8) (by omega) (by omega) (by omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · rw [hm]
    by_cases e : j = J ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := e
      rw [show la (scr σ) j 3 = at' σ (32 * j + 24) from rfl, Mem.readW_writeW_self64, ite_eq_left ⟨rfl, by omega⟩]
    · have e' := readW_writeW_off s.mem (scr σ) ((xorAt Y 0 (hblk σ i))[J]!) (d := 32 * j + 8 * k)
        (e := 32 * J + 24) (n := 8) (by omega) (by omega) (by omega)
      rw [show la (scr σ) j k = scr σ + BitVec.ofNat 64 (32 * j + 8 * k) from rfl, e', ← la, h.w j hj k hk]
      by_cases c : k = 3 ∧ j < J
      · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega⟩]
      · rw [ite_eq_right c, ite_eq_right (by omega)]
  · rw [hm, wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)]
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
  · rw [h.lanes j hj k hk, ite_eq_right (by omega), Nat.zero_add]
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
        · rw [ite_eq_right (by omega), L3_three, xorAt_lane _ _ _ hj, ite_eq_right c]
      · rw [ite_eq_right (by omega), L3_lt (by omega), L3_lt (by omega)]
    · rw [u₁.gpr, ht.r8, hbA, hbA, at', at', show (136 : BitVec 32).signExtend 64 = BitVec.ofNat 64 136 from rfl, Offset.add_add,
        show oHB + 136 * i + 136 = oHB + 136 * (i + 1) by omega]

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_nil) in
/-- The three squeezes, each after XORing the next block into the fourth state. -/
theorem squeezesH_ok {fast : Bool} {σ : State} (hp : PreW w16 σ) {s : State} (h : SqY w16 σ (hst σ 0) 0 0 s)
    (hr : HR σ s.mem) : WP isa (squeezesH fast) s fun s' => SqY w16 σ (hst σ 3) 0 3 s' ∧ HR σ s'.mem := by
  unfold squeezesH
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_nil ?_)
  have k : Keep [.r8] s s₂ := ⟨fun r hr => by
      rw [u₂.other r (by simpa using hr), u₁.other r (by simpa using hr)], u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  have hm : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  have h₂ : SqY w16 σ (hst σ 0) 0 0 s₂ := ⟨h.env.keep hm k (by decide), by rw [k.gpr (by decide), h.r14],
    by rw [hm]; exact h.rc, by rw [hm]; exact h.lanes, by rw [hm]; exact h.buf⟩
  have r₂ : HR σ s₂.mem := by rw [hm]; exact hr
  have ebx : s₂.gpr .rbx = scr σ := by rw [k.gpr (by decide), h.env.rbx]
  have e₈ : s₂.gpr .r8 = hbA σ 0 := by
    rw [u₂.gpr, u₁.gpr, h.env.rbx, hbA, at', sx_ofNat (by simp only [oHB]; omega), Nat.mul_zero, Nat.add_zero]
  refine WP.mono (blocks_ok (b := 0) (P := fun i t => SqY w16 σ (hst σ i) 0 i t ∧ HR σ t.mem ∧ t.gpr .r8 = hbA σ i)
    (by decide) (by decide) (by simp only [oBuf]; omega) (by decide)
    (fun _ _ _ ⟨h', r', e'⟩ hm hrd hwr hg => ⟨h'.frame hm hrd hwr hg, by rw [hm]; exact r',
      by rw [hg _ (by decide) (by decide)]; exact e'⟩)
    (fun i t _ hi ⟨hi', ri, ei⟩ hbp => ?_) ⟨h₂, r₂, e₈⟩) fun t ⟨ht, rt, _⟩ => ⟨ht, rt⟩
  unfold squeezeH
  refine WP.seq (WP.mono (hxor_ok hp (by omega) hi' ri ei) fun t₁ ⟨⟨h₁, r₁, e₁, _⟩, bp₁, r10₁⟩ => ?_)
  refine WP.mono (sqY_ok (fast := fast) hp (by omega) h₁ ?_) fun t₂ ⟨⟨h₃, f₃⟩, bp₃, r10₃, e₃⟩ =>
    ⟨⟨h₃, r₁.low f₃, by rw [e₃, e₁]⟩, by rw [bp₃, bp₁], by rw [r10₃, r10₁]⟩
  rw [bp₁, hbp, ebx, at', Offset.add_add, Nat.sub_zero]

/-! ## The fourth state back to the sponge's -/

/-- During the copy of the fourth state: its first `i` lanes. -/
structure HSI (w16 : Bool) (σ : State) (Y : Spec.Sha3.State) (i : Nat) (s : State) : Prop where
  sq : SqY w16 σ Y 0 3 s
  w : ∀ j < i, s.mem.readW (at' σ (oHS + 8 * j)) 64 = Y[j]!

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem hsave_step {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {i : Nat} (hi : i < 25) {s : State}
    (h : HSI w16 σ Y i s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax]) s
      (HSI w16 σ Y (i + 1)) := by
  refine wp_movm (a := at' σ (32 * i + 24)) (by rw [ea_at, h.sq.env.rbx])
    (in_scr' hp h.sq.env.rd h.sq.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (oHS + 8 * i))
      (by rw [ea_at, u₁.other _ (by decide), h.sq.env.rbx])
      (by rw [u₁.wr]; exact in_scr hp h.sq.env.wr (by simp only [oHS]; omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hv : s.mem.readW (at' σ (32 * i + 24)) 64 = Y[i]! := by
    rw [show at' σ (32 * i + 24) = la (scr σ) i 3 from rfl, h.sq.lanes i hi 3 (by decide), L3_three]
  have hm : s₂.mem = s.mem.writeW (at' σ (oHS + 8 * i)) (Y[i]!) := by rw [m₂, u₁.mem, u₁.gpr, hv]
  have hf : Frame [⟨at' σ (oHS + 8 * i), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.sq.apart (by decide) hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.base_disjoint _ (by simp only [oSave, oHS]; omega) (by simp only [oHS]; omega))
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by simp only [oSave, oHS]; omega)) (by simp only [oSave]; omega)
        (by simp only [oHS]; omega))
    (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oHS]; omega)⟩)
    (r₂.trans u₁.rd) (w₂.trans u₁.wr) fun r hr => by
      rw [g₂, u₁.other r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)], fun j hj => ?_⟩
  rw [hm]
  by_cases e : j = i
  · subst e; exact Mem.readW_writeW_self64 _ _ _
  · rw [rd64_off (by simp only [oHS]; omega) (by simp only [oHS]; omega) (by omega)]
    exact h.w j (by omega)

theorem hsave_eq : hsave = (List.range 25).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax] := rfl

/-- The fourth state to the sponge's. -/
theorem hsave_ok {σ : State} (hp : PreW w16 σ) {Y : Spec.Sha3.State} {s : State} (h : SqY w16 σ Y 0 3 s) :
    WP isa (.block hsave) s fun s' => SqY w16 σ Y 0 3 s' ∧ stateAt s'.mem (hsA σ) = Y := by
  rw [hsave_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (HSI w16 σ Y) (fun i s hi h => hsave_step hp hi h) 25 (Nat.le_refl _) s
    ⟨h, fun _ h => absurd h (by omega)⟩) fun s' h' => ⟨h'.sq, stateAt_of_lanes fun i hi => ?_⟩
  rw [hsA, at', Offset.add_add]
  exact h'.w i hi

end VG.Proof.MlKem.X86_64.SH
