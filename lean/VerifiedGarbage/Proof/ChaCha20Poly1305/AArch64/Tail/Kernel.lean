module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Round
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting: the kernel

`Tail.kernel`, from the state after the chunks: the keystream of the four
blocks from the stream's counter in the buffer `x3[0, 256)`, and the 512
bytes before the rest absorbed into the accumulator in `x21`–`x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Tail

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds LoadSame input input_same input_eq)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_subImm)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc)
open VG.Spec.ChaCha20 (innerBlock stateAt serialize block)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-! ## The buffer zeroed -/

/-- `c[0, 16 j)` is zero, and `m` is `m₀` elsewhere. -/
def Zeroed (c : Addr) (j : Nat) (m₀ m : Mem) : Prop :=
  ∀ x, m x = if (x - c).toNat < 16 * j then 0 else m₀ x

theorem zeroStores_step (j : Nat) :
    (List.range (j + 1)).map (fun i => Instr.strq .v28 .x3 (16 * i)) =
      (List.range j).map (fun i => Instr.strq .v28 .x3 (16 * i)) ++
        ([.strq .v28 .x3 (16 * j)] : List Instr) := by
  simp [List.range_succ]

/-- The first `j` stores of zeros. -/
theorem zeroStores_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hx3 : s.gpr .x3 = c)
    (hv : s.v .v28 = 0) (hw : ∀ a, a + 16 ≤ 256 → InRegions s.wr (c + BitVec.ofNat 64 a) 16) :
    WP isa (.block ((List.range j).map fun i => .strq .v28 .x3 (16 * i))) s fun s' =>
      Short.Same s s' ∧ Zeroed c j s.mem s'.mem := by
  induction j with
  | zero =>
    refine WP.block_nil (M := isa) ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun x => ?_⟩
    rw [ite_eq_right_iff.mpr fun h => absurd h (by omega)]
  | succ j ih =>
    rw [zeroStores_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, z₁⟩ => ?_)
    have ho : InRegions s₁.wr (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j)) 16 := by
      rw [g₁.wr, g₁.gpr, hx3]; exact hw (16 * j) (by omega)
    refine WP.block_cons_iff.mpr ⟨_, Short.exec_strq (by omega) ho,
      WP.block_nil ⟨⟨g₁.gpr, g₁.v, g₁.rd, g₁.wr, g₁.sp⟩, fun x => ?_⟩⟩
    show (if (x - (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j))).toNat < 16 then
      (s₁.v .v28).extractLsb' (8 * (x - (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j))).toNat) 8
      else s₁.mem x) = _
    rw [g₁.gpr, hx3, g₁.v, hv]
    by_cases h : (x - (c + BitVec.ofNat 64 (16 * j))).toNat < 16
    · have h' := (Offset.lt_iff x c (by omega)).mp h
      have h2 : (x - c).toNat < 16 * (j + 1) := by omega
      simp only [h, h2, ite_true]
      ext i hi
      simp
    · have h' := mt (Offset.lt_iff x c (d := 16 * j) (n := 16) (by omega)).mpr h
      simp only [h, ite_false]
      rw [z₁ x]
      by_cases h'' : (x - c).toNat < 16 * j
      · have h2 : (x - c).toNat < 16 * (j + 1) := by omega
        simp only [h'', h2, ite_true]
      · have h2 : ¬ (x - c).toNat < 16 * (j + 1) := by omega
        simp only [h'', h2, ite_false]

/-- The buffer zeroed. -/
theorem zero_ok {c : Addr} {s : State} (hx3 : s.gpr .x3 = c)
    (hw : ∀ a, a + 16 ≤ 256 → InRegions s.wr (c + BitVec.ofNat 64 a) 16) :
    WP isa (.block (([.vop (.logic .eor .v28 .v28 .v28)] : List Instr) ++
        (List.range 16).map (fun i => .strq .v28 .x3 (16 * i)))) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .v28 → s'.v r = s.v r) ∧ Zeroed c 16 s.mem s'.mem := by
  refine WP.block_cons_iff.mpr ⟨s.setV .v28 (s.v .v28 ^^^ s.v .v28), rfl, ?_⟩
  have hv : (s.setV .v28 (s.v .v28 ^^^ s.v .v28)).v .v28 = 0 := by
    rw [RegUpd.v_setV_self, BitVec.xor_self]; rfl
  refine WP.mono (zeroStores_ok (j := 16) (Nat.le_refl _) (by rw [RegUpd.gpr_setV]; exact hx3) hv
    (by rw [RegUpd.wr_setV]; exact hw)) fun s' ⟨g, z⟩ => ⟨by rw [g.gpr, RegUpd.gpr_setV],
      by rw [g.rd, RegUpd.rd_setV], by rw [g.wr, RegUpd.wr_setV], by rw [g.sp, RegUpd.sp_setV],
      fun r hr => by rw [g.v, RegUpd.v_setV_of_ne (s := s) _ hr], z⟩

theorem Zeroed.byte {c : Addr} {m₀ m : Mem} (h : Zeroed c 16 m₀ m) {k : Nat} (hk : k < 256) :
    m (c + BitVec.ofNat 64 k) = 0 := by
  rw [h, Mem.sub_ofNat_toNat c (by omega)]
  simp only [show k < 16 * 16 by omega, ite_true]

theorem Zeroed.frame {c : Addr} {m₀ m : Mem} (h : Zeroed c 16 m₀ m) :
    Frame [⟨c, 256⟩] m₀ m := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hx'
  rw [h x, ite_eq_right_iff.mpr fun h' => absurd (by omega) hx']

/-! ## The kernel -/

theorem block_eq (S : CState) (k : Fin 16) :
    (block S)[k] = (Nat.repeat innerBlock 10 S)[k] + S[k] := by
  simp only [block, Fin.getElem_fin, Vector.getElem_zipWith]

theorem kernel_ok {R a : Nat} {W : Addr} {s : State}
    (hx20 : s.gpr .x20 = W)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ d, d + 16 ≤ 256 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16)
    (hst : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩)
    (hr : Readable W s) (ha : Acc R a s) :
    WP isa Tail.kernel s fun u =>
      (∀ k < 256, u.mem (s.gpr .x3 + BitVec.ofNat 64 k) =
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x3, 256⟩] s.mem u.mem ∧
      Poly.hval u % Spec.Poly1305.P = absorbAll R a (bytesAt s.mem W 512) % Spec.Poly1305.P ∧
      (u.gpr .x23).toNat ≤ 4 ∧
      (∀ r, r ∉ [Reg.x1, .x4] → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  unfold Tail.kernel
  -- The four blocks' states.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.setup_ok s hin).mono
    fun s₂ ⟨h₂, l₂, t₂⟩ => ?_)
  -- Two blocks, and the count.
  have m₂ : s₂.mem = s.mem := l₂.mem
  have ha₂ : Acc R (absorbAll R a (bytesAt s₂.mem W (16 * 0))) s₂ := by
    have e : bytesAt s₂.mem W (16 * 0) = [] := rfl
    rw [e, Poly1305.absorbAll_nil]
    refine ha.of (fun r hr => ?_) m₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact l₂.gpr _ (by decide)
  have hp₂ : s₂.gpr .x20 = W + BitVec.ofNat 64 (16 * 0) := by
    rw [l₂.gpr _ (by decide), hx20, Nat.mul_zero, BitVec.add_zero]
  have hr₂ : Readable W s₂ := hr.of l₂.rd l₂.wr (l₂.gpr _ (by decide))
  have hvs : ∀ i ∈ (List.replicate 2 Poly.block).flatten, vdstOf i = none := by decide +kernel
  apply WP.seq
  rw [Tail.start, show Poly.block ++ Poly.block = (List.replicate 2 Poly.block).flatten by
    simp only [List.replicate, List.flatten_cons, List.flatten_nil, List.append_nil]]
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hvs
    (absorbN_ok 2 (n := 0) (by decide) ha₂ hp₂ hr₂)).mono
    fun s₃ ⟨⟨a₃, p₃, k₃⟩, v₃, sp₃, rd₃, wr₃⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨s₃.write .x .x4 ((10 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide,
      ite_true]
  -- The loop, from its invariant.
  let s₄ := s₃.write .x .x4 ((10 : BitVec 16).setWidth 64)
  have m₃ : s₃.mem = s.mem := k₃.2.1.trans m₂
  let vs : Nat → CState := fun j => ctr (stateAt s.mem (s.gpr .x0)) j
  have h₄ : TI vs R a W s₄ s₄ 0 := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
    · intro k j hj
      rw [Stitch.write_v, v₃]
      exact h₂ k j hj
    · rw [Stitch.write_v, v₃, t₂]
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), p₃]
    · have e : bytesAt s₄.mem W (16 * (2 + 3 * 0)) = bytesAt s₂.mem W (16 * (0 + 2)) := by
        show bytesAt s₃.mem W _ = _
        rw [k₃.2.1]
      rw [e]
      exact a₃.of (fun r hr => RegUpd.gpr_write_of_ne s₃ .x _ (by
        intro he; rw [he] at hr; exact absurd hr (by decide))) rfl
    · rw [RegUpd.gpr_write_self]; rfl
  have hr₄ : Readable W s₄ := hr₂.of (by show s₃.rd = _; rw [rd₃]) (by show s₃.wr = _; rw [wr₃])
    (by rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), k₃.gpr' (r := .x0)])
  refine WP.seq ((rounds_ok hr₄ h₄).mono fun s₅ h₅ => ?_)
  have x3₅ : s₅.gpr .x3 = s.gpr .x3 := by
    rw [h₅.keep _ (by decide) (by decide), RegUpd.gpr_write_of_ne s₃ .x _ (by decide),
      k₃.gpr' (r := .x3), l₂.gpr _ (by decide)]
  have wr₅ : s₅.wr = s.wr := by rw [h₅.wr]; show s₃.wr = _; rw [wr₃, l₂.wr]
  have rd₅ : s₅.rd = s.rd := by rw [h₅.rd]; show s₃.rd = _; rw [rd₃, l₂.rd]
  have sp₅ : s₅.sp = s.sp := by rw [h₅.sp]; show s₃.sp = _; rw [sp₃, l₂.sp]
  have mm₅ : s₅.mem = s.mem := by rw [h₅.mem]; exact m₃
  -- The buffer zeroed, then the keystream XORed into it.
  rw [Tail.finish, List.append_assoc]
  apply WP.block_append
  refine (zero_ok x3₅ (by rw [wr₅]; exact hw)).mono fun s₆ ⟨g₆, rd₆, wr₆, sp₆, v₆, z₆⟩ => ?_
  let s₇ := s₆.write .x .x1 (s₆.gpr .x3)
  have hx₇ : exec (VG.Impl.ChaCha20.AArch64.Xor.mov .x1 .x3) s₆ = some s₇ := by
    show exec (.addImm .x .x1 .x3 0) s₆ = some s₇
    simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
      exec_addImm_x (s := s₆) (d := .x1) (n := .x3) (imm := 0) (by decide)
  refine WP.block_cons_iff.mpr ⟨s₇, hx₇, ?_⟩
  show WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.finish) s₇ _
  have u₇ := VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 s₆ .x1 (s₆.gpr .x3)
  have x1₇ : s₇.gpr .x1 = s.gpr .x3 := by rw [u₇.gpr, g₆, x3₅]
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 := by
    rw [u₇.other _ (by decide), g₆, h₅.keep _ (by decide) (by decide),
      RegUpd.gpr_write_of_ne s₃ .x _ (by decide), k₃.gpr' (r := .x0), l₂.gpr _ (by decide)]
  have f₆ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₇.mem := by
    rw [u₇.mem, ← mm₅]; exact z₆.frame
  have st₇ : stateAt s₇.mem (s.gpr .x0) = stateAt s.mem (s.gpr .x0) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hst
  have hv₇ : Holds (fun j => Nat.repeat innerBlock 10 (vs j)) s₇ := by
    intro k j hj
    rw [show s₇.v = s₆.v from rfl, v₆ _ (fun e => absurd e
      ((show ∀ k : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v28 by decide) k))]
    exact h₅.vec k j hj
  have hin₇ : ∀ k : Fin 16, InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [u₇.rd, u₇.wr, rd₆, wr₆, rd₅, wr₅, x0₇]; exact hin k
  unfold VG.Impl.ChaCha20.AArch64.Neon4.finish
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv₇ hin₇).mono
    fun s₈ ⟨h₈, l₈⟩ => ?_)
  have hc₈ : Holds (fun j => block (vs j)) s₈ := by
    intro k j hj
    rw [h₈ k j hj, input_eq, x0₇, st₇, block_eq]
  have ho : ∀ r j : Fin 4, InRegions s₈.wr
      (s₈.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j
    rw [l₈.wr, l₈.gpr _ (by decide), u₇.wr, wr₆, wr₅, x1₇]
    exact hw _ (by omega)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hc₈ ho).mono
    fun s₉ ⟨d₉, f₉, k₉⟩ => ?_
  have x1₈ : s₈.gpr .x1 = s.gpr .x3 := by rw [l₈.gpr _ (by decide), x1₇]
  have g₉ (r : Reg) (h4 : r ≠ .x4) : s₉.gpr r = s₇.gpr r := by rw [k₉.gpr, l₈.gpr _ h4]
  have g₅ (r : Reg) (h4 : r ≠ .x4) (hp : r ∉ Poly.regs) : s₅.gpr r = s₃.gpr r := by
    rw [h₅.keep _ h4 hp, RegUpd.gpr_write_of_ne s₃ .x _ h4]
  have acc₅ := h₅.acc
  rw [show 16 * (2 + 3 * 10) = 512 from rfl, show s₄.mem = s.mem from m₃] at acc₅
  have e21 : ∀ r ∈ [Reg.x21, .x22, .x23], s₉.gpr r = s₅.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr hp => ?_, ?_, ?_, ?_⟩
  · have e := d₉ k hk
    have z : ∀ x : BitVec 8, (0 : BitVec 8) ^^^ x = x := fun x => by ext i; simp
    rw [x1₈, show s₈.mem = s₇.mem from l₈.mem, u₇.mem, z₆.byte hk, z] at e
    exact e
  · rw [← x1₈]
    have f₈ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₈.mem := by rw [l₈.mem]; exact f₆
    rw [x1₈] at f₉ ⊢
    exact f₈.trans f₉
  · rw [show Poly.hval s₉ = Poly.hval s₅ by
      simp only [Poly.hval, e21 .x21 (by simp), e21 .x22 (by simp), e21 .x23 (by simp)]]
    exact acc₅.h
  · rw [e21 .x23 (by simp)]; exact acc₅.h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h4⟩ := hr
    rw [g₉ _ h4, u₇.other _ h1, g₆, g₅ _ h4 hp, k₃.gpr' (r := r) hp, l₂.gpr _ h4]
  · rw [k₉.rd, l₈.rd, u₇.rd, rd₆, rd₅]
  · rw [k₉.wr, l₈.wr, u₇.wr, wr₆, wr₅]
  · rw [k₉.sp, l₈.sp, show s₇.sp = s₆.sp from rfl, sp₆, sp₅]

end VG.Proof.ChaCha20Poly1305.AArch64.Tail
