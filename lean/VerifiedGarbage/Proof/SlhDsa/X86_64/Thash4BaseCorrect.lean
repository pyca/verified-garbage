module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4Base
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

-- separate module: it builds in parallel with the constant-time checks (`Thash4BaseCT`).

/-!
# SLH-DSA on x86-64: the baseline `thash4`, correctness

`Thash4Base.thash4 n` from a state satisfying `Thash4Pre n 8` ends with
each output `SHAKE256` of its message and the callee-saved registers kept
(`correct`), by `Thash4Avx.correctWith`: its states are zeroed by scalar
stores (`zeroOk_S`), and `permute4S` permutes them one at a time
(`permOk_S`), each copied to `work[800..1000)` (`gather_ok`), permuted there
by the scalar Keccak-f[1600] (`Proof.Sha3.X86_64.call_ok`) and copied back
(`scatter_ok`), with `r9`–`r11` and the three slots kept in `xmm8`–`xmm13`,
which the scalar permutation does not write.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Thash4Base

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64.Thash4Base
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3.X86_64.X4 (Lanes4 la KState)
open VG.Spec.Sha3 (stateAt keccakF bytesAt)
open VG.Proof.SlhDsa.X86_64 (Thash4Pre msg outAt thash4Changes workLen ea_at' sx_ofNat add_ofNat)
open VG.Proof.SlhDsa.X86_64.Thash4Avx (W cs_ne wr_work rw_work sub_off sub_pre disj_base lanes4_frame lanes4_congr
  ZeroOk PermOk correctWith tailOk_nil)

variable {n stk : Nat} {σ : State}

/-! ## Memory -/

/-- Byte `j < 8` of the word at `a`. -/
theorem byte_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- A word stored again with the value it had in `m`. -/
theorem frame_restore {rs : List Region} {m m' : Mem} (h : Frame rs m m') (a : Addr) :
    Frame rs m (m'.writeW a (m.readW a 64)) := by
  intro x hx
  by_cases c : (x - a).toNat < 8
  · have e : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [← e, byte_readW (m'.writeW a (m.readW a 64)) a c, Mem.readW_writeW_self64, ← byte_readW m a c]
  · exact (Mem.write_apply (n := 8) c).trans (h x hx)

theorem stateAt_of {m : Mem} {p : Addr} {A : KState}
    (h : ∀ i < 25, m.readW (p + BitVec.ofNat 64 (8 * i)) 64 = A[i]!) : stateAt m p = A := by
  apply Vector.ext; intro i hi
  rw [stateAt, Vector.getElem_ofFn, h i hi, Proof.Sha3.getElem!_eq _ hi]

theorem getElem!_stateAt (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (stateAt m p)[i]! = m.readW (p + BitVec.ofNat 64 (8 * i)) 64 := by
  rw [Proof.Sha3.getElem!_eq _ hi, stateAt, Vector.getElem_ofFn]

theorem extract_movq (v : BitVec 64) : ((0 : BitVec 64) ++ v).extractLsb' 0 64 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem lanes4_writeW {m : Mem} {p a : Addr} {A : Nat → KState} (h : Lanes4 m p A)
    (hd : Region.Disjoint ⟨p, 800⟩ ⟨a, 8⟩) (v : BitVec 64) : Lanes4 (m.writeW a v) p A :=
  lanes4_frame h (Frame.writeW (Frame.refl [⟨a, 8⟩] m) (List.mem_singleton_self _) v
    (by simp [Region.Contains])) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

/-! ## Steps -/

theorem wp_movqx {s : State} {x : XReg} {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) (s.setXmm x ((0 : BitVec 64) ++ s.gpr r)) Q) :
    WP isa (.block (.xop (.movq x r) :: is)) s Q :=
  Steps.WP.cons rfl k

theorem wp_movqr {s : State} {d : Reg} {x : XReg} {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) (s.setReg d ((s.xmm x).extractLsb' 0 64)) Q) :
    WP isa (.block (.movqR d x :: is)) s Q :=
  Steps.WP.cons rfl k

theorem wp_movm' {s : State} {d : Reg} {m : MemOp} {a : Addr} {is : List Instr} {Q : State → Prop}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : WP isa (.block is) (s.setReg d (s.mem.readW a 64)) Q) : WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine Steps.WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ k
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_store' {s : State} {m : MemOp} {r : Reg} {a : Addr} {is : List Instr} {Q : State → Prop}
    (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.gpr r) } Q) : WP isa (.block (.store m r :: is)) s Q :=
  Steps.WP.cons (by simp [exec, State.store64, ha, hout]) k

/-- A postcondition of code that writes no vector register keeps them. -/
theorem wp_xmm_keep {c : Prog isa} (hc : ∀ i ∈ instrs c, Impl.Scrub.X86_64.writesVec i = false) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) : WP isa c s fun s' => Q s' ∧ s'.xmm = s.xmm := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Residue.Exec.xmmKeep hc he⟩

/-! ## Zeroing the states -/

theorem zeros_ok (hp : Thash4Pre n stk σ) : ∀ j ≤ 100, ∀ t : State, t.gpr .r8 = W σ → t.wr = σ.wr →
    t.gpr .rax = 0 →
    WP isa (.block ((List.range j).map fun i => .store (at_ .r8 (8 * i)) .rax)) t (fun t' => t'.gpr = t.gpr ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ i < j, t'.mem.readW (W σ + BitVec.ofNat 64 (8 * i)) 64 = 0) ∧
      Frame [⟨W σ, 800⟩] t.mem t'.mem) := by
  intro j
  induction j with
  | zero => intro _ t _ _ _; exact WP.block_nil ⟨rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h8 hw h0
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h8 hw h0) fun t₁ ⟨g₁, r₁, w₁, b₁, f₁⟩ => ?_)
    refine Proof.Sha3.X86_64.wp_store (a := W σ + BitVec.ofNat 64 (8 * j)) (by rw [ea_at', g₁, h8])
      (wr_work hp (by rw [w₁, hw]) (by simp only [workLen]; omega_using [hj])) fun t₂ g₂ m₂ r₂ w₂ => WP.block_nil ?_
    refine ⟨by rw [g₂, g₁], by rw [r₂, r₁], by rw [w₂, w₁], fun i hi => ?_, ?_⟩
    · rw [m₂, g₁, h0]
      by_cases c : i < j
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [c]) (by omega_using [hj, c]) (by omega_using [hj]))
          (by decide), b₁ i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [Mem.readW_writeW_self64]
    · rw [m₂]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))

theorem zeroOk_S (hp : Thash4Pre n stk σ) : ZeroOk zeroS σ :=
  Steps.wp_mov32i fun s₁ u₁ => WP.mono (zeros_ok hp 100 (by decide) s₁ (by rw [u₁.other _ (by decide)])
    (by rw [u₁.wr]) (by rw [u₁.gpr]; rfl)) fun s₂ ⟨g₂, r₂, w₂, b₂, f₂⟩ =>
    ⟨fun r h => by rw [g₂, u₁.other _ h], by rw [r₂, u₁.rd], by rw [w₂, u₁.wr], fun q hq => by
      rw [show W σ + BitVec.ofNat 64 q = W σ + BitVec.ofNat 64 (8 * (q / 8)) + BitVec.ofNat 64 (q % 8) by
          rw [add_ofNat, Nat.div_add_mod], byte_readW s₂.mem _ (Nat.mod_lt q (by decide)), b₂ _ (by omega_using [hq])]
      simp, by rw [← u₁.mem]; exact f₂⟩

/-! ## Copying words within `work` -/

/-- The words at `src i` copied to `dst i` in `work`, for `i < j`, through `rax`. -/
abbrev copy (src dst : Nat → Nat) (j : Nat) : List Instr :=
  (List.range j).flatMap fun i => [.mov .rax (.mem (at_ .r8 (src i))), .store (at_ .r8 (dst i)) .rax]

theorem copy_ok (hp : Thash4Pre n stk σ) {src dst : Nat → Nat} {D : Region}
    (hs : ∀ i < 25, src i + 8 ≤ workLen) (hd : ∀ i < 25, dst i + 8 ≤ workLen)
    (hsd : ∀ i < 25, ∀ i' < 25, dst i + 8 ≤ src i' ∨ src i' + 8 ≤ dst i)
    (hdd : ∀ i < 25, ∀ i' < i, dst i' + 8 ≤ dst i ∨ dst i + 8 ≤ dst i')
    (hD : ∀ i < 25, D.Contains (W σ + BitVec.ofNat 64 (dst i)) 8) :
    ∀ j ≤ 25, ∀ t : State, t.gpr .r8 = W σ → t.wr = σ.wr →
      WP isa (.block (copy src dst j)) t fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧
        t'.wr = t.wr ∧
        (∀ i < j, t'.mem.readW (W σ + BitVec.ofNat 64 (dst i)) 64 = t.mem.readW (W σ + BitVec.ofNat 64 (src i)) 64) ∧
        (∀ e, e + 8 ≤ workLen → (∀ i < j, dst i + 8 ≤ e ∨ e + 8 ≤ dst i) →
          t'.mem.readW (W σ + BitVec.ofNat 64 e) 64 = t.mem.readW (W σ + BitVec.ofNat 64 e) 64) ∧
        Frame [D] t.mem t'.mem := by
  have sep : ∀ {d e : Nat}, d + 8 ≤ workLen → e + 8 ≤ workLen → (d + 8 ≤ e ∨ e + 8 ≤ d) →
      Mem.Sep (W σ + BitVec.ofNat 64 d) 8 (W σ + BitVec.ofNat 64 e) 8 := fun hd he h =>
    Offset.sep _ h (by simp only [workLen] at hd; omega_using [hd]) (by simp only [workLen] at he; omega_using [he])
  intro j
  induction j with
  | zero =>
    intro _ t _ _
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), fun _ _ _ => rfl,
      Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h8 hw
    rw [copy, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h8 hw) fun t₁ ⟨g₁, r₁, w₁, c₁, e₁, f₁⟩ => ?_)
    have hj' : j < 25 := by omega_using [hj]
    refine Steps.wp_movm (a := W σ + BitVec.ofNat 64 (src j)) (by rw [ea_at', g₁ _ (by decide), h8])
      (rw_work hp (by rw [w₁, hw]) (hs j hj')) fun t₂ u₂ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := W σ + BitVec.ofNat 64 (dst j))
      (by rw [ea_at', u₂.other _ (by decide), g₁ _ (by decide), h8])
      (wr_work hp (by rw [u₂.wr, w₁, hw]) (hd j hj')) fun t₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
    have hsj : t₁.mem.readW (W σ + BitVec.ofNat 64 (src j)) 64 = t.mem.readW (W σ + BitVec.ofNat 64 (src j)) 64 :=
      e₁ _ (hs j hj') fun i hi => hsd i (by omega_using [hi, hj]) j hj'
    have hm₃ : t₃.mem =
        t₁.mem.writeW (W σ + BitVec.ofNat 64 (dst j)) (t.mem.readW (W σ + BitVec.ofNat 64 (src j)) 64) := by
      rw [m₃, u₂.gpr, u₂.mem, hsj]
    refine ⟨fun g h => by rw [g₃, u₂.other _ h, g₁ _ h], by rw [r₃, u₂.rd, r₁], by rw [w₃, u₂.wr, w₁],
      fun i hi => ?_, fun e he hd' => ?_, ?_⟩
    · rw [hm₃]
      by_cases c : i < j
      · rw [Mem.readW_writeW_sep (sep (hd i (by omega_using [c, hj])) (hd j hj') (hdd j hj' i c)) (by decide),
          c₁ i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [Mem.readW_writeW_self64]
    · rw [hm₃, Mem.readW_writeW_sep (sep he (hd j hj') (hd' j (by omega_using [])).symm) (by decide),
        e₁ e he fun i hi => hd' i (by omega_using [hi])]
    · rw [hm₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (hD j hj')

/-- State `k` copied to `work[800..1000)`. -/
theorem gather_ok (hp : Thash4Pre n stk σ) {k : Nat} (hk : k < 4) {t : State} (h8 : t.gpr .r8 = W σ)
    (hw : t.wr = σ.wr) {Y : Nat → KState} (hl : Lanes4 t.mem (W σ) Y) :
    WP isa (.block (gather k)) t fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      stateAt t'.mem (W σ + BitVec.ofNat 64 800) = Y k ∧
      Frame [⟨W σ + BitVec.ofNat 64 800, 200⟩] t.mem t'.mem :=
  WP.mono (copy_ok hp (src := fun i => 32 * i + 8 * k) (dst := fun i => 800 + 8 * i)
      (fun i hi => by simp only [workLen]; omega_using [hi, hk]) (fun i hi => by simp only [workLen]; omega_using [hi])
      (fun i hi i' hi' => by omega_using [hi, hi', hk]) (fun i _ i' hi' => by omega_using [hi'])
      (fun i hi => by
        rw [← add_ofNat]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      25 (by decide) t h8 hw)
    fun t' ⟨g, r, w, c, _, f⟩ => ⟨g, r, w, stateAt_of fun i hi => by
      rw [add_ofNat]; exact (c i hi).trans (hl i hi k hk), f⟩

/-- `work[800..1000)` copied to state `k`. -/
theorem scatter_ok (hp : Thash4Pre n stk σ) {k : Nat} (hk : k < 4) {t : State} (h8 : t.gpr .r8 = W σ)
    (hw : t.wr = σ.wr) {Y : Nat → KState} (hl : Lanes4 t.mem (W σ) Y) {B : KState}
    (hB : stateAt t.mem (W σ + BitVec.ofNat 64 800) = B) :
    WP isa (.block (scatter k)) t fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      Lanes4 t'.mem (W σ) (fun j => if j = k then B else Y j) ∧ Frame [⟨W σ, 800⟩] t.mem t'.mem := by
  refine WP.mono (copy_ok hp (src := fun i => 800 + 8 * i) (dst := fun i => 32 * i + 8 * k)
      (fun i hi => by simp only [workLen]; omega_using [hi]) (fun i hi => by simp only [workLen]; omega_using [hi, hk])
      (fun i hi i' hi' => by omega_using [hi, hi', hk]) (fun i _ i' hi' => by omega_using [hi'])
      (fun i hi => Offset.contains_base _ (by omega_using [hi, hk]) (by omega_using [hi, hk]))
      25 (by decide) t h8 hw) fun t' ⟨g, r, w, c, e, f⟩ => ⟨g, r, w, fun i hi k' hk' => ?_, f⟩
  by_cases h : k' = k
  · subst h
    have e : (fun j => if j = k' then B else Y j) k' = B := by simp
    rw [e, ← hB, getElem!_stateAt _ _ hi, add_ofNat]
    exact c i hi
  · have e' : (fun j => if j = k then B else Y j) k' = Y k' := by simp [h]
    rw [e']
    exact (e _ (by simp only [workLen]; omega_using [hi, hk']) fun i' hi' => by omega_using [hi', hi, hk, hk', h]).trans
      (hl i hi k' hk')

/-! ## The permutation -/

theorem permute_noVec : ∀ i ∈ instrs Impl.Sha3.X86_64.permute, Impl.Scrub.X86_64.writesVec i = false := by
  have h : ((instrs Impl.Sha3.X86_64.permute).all fun i => !Impl.Scrub.X86_64.writesVec i) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem permOne_noVec (k : Nat) : ∀ i ∈ instrs (permOne k), Impl.Scrub.X86_64.writesVec i = false := by
  intro i hi
  simp only [permOne, instrs, List.mem_append] at hi
  rcases hi with (hi | hi) | hi | hi | hi
  · simp only [gather, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨_, _, rfl | rfl⟩ := hi <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  · exact permute_noVec i hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl
  · simp only [scatter, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨_, _, rfl | rfl⟩ := hi <;> rfl

/-- State `k` permuted, the others kept, by a call of the scalar
permutation. -/
theorem permOne_ok (hp : Thash4Pre n 8 σ) {k : Nat} (hk : k < 4) {t : State} (hw : t.wr = σ.wr)
    (hsp : t.gpr .rsp = σ.gpr .rsp) (h8 : t.gpr .r8 = W σ) {Y : Nat → KState} (hl : Lanes4 t.mem (W σ) Y) :
    WP isa (permOne k) t fun t' => (t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.gpr .r8 = W σ ∧
      (∀ g ∈ calleeSaved, t'.gpr g = t.gpr g) ∧
      Lanes4 t'.mem (W σ) (fun j => if j = k then keccakF (Y k) else Y j) ∧
      Frame [⟨W σ, 1600⟩, below (σ.gpr .rsp) 8] t.mem t'.mem) ∧ t'.xmm = t.xmm := by
  refine wp_xmm_keep (permOne_noVec k) ?_
  have hW := hp.work_fit
  simp only [permOne, oSt, oKs]
  refine WP.seq (WP.block_append (WP.mono (gather_ok hp hk h8 hw hl) fun t₁ ⟨g₁, r₁, w₁, s₁, f₁⟩ => ?_))
  refine Steps.wp_mov fun t₂ v₂ => Steps.wp_addi fun t₃ v₃ => Steps.wp_mov fun t₄ v₄ =>
    Steps.wp_addi fun t₅ v₅ => WP.block_nil ?_
  have hdi : t₅.gpr .rdi = W σ + BitVec.ofNat 64 800 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.gpr, g₁ _ (by decide), h8, sx_ofNat (by decide)]
  have hsi : t₅.gpr .rsi = W σ + BitVec.ofNat 64 1000 := by
    rw [v₅.gpr, v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), g₁ _ (by decide), h8, sx_ofNat (by decide)]
  have hsp₅ : t₅.gpr .rsp = σ.gpr .rsp := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      g₁ _ (by decide), hsp]
  have cs₅ : ∀ g ∈ calleeSaved, t₅.gpr g = t.gpr g := fun g hg => by
    have h := cs_ne hg
    rw [v₅.other _ h.2.2.2.1, v₄.other _ h.2.2.2.1, v₃.other _ h.2.2.2.2.1, v₂.other _ h.2.2.2.2.1, g₁ _ h.1]
  have m₅ : t₅.mem = t₁.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem]
  have w₅ : t₅.wr = σ.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁, hw]
  have rd₅ : t₅.rd = t.rd := by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, r₁]
  have hstk : ∀ {d l : Nat}, d + l ≤ workLen → (below (t₅.gpr .rsp) 8).Disjoint ⟨W σ + BitVec.ofNat 64 d, l⟩ :=
    fun h => by rw [hsp₅]; exact hp.stk_work.sub_right (sub_off _ h)
  have hlw : ∀ {d l : Nat}, 800 ≤ d → d + l ≤ workLen → Region.Disjoint ⟨W σ, 800⟩ ⟨W σ + BitVec.ofNat 64 d, l⟩ :=
    fun h h' => (disj_base _ h (by simp only [workLen] at h' hW; omega_using [h', hW])).symm
  have hl₁ : Lanes4 t₁.mem (W σ) Y := lanes4_frame hl f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hlw (by decide) (by decide)
  refine WP.seq (Proof.Sha3.X86_64.call_ok hdi hsi (Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide))
    (hstk (by decide)) (hstk (by decide)) ?_ fun t₆ r₆ w₆ c₆ f₆ st₆ di₆ _ => ?_)
  · rw [w₅, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W σ, workLen⟩, by simp, 800, rfl, by simp [workLen]⟩
    · exact ⟨⟨W σ, workLen⟩, by simp, 1000, rfl, by simp [workLen]⟩
  rw [m₅] at f₆
  have hl₆ : Lanes4 t₆.mem (W σ) Y := lanes4_frame hl₁ f₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hlw (by decide) (by decide)
    · exact hlw (by decide) (by decide)
    · exact (hstk (d := 0) (l := 800) (by decide)).symm.sub_left fun a h => by simpa using h
  refine WP.block_append (Steps.wp_mov fun t₇ v₇ => Proof.Sha3.X86_64.wp_subi fun t₈ v₈ _ => WP.block_nil ?_)
  have h8₈ : t₈.gpr .r8 = W σ := by
    rw [v₈.gpr, v₇.gpr, di₆, sx_ofNat (by decide), BitVec.add_sub_cancel]
  have m₈ : t₈.mem = t₆.mem := by rw [v₈.mem, v₇.mem]
  refine WP.mono (scatter_ok hp hk h8₈ (by rw [v₈.wr, v₇.wr, w₆, w₅]) (Y := Y) (by rw [m₈]; exact hl₆)
    (B := keccakF (Y k)) (by rw [m₈, st₆, m₅, s₁])) fun t₉ ⟨g₉, r₉, w₉, l₉, f₉⟩ => ?_
  refine ⟨by rw [r₉, v₈.rd, v₇.rd, r₆, rd₅], by rw [w₉, v₈.wr, v₇.wr, w₆, w₅, hw], by rw [g₉ _ (by decide), h8₈],
    fun g hg => ?_, l₉, ?_⟩
  · have h := cs_ne hg
    rw [g₉ _ h.1, v₈.other _ h.2.2.2.2.2.1, v₇.other _ h.2.2.2.2.2.1, c₆ g hg, cs₅ g hg]
  · rw [m₈] at f₉
    rw [hsp₅] at f₆
    have S : ∀ {d l : Nat}, d + l ≤ 1600 →
        Region.Sub ⟨W σ + BitVec.ofNat 64 d, l⟩ ⟨W σ, 1600⟩ := fun h => sub_off _ h
    refine (f₁.sub fun r hr => ?_).trans ((f₆.sub fun r hr => ?_).trans (f₉.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., S (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., S (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., S (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., sub_pre _ (by decide)⟩

/-! ## Keeping registers and slots in `xmm8`–`xmm13` -/

open RegUpd in
theorem park_ok (hp : Thash4Pre n stk σ) {u : State} (hw : u.wr = σ.wr) (h8 : u.gpr .r8 = W σ) :
    WP isa (.block park) u fun p => p.rd = u.rd ∧ p.wr = u.wr ∧ p.mem = u.mem ∧
      (∀ g, g ≠ .rax → p.gpr g = u.gpr g) ∧ p.xmm .xmm8 = (0 : BitVec 64) ++ u.gpr .r9 ∧
      p.xmm .xmm9 = (0 : BitVec 64) ++ u.gpr .r10 ∧ p.xmm .xmm10 = (0 : BitVec 64) ++ u.gpr .r11 ∧
      p.xmm .xmm11 = (0 : BitVec 64) ++ u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr) 64 ∧
      p.xmm .xmm12 = (0 : BitVec 64) ++ u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft) 64 ∧
      p.xmm .xmm13 = (0 : BitVec 64) ++ u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos) 64 := by
  unfold park
  refine wp_movqx (wp_movqx (wp_movqx (wp_movm' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr) ?_ ?_ (wp_movqx
    (wp_movm' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft) ?_ ?_ (wp_movqx
      (wp_movm' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos) ?_ ?_ (wp_movqx (WP.block_nil ?_)))))))))
  · simp only [ea_at', gpr_setXmm, h8]
  · exact rw_work hp (by simp only [wr_setXmm, hw]) (by decide)
  · simp only [ea_at', gpr_setXmm, gpr_setReg, reduceCtorEq, ↓reduceIte, h8]
  · exact rw_work hp (by simp only [wr_setXmm, wr_setReg, hw]) (by decide)
  · simp only [ea_at', gpr_setXmm, gpr_setReg, reduceCtorEq, ↓reduceIte, h8]
  · exact rw_work hp (by simp only [wr_setXmm, wr_setReg, hw]) (by decide)
  · exact ⟨rfl, rfl, rfl, fun g h => by simp only [gpr_setXmm, gpr_setReg, h, ↓reduceIte], rfl, rfl, rfl, rfl, rfl, rfl⟩

open RegUpd in
theorem unpark_ok (hp : Thash4Pre n stk σ) {q : State} (hw : q.wr = σ.wr) (h8 : q.gpr .r8 = W σ) :
    WP isa (.block unpark) q fun z => z.rd = q.rd ∧ z.wr = q.wr ∧
      (∀ g, g ≠ .rax → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → z.gpr g = q.gpr g) ∧
      z.gpr .r9 = (q.xmm .xmm8).extractLsb' 0 64 ∧ z.gpr .r10 = (q.xmm .xmm9).extractLsb' 0 64 ∧
      z.gpr .r11 = (q.xmm .xmm10).extractLsb' 0 64 ∧
      z.mem = ((q.mem.writeW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr) ((q.xmm .xmm11).extractLsb' 0 64)).writeW
        (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft) ((q.xmm .xmm12).extractLsb' 0 64)).writeW
        (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos) ((q.xmm .xmm13).extractLsb' 0 64) := by
  unfold unpark
  refine wp_movqr (wp_movqr (wp_movqr (wp_movqr (wp_store' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr) ?_ ?_
    (wp_movqr (wp_store' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft) ?_ ?_
      (wp_movqr (wp_store' (a := W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos) ?_ ?_ (WP.block_nil ?_)))))))))
  · simp only [ea_at', gpr_setReg, reduceCtorEq, ↓reduceIte, h8]
  · exact wr_work hp (by simp only [wr_setReg, hw]) (by decide)
  · simp only [ea_at', gpr_setReg, reduceCtorEq, ↓reduceIte, h8]
  · exact wr_work hp (by simp only [wr_setReg, hw]) (by decide)
  · simp only [ea_at', gpr_setReg, reduceCtorEq, ↓reduceIte, h8]
  · exact wr_work hp (by simp only [wr_setReg, hw]) (by decide)
  · exact ⟨rfl, rfl, fun g h₁ h₂ h₃ h₄ => by simp only [gpr_setReg, h₁, h₂, h₃, h₄, ↓reduceIte], rfl, rfl, rfl, rfl⟩

/-- `permute4S` meets `PermOk`, with 8 bytes of stack. -/
theorem permOk_S (hp : Thash4Pre n 8 σ) : PermOk permute4S σ 8 := by
  intro u X _ hwr hsp h8 _ _ _ _ hl _
  unfold permute4S
  refine WP.seq (WP.mono (park_ok hp hwr h8) fun p ⟨rdp, wrp, mp, gp, x8, x9, x10, x11, x12, x13⟩ => ?_)
  have wp' : p.wr = σ.wr := by rw [wrp, hwr]
  have hrsp : Reg.rsp ∈ calleeSaved := by decide
  refine WP.seq (WP.mono (permOne_ok hp (k := 0) (by decide) wp' (by rw [gp _ (by decide), hsp])
    (by rw [gp _ (by decide), h8]) (Y := X) (by rw [mp]; exact hl))
    fun q₀ ⟨⟨rd₀, wr₀, r8₀, cs₀, l₀, f₀⟩, xm₀⟩ => ?_)
  refine WP.seq (WP.mono (permOne_ok hp (k := 1) (by decide) (by rw [wr₀, wp'])
    (by rw [cs₀ _ hrsp, gp _ (by decide), hsp]) r8₀ l₀) fun q₁ ⟨⟨rd₁, wr₁, r8₁, cs₁, l₁, f₁⟩, xm₁⟩ => ?_)
  refine WP.seq (WP.mono (permOne_ok hp (k := 2) (by decide) (by rw [wr₁, wr₀, wp'])
    (by rw [cs₁ _ hrsp, cs₀ _ hrsp, gp _ (by decide), hsp]) r8₁ l₁)
    fun q₂ ⟨⟨rd₂, wr₂, r8₂, cs₂, l₂, f₂⟩, xm₂⟩ => ?_)
  refine WP.seq (WP.mono (permOne_ok hp (k := 3) (by decide) (by rw [wr₂, wr₁, wr₀, wp'])
    (by rw [cs₂ _ hrsp, cs₁ _ hrsp, cs₀ _ hrsp, gp _ (by decide), hsp]) r8₂ l₂)
    fun q₃ ⟨⟨rd₃, wr₃, r8₃, cs₃, l₃, f₃⟩, xm₃⟩ => ?_)
  refine WP.mono (unpark_ok hp (by rw [wr₃, wr₂, wr₁, wr₀, wp']) r8₃) fun z ⟨rdz, wrz, gz, z9, z10, z11, mz⟩ => ?_
  have hx : q₃.xmm = p.xmm := by rw [xm₃, xm₂, xm₁, xm₀]
  have mz' : z.mem = ((q₃.mem.writeW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr)
      (u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPtr) 64)).writeW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft)
      (u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oLeft) 64)).writeW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos)
      (u.mem.readW (W σ + BitVec.ofNat 64 Impl.SlhDsa.X86_64.Thash4.oPos) 64) := by
    rw [mz, hx, x11, x12, x13, extract_movq, extract_movq, extract_movq]
  have cs : ∀ g ∈ calleeSaved, q₃.gpr g = p.gpr g := fun g hg => by rw [cs₃ g hg, cs₂ g hg, cs₁ g hg, cs₀ g hg]
  have hd : ∀ {d : Nat}, 800 ≤ d → d + 8 ≤ 2400 → Region.Disjoint ⟨W σ, 800⟩ ⟨W σ + BitVec.ofNat 64 d, 8⟩ :=
    fun h h' => (disj_base _ h (by omega_using [h'])).symm
  rw [mp] at f₀
  refine ⟨?_, ?_, by rw [rdz, rd₃, rd₂, rd₁, rd₀, rdp], by rw [wrz, wr₃, wr₂, wr₁, wr₀, wrp], fun g hg => ?_,
    fun g hg => ?_⟩
  · rw [mz']
    refine lanes4_writeW (lanes4_writeW (lanes4_writeW (lanes4_congr l₃ fun k hk => ?_) (hd (by decide) (by decide)) _)
      (hd (by decide) (by decide)) _) (hd (by decide) (by decide)) _
    rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> simp
  · rw [mz']
    exact frame_restore (frame_restore (frame_restore (f₀.trans (f₁.trans (f₂.trans f₃))) _) _) _
  · rcases hg with rfl | rfl | rfl | rfl | rfl
    · rw [gz _ (by decide) (by decide) (by decide) (by decide), r8₃, h8]
    · rw [z9, hx, x8, extract_movq]
    · rw [z10, hx, x9, extract_movq]
    · rw [z11, hx, x10, extract_movq]
    · rw [gz _ (by decide) (by decide) (by decide) (by decide), cs _ hrsp, gp _ (by decide)]
  · have h := cs_ne hg
    rw [gz _ h.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2, cs g hg, gp _ h.1]

/-! ## `thash4` -/

/-- The baseline `thash4 n` writes each output, changes only the outputs,
`work` but its table and the 8 bytes below the stack pointer, and keeps the
callee-saved registers. -/
theorem correct (hp : Thash4Pre n 8 σ) (hn : n % 8 = 0) (hn' : n ≤ 136) :
    WP isa (thash4 n) σ (fun s' => (∀ k < 4, bytesAt s'.mem (outAt σ k) n = Spec.Sha3.shake256 (msg σ k) n) ∧
      Frame (thash4Changes n 8 σ) σ.mem s'.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) :=
  correctWith hp hn hn' (zeroOk_S hp) (permOk_S hp) tailOk_nil

end VG.Proof.SlhDsa.X86_64.Thash4Base
