import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase`. -/
section

/-!
# ML-DSA on 32-bit ARM: what the proofs of `HintBitPack` and `HintBitUnpack` share

The comparisons of small numbers (`ltBit`), pointers that do not wrap around,
the parameters, and the frames: the words a push stores, which the body and
the pop reload.
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Spec.MlDsa

/-! ## Numbers -/

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ 55 ≤ ω ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- The sign bit of `x - y`, for `x` and `y` less than `2³¹`: whether `x < y`. -/
theorem ltBit_val {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    (x - y) >>> 31 = if x.toNat < y.toNat then 1 else 0 := by
  split <;> bv_omega

/-- `Z` after `ltBit`: set iff `x ≥ y`. -/
theorem ltBit_z {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    ((x - y) >>> 31 - 0 == 0) = decide (y.toNat ≤ x.toNat) := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.ltBit_val hx hy]
  split
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

theorem sub_zero32 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem toNat_ofNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_succ32 (x : Nat) : BitVec.ofNat 32 x + 1 = BitVec.ofNat 32 (x + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]

theorem ptr_add (p : BitVec 32) (a b : Nat) : p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `Z` after comparing a counter with a constant. -/
theorem cmp_const {j c : Nat} (hj : j < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 j - BitVec.ofNat 32 c == 0) = decide (j = c) := by
  rw [VG.Proof.MlKem.Arm.cmp_z _ _ hc, VG.Proof.MlDsa.Arm.Pack.Hint.toNat_ofNat32 hj]

/-- The byte `strb` stores of a small number. -/
theorem setWidth8_ofNat (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A byte, as `ldrb` loads it. -/
theorem byte_toNat32 (b : Byte) : (b.setWidth 32).toNat = b.toNat := VG.Proof.MlKem.Arm.setWidth32_toNat b

/-! ## Addresses -/

theorem addr_ofNat (p : BitVec 32) {a : Nat} (h : p.toNat + a < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 a) = State.addr p + BitVec.ofNat 64 a := addr_add h

theorem addr_sub' {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  have := a.isLt
  simp only [State.addr]; bv_omega

/-! ## Frames -/

/-- Word `i` a push stored. -/
theorem storeWords_readW (m : Mem) (a : BitVec 32) (vs : List (BitVec 32)) (h : a.toNat + 4 * vs.length ≤ 2 ^ 32)
    {i : Nat} (hi : i < vs.length) :
    (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i] := by
  induction vs generalizing m a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons v vs ih =>
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    cases i with
    | zero =>
      have hf := storeWords_frame (m.writeW (State.addr a) v) (a + 4) vs (by bv_omega)
      rw [show a + BitVec.ofNat 32 (4 * 0) = a by simp, hf.readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          by_cases hv : vs.length = 0
          · intro x _ h2; simp only [Region.Contains, hv] at h2; omega
          rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.Arm.Pack.Hint.addr_ofNat a (by omega)]
          exact Offset.base_disjoint _ (Nat.le_refl 4) (by have := addr_toNat' a; omega)) (by decide),
        Mem.readW_writeW_self32]
      rfl
    | succ j =>
      rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
        rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.Arm.Pack.Hint.ptr_add]; congr 2; omega]
      exact ih _ _ (by bv_omega) (by omega)

/-- The region of the frame of `rs`. -/
abbrev frameR (s : State) (rs : List Reg) : Region :=
  ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩

/-- A push changes memory only in its frame. -/
theorem pushed_frame (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    Frame [VG.Proof.MlDsa.Arm.Pack.Hint.frameR s rs] s.mem (pushed rs s).mem := by
  have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega)
  rwa [List.length_map] at this

/-- The word of register `rs[i]` in the frame. -/
theorem pushed_word (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (pushed rs s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 32 =
      s.gpr rs[i] := by
  have := VG.Proof.MlDsa.Arm.Pack.Hint.storeWords_readW s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega) (i := i) (by rw [List.length_map]; exact hi)
  rw [List.getElem_map] at this
  exact this

/-- The frame of `rs` is the bytes below `sp`. -/
theorem frameR_eq (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    VG.Proof.MlDsa.Arm.Pack.Hint.frameR s rs = ⟨State.addr s.sp - BitVec.ofNat 64 (4 * rs.length), 4 * rs.length⟩ := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.frameR, VG.Proof.MlDsa.Arm.Pack.Hint.addr_sub' h]

theorem frameR_contains (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (VG.Proof.MlDsa.Arm.Pack.Hint.frameR s rs).Contains (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 4 := by
  have := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 (4 * rs.length)).toNat = s.sp.toNat - 4 * rs.length := by bv_omega
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.addr_ofNat _ (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Word `i` of the frame, after the body changed memory only outside it. -/
theorem frame_saved (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {m : Mem} {R : List Region}
    (hf : Frame R (pushed rs s).mem m) (hd : ∀ r ∈ R, (VG.Proof.MlDsa.Arm.Pack.Hint.frameR s rs).Disjoint r) {i : Nat} (hi : i < rs.length) :
    m.readW (State.addr ((pushed rs s).sp + BitVec.ofNat 32 (4 * i))) 32 = s.gpr rs[i] := by
  rw [pushed_sp, hf.readW (VG.Proof.MlDsa.Arm.Pack.Hint.frameR_contains rs h hi) hd (by decide), VG.Proof.MlDsa.Arm.Pack.Hint.pushed_word rs h hi]

/-- The load of the stack argument into `r12`. -/
theorem entry_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldrSp .r12 0]) s fun s' =>
      s' = s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32) := by
  run_block [ia]

/-- No instruction of `c` writes `r`, by evaluating `Code.allInstrs`. -/
theorem noWrite {c : Prog isa} {r : Reg} (h : c.allInstrs (fun i => dstOf i != some r) = true) :
    ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using h i hi

end VG.Proof.MlDsa.Arm.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintCT`. -/
section

/-!
# Constant time of code that leaks memory both runs agree on (ARMv7)

The ARMv7 counterpart of the x86-64 `memTaint` of ML-DSA
(`Proof/MlDsa/X86_64/Pack/MemTaint.lean`), for `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which branch and index memory on their input,
which they load from memory.

The taint analysis (`Proof/Framework/Arm/Taint.lean`) treats loaded memory as
secret. `memTaint` is one for code that runs from states whose permitted
memory both runs agree on (`MemEq`): every load (`ldr`, `ldrb`) it makes is
then public, and a store keeps the agreement if it stores a public value at a
public address.

On ARMv7 these functions run in a frame, which holds the callee-saved
registers of each run, which differ; the analysis would take them for
public. So the code that needs it runs from states narrowed to the regions it
accesses (`RelCT.narrow`): a run with fewer permissions is the actual run
(`Exec.widen` and determinism). What is left of the frame, the instructions
that only access the stack (`spOnly`), leaks only addresses computed from
the stack pointer (`RelCT.spBlock`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Arm.Taint (T pub)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The taint agrees, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : VG.Arm.State) : Prop :=
  VG.Arm.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ VG.Proof.MlDsa.Arm.Pack.Hint.MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Loads are public; stores must store public values; the stack and frames
are not analysed. -/
def mstep (τ : T) : Instr → Option T
  | .ldr t n off => (VG.Arm.Taint.stepK τ (.ldr t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .ldrb t n off => (VG.Arm.Taint.stepK τ (.ldrb t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .str t n off => if pub τ t then VG.Arm.Taint.stepK τ (.str t n off) else none
  | .strb t n off => if pub τ t then VG.Arm.Taint.stepK τ (.strb t n off) else none
  | .ldrSp .. | .push _ | .pop .. => none
  | i => VG.Arm.Taint.stepK τ i

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.Arm.Pack.Hint.MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.writeW {rs : List Region} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.Arm.Pack.Hint.MemEq rs m₁ m₂) (a : Addr) {w : Nat}
    (v : BitVec w) : VG.Proof.MlDsa.Arm.Pack.Hint.MemEq rs (m₁.writeW a v) (m₂.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact h x hx

/-- A register made public, whose values agree. -/
theorem agree_insert {τ : T} {s₁ s₂ : VG.Arm.State} (ha : VG.Arm.Taint.Agree τ s₁ s₂) {d : Reg}
    (hd : s₁.gpr d = s₂.gpr d) : VG.Arm.Taint.Agree { τ with regs := τ.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact hd
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ⟨ha.wf₁.lens, ha.wf₁.bases, ha.wf₁.args, ha.wf₁.argBases⟩,
    ⟨ha.wf₂.lens, ha.wf₂.bases, ha.wf₂.args, ha.wf₂.argBases⟩, ha.ok, ha.slots, ha.sp, ha.argMem⟩

/-- The instructions that neither access memory nor change the stack. -/
theorem exec_pure {i : Instr} (hi : ∀ t n off, i ≠ .ldr t n off ∧ i ≠ .ldrb t n off ∧ i ≠ .str t n off ∧
      i ≠ .strb t n off ∧ i ≠ .ldrSp t off)
    {s s' : VG.Arm.State} (h : exec i s = some s') : s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | ldr t n off => exact absurd rfl (hi t n off).1
  | ldrb t n off => exact absurd rfl (hi t n off).2.1
  | str t n off => exact absurd rfl (hi t n off).2.2.1
  | strb t n off => exact absurd rfl (hi t n off).2.2.2.1
  | ldrSp t off => exact absurd rfl (hi t t off).2.2.2.2
  | push => simp only [exec, reduceCtorEq] at h
  | pop | alloc | free => simp only [exec, reduceCtorEq] at h
  | addSp d imm =>
    simp only [exec] at h
    split at h <;> cases h
    exact ⟨rfl, rfl, rfl⟩
  | _ =>
    simp only [exec, Option.map_eq_some_iff, Option.some.injEq] at h
    first
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)
    | (subst h; exact ⟨rfl, rfl, rfl⟩)

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : VG.Arm.State} (ha : VG.Proof.MlDsa.Arm.Pack.Hint.MAgree τ s₁ s₂)
    (hs : VG.Proof.MlDsa.Arm.Pack.Hint.mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.MAgree τ' s₁' s₂' := by
  obtain ⟨hA, hrd, hwr, hm⟩ := ha
  -- Instructions the base analysis handles, which keep the memory.
  have base : ∀ {j : Instr}, (∀ t n off, j ≠ .ldr t n off ∧ j ≠ .ldrb t n off ∧ j ≠ .str t n off ∧
      j ≠ .strb t n off ∧ j ≠ .ldrSp t off) → VG.Arm.Taint.stepK τ j = some τ' → exec j s₁ = some s₁' →
      exec j s₂ = some s₂' → addrs j s₁ = addrs j s₂ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.MAgree τ' s₁' s₂' := fun hj hs' e₁ e₂ => by
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound ⟨hA.rf, hA.wr, hA.wf₁, hA.wf₂, hA.ok, hA.slots, hA.sp, hA.argMem⟩
      (VG.Arm.Taint.stepK_eq ▸ hs') e₁ e₂
    obtain ⟨m₁, r₁, w₁⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.exec_pure hj e₁
    obtain ⟨m₂, r₂, w₂⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.exec_pure hj e₂
    exact ⟨hadd, ht, by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], by rw [m₁, m₂, r₁, w₁]; exact hm⟩
  cases i with
  | ldr t n off =>
    simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], VG.Proof.MlDsa.Arm.Pack.Hint.agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, Mem.readW, ← hadd, hm.read hi (by decide)]
  | ldrb t n off =>
    simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load8] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], VG.Proof.MlDsa.Arm.Pack.Hint.agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, ← hadd, hm _ hi]
  | str t n off =>
    simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | strb t n off =>
    simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | ldrSp => simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep, reduceCtorEq] at hs
  | push => simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep, reduceCtorEq] at hs
  | pop => simp only [VG.Proof.MlDsa.Arm.Pack.Hint.mstep, reduceCtorEq] at hs
  | mov => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | dp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | adds => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | adc => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | subs => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | cmp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | movw => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | movt => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | rev => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | mul => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | addSp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | alloc | free => simp only [exec, reduceCtorEq] at e₁

/-- Taint tracking over memory both runs agree on, for ARMv7. -/
def memTaint : VG.Taint isa where
  T := T
  Agree := VG.Proof.MlDsa.Arm.Pack.Hint.MAgree
  step := VG.Proof.MlDsa.Arm.Pack.Hint.mstep
  step_sound := VG.Proof.MlDsa.Arm.Pack.Hint.mstep_sound
  condPub τ _ := τ.flags
  cond_sound ha hc := VG.Arm.Taint.cond_sound ha.1 hc
  meet := VG.Arm.Taint.meet
  meet_left h := ⟨VG.Arm.Taint.meet_left h.1, h.2⟩
  meet_right h := ⟨VG.Arm.Taint.meet_right h.1, h.2⟩
  le := VG.Arm.Taint.leK
  le_sound hle h := ⟨VG.Arm.Taint.le_sound (VG.Arm.Taint.leK_eq ▸ hle) h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

/-! ## Narrowing the permissions -/

/-- Two runs of `c` leak the same trace if its runs from the states narrowed
to the regions `rd`, `wr` do, and exist. -/
theorem RelCT.narrow {c : Prog isa} {P : VG.Arm.State → VG.Arm.State → Prop} (rd wr : VG.Arm.State → List Region)
    (hc : ∀ a b, P a b → Covers (rd a ++ wr a) (a.rd ++ a.wr) ∧ Covers (wr a) a.wr ∧
      Covers (rd b ++ wr b) (b.rd ++ b.wr) ∧ Covers (wr b) b.wr)
    (hrun : ∀ a b, P a b → (∃ t s', Exec isa c (a.withRegions (rd a) (wr a)) t s') ∧
      ∃ t s', Exec isa c (b.withRegions (rd b) (wr b)) t s')
    (hct : RelCT isa (fun a' b' => ∃ a b, P a b ∧ a' = a.withRegions (rd a) (wr a) ∧
      b' = b.withRegions (rd b) (wr b)) c fun _ _ => True) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂⟩ := hc _ _ hp
  obtain ⟨⟨u₁, n₁, f₁⟩, ⟨u₂, n₂, f₂⟩⟩ := hrun _ _ hp
  have g₁ := Exec.widen f₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have g₂ := Exec.widen f₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at g₁ g₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ g₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ g₂
  exact ⟨(hct _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

/-! ## Instructions that only access the stack -/

/-- The instructions whose addresses depend only on the stack pointer. -/
def spOnly : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_spOnly {i : Instr} (hi : VG.Proof.MlDsa.Arm.Pack.Hint.spOnly i = true) {s₁ s₂ : VG.Arm.State} (hsp : s₁.sp = s₂.sp) :
    addrs i s₁ = addrs i s₂ := by
  cases i <;> simp_all [VG.Proof.MlDsa.Arm.Pack.Hint.spOnly, addrs]

theorem execBlock_spOnly {is : List Instr} (h : is.all VG.Proof.MlDsa.Arm.Pack.Hint.spOnly = true) {s₁ s₂ s₁' s₂' : VG.Arm.State}
    {t₁ t₂ : List Leak} (hsp : s₁.sp = s₂.sp) (e₁ : execBlock isa is s₁ = some (s₁', t₁))
    (e₂ : execBlock isa is s₂ = some (s₂', t₂)) : t₁ = t₂ := by
  induction is generalizing s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    split at e₂ <;> [cases e₂; skip]
    rename_i a₁ x₁ _ a₂ x₂
    simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e₁ e₂
    obtain ⟨_, u₁, f₁, rfl, rfl⟩ := e₁
    obtain ⟨_, u₂, f₂, rfl, rfl⟩ := e₂
    have ha : addrs i s₁ = addrs i s₂ := VG.Proof.MlDsa.Arm.Pack.Hint.addrs_spOnly h.1 hsp
    rw [ha, ih h.2 (by rw [exec_sp x₁, exec_sp x₂, hsp]) f₁ f₂]

/-- A block of instructions that only access the stack leaks the same trace
from states with the same stack pointer. -/
theorem RelCT.spBlock {is : List Instr} (h : is.all VG.Proof.MlDsa.Arm.Pack.Hint.spOnly = true) {P : VG.Arm.State → VG.Arm.State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block e₁ =>
    cases e₂ with
    | block e₂ => exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.execBlock_spOnly h (hsp _ _ hp) e₁ e₂, trivial⟩

/-! ## Helpers -/

theorem relct_wp {c : Prog isa} {P : VG.Arm.State → VG.Arm.State → Prop} {F₁ F₂ : VG.Arm.State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.MlDsa.Arm.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPack`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, correct

As on x86-64, the code follows the fold form of `HintBitPack`
(`Proof/MlDsa/Pack/Hint.lean`) step by step: the bytes of `y` are the array of
the spec, and `r1` its index, which stays below `ω` because it counts the 1s
before the current coefficient (`hpIdx_lt`). The loops (`main_ok`) run from
any state that permits reading the hint and writing `y`, so that constant time
can narrow the state to those two regions (`HintPackCT.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `h`, `ω`, `y` and `len`. -/
abbrev pH : BitVec 32 := s₀.gpr .r0
abbrev pW : BitVec 32 := s₀.gpr .r2
abbrev pY : BitVec 32 := s₀.gpr .r3
abbrev pL : BitVec 32 := stackArg s₀ 0
abbrev pω : Nat := (VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀).toNat
abbrev pLen : Nat := (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀).toNat
abbrev pk : Nat := VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀ - VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀
abbrev hR : Region := ⟨State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀), (s₀.gpr .r1).toNat * 4⟩
abbrev yR : Region := ⟨State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀), VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The hint. -/
abbrev pHint : List (Vector Bool n) := hintAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀)

end

/-- The precondition, as `sig_pre` states it. -/
structure PPre (s : State) : Prop where
  sp : 8 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [VG.Proof.MlDsa.Arm.Pack.Hint.hR s, VG.Proof.MlDsa.Arm.Pack.Hint.argR s]
  wr : s.wr = [VG.Proof.MlDsa.Arm.Pack.Hint.yR s]
  d_hy : (VG.Proof.MlDsa.Arm.Pack.Hint.hR s).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.yR s)
  d_ya : (VG.Proof.MlDsa.Arm.Pack.Hint.yR s).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.argR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.hR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.yR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (VG.Proof.MlDsa.Arm.Pack.Hint.argR s)
  fitH : (VG.Proof.MlDsa.Arm.Pack.Hint.pH s).toNat + (s.gpr .r1).toNat * 4 ≤ 2 ^ 32
  fitY : (VG.Proof.MlDsa.Arm.Pack.Hint.pY s).toNat + VG.Proof.MlDsa.Arm.Pack.Hint.pLen s ≤ 2 ^ 32
  par : (VG.Proof.MlDsa.Arm.Pack.Hint.pω s, VG.Proof.MlDsa.Arm.Pack.Hint.pk s) ∈ hintParams
  ωle : VG.Proof.MlDsa.Arm.Pack.Hint.pω s ≤ VG.Proof.MlDsa.Arm.Pack.Hint.pLen s
  hlen : (s.gpr .r1).toNat = 256 * VG.Proof.MlDsa.Arm.Pack.Hint.pk s
  ones : hintOnes (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s) ≤ VG.Proof.MlDsa.Arm.Pack.Hint.pω s

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀)
include hp

theorem pfacts : 4 ≤ VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ ≤ 8 ∧ 55 ≤ VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ ≤ 80 ∧ VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ = VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀ ∧ VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀ ≤ 88 := by
  have := VG.Proof.MlDsa.Arm.Pack.Hint.mem_hintParams hp.par
  have := hp.ωle
  have e : VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ = VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀ - VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ := rfl
  omega

/-! ## Zeroing `y` -/

omit hp in
theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r1 .r12 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r1 = s.gpr .r12 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

omit hp in
theorem zeroStep_ok {s : State} {y c : BitVec 32} (h5 : s.gpr .r5 = y) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r12 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) ((s.gpr .r12).setWidth 8) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

/-- Zeroing the `len` bytes of `y`, from the entry values of the registers. -/
theorem zero_ok {s : State} (h0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀) (h2 : s.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀) (h3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)
    (h12 : s.gpr .r12 = VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀) (hwr : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀ ∈ s.wr) :
    WP isa hbpZero s fun s' => s'.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ ∧ s'.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) ∧
      s'.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀ ∧ s'.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ ∧
      bytesAt s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = List.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) 0 ∧
      Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.pfacts hp
  have fY := hp.fitY
  have hL := (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀).isLt
  unfold hbpZero
  refine WP.seq (WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.zeroPro_ok fun s₁ ⟨r1₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (N := VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) (fun t s' => s'.gpr .r5 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 t ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ ∧
      s'.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) ∧ s'.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀ ∧ s'.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ ∧
      Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] s.mem s'.mem ∧ (∀ u < t, s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 u) = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega)
    (fun t ht s' ⟨i5, i4, i12, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s' ⟨_, _, _, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ⟨i0, i1, i2, i3,
      VG.Proof.MlKem.bytesAt_eq (by simp) fun u hu => by rw [hz u hu]; simp, hf, hrd, hwr', hsp⟩)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], ?_, by rw [r2₁, h2], by rw [r3₁, h3], by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩
  · have ea : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 t + BitVec.ofNat 32 0) = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 t :=
      addr_ptr _ _ _ (by omega)
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.zeroStep_ok i5 i4 (by
        rw [ea, hwr']; exact ⟨_, hwr, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s'' ⟨r5', r4', z', m', r0', r1', r2', r3', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', BitVec.add_assoc, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32], by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r1', i1], by rw [r2', i2], by rw [r3', i3], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩, by rw [z']; exact count_z (k := 1) ht (by decide) (by omega)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m', ea, VG.Proof.MlKem.Arm.byte_writeW8 _ _ (by omega) (by omega)]
      split
      · rw [i12]; rfl
      · exact hz u (by omega)
  · rw [r1₁, h12, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by have := hp.ωle; exact this), VG.Proof.MlDsa.Arm.Pack.Hint.toNat_ofNat32 (by omega)]

end

/-! ## The spec, step by step -/

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀)) (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀).getD i noHint)) (VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ i)

theorem hpT_zero (s₀ : State) (i : Nat) : VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i 0 = VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ i := by
  simp only [VG.Proof.MlDsa.Arm.Pack.Hint.hpT, List.range_zero, List.foldl_nil]


theorem hpS_idx (s₀ : State) (i : Nat) : (VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ i).2 = onesBefore (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) i 0 := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2 = onesBefore (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) i j := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hpT, hpSteps_idx, VG.Proof.MlDsa.Arm.Pack.Hint.hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (s₀ : State) (i j : Nat) :
    VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i (j + 1) = hpStep ((VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀).getD i noHint) (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j) j := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ (i + 1) = ((VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i n).1.set! (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i) (BitVec.ofNat 8 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i n).2), (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i n).2) := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-! ## The polynomials -/

/-- Before coefficient `j` of polynomial `i`, in the loops that start from `sA`. -/
structure CInv (s₀ sA : State) (i j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2
  r3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ - i))
  r5 : s.gpr .r5 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i)
  r12 : s.gpr .r12 = BitVec.ofNat 32 j
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).1.toList

/-- What the loops need of the state they start from: permission to read the
hint and write `y`, and the hint of the entry state. -/
structure MainPre (s₀ sA : State) : Prop where
  rd : VG.Proof.MlDsa.Arm.Pack.Hint.hR s₀ ∈ sA.rd
  wr : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀ ∈ sA.wr
  hint : ∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀, coeffAt sA.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) t = coeffAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) t

theorem coefLoad_ok {s : State} {x : BitVec 32} (h0 : s.gpr .r0 = x)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r2 .r0 0, .cmp .r2 (.imm 0)]) s fun s' =>
      s'.z = (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h0, ia]
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem coefSet_ok {s : State} {y i j : BitVec 32} (h1 : s.gpr .r1 = i) (h3 : s.gpr .r3 = y)
    (h12 : s.gpr .r12 = j) (o : InRegions s.wr (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r2 .r3 (.reg .r1), .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = i + 1 ∧ s'.mem = s.mem.writeW (State.addr (y + i + BitVec.ofNat 32 0)) (j.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h1, h3, h12, o]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h1, ite_neg' h2]

theorem coefNext_ok {s : State} {x j : BitVec 32} (h0 : s.gpr .r0 = x) (h12 : s.gpr .r12 = j) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 1), .cmp .r12 (.imm 256)]) s fun s' =>
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r12 = j + 1 ∧ s'.z = (j + 1 - 256 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block [h0, h12]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h2, ite_neg' h1]

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.MainPre s₀ sA)
include hp hA

/-- A coefficient. -/
theorem coef_ok {i j : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (hj : j < 256) {s : State} (hI : VG.Proof.MlDsa.Arm.Pack.Hint.CInv s₀ sA i j s) :
    WP isa hbpCoef s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.CInv s₀ sA i (j + 1) s' ∧ s'.z = decide (j + 1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.pfacts hp
  have fH := hp.fitH
  have fY := hp.fitY
  have hl := hp.hlen
  have t_lt : 256 * i + j < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ := by omega
  have hin : (VG.Proof.MlDsa.Arm.Pack.Hint.hR s₀).Contains (coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have ea : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)) + BitVec.ofNat 32 0) =
      coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j) := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hw : s.mem.readW (coeffAddr (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j)) 32 =
      coeffAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j) := by
    rw [← hA.hint _ t_lt, coeffAt_eq]
    exact hI.frame.readW hin (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide)
  have hbit := VG.Proof.MlDsa.Arm.Pack.Hint.hintAt_get (m := s₀.mem) (p := State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) hi (show j < n from hj)
  have hT := VG.Proof.MlDsa.Arm.Pack.Hint.hpT_succ s₀ i j
  have hidx := VG.Proof.MlDsa.Arm.Pack.Hint.hpT_idx s₀ i j
  unfold hbpCoef
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.coefLoad_ok hI.r0 (by
      rw [ea, hI.rd, hI.wr]; exact ⟨_, List.mem_append_left _ hA.rd, hin⟩))
    fun s₁ ⟨z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  rw [ea, hw, VG.Proof.MlDsa.Arm.Pack.Hint.sub_zero32] at z₁
  refine WP.seq (WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun h0 => ?_) (fun h1 => ?_))
  · -- A 0.
    have h0 : coeffAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j) = 0 := by
      rw [z₁] at h0; exact beq_iff_eq.mp h0
    refine WP.block_nil (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.coefNext_ok (x := VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₁ _ (by decide), hI.r0])
        (by rw [g₁ _ (by decide), hI.r12])) fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₁, hI.rd], by rw [wr₃, wr₁, hI.wr], by rw [sp₃, sp₁, hI.sp],
        by rw [m₃, m₁]; exact hI.frame, ?_⟩, ?_⟩)
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.Arm.Pack.Hint.ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r1, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32]
    · rw [m₃, m₁, hI.y, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [z₃, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32]; exact VG.Proof.MlDsa.Arm.Pack.Hint.cmp_const (by omega) (by decide)
  · -- A 1: `y[index] ← j`.
    have h1 : coeffAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) (256 * i + j) ≠ 0 := by
      rw [z₁] at h1; exact fun e => by rw [e] at h1; exact absurd h1 (by decide)
    have hlt : (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2 < VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ := by
      have : onesBefore (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) i j < hintOnes (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) :=
        hpIdx_lt (VG.Proof.MlDsa.Arm.Pack.Hint.hintAt_length s₀.mem _ _) hi hj (by rw [hbit]; exact decide_eq_true h1)
      have := hp.ones
      omega
    have eb : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2 + BitVec.ofNat 32 0) =
        State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2 := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    have hinY : (VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀).Contains (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.coefSet_ok (i := BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i j).2) (y := VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) (j := BitVec.ofNat 32 j)
        (by rw [g₁ _ (by decide), hI.r1]) (by rw [g₁ _ (by decide), hI.r3])
        (by rw [g₁ _ (by decide), hI.r12]) (by rw [eb, wr₁, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
      fun s₂ ⟨r1₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.coefNext_ok (x := VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r0])
        (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r12]))
      fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁, hI.rd], by rw [wr₃, wr₂, wr₁, hI.wr],
        by rw [sp₃, sp₂, sp₁, hI.sp], ?_, ?_⟩, ?_⟩
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.Arm.Pack.Hint.ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [g₃ _ (by decide) (by decide), r1₂, hT, hpStep, hbit, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32]
    · rw [m₃, m₂, m₁, eb]
      exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
    · rw [m₃, m₂, m₁, eb, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hT, hpStep, hbit,
        VG.Proof.MlDsa.Arm.Pack.Hint.setWidth8_ofNat]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Array.set!_eq_setIfInBounds,
        Array.toList_setIfInBounds]
    · rw [z₃, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32]; exact VG.Proof.MlDsa.Arm.Pack.Hint.cmp_const (by omega) (by decide)

/-- The coefficients of polynomial `i`. -/
theorem coefs_ok {i : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) {s : State} (hI : VG.Proof.MlDsa.Arm.Pack.Hint.CInv s₀ sA i 0 s) :
    WP isa (.loop hbpCoef .ne) s (VG.Proof.MlDsa.Arm.Pack.Hint.CInv s₀ sA i 256) :=
  wp_loop_ne (VG.Proof.MlDsa.Arm.Pack.Hint.CInv s₀ sA i) (N := 256) (by decide) (fun j hj _ h => VG.Proof.MlDsa.Arm.Pack.Hint.coef_ok hp hA hi hj h) (fun _ h => h) hI

end

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure HPInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ + BitVec.ofNat 32 (4 * (256 * i))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ i).2
  r3 : s.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀ - i))
  r5 : s.gpr .r5 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i)
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = (VG.Proof.MlDsa.Arm.Pack.Hint.hpS s₀ i).1.toList

theorem polyStart_ok {s : State} :
    WP isa (.block [.mov .r12 (.imm 0)]) s fun s' => s'.gpr .r12 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem polyEnd_ok {s : State} {x y c : BitVec 32} (h1 : s.gpr .r1 = x) (h5 : s.gpr .r5 = y)
    (h4 : s.gpr .r4 = c) (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r1 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) (x.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [h1, h5, h4, o]
  simp only [true_and]; intro r h4 h5; rw [ite_neg' h4, ite_neg' h5]

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.MainPre s₀ sA)
include hp hA

/-- A polynomial. -/
theorem poly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) {s : State} (hP : VG.Proof.MlDsa.Arm.Pack.Hint.HPInv s₀ sA i s) :
    WP isa hbpPoly s fun s' => VG.Proof.MlDsa.Arm.Pack.Hint.HPInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.pfacts hp
  have fY := hp.fitY
  unfold hbpPoly
  refine WP.seq (WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.polyStart_ok fun s₁ ⟨r12₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.coefs_ok hp hA hi (s := s₁) ⟨by rw [g₁ _ (by decide), hP.r0, Nat.add_zero], by rw [g₁ _ (by decide), hP.r1, VG.Proof.MlDsa.Arm.Pack.Hint.hpT_zero],
    by rw [g₁ _ (by decide), hP.r3], by rw [g₁ _ (by decide), hP.r4], by rw [g₁ _ (by decide), hP.r5], by rw [r12₁]; rfl,
    by rw [rd₁, hP.rd], by rw [wr₁, hP.wr], by rw [sp₁, hP.sp], by rw [m₁]; exact hP.frame,
    by rw [m₁, hP.y, VG.Proof.MlDsa.Arm.Pack.Hint.hpT_zero]⟩) fun s₂ hI => ?_)
  have hidx : (VG.Proof.MlDsa.Arm.Pack.Hint.hpT s₀ i 256).2 < 256 := by
    have := VG.Proof.MlDsa.Arm.Pack.Hint.hpT_idx s₀ i 256
    have h1 : onesBefore (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) i 256 ≤ hintOnes (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) := onesBefore_n_le (VG.Proof.MlDsa.Arm.Pack.Hint.hintAt_length _ _ _) hi
    have := hp.ones
    omega
  have ea : State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ + BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i) + BitVec.ofNat 32 0) =
      State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i) := by
    rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
  have hinY : (VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀).Contains (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀) + BitVec.ofNat 64 (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + i)) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.polyEnd_ok hI.r1 hI.r5 hI.r4 (by rw [ea, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
    fun s₃ ⟨r5₃, r4₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₃, hI.rd], by rw [wr₃, hI.wr],
      by rw [sp₃, hI.sp], ?_, ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hI.r0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [g₃ _ (by decide) (by decide), hI.r1, VG.Proof.MlDsa.Arm.Pack.Hint.hpS_succ]
  · rw [g₃ _ (by decide) (by decide), hI.r3]
  · rw [r4₃]; exact count_sub (k := 1) hi
  · rw [r5₃, BitVec.add_assoc, VG.Proof.MlDsa.Arm.Pack.Hint.ofNat_succ32, Nat.add_assoc]
  · rw [m₃, ea]
    exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
  · rw [m₃, ea, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, VG.Proof.MlDsa.Arm.Pack.Hint.hpS_succ, VG.Proof.MlDsa.Arm.Pack.Hint.setWidth8_ofNat,
      Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · rw [z₃]; exact count_z (k := 1) hi (by decide) (by omega)

end

theorem mainPro_ok {s : State} :
    WP isa (.block [.mov .r4 (.reg .r1), .dp .add .r5 .r3 (.reg .r2), .mov .r1 (.imm 0)]) s fun s' =>
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 + s.gpr .r2 ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

/-- The polynomials, from the state after zeroing `y`. -/
theorem main_ok {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀) {sA : State} (hA : VG.Proof.MlDsa.Arm.Pack.Hint.MainPre s₀ sA) (h0 : sA.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)
    (h1 : sA.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀)) (h2 : sA.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀) (h3 : sA.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)
    (hz : bytesAt sA.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = List.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) 0) :
    WP isa hbpMain sA fun s' =>
      bytesAt s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = hintBitPack (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) ∧
      Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] sA.mem s'.mem ∧ s'.rd = sA.rd ∧ s'.wr = sA.wr ∧ s'.sp = sA.sp := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.pfacts hp
  unfold hbpMain
  refine WP.seq (WP.mono VG.Proof.MlDsa.Arm.Pack.Hint.mainPro_ok fun s₁ ⟨r4₁, r5₁, r1₁, r0₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Pack.Hint.HPInv s₀ sA) (N := VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (by omega) (fun i hi s h => VG.Proof.MlDsa.Arm.Pack.Hint.poly_ok hp hA hi h)
    (fun s hP => ⟨hP.y.trans (hintBitPack_eq _ _ _).symm, hP.frame, hP.rd, hP.wr, hP.sp⟩)
    ⟨by rw [r0₁, h0]; simp, by rw [r1₁]; rfl, by rw [r3₁, h3], by rw [r4₁, h1, Nat.one_mul, Nat.sub_zero],
      by rw [r5₁, h3, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq], rd₁, wr₁, sp₁,
      by rw [m₁]; exact Frame.refl _ _, ?_⟩
  rw [m₁, hz]
  show _ = (Array.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀ + VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]

/-! ## The function -/

theorem ldr5_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4) :
    WP isa (.block [.ldrSp .r5 4]) s fun s' =>
      s' = s.setReg .r5 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32) := by
  run_block [ia]

theorem frameR2 {s : State} (h : 8 ≤ s.sp.toNat) :
    VG.Proof.MlDsa.Arm.Pack.Hint.frameR s [.r4, .r5] = ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.frameR_eq [.r4, .r5] h

/-- The state the body runs from. -/
abbrev P1 (s₀ : State) : State := pushed [.r4, .r5] (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀))

/-- The state after zeroing `y`. -/
def ZP (s₀ a : State) : Prop :=
  a.gpr .r0 = VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀ ∧ a.gpr .r1 = BitVec.ofNat 32 (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) ∧ a.gpr .r2 = VG.Proof.MlDsa.Arm.Pack.Hint.pW s₀ ∧ a.gpr .r3 = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀ ∧
    bytesAt a.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = List.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) 0 ∧ Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).mem a.mem ∧
    a.rd = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).rd ∧ a.wr = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).wr ∧ a.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).sp

section
variable {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀)
include hp

theorem hsp8 : 4 * [Reg.r4, Reg.r5].length ≤ (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)).sp.toNat := hp.sp

theorem hfr : VG.Proof.MlDsa.Arm.Pack.Hint.frameR (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) [.r4, .r5] = ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩ :=
  VG.Proof.MlDsa.Arm.Pack.Hint.frameR2 (s := s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) hp.sp

theorem zeroP_ok : WP isa hbpZero (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₀) :=
  VG.Proof.MlDsa.Arm.Pack.Hint.zero_ok hp rfl rfl rfl rfl (by simp [RegUpd.wr_setReg, hp.wr])

/-- The body changes memory only in the frame and `y`. -/
theorem zp_frame {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₀ a) :
    Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩, VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] s₀.mem a.mem := by
  have hpf := VG.Proof.MlDsa.Arm.Pack.Hint.pushed_frame [.r4, .r5] (VG.Proof.MlDsa.Arm.Pack.Hint.hsp8 hp)
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hfr hp] at hpf
  exact (hpf.mono (by simp)).trans (hz.2.2.2.2.2.1.mono (by simp))

theorem zp_hint {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₀ a) :
    ∀ t < 256 * VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀, coeffAt a.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) t = coeffAt s₀.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₀)) t := by
  intro t ht
  have fH := hp.fitH
  have hl := hp.hlen
  rw [coeffAt_eq, coeffAt_eq]
  exact (VG.Proof.MlDsa.Arm.Pack.Hint.zp_frame hp hz).readW (r := VG.Proof.MlDsa.Arm.Pack.Hint.hR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.b_h.symm
    · exact hp.d_hy) (by decide)

theorem mainPre_of {a : State} (hz : VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₀ a) {rd wr : List Region} (hr : VG.Proof.MlDsa.Arm.Pack.Hint.hR s₀ ∈ rd) (hw : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀ ∈ wr) :
    VG.Proof.MlDsa.Arm.Pack.Hint.MainPre s₀ (a.withRegions rd wr) := ⟨hr, hw, VG.Proof.MlDsa.Arm.Pack.Hint.zp_hint hp (a := a) hz⟩

end

/-- The body of the frame: `y`, the reload of `r5`, and the word the pop reloads into `r4`. -/
theorem body_ok {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀) :
    WP isa hintBitPackBody (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀) fun s₂ => s₂.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).sp ∧ s₂.gpr .r5 = s₀.gpr .r5 ∧
      s₂.mem.readW (State.addr s₂.sp) 32 = s₀.gpr .r4 ∧
      bytesAt s₂.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = Spec.MlDsa.hintBitPack (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) := by
  have hsp8 := VG.Proof.MlDsa.Arm.Pack.Hint.hsp8 hp
  unfold hintBitPackBody
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.zeroP_ok hp) fun sa hz => ?_)
  obtain ⟨a0, a1, a2, a3, az, af, ard, awr, asp⟩ := id hz
  have hA : VG.Proof.MlDsa.Arm.Pack.Hint.MainPre s₀ sa := by
    have := VG.Proof.MlDsa.Arm.Pack.Hint.mainPre_of hp hz (rd := sa.rd) (wr := sa.wr)
      (by rw [ard]; simp [RegUpd.rd_setReg, hp.rd]) (by rw [awr]; simp [RegUpd.wr_setReg, hp.wr])
    rwa [State.withRegions_self] at this
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.main_ok hp hA a0 a1 a2 a3 az) fun sb ⟨by', bf, brd, bwr, bsp⟩ => ?_)
  have hfb : Frame [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀] (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).mem sb.mem := af.trans bf
  have hdy : ∀ r ∈ [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₀], (VG.Proof.MlDsa.Arm.Pack.Hint.frameR (s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) [.r4, .r5]).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [VG.Proof.MlDsa.Arm.Pack.Hint.hfr hp]; exact hp.b_y
  have hsb : sb.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).sp := by rw [bsp, asp]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.ldr5_ok (by
      rw [bwr, awr, pushed_wr, hsb]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
        VG.Proof.MlDsa.Arm.Pack.Hint.frameR_contains [.r4, .r5] (s := s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) hsp8 (i := 1) (by decide)⟩))
    fun s₂ e₂ => ?_
  subst e₂
  refine ⟨hsb, ?_, ?_, by' ⟩
  · simp only [RegUpd.gpr_setReg_self]
    rw [hsb, VG.Proof.MlDsa.Arm.Pack.Hint.frame_saved [.r4, .r5] (s := s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) hsp8 hfb hdy (i := 1) (by decide)]
    rfl
  · simp only [RegUpd.mem_setReg, RegUpd.sp_setReg]
    rw [hsb, show State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).sp = State.addr ((VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₀).sp + BitVec.ofNat 32 (4 * 0)) by simp,
      VG.Proof.MlDsa.Arm.Pack.Hint.frame_saved [.r4, .r5] (s := s₀.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₀)) hsp8 hfb hdy (i := 0) (by decide)]
    rfl

/-- The whole function: `y`, and the registers it saves and restores (the
others it never writes). -/
theorem correct {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitPack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧
      s'.gpr .lr = s₀.gpr .lr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₀)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₀) = Spec.MlDsa.hintBitPack (VG.Proof.MlDsa.Arm.Pack.Hint.pω s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pk s₀) (VG.Proof.MlDsa.Arm.Pack.Hint.pHint s₀) := by
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.argR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.frame (rs := [.r4, .r5]) (r := .r4) rfl (VG.Proof.MlDsa.Arm.Pack.Hint.hsp8 hp) (by decide)
    (WP.mono (WP.gpr (VG.Proof.MlDsa.Arm.Pack.Hint.body_ok hp) (r := .lr) (VG.Proof.MlDsa.Arm.Pack.Hint.noWrite (by decide +kernel))) fun s₂ ⟨⟨hsp, h5, h4, hy⟩, hlr⟩ => ?_)
  refine ⟨?_, by rw [popped_gpr (by decide), h5], by rw [popped_gpr (by decide), hlr]; rfl, ?_, hy⟩
  · simp only [popped, State.setReg, ite_true]; exact h4
  · simp only [popped_sp, hsp, VG.Proof.MlDsa.Arm.Pack.Hint.P1, pushed_sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the lengths,
`ω`, the stack pointer and the hint, which the contract lets the function
leak) leak the same trace (`RelCT`), phase by phase: the load of `len` and the
frame's reload of `r5` access only the stack (`RelCT.spBlock`); zeroing `y` is
proved by the taint analysis; the loops by `memTaint`, from the states
narrowed to the hint and `y` (`RelCT.narrow`), on which both runs agree once
`y` is zeroed. What each run is at each point comes from the correctness proof
(`RelCT.wp`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

theorem pre_of {s : State} (h : (hintBitPackContract Arm.abi 8).pre s) : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₁
  hp₂ : VG.Proof.MlDsa.Arm.Pack.Hint.PPre s₂
  sp : s₁.sp = s₂.sp
  leak : (List.range (s₁.gpr .r1).toNat).map (fun i => (coeffAt s₁.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₁)) i).toNat) =
    (List.range (s₂.gpr .r1).toNat).map (fun i => (coeffAt s₂.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₂)) i).toNat)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  arg : stackArg s₁ 0 = stackArg s₂ 0

section
variable {s₁ s₂ : State} (h : VG.Proof.MlDsa.Arm.Pack.Hint.Two s₁ s₂)
include h

theorem hR_eq : VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁ = VG.Proof.MlDsa.Arm.Pack.Hint.hR s₂ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.hR, VG.Proof.MlDsa.Arm.Pack.Hint.pH, h.r0, h.r1]

theorem yR_eq : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁ = VG.Proof.MlDsa.Arm.Pack.Hint.yR s₂ := by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.yR, VG.Proof.MlDsa.Arm.Pack.Hint.pY, VG.Proof.MlDsa.Arm.Pack.Hint.pLen, VG.Proof.MlDsa.Arm.Pack.Hint.pL, h.r3, h.arg]

/-- The hint and the zeroed `y`: the memory both runs agree on. -/
theorem memEq {a b : State} (ha : VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₁ a) (hb : VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₂ b) : Hint.MemEq ([VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁] ++ [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁]) a.mem b.mem := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.pfacts hp₁
  intro x ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · -- The hint: as on entry.
    have e₁ := VG.Proof.MlDsa.Arm.Pack.Hint.zp_frame hp₁ ha x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₁.b_h x hc' hc
      · exact hp₁.d_hy x hc hc')
    rw [VG.Proof.MlDsa.Arm.Pack.Hint.hR_eq h] at hc
    have e₂ := VG.Proof.MlDsa.Arm.Pack.Hint.zp_frame hp₂ hb x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₂.b_h x hc' hc
      · exact hp₂.d_hy x hc hc')
    rw [e₁, e₂]
    rw [← VG.Proof.MlDsa.Arm.Pack.Hint.hR_eq h] at hc
    have hl := h.leak
    rw [show State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₂) = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pH s₁) by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.pH, h.r0], ← h.r1] at hl
    exact VG.Proof.MlDsa.Arm.Pack.Hint.bytes_of_words hl hc
  · -- `y`: zeros.
    have hlt : (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat < VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₁ := by simp only [Region.Contains] at hc; omega
    have ea : x = State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁) + BitVec.ofNat 64 (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have e₁ : (bytesAt a.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₁)).getD (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat 0 =
        (List.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₁) (0 : Byte)).getD (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat 0 := by rw [ha.2.2.2.2.1]
    have e₂ : (bytesAt b.mem (State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₂)) (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₂)).getD (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat 0 =
        (List.replicate (VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₂) (0 : Byte)).getD (x - State.addr (VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁)).toNat 0 := by rw [hb.2.2.2.2.1]
    rw [bytesAt_getD _ _ hlt, ← ea] at e₁
    rw [show VG.Proof.MlDsa.Arm.Pack.Hint.pY s₂ = VG.Proof.MlDsa.Arm.Pack.Hint.pY s₁ by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.pY, h.r3], show VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₂ = VG.Proof.MlDsa.Arm.Pack.Hint.pLen s₁ by simp only [VG.Proof.MlDsa.Arm.Pack.Hint.pLen, VG.Proof.MlDsa.Arm.Pack.Hint.pL, h.arg],
      bytesAt_getD _ _ hlt, ← ea] at e₂
    rw [e₁, e₂]

/-- The loops, from the states narrowed to the hint and `y`. -/
theorem main_ct : RelCT isa (fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₂ b) hbpMain fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁]) (fun _ => [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁]) (fun a b ⟨ha, hb⟩ => ?_) (fun a b ⟨ha, hb⟩ => ?_) ?_
  · have hra : VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁ ∈ a.rd := by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd]
    have hwa : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁ ∈ a.wr := by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr]
    have hrb : VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁ ∈ b.rd := by rw [hb.2.2.2.2.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.hR_eq h]; simp [RegUpd.rd_setReg, hp₂.rd]
    have hwb : VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁ ∈ b.wr := by rw [hb.2.2.2.2.2.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.yR_eq h]; simp [RegUpd.wr_setReg, hp₂.wr]
    exact ⟨Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hra
        · exact List.mem_append_right _ hwa,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwa,
      Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hrb
        · exact List.mem_append_right _ hwb,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwb⟩
  · obtain ⟨a0, a1, a2, a3, az, -⟩ := id ha
    obtain ⟨b0, b1, b2, b3, bz, -⟩ := id hb
    obtain ⟨t₁, u₁, e₁, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.main_ok hp₁ (VG.Proof.MlDsa.Arm.Pack.Hint.mainPre_of hp₁ ha (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁]) (wr := [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁])
      (List.mem_singleton_self _) (List.mem_singleton_self _)) a0 a1 a2 a3 az
    obtain ⟨t₂, u₂, e₂, -⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.main_ok hp₂ (VG.Proof.MlDsa.Arm.Pack.Hint.mainPre_of hp₂ hb (rd := [VG.Proof.MlDsa.Arm.Pack.Hint.hR s₁]) (wr := [VG.Proof.MlDsa.Arm.Pack.Hint.yR s₁])
      (by rw [VG.Proof.MlDsa.Arm.Pack.Hint.hR_eq h]; exact List.mem_singleton_self _) (by rw [VG.Proof.MlDsa.Arm.Pack.Hint.yR_eq h]; exact List.mem_singleton_self _))
      b0 b1 b2 b3 bz
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by taint_decide)
    subst ea eb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, VG.Proof.MlDsa.Arm.Pack.Hint.memEq h (a := a) (b := b) ha hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [State.withRegions_gpr, ha.1, hb.1, VG.Proof.MlDsa.Arm.Pack.Hint.pH, h.r0]
    · simp only [State.withRegions_gpr, ha.2.1, hb.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.pk, VG.Proof.MlDsa.Arm.Pack.Hint.pLen, VG.Proof.MlDsa.Arm.Pack.Hint.pL, VG.Proof.MlDsa.Arm.Pack.Hint.pω, VG.Proof.MlDsa.Arm.Pack.Hint.pW, h.r2, h.arg]
    · simp only [State.withRegions_gpr, ha.2.2.1, hb.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.pW, h.r2]
    · simp only [State.withRegions_gpr, ha.2.2.2.1, hb.2.2.2.1, VG.Proof.MlDsa.Arm.Pack.Hint.pY, h.r3]

/-- The body of the frame. -/
theorem body_ct : RelCT isa (fun a b => a = VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₁ ∧ b = VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₂) hintBitPackBody fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold hintBitPackBody
  refine RelCT.seq (R := fun a b => VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₁ a ∧ VG.Proof.MlDsa.Arm.Pack.Hint.ZP s₂ b) (VG.Proof.MlDsa.Arm.Pack.Hint.relct_wp ?_ fun a b ⟨ea, eb⟩ =>
    ⟨by rw [ea]; exact VG.Proof.MlDsa.Arm.Pack.Hint.zeroP_ok hp₁, by rw [eb]; exact VG.Proof.MlDsa.Arm.Pack.Hint.zeroP_ok hp₂⟩) ?_
  · refine RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r2, .r3, .r12])
      (fun a b ⟨ea, eb⟩ => Taint.agree_ofRegs fun r hr => ?_) (by taint_decide)
    subst ea eb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.P1, pushed_gpr, RegUpd.gpr_setReg, h.r2]; rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.P1, pushed_gpr, RegUpd.gpr_setReg, h.r3]; rfl
    · simp only [VG.Proof.MlDsa.Arm.Pack.Hint.P1, pushed_gpr, RegUpd.gpr_setReg, VG.Proof.MlDsa.Arm.Pack.Hint.pL, h.arg]; rfl
  refine RelCT.seq (R := fun (a b : State) => a.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₁).sp ∧ b.sp = (VG.Proof.MlDsa.Arm.Pack.Hint.P1 s₂).sp)
    (VG.Proof.MlDsa.Arm.Pack.Hint.relct_wp (VG.Proof.MlDsa.Arm.Pack.Hint.main_ct h) fun a b hab => ⟨?_, ?_⟩) ?_
  · have ha := hab.1
    obtain ⟨a0, a1, a2, a3, az, -, -, -, asp⟩ := id ha
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.main_ok hp₁ ?_ a0 a1 a2 a3 az) fun s' hs => hs.2.2.2.2.trans asp
    have := VG.Proof.MlDsa.Arm.Pack.Hint.mainPre_of hp₁ ha (rd := a.rd) (wr := a.wr) (by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd])
      (by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr])
    rwa [State.withRegions_self] at this
  · have hb := hab.2
    obtain ⟨b0, b1, b2, b3, bz, -, -, -, bsp⟩ := id hb
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.Hint.main_ok hp₂ ?_ b0 b1 b2 b3 bz) fun s' hs => hs.2.2.2.2.trans bsp
    have := VG.Proof.MlDsa.Arm.Pack.Hint.mainPre_of hp₂ hb (rd := b.rd) (wr := b.wr) (by rw [hb.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₂.rd])
      (by rw [hb.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₂.wr])
    rwa [State.withRegions_self] at this
  · exact Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by
      rw [ea, eb]; simp only [VG.Proof.MlDsa.Arm.Pack.Hint.P1, pushed_sp, RegUpd.sp_setReg, h.sp]

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) Impl.MlDsa.Arm.Pack.hintBitPack fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine RelCT.seq (R := fun a b => a = s₁.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₁) ∧ b = s₂.setReg .r12 (VG.Proof.MlDsa.Arm.Pack.Hint.pL s₂))
    (VG.Proof.MlDsa.Arm.Pack.Hint.relct_wp (Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by rw [ea, eb, h.sp]) fun a b ⟨ea, eb⟩ =>
      ⟨by rw [ea]; exact VG.Proof.MlDsa.Arm.Pack.Hint.entry_ok (by rw [hp₁.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.argR s₁, by simp, Region.contains_self _ _⟩),
       by rw [eb]; exact VG.Proof.MlDsa.Arm.Pack.Hint.entry_ok (by rw [hp₂.rd]; exact ⟨VG.Proof.MlDsa.Arm.Pack.Hint.argR s₂, by simp, Region.contains_self _ _⟩)⟩) ?_
  refine RelCT.frame (fun a b ⟨ea, eb⟩ => by rw [ea, eb]; simp only [RegUpd.sp_setReg, h.sp]) ?_
  refine RelCT.mono (VG.Proof.MlDsa.Arm.Pack.Hint.body_ct h) (fun a b ⟨x, y, ⟨ex, ey⟩, px, py⟩ => ?_) fun _ _ h => h
  subst ex ey
  exact ⟨(push_pushed' px).1, (push_pushed' py).1⟩

end

/-! ## Verified -/

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := by
  simp [coeffAt, Mem.readW, Mem.read]

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, VG.Proof.MlDsa.Arm.Pack.Hint.sum_zero l]

theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, VG.Proof.MlDsa.Arm.Pack.Hint.coeffAt_zero, Function.comp_def, VG.Proof.MlDsa.Arm.Pack.Hint.filter_false, VG.Proof.MlDsa.Arm.Pack.Hint.sum_zero]

theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ t < 256 * k, coeffAt m p t = coeffAt m' p t) : hintAt m p k = hintAt m' p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  congr 1; funext j
  have hj : j.val < 256 := j.isLt
  rw [h _ (by omega)]

/-- The memory of the satisfying state: `len = 84` on the stack. -/
def satMem : Mem := fun a => if a = 0x8000 then 84 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1024 | .r2 => 80 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.MlDsa.Arm.Pack.Hint.satMem
  rd := [⟨0x1000, 4096⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 84⟩]

theorem satArg : stackArg VG.Proof.MlDsa.Arm.Pack.Hint.satState 0 = 84 := by decide +kernel

theorem satHint : hintOnes (hintAt VG.Proof.MlDsa.Arm.Pack.Hint.satMem 0x1000 4) = 0 := by
  rw [VG.Proof.MlDsa.Arm.Pack.Hint.hintAt_congr (m' := fun _ => 0) fun t ht => ?_, VG.Proof.MlDsa.Arm.Pack.Hint.hintOnes_zero]
  rw [coeffAt_eq, coeffAt_eq]
  refine Mem.readW_congr fun b hb => ?_
  simp only [VG.Proof.MlDsa.Arm.Pack.Hint.satMem]
  rw [ite_neg' fun e => by bv_omega]

theorem hintBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.hintBitPack (hintBitPackContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := VG.Proof.MlDsa.Arm.Pack.Hint.pre_of hs
    obtain ⟨t, s', he, h4, h5, hlr, hsp, hy⟩ := VG.Proof.MlDsa.Arm.Pack.Hint.correct hp
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h4
      · exact h5
      rotate_right
      · exact hlr
      all_goals exact Exec.gpr (VG.Proof.MlDsa.Arm.Pack.Hint.noWrite (by decide +kernel)) he
    · sig_post [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      exact hy
  · have hp₁ := VG.Proof.MlDsa.Arm.Pack.Hint.pre_of h₁
    have hp₂ := VG.Proof.MlDsa.Arm.Pack.Hint.pre_of h₂
    sig_pub [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, ha⟩ := hpub
    exact (VG.Proof.MlDsa.Arm.Pack.Hint.all_ct ⟨hp₁, hp₂, hsp, hl, h0, h1, h2, h3, ha⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlDsa.Arm.Pack.Hint.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      rotate_right
      · rw [VG.Proof.MlDsa.Arm.Pack.Hint.satArg, show (BitVec.setWidth 32 (BitVec.setWidth 64 (84 : BitVec 32))).toNat -
          (BitVec.setWidth 32 (BitVec.setWidth 64 (80 : BitVec 32))).toNat = 4 by decide,
          show BitVec.setWidth 64 (4096 : BitVec 32) = 0x1000 by decide, VG.Proof.MlDsa.Arm.Pack.Hint.satHint]
        exact Nat.zero_le _
      all_goals decide +kernel

end VG.Proof.MlDsa.Arm.Pack.Hint

end
