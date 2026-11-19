module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Sym
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym
public import VerifiedGarbage.Proof.ChaCha20.Keystream

/-! ### `ChaCha20.X86_64.Avx512.Setup`, which this module and modules that import it used -/

section

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen input states
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt)
open VG.Proof.ChaCha20

/-- The counter increments `0, …, 15`, as doublewords at `buf + 128`. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ j < 16, m.readW (buf + BitVec.ofNat 64 (4 * (32 + j))) 32 = BitVec.ofNat 32 j

/-- Word `k` of block `p` after the setup: word `k` of the state, plus `p`
for the counter. -/
def setupT (k p : Nat) : T := if k = 12 then .add (.mem 0 12) (.mem 1 (32 + p)) else .mem 0 k

def setupCheck (to : Bool) : Bool :=
  match Sym.init.runT to setup with
  | some σ => !σ.dirty && (List.range 16).all fun k => (List.range 16).all fun p => σ.reg k p == setupT k p
  | none => false

theorem setupCheck_in : setupCheck false = true := by decide +kernel
theorem setupCheck_to : setupCheck true = true := by decide +kernel

theorem setup_run (to : Bool) : ∃ σ, Sym.init.runT to setup = some σ ∧ σ.dirty = false ∧
    ∀ k < 16, ∀ p < 16, σ.reg k p = setupT k p := by
  have e : setupCheck to = true := by cases to; exacts [setupCheck_in, setupCheck_to]
  unfold setupCheck at e
  split at e
  · rename_i σ h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e.1, e.2⟩
  · cases e

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = (stateAt m p)[k] := by
  simp [stateAt]

/-- In place or from a source to a destination (`to`). -/
theorem setup_ok {to : Bool} {s : State} (hc : CtxT to s) (hi : Incs s.mem (s.gpr .rcx)) :
    WP isa (.block setup) s fun s' =>
      ZH (fun j => ctr (stateAt s.mem (s.gpr .rdi)) j) s' ∧ s'.mem = s.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hd, hk⟩ := setup_run to
  refine WP.mono (srunT_ok hc setup (SRelT.init to s) hr) fun s' h => ⟨fun r j hj => ?_,
    h.clean hd, h.gpr, h.rd, h.wr⟩
  rw [h.reg r j hj, hk _ (xidx_lt r) j hj, Avx2.ctr_get _ _ _ (xidx_lt r)]
  simp only [setupT]
  split
  · simp only [T.eval, memBase_0, memBase_1]
    rw [stateAt_get _ _ (by decide), hi j hj]
  · simp only [T.eval, memBase_0]
    exact stateAt_get _ _ (xidx_lt r)

end VG.Proof.ChaCha20.X86_64.Avx512

end

end

/-! ### `ChaCha20.X86_64.Avx512.Finish`, which this module and modules that import it used -/

section

/-!
# ChaCha20 on x86-64 with AVX-512: the sixteen blocks, from the source into the destination
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (plus)

/-- Word `w` of block `j` of the output: the rounds' result (in `zmm w`) plus
the input state, with the counter increment `j` for word 12. -/
def outT (w j : Nat) : T :=
  if w = 12 then .add (.add (.reg 12 j) (.mem 0 12)) (.mem 1 (32 + j)) else .add (.reg w j) (.mem 0 w)

def finishCheck : Bool :=
  match Sym.init.runT true finish with
  | some σ => (List.range 256).all fun i => σ.mem 3 i == .xor (.mem 2 i) (outT (i % 16) (i / 16))
  | none => false

theorem finishCheck_eq : finishCheck = true := by decide +kernel

theorem finish_run : ∃ σ, Sym.init.runT true finish = some σ ∧
    ∀ i < 256, σ.mem 3 i = .xor (.mem 2 i) (outT (i % 16) (i / 16)) := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ h
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, h, e⟩
  · cases e

/-- A byte, from the doubleword holding it. -/
theorem byte_dword (m : Mem) (a : Addr) (k : Nat) :
    m (a + BitVec.ofNat 64 k) = (m.readW (a + BitVec.ofNat 64 (4 * (k / 4))) 32).extractLsb' (8 * (k % 4)) 8 := by
  rw [byte_readW m _ (w := 32) (k := k % 4) (by omega_using []), add_ofNat']
  congr 3; omega_using []

theorem outT_eval {s : State} {vs : Nat → CState} (hz : ZH vs s) (hi : Incs s.mem (s.gpr .rcx)) {w j : Nat}
    (hw : w < 16) (hj : j < 16) :
    (outT w j).eval s = (plus vs (stateAt s.mem (s.gpr .rdi)) j)[w] := by
  have r := hz (zreg w) j hj
  simp only [xidx_zreg w hw] at r
  simp only [plus, Vector.getElem_zipWith, Avx2.ctr_get _ _ _ hw, outT]
  split
  · rename_i e; subst e
    simp only [T.eval, memBase_0, memBase_1, r, stateAt_get _ _ (show 12 < 16 by decide), hi j hj,
      BitVec.add_assoc]
  · simp only [T.eval, memBase_0, r, stateAt_get _ _ hw]

/-- The sixteen blocks, XORed with the 1024 bytes of the source at `rsi`
into the destination at `rsi + r11` (`dstR`). -/
theorem finish_ok {s : State} (hc : CtxT true s) (hi : Incs s.mem (s.gpr .rcx)) {vs : Nat → CState}
    (hz : ZH vs s) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 1024, s'.mem ((dstR 256 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (stateAt s.mem (s.gpr .rdi)) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregsT true s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨σ, hr, hm⟩ := finish_run
  refine WP.mono (srunT_ok hc finish (SRelT.init true s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
    h.rd, h.wr⟩
  have d := h.mem3 rfl (k / 4) (by omega_using [hk])
  rw [hm _ (by omega_using [hk])] at d
  simp only [T.eval, memBase_2] at d
  rw [show k / 4 % 16 = k % 64 / 4 by omega_using [], show k / 4 / 16 = k / 64 by omega_using []] at d
  rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
    serialize_getD _ (Nat.mod_lt _ (by decide)), outT_eval hz hi (by omega_using []) (by omega_using [hk]),
    show k % 64 % 4 = k % 4 by omega_using []]

end VG.Proof.ChaCha20.X86_64.Avx512

end

end

/-! ### `ChaCha20.X86_64.Avx512Tail.Out`, which this module and modules that import it used -/

section

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: the input states and the output

The terms the code around the rounds leaves (`Sym`), compared by the kernel
with the input states and the keystream blocks, and evaluated.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init dstR xidx xidx_lt zw xidx_zreg stateAt_get byte_dword
  add_ofNat')
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus ctr_get)

/-- The first doubleword of the lane increments of set `k` in `buf`. -/
def incB : Nat → Nat
  | 0 => 64 | 1 => 48 | _ => 0

/-- The lane increments in `buf`: `0, 1, 2, 3` for the first set and `4, 5,
6, 7` for the second, each in doubleword 0 of a lane. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ k < 2, ∀ p < 16, m.readW (buf + BitVec.ofNat 64 (4 * (incB k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (4 * k + p / 4) else 0

/-- As `Incs`, with `8, 9, 10, 11` for the third set, as `part3` stores them. -/
def Incs3 (m : Mem) (buf : Addr) : Prop :=
  ∀ k < 3, ∀ p < 16, m.readW (buf + BitVec.ofNat 64 (4 * (incB k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (4 * k + p / 4) else 0

/-- Word `i` of block `l` of set `k` before the rounds: word `i` of the
state, with the lane increment added to row 3. -/
def inT (k i l : Nat) : T :=
  if i / 4 = 3 then .add (.mem 0 i) (.mem 1 (incB k + 4 * l + i % 4)) else .mem 0 i

/-- Word `i` of block `l` of set `k` of the output: the rounds' result plus
the input. -/
def outT (k i l : Nat) : T :=
  .add (.reg (4 * k + i / 4) (4 * l + i % 4)) (inT k i l)

/-- The same, as `finish2` adds row 3 of the input. -/
def outT2 (k i l : Nat) : T :=
  .add (.reg (4 * k + i / 4) (4 * l + i % 4))
    (if i / 4 = 3 then .add (.mem 1 (incB k + 4 * l + i % 4)) (.mem 0 i) else .mem 0 i)

/-! ## The kernel's checks -/

def setupCheck : Bool :=
  match run 0 Sym.init setup with
  | some σ => !σ.dirty && (List.range 4).all fun r => (List.range 16).all fun p =>
      σ.reg r p == inT 0 (4 * r + p % 4) (p / 4)
  | none => false

def setup2Check : Bool :=
  match run 0 Sym.init setup2 with
  | some σ => !σ.dirty && (List.range 2).all fun k => (List.range 4).all fun r => (List.range 16).all fun p =>
      σ.reg (4 * k + r) p == inT k (4 * r + p % 4) (p / 4)
  | none => false

def finishCheck : Bool :=
  match run 0 Sym.init finish with
  | some σ => (List.range 4).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT 0 i l
  | none => false

def fullCheck : Bool :=
  match runT true 128 Sym.init (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256) with
  | some σ =>
    ((List.range 8).all fun j => (List.range 16).all fun i =>
      σ.mem 3 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (outT2 (j / 4) i (j % 4))) &&
    (List.range 80).all fun i => σ.mem 1 i == .mem 1 i
  | none => false

def partCheck : Bool :=
  match runT true 64 Sym.init (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7) with
  | some σ =>
    (List.range 4).all fun l => (List.range 16).all fun i =>
      σ.mem 3 (16 * l + i) == .xor (.mem 2 (16 * l + i)) (outT2 0 i l) &&
      σ.mem 1 (16 * l + i) == outT2 1 i l
  | none => false

def setup3Check : Bool :=
  match run 0 Sym.init setup3 with
  | some σ => !σ.dirty && (List.range 3).all fun k => (List.range 4).all fun r => (List.range 16).all fun p =>
      σ.reg (4 * k + r) p == inT k (4 * r + p % 4) (p / 4)
  | none => false

def part3Check : Bool :=
  match runT true 128 Sym.init finish3 with
  | some σ =>
    ((List.range 8).all fun j => (List.range 16).all fun i =>
      σ.mem 3 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (outT2 (j / 4) i (j % 4))) &&
    (List.range 4).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT2 2 i l
  | none => false

theorem setupCheck_eq : setupCheck = true := by decide +kernel
theorem setup2Check_eq : setup2Check = true := by decide +kernel
theorem finishCheck_eq : finishCheck = true := by decide +kernel
theorem fullCheck_eq : fullCheck = true := by decide +kernel
theorem partCheck_eq : partCheck = true := by decide +kernel
theorem setup3Check_eq : setup3Check = true := by decide +kernel
theorem part3Check_eq : part3Check = true := by decide +kernel


/-! ## Evaluation -/

section
variable {D : Nat} {s : State}

/-- The state at `rdi`. -/
abbrev S0 (s : State) : CState := stateAt s.mem (s.gpr .rdi)

theorem inT_eval (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (inT k i l) = (ctr (S0 s) (4 * k + l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega_arith)
  rw [show incB k + (4 * l + i % 4) = incB k + 4 * l + i % 4 by omega_arith,
    show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith] at e
  split
  · rename_i h3
    simp only [T.eval, memBase_0, memBase_1, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega_arith), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, memBase_0, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega_arith)]

theorem reg_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) {k i l : Nat} (hk : k < S) (hi : i < 16)
    (hl : l < 4) : T.eval D s (.reg (4 * k + i / 4) (4 * l + i % 4)) = (vs (4 * k + l))[i] := by
  simp only [T.eval, zw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith]
  exact hz k hk l hl i hi

theorem outT_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (outT k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
  simp only [outT, plus, Vector.getElem_zipWith]
  rw [← inT_eval (D := D) hi hk2 hi16 hl, ← reg_eval hz hk hi16 hl]
  rfl

theorem outT2_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (outT2 k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
  rw [← outT_eval (D := D) hz hi hk hk2 hi16 hl]
  simp only [outT2, outT, inT]
  split
  · simp only [T.eval]; exact congrArg _ (BitVec.add_comm _ _)
  · rfl

theorem inT_eval3 (hi : Incs3 s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 3) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (inT k i l) = (ctr (S0 s) (4 * k + l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega_arith)
  rw [show incB k + (4 * l + i % 4) = incB k + 4 * l + i % 4 by omega_arith,
    show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith] at e
  split
  · rename_i h3
    simp only [T.eval, memBase_0, memBase_1, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega_arith), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, memBase_0, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega_arith)]

theorem outT2_eval3 {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs3 s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk3 : k < 3) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (outT2 k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
  have e : T.eval D s (outT k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
    simp only [outT, plus, Vector.getElem_zipWith]
    rw [← inT_eval3 (D := D) hi hk3 hi16 hl, ← reg_eval hz hk hi16 hl]
    rfl
  rw [← e]
  simp only [outT2, outT, inT]
  split
  · simp only [T.eval]; exact congrArg _ (BitVec.add_comm _ _)
  · rfl

end

/-! ## The instructions -/

theorem setup_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup) s fun s' =>
      HB 1 (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setupCheck_eq
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega_arith
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega_arith)
    rw [xidx_zreg _ (by omega_arith), e.2 _ (by omega_arith) _ (by omega_arith)] at r
    simp only [zw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega_arith] at r
    rw [r, inT_eval hi (by decide) hi16 hl]
  · cases e

theorem setup2_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup2) s fun s' =>
      HB 2 (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setup2Check_eq
  unfold setup2Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup2 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega_arith)
    rw [xidx_zreg _ (by omega_arith), e.2 k hk _ (by omega_arith) _ (by omega_arith)] at r
    simp only [zw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith,
      show 4 * (i / 4) + i % 4 = i by omega_arith] at r
    rw [r, inT_eval hi hk hi16 hl]
  · cases e

/-- A byte of the output, from its doubleword. -/
theorem byte_out {m : Mem} {a : Addr} {f : Nat → CState} {k : Nat}
    (h : m.readW (a + BitVec.ofNat 64 (4 * (k / 4))) 32 = (f (k / 64))[k % 64 / 4]'(by omega_arith)) :
    m (a + BitVec.ofNat 64 k) = (serialize (f (k / 64))).getD (k % 64) 0 := by
  rw [byte_dword m a k, h, serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]

theorem finish_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 1 vs s) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc finish (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e _ (by omega_arith) _ (by omega_arith),
      outT_eval hz hi (by decide) (by decide) (by omega_arith) (by omega_arith)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith, Nat.mul_zero, Nat.zero_add] at d
    exact d
  · cases e

/-- Eight blocks, XORed with the 512 bytes of the source at `rsi` into the
destination at `rsi + r11` (`dstR`). -/
theorem full_ok {s : State} (hc : CtxT true 128 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256)) s
      fun s' =>
      (∀ k < 512, s'.mem ((dstR 128 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ i < 80, s'.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) 32 =
        s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) 32) ∧
      Frame (wregsT true 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := fullCheck_eq
  unfold fullCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srunT_ok hc _ (SRelT.init true 128 s) hr) fun s' h => ⟨fun k hk => ?_, fun i hi' => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem3 rfl (k / 4) (by omega_arith)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e.1 _ (by omega_arith) _ (by omega_arith)] at d
      simp only [T.eval, memBase_2] at d
      rw [outT2_eval hz hi (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        show 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 by omega_arith,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · have d := h.mem 1 i (by decide) (by simp only [bsize]; omega_arith) (fun _ e => nomatch e)
      rw [e.2 i hi'] at d
      simpa only [T.eval, memBase_1, regn, baseR] using d
  · cases e

/-- Eight blocks: the first four XORed with the 256 bytes of the source at
`rsi` into the destination at `rsi + r11` (`dstR`), the others into `buf`. -/
theorem part_ok {s : State} (hc : CtxT true 64 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7)) s
      fun s' =>
      (∀ k < 256, s'.mem ((dstR 64 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (4 + k / 64))).getD (k % 64) 0) ∧
      Frame (wregsT true 64 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := partCheck_eq
  unfold partCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srunT_ok hc _ (SRelT.init true 64 s) hr) fun s' h => ⟨fun k hk => ?_, fun k hk => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem3 rfl (k / 4) (by omega_arith)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, (e _ (by omega_arith) _ (by omega_arith)).1] at d
      simp only [T.eval, memBase_2] at d
      rw [outT2_eval hz hi (by decide) (by decide) (by omega_arith) (by omega_arith), Nat.mul_zero, Nat.zero_add,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith) (fun _ e => nomatch e)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, (e _ (by omega_arith) _ (by omega_arith)).2,
        outT2_eval hz hi (by decide) (by decide) (by omega_arith) (by omega_arith)] at d
      simp only [regn, baseR] at d
      rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith, Nat.mul_one] at d
      rw [byte_dword s'.mem, d, serialize_getD _ (Nat.mod_lt _ (by decide)),
        show k % 64 % 4 = k % 4 by omega_arith]
  · cases e

theorem setup3_ok {s : State} (hc : Ctx 0 s) (hi : Incs3 s.mem (s.gpr .r9)) :
    WP isa (.block setup3) s fun s' =>
      HB 3 (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setup3Check_eq
  unfold setup3Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup3 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega_arith)
    rw [xidx_zreg _ (by omega_arith), e.2 k hk _ (by omega_arith) _ (by omega_arith)] at r
    simp only [zw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith,
      show 4 * (i / 4) + i % 4 = i by omega_arith] at r
    rw [r, inT_eval3 hi hk hi16 hl]
  · cases e

/-- Twelve blocks: the first eight XORed with the 512 bytes of the source at
`rsi` into the destination at `rsi + r11` (`dstR`), the others into `buf`. -/
theorem part3_ok {s : State} (hc : CtxT true 128 s) (hi : Incs3 s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 3 vs s) :
    WP isa (.block finish3) s fun s' =>
      (∀ k < 512, s'.mem ((dstR 128 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (8 + k / 64))).getD (k % 64) 0) ∧
      Frame (wregsT true 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := part3Check_eq
  unfold part3Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srunT_ok hc _ (SRelT.init true 128 s) hr) fun s' h => ⟨fun k hk => ?_, fun k hk => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem3 rfl (k / 4) (by omega_arith)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e.1 _ (by omega_arith) _ (by omega_arith)] at d
      simp only [T.eval, memBase_2] at d
      rw [outT2_eval3 hz hi (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        show 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 by omega_arith,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith) (fun _ e => nomatch e)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e.2 _ (by omega_arith) _ (by omega_arith),
        outT2_eval3 hz hi (by decide) (by decide) (by omega_arith) (by omega_arith)] at d
      simp only [regn, baseR] at d
      rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
      rw [byte_dword s'.mem, d, serialize_getD _ (Nat.mod_lt _ (by decide)),
        show k % 64 % 4 = k % 4 by omega_arith]
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx512Tail

end

end

/-! ### `ChaCha20.X86_64.Avx2Tail.Sym`, which this module and modules that import it used -/

section

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: straight-line code

The symbolic evaluation of `Avx512Tail/Sym.lean`, for `ymm` registers (eight
doublewords, `p` in lane `p / 4`), on the same regions (`Avx512Tail.regn`):
the state (at `rdi`), `buf` (at `r9`, of which the first 256 bytes are
written) and `4 D` bytes of data (at `rsi`); from a source to a destination
(`to`), the data is the source, and the destination, at `rsi + r11`, a
fourth region (`stepT`, `SRelT`), as there.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word)
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init Sym.setReg sel2 sel2_eq sel2_lt add_ofNat' ofInt_ofNat
  xidx xidx_lt xidx_inj zreg_xidx dstR slotD slotD_ok symStore clean3 clean_of Ctx3)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (baseR bsize wsize regn wregs slot slot_ok wsize_le Ctx
  bsize_le regn_contains in_regn in_regn' memBase memBase_0 memBase_1 memBase_2 memBase_3 memBase_lt CtxT wregsT
  src_after dst_contains)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)

/-- Doubleword `p % 4` of lane `p / 4` of `r`. -/
abbrev yw (s : State) (r : XReg) (p : Nat) : Word := dword (s.lane r (p / 4)) (p % 4)

def T.eval (D : Nat) (s₀ : State) : T → Word
  | .reg r p => yw s₀ (zreg r) p
  | .mem b i => s₀.mem.readW (memBase D s₀ b + BitVec.ofNat 64 (4 * i)) 32
  | .add a b => T.eval D s₀ a + T.eval D s₀ b
  | .xor a b => T.eval D s₀ a ^^^ T.eval D s₀ b
  | .inp _ => 0

/-- Lane `j` of `vperm2i128 a, b, n`, without zeroing: lane `k % 2` of `a`
or of `b`, `k` the two bits of `n` for `j`. -/
def permT (A B : Nat → T) (n : BitVec 8) (p : Nat) : T :=
  let k := (n.extractLsb' (4 * (p / 4)) 2).toNat
  (if k < 2 then A else B) (4 * (k % 2) + p % 4)

def stepT (to : Bool) (D : Nat) (σ : Sym) : Instr → Option Sym
  | .vop (.vbin op .l256 d a b) =>
    if op = .vpaddd then some (σ.setReg (xidx d) fun p => .add (σ.reg (xidx a) p) (σ.reg (xidx b) p))
    else if op = .vpxor then some (σ.setReg (xidx d) fun p => .xor (σ.reg (xidx a) p) (σ.reg (xidx b) p))
    else if op = .vpor ∧ a = b then some (σ.setReg (xidx d) (σ.reg (xidx a)))
    else none
  | .vop (.vperm2i128 d a b n) =>
    if n.getLsbD 3 = false ∧ n.getLsbD 7 = false then
      some (σ.setReg (xidx d) (permT (σ.reg (xidx a)) (σ.reg (xidx b)) n))
    else none
  | .vmovdquLoad .l256 d m => (slot m 8 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 8 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p))
  | .vbroadcasti128 d m => (slot m 4 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 4 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p % 4))
  | .vmovdquStore .l256 m r =>
    if to then
      match slotD m 8 D with
      | some i => some (symStore σ 3 i 8 (xidx r))
      | none => (slot m 8 (wsize 0)).map fun (b, i) => symStore σ b i 8 (xidx r)
    else (slot m 8 (wsize D)).map fun (b, i) => symStore σ b i 8 (xidx r)
  | _ => none

def runT (to : Bool) (D : Nat) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (stepT to D σ i).bind fun σ' => runT to D σ' is

/-- In place. -/
abbrev step (D : Nat) := stepT false D
abbrev run (D : Nat) := runT false D

/-! ## The machine agrees -/

/-- The terms `σ` hold in `s`: in the registers, and in regions 0 to 2 (from
a source to a destination, in the source where its destination is as on
entry) and the destination. -/
structure SRelT (to : Bool) (D : Nat) (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 8 → yw s r p = T.eval D s₀ (σ.reg (xidx r) p)
  mem : ∀ b i, b < 3 → i < bsize D b → (to = true → b = 2 → σ.mem 3 i = .mem 3 i) →
    s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i)
  mem3 : to = true → ∀ i < D,
    s.mem.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem 3 i)
  src : to = true → ∀ i, σ.mem 2 i = .mem 2 i
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (wregsT to D s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

/-- In place. -/
abbrev SRel (D : Nat) := SRelT false D

theorem SRel.mem {D : Nat} {σ : Sym} {s₀ s : State} (h : SRel D σ s₀ s) :
    ∀ b i, b < 3 → i < bsize D b →
      s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i) :=
  fun b i hb hi => SRelT.mem h b i hb hi (fun e => nomatch e)

theorem SRelT.init (to : Bool) (D : Nat) (s₀ : State) : SRelT to D Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, zreg_xidx],
   fun b i hb _ _ => by simp only [Sym.init, T.eval, memBase_lt hb],
   fun _ i _ => by simp only [Sym.init, T.eval, memBase_3],
   fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ => rfl⟩

theorem SRel.init (D : Nat) (s₀ : State) : SRel D Sym.init s₀ s₀ := SRelT.init false D s₀

theorem SRelT.setReg {to : Bool} {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRelT to D σ s₀ s) {d : XReg}
    {f : Nat → T} (hz : ∀ r p, p < 8 → yw s' r p = if r = d then T.eval D s₀ (f p) else yw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRelT to D (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi hc => by rw [hm]; exact h.mem b i hb hi hc,
    fun ht i hi => by rw [hm]; exact h.mem3 ht i hi, h.src, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

theorem SRel.setReg {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRel D σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 8 → yw s' r p = if r = d then T.eval D s₀ (f p) else yw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRel D (σ.setReg (xidx d) f) s₀ s' :=
  SRelT.setReg h hz hm hg hr hw

theorem mod4_lt' (p : Nat) : p % 4 < 4 := Nat.mod_lt _ (by decide)

theorem yw_lk (s : State) (r : XReg) {l k : Nat} (hk : k < 4) :
    yw s r (4 * l + k) = dword (s.lane r l) k := by
  simp only [yw]; rw [show (4 * l + k) / 4 = l by omega_arith, show (4 * l + k) % 4 = k by omega_arith]

theorem lane_setV256_lt (s : State) (d r : XReg) (f : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    (s.setV .l256 d (f 0) (f 1)).lane r l = if r = d then f l else s.lane r l := by
  rw [State.lane_setV256]
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp

theorem dword_read256 (m : Mem) (a : Addr) {p : Nat} (hp : p < 8) :
    dword ((m.readW a 256).extractLsb' (128 * (p / 4)) 128) (p % 4) =
      m.readW (a + BitVec.ofNat 64 (4 * p)) 32 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega_arith), show 128 * (p / 4) + 32 * (p % 4) = 8 * (4 * p) by omega_arith]
  exact readW_extract m a (w := 256) (k := 4 * p) (n := 4) (by omega_arith)

theorem ymm_extract (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    (s.ymm r).extractLsb' (8 * (4 * k)) (8 * 4) = dword (s.lane r (k / 4)) (k % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : k < 4
  · simp only [show 8 * (4 * k) + j < 128 by omega_arith, ite_true, show k / 4 = 0 by omega_arith]
    exact congrArg _ (by omega_arith)
  · simp only [show ¬ 8 * (4 * k) + j < 128 by omega_arith, ite_false, show k / 4 = 1 by omega_arith,
      show (1 : Nat) ≠ 0 by decide]
    exact congrArg _ (by omega_arith)

theorem perm2Lanes_eq (a b : Nat → BitVec 128) (n : BitVec 8) {j : Nat} (h : n.getLsbD (4 * j + 3) = false) :
    perm2Lanes a b n j =
      (if (n.extractLsb' (4 * j) 2).toNat < 2 then a else b) ((n.extractLsb' (4 * j) 2).toNat % 2) := by
  simp only [perm2Lanes, h, Bool.false_eq_true, ite_false]
  by_cases hk : (n.extractLsb' (4 * j) 2).toNat < 2
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- A store of `ymm r` at doubleword `i` of a region whose doublewords
`j < D'` are at `p + 4 j`: the doublewords after it. -/
theorem read_store {m : Mem} {p : Addr} {i j D' : Nat} (hD : D' ≤ 128) (hi : i + 8 ≤ D') (hj : j < D')
    (v : BitVec 256) :
    (m.writeW (p + BitVec.ofNat 64 (4 * i)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      if i ≤ j ∧ j < i + 8 then v.extractLsb' (8 * (4 * (j - i))) (8 * 4) else m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  by_cases hx : i ≤ j ∧ j < i + 8
  · rw [ite_eq_left hx, show p + BitVec.ofNat 64 (4 * j) =
        p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (4 * (j - i)) by
      rw [add_ofNat']; congr 2; omega_arith]
    exact readW_writeW_inside m _ v (k := 4 * (j - i)) (n := 4) (by omega_arith) (by decide)
  · rw [ite_eq_right hx]
    exact readW_writeW_off m _ v (d := 4 * j) (e := 4 * i) (n := 4) (by omega_arith) (by omega_arith)
      (by omega_arith)

/-- A store in place, to `buf` or the data. -/
theorem store_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) {σ : Sym} {s : State} (h : SRelT false D σ s₀ s)
    {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 8 (wsize D) = some (b, i)) :
    ∃ s', exec (.vmovdquStore .l256 m r) s = some s' ∧ SRelT false D (symStore σ b i 8 (xidx r)) s₀ s' := by
  have hD := hc.small
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hi' : i + 8 ≤ bsize D b := Nat.le_trans hi (wsize_le D b)
  have hb0 : b = 1 ∨ b = 2 := by
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
    · simp [wsize] at hi
    · exact .inl e
    · exact .inr e
  have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin := in_regn hc hb h.wr hi' (by decide)
  refine ⟨s.setMem (s.mem.writeW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)),
    by simp only [exec, ea, State.store256_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' _ => ?_, (fun e => nomatch e), (fun e => nomatch e), by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], ?_, fun hd => by cases hd⟩⟩
  · simp only [yw, State.setMem_lane]; exact h.reg r' p hp
  · simp only [State.setMem_mem, symStore]
    by_cases e : b' = b
    · subst e
      rw [read_store (bsize_le hD b') hi' hi'']
      by_cases hx : i ≤ i' ∧ i' < i + 8
      · rw [ite_eq_left hx, ite_eq_left ⟨rfl, hx⟩, ymm_extract _ _ (by omega_arith)]
        exact h.reg r _ (by omega_arith)
      · rw [ite_eq_right hx, ite_eq_right (fun h' => hx h'.2)]
        exact h.mem b' i' hb' hi'' (fun e => nomatch e)
    · have f := (Frame.refl [regn D s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.ymm r)
        (regn_contains hD s₀ (n := 8) hi')
      rw [f.readW (r := regn D s₀ b') (regn_contains hD s₀ (n := 1) (by omega_arith))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
        (by decide), ite_eq_right (fun hx => e hx.1)]
      exact h.mem b' i' hb' hi'' (fun e => nomatch e)
  · simp only [State.setMem_mem]
    refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .r9, 256⟩ else ⟨s₀.gpr .rsi, 4 * D⟩)
      (by rcases hb0 with rfl | rfl <;> simp [wregsT, wregs]) _ ?_
    rcases hb0 with rfl | rfl
    · simp only [regn, baseR, Region.Contains, ite_true]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith
    · simp only [regn, baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith

/-- From a source to a destination: a store to the destination. -/
theorem store3_ok {D : Nat} {s₀ : State} (hc : Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128) {σ : Sym} {s : State}
    (h : SRelT true D σ s₀ s) {m : MemOp} {r : XReg} {i : Nat} (hs : slotD m 8 D = some i) :
    ∃ s', exec (.vmovdquStore .l256 m r) s = some s' ∧ SRelT true D (symStore σ 3 i 8 (xidx r)) s₀ s' := by
  have hD := hc.2.2
  obtain ⟨hi, hea⟩ := slotD_ok hs
  have ea : s.ea m = (dstR D s₀).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (4 * 8) := by
    rw [h.wr]; exact hc.2.1.w i 8 hi (by decide)
  have hdc : ∀ {j n : Nat}, j + n ≤ D → (dstR D s₀).Contains ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) (4 * n) :=
    fun hj => dst_contains hD s₀ hj
  have f := (Frame.refl [dstR D s₀] s.mem).writeW (List.mem_singleton_self _) (s.ymm r) (hdc (n := 8) hi)
  have F : Frame [⟨s₀.gpr .r9, 256⟩, dstR D s₀] s₀.mem
      (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)) :=
    (h.frame.writeW (r := dstR D s₀) (by simp [wregsT]) _ (hdc (n := 8) hi))
  have m3 : ∀ j < D, (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)).readW
      ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) 32 = T.eval D s₀ ((symStore σ 3 i 8 (xidx r)).mem 3 j) := by
    intro j hj
    rw [read_store hD hi hj]
    simp only [symStore, true_and]
    by_cases hx : i ≤ j ∧ j < i + 8
    · rw [ite_eq_left hx, ite_eq_left hx, ymm_extract _ _ (by omega_arith)]
      exact h.reg r _ (by omega_arith)
    · rw [ite_eq_right hx, ite_eq_right hx]
      exact h.mem3 rfl j hj
  refine ⟨s.setMem (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)),
    by simp only [exec, ea, State.store256_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ => h.src rfl, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [yw, State.setMem_lane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    have e3 : (symStore σ 3 i 8 (xidx r)).mem b' i' = σ.mem b' i' := by
      simp only [symStore, show b' ≠ 3 by omega_arith, false_and, ite_false]
    rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [e3, f.readW (r := regn D s₀ 0) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (by simpa using (hc.2.1.d 0 (by decide)).1) (by decide)]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [e3, f.readW (r := regn D s₀ 1) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (by simpa using (hc.2.1.d 1 (by decide)).1) (by decide)]
      exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · have hi2 : i' < D := by simpa [bsize] using hi''
      rw [show (symStore σ 3 i 8 (xidx r)).mem 2 i' = .mem 2 i' by
        simp only [symStore, show (2 : Nat) ≠ 3 by decide, false_and, ite_false]; exact h.src rfl i']
      simp only [T.eval, memBase_2]
      refine src_after hc F hi2 ?_
      have := m3 i' hi2
      rw [hcl rfl rfl] at this
      simpa only [T.eval, memBase_3] using this

/-- From a source to a destination: a store to `buf`. -/
theorem storeB_ok {D : Nat} {s₀ : State} (hc : Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128) {σ : Sym} {s : State}
    (h : SRelT true D σ s₀ s) {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 8 (wsize 0) = some (b, i)) :
    ∃ s', exec (.vmovdquStore .l256 m r) s = some s' ∧ SRelT true D (symStore σ b i 8 (xidx r)) s₀ s' := by
  have hD := hc.2.2
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hb1 : b = 1 := by
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | rfl
    · simp [wsize] at hi
    · exact e
    · simp [wsize] at hi
  subst hb1
  have hi' : i + 8 ≤ bsize D 1 := Nat.le_trans hi (by simp [wsize, bsize])
  have ea : s.ea m = (regn D s₀ 1).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (4 * 8) :=
    in_regn hc.1 (b := 1) (by decide) h.wr hi' (by decide)
  have f := (Frame.refl [regn D s₀ 1] s.mem).writeW (List.mem_singleton_self _) (s.ymm r)
    (regn_contains hD s₀ (n := 8) hi')
  have F : Frame [⟨s₀.gpr .r9, 256⟩, dstR D s₀] s₀.mem
      (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)) :=
    h.frame.writeW (r := ⟨s₀.gpr .r9, 256⟩) (by simp [wregsT]) _ (by
      simp only [regn, baseR, Region.Contains]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
  have m3 : ∀ j < D, (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)).readW
      ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) 32 = T.eval D s₀ ((symStore σ 1 i 8 (xidx r)).mem 3 j) := by
    intro j hj
    rw [f.readW (r := dstR D s₀) (by
        simp only [Region.Contains, dstR]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
      (by simpa using (hc.2.1.d 1 (by decide)).1.symm) (by decide)]
    simp only [symStore, show (3 : Nat) ≠ 1 by decide, false_and, ite_false]
    exact h.mem3 rfl j hj
  have hs2 : ∀ j, (symStore σ 1 i 8 (xidx r)).mem 2 j = .mem 2 j := fun j => by
    simp only [symStore, show (2 : Nat) ≠ 1 by decide, false_and, ite_false]; exact h.src rfl j
  refine ⟨s.setMem (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.ymm r)),
    by simp only [exec, ea, State.store256_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ j => ?_, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [yw, State.setMem_lane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [f.readW (r := regn D s₀ 0) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hc.1.d 0 1 (by decide) (by decide) (by decide))
        (by decide)]
      simp only [symStore, show (0 : Nat) ≠ 1 by decide, false_and, ite_false]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [read_store (bsize_le hD 1) hi' hi'']
      simp only [symStore, true_and]
      by_cases hx : i ≤ i' ∧ i' < i + 8
      · rw [ite_eq_left hx, ite_eq_left hx, ymm_extract _ _ (by omega_arith)]
        exact h.reg r _ (by omega_arith)
      · rw [ite_eq_right hx, ite_eq_right hx]
        exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · have hi2 : i' < D := by simpa [bsize] using hi''
      rw [hs2 i']
      simp only [T.eval, memBase_2]
      refine src_after hc F hi2 ?_
      have := m3 i' hi2
      rw [hcl rfl rfl] at this
      simpa only [T.eval, memBase_3] using this
  · exact hs2 j

/-- One instruction. -/
theorem sstepT_ok {to : Bool} {D : Nat} {s₀ : State} (hc : CtxT to D s₀) {σ σ' : Sym} {s : State}
    (h : SRelT to D σ s₀ s) {i : Instr} (e : stepT to D σ i = some σ') :
    ∃ s', exec i s = some s' ∧ SRelT to D σ' s₀ s' := by
  have hD := hc.small
  unfold stepT at e
  split at e
  · rename_i op d a b
    split at e
    · rename_i hop; subst hop; cases e
      refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
      simp only [yw, lane_vbin256]
      split
      · simp only [reduceVBinOpSse, T.eval, dword_paddd _ _ (mod4_lt' p)]
        rw [← yw, ← yw, h.reg a p hp, h.reg b p hp]
      · rfl
    · split at e
      · rename_i hop; subst hop; cases e
        refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
        simp only [yw, lane_vbin256]
        split
        · simp only [reduceVBinOpSse, T.eval, dword_pxor]
          rw [← yw, ← yw, h.reg a p hp, h.reg b p hp]
        · rfl
      · split at e
        · rename_i hor
          obtain ⟨rfl, rfl⟩ := hor
          cases e
          refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
          simp only [yw, lane_vbin256]
          split
          · simp only [reduceVBinOpSse, dword_por, BitVec.or_self]
            rw [← yw]; exact h.reg a p hp
          · rfl
        · cases e
  · rename_i d a b n
    split at e
    · rename_i hn
      cases e
      refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
      simp only [yw, VOp.exec]
      rw [lane_setV256_lt _ _ _ (perm2Lanes (s.lane a) (s.lane b) n) (by omega_arith)]
      split
      · have h3 : n.getLsbD (4 * (p / 4) + 3) = false := by
          rcases (by omega_arith : p / 4 = 0 ∨ p / 4 = 1) with e | e <;> rw [e]
          · exact hn.1
          · exact hn.2
        rw [perm2Lanes_eq _ _ _ h3]
        simp only [permT]
        have hk : (n.extractLsb' (4 * (p / 4)) 2).toNat < 4 := by
          have := (n.extractLsb' (4 * (p / 4)) 2).isLt; simpa using this
        split
        · rw [← yw_lk s a (mod4_lt' p)]; exact h.reg a _ (by omega_arith)
        · rw [← yw_lk s b (mod4_lt' p)]; exact h.reg b _ (by omega_arith)
      · rfl
    · cases e
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 8 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setV .l256 d ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb' 0 128)
      ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb' 128 128),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    simp only [yw]
    rw [lane_setV256_lt _ _ _ (fun l => (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 256).extractLsb'
      (128 * l) 128) (by omega_arith)]
    split
    · rw [dword_read256 _ _ hp, add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega_arith) (clean_of hcl hp)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 4 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setV .l256 d (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128),
      by simp only [exec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    simp only [yw]
    rw [lane_setV256_lt _ _ _ (fun _ => s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (by omega_arith)]
    split
    · rw [dword_readW _ _ (mod4_lt' p), add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := mod4_lt' p; omega_arith) (clean_of hcl (mod4_lt' p))
    · rfl
  · rename_i m r
    cases to
    · -- In place: `buf` or the data.
      simp only [Bool.false_eq_true, ite_false] at e
      obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
      exact store_ok hc h hs
    · simp only [ite_true] at e
      split at e
      · -- The destination.
        rename_i j hj
        cases e
        exact store3_ok hc h hj
      · -- `buf`.
        obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
        exact storeB_ok hc h hs
  · cases e

/-- A block of instructions. -/
theorem srunT_ok {to : Bool} {D : Nat} {s₀ : State} (hc : CtxT to D s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRelT to D σ s₀ s → runT to D σ is = some σ' →
      WP isa (.block is) s (SRelT to D σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [runT, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstepT_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srunT_ok hc is h₁ e₂⟩

/-- A block of instructions, in place. -/
theorem srun_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) (is : List Instr) {σ σ' : Sym} {s : State}
    (h : SRel D σ s₀ s) (e : run D σ is = some σ') : WP isa (.block is) s (SRel D σ' s₀) :=
  srunT_ok (to := false) hc is h e

end VG.Proof.ChaCha20.X86_64.Avx2Tail

end

end

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: the input states and the output

The terms the code around the rounds leaves (`Sym`), compared by the kernel
with the input states and the keystream blocks, and evaluated.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt xidx_zreg stateAt_get byte_dword add_ofNat')
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out memBase_0 memBase_1 memBase_2
  memBase_3 wregsT CtxT)
open VG.Proof.ChaCha20.X86_64.Avx512 (dstR Ctx3)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus ctr_get Consts hiR hiR_contains)

/-- The lane increments in `buf`: `0, 1` for the first set and `2, 3` for the
second, each in doubleword 0 of a lane, from `buf + 224`. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ k < 2, ∀ p < 8, m.readW (buf + BitVec.ofNat 64 (4 * (56 + 8 * k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (2 * k + p / 4) else 0

/-- Word `i` of block `l` of set `k` before the rounds. -/
def inT (k i l : Nat) : T :=
  if i / 4 = 3 then .add (.mem 0 i) (.mem 1 (56 + 8 * k + 4 * l + i % 4)) else .mem 0 i

/-- Word `i` of block `l` of set `k` of the output. -/
def outT (k i l : Nat) : T := .add (.reg (4 * k + i / 4) (4 * l + i % 4)) (inT k i l)

/-- The lane increments survive a frame that does not touch them. -/
theorem incs_frame {buf : Addr} {m m' : Mem} {rs : List Region} (h : Incs m buf) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Incs m' buf := by
  intro k hk p hp
  rw [← h k hk p hp]
  exact hf.readW (hiR_contains buf (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The kernel's checks -/

/-- The masks, loaded from `buf + 128` and `buf + 160`. -/
def masksOk (σ : Sym) : Bool :=
  (List.range 8).all fun p => σ.reg 8 p == .mem 1 (32 + p) && σ.reg 9 p == .mem 1 (40 + p)

def setupCheck (D : Nat) : Bool :=
  match run D Sym.init setup with
  | some σ => !σ.dirty && masksOk σ && (List.range 2).all fun k => (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg (4 * k + r) p == inT k (4 * r + p % 4) (p / 4)
  | none => false

def setup1Check : Bool :=
  match run 0 Sym.init setup1 with
  | some σ => !σ.dirty && masksOk σ && (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg r p == inT 0 (4 * r + p % 4) (p / 4)
  | none => false

def lastCheck : Bool :=
  match run 0 Sym.init (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128) with
  | some σ => (List.range 4).all fun j => (List.range 16).all fun i =>
      σ.mem 1 (16 * j + i) == outT (j / 2) i (j % 2)
  | none => false

def last1Check : Bool :=
  match run 0 Sym.init (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) with
  | some σ => (List.range 2).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT 0 i l
  | none => false

theorem setupCheck_0 : setupCheck 0 = true := by decide +kernel
theorem setup1Check_eq : setup1Check = true := by decide +kernel
theorem lastCheck_eq : lastCheck = true := by decide +kernel
theorem last1Check_eq : last1Check = true := by decide +kernel


/-! ## Evaluation -/

section
variable {D : Nat} {s : State}

theorem inT_eval (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (inT k i l) = (ctr (S0 s) (2 * k + l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega_arith)
  rw [show 56 + 8 * k + (4 * l + i % 4) = 56 + 8 * k + 4 * l + i % 4 by omega_arith,
    show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith] at e
  split
  · simp only [T.eval, memBase_0, memBase_1, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega_arith), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, memBase_0, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega_arith)]

theorem outT_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (outT k i l) = (plus vs (S0 s) (2 * k + l))[i] := by
  simp only [outT, plus, Vector.getElem_zipWith]
  rw [← inT_eval (D := D) hi hk2 hi16 hl]
  simp only [T.eval, yw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith]
  rw [hz k hk l hl i hi16]

end

/-- A register loaded with the 32 bytes at `buf + 4 o`, each lane `x`. -/
theorem lane_of {D : Nat} {σ : Sym} {s s' : State} (h : SRel D σ s s') (r : XReg) (o : Nat) (x : BitVec 128)
    (hr : ∀ p < 8, σ.reg (xidx r) p = .mem 1 (o + p))
    (h0 : (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) 256).extractLsb' 0 128 = x)
    (h1 : (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) 256).extractLsb' 128 128 = x) :
    ∀ l, s'.lane r l = x := by
  have hl : ∀ l < 2, s'.lane r l = x := by
    intro l hl
    have dq : ∀ q < 4, dword (s'.lane r l) q = dword x q := by
      intro q hq
      rw [← yw_lk s' r hq, h.reg r _ (by omega_arith), hr _ (by omega_arith)]
      simp only [T.eval, memBase_1]
      have d := dword_read256 s.mem (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) (p := 4 * l + q) (by omega_arith)
      rw [show (4 * l + q) / 4 = l by omega_arith, show (4 * l + q) % 4 = q by omega_arith, add_ofNat',
        show 4 * o + 4 * (4 * l + q) = 4 * (o + (4 * l + q)) by omega_arith] at d
      rw [← d]
      rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
      · rw [Nat.mul_zero, h0]
      · rw [Nat.mul_one, h1]
    exact ext_dword (dq 0 (by decide)) (dq 1 (by decide)) (dq 2 (by decide)) (dq 3 (by decide))
  intro l
  by_cases h0 : l = 0
  · exact hl l (by omega_arith)
  · rw [show s'.lane r l = s'.lane r 1 by simp [State.lane, h0]]; exact hl 1 (by decide)

/-- The masks in `ymm8`, `ymm9`, from the terms the setup leaves there. -/
theorem ym_of {D : Nat} {σ : Sym} {s s' : State} (h : SRel D σ s s') (hm : masksOk σ = true)
    (hc : Consts s.mem (s.gpr .r9)) : YM s' := by
  simp only [masksOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hm
  intro l
  exact ⟨lane_of h .xmm8 32 _ (fun p hp => (hm p hp).1) hc.lo16 hc.hi16 l,
    lane_of h .xmm9 40 _ (fun p hp => (hm p hp).2) hc.m8.1 hc.m8.2 l⟩

/-! ## The instructions -/

theorem setup_ok {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9))
    (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup) s fun s' =>
      HB 2 (fun j => ctr (S0 s) j) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setupCheck_0
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega_arith)
    rw [xidx_zreg _ (by omega_arith), e.2 k hk _ (by omega_arith) _ (by omega_arith)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith,
      show 4 * (i / 4) + i % 4 = i by omega_arith] at r
    rw [r, inT_eval hi hk hi16 hl]
  · cases e

theorem setup1_ok {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9)) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup1) s fun s' =>
      HB 1 (fun j => ctr (S0 s) j) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup1Check_eq
  unfold setup1Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup1 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega_arith
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega_arith)
    rw [xidx_zreg _ (by omega_arith), e.2 _ (by omega_arith) _ (by omega_arith)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega_arith, show (4 * l + i % 4) % 4 = i % 4 by omega_arith,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega_arith] at r
    rw [r, inT_eval hi (by decide) hi16 hl]
  · cases e

theorem last_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128)) s
      fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := lastCheck_eq
  unfold lastCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e _ (by omega_arith) _ (by omega_arith),
      outT_eval hz hi (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
      show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega_arith] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
    exact d
  · cases e

theorem last1_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 1 vs s) :
    WP isa (.block (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0)) s fun s' =>
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := last1Check_eq
  unfold last1Check at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_arith, e _ (by omega_arith) _ (by omega_arith),
      outT_eval hz hi (by decide) (by decide) (by omega_arith) (by omega_arith)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_arith, Nat.mul_zero, Nat.zero_add] at d
    exact d
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx2Tail
