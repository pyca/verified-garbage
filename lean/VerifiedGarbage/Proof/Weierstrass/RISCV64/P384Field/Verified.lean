module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Fn

/-!
# Arithmetic modulo P-384's prime on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`: `ws` in
`a0`, aligned, as a `[u64]` is, and the offsets' low words in `a1`–`a3`),
from `fn_ok` (`numAt` of an offset is the six doublewords there,
`numAt_d6`; the regions the function writes keep every other byte,
`keeps_of_frame`). A function is constant time (`fn_ct`) when the taint
analysis finds every branch and address of its core depends only on
`a0`–`a3`, which are public after the zero-extension, related by its
results (`mulZext_rel`).
-/

-- Checking `P` against the contract's modulus evaluates `2³⁸⁴`.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P384Field

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P384Field
open VG.Proof.X448.RISCV64.R64 (colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps p384p Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem numAt_d6 (m : Mem) (W : Addr) (o : BitVec 32) : numAt m W o 6 = d6 m (W + BitVec.ofNat 64 o.toNat) := by
  have h := VG.Proof.Mont.read_eq_wordsVal m (W + BitVec.ofNat 64 o.toNat) 6 0
  simp only [VG.Proof.Mont.off, BitVec.add_zero] at h
  rw [numAt, h]
  simp only [VG.Proof.Mont.wordsVal, VG.Proof.Mont.word, VG.Proof.Mont.off, d6, colsV,
    VG.Proof.X448.RISCV64.R64.dw, Nat.reduceAdd, Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  omega

/-- A byte of the working space outside a range of it. -/
theorem byte_out {W : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Contains (W + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint W (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _
    (Region.contains_self _ _) hc

/-- The regions the functions write keep every byte the contracts do. -/
theorem keeps_of_frame {W : Addr} {o : BitVec 32} (ho : o.toNat + 48 ≤ 3712) {m m' : Mem}
    (hf : Frame (fnW W o.toNat) m m') : Keeps 6 W o m m' := by
  intro i hi hown hoi
  simp only [Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at hi hown
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega) (by omega) (by omega)
  · exact byte_out (by omega) (by omega) hoi

theorem p_eq : p384p.m = P := rfl

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre p384p s) (hp : pre (arg p384p s .a2) (arg p384p s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg p384p s .a2) (arg p384p s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show p384p.k ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p384p.k = 6 from rfl, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

/-- `fnA core` meets a contract by register for offsets as the calls set
them, from `fnA_ok`, for any six-word modulus. -/
theorem fnA_rv {S : Impl.Weierstrass.Mont.Modulus} (hk : S.k = 6) {core : Prog isa} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreOk core pre res) {s : State} (hs : rvPre S s)
    (hoff : VG.Proof.Weierstrass.RISCV64.OffsOk s) (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fnA core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, hk, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show 6 ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, hk, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fnA_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb
    (hoff _ (by simp)) (hoff _ (by simp)) (hoff _ (by simp)) hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p384p)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p384p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnA_rv rfl (@mulCore_core) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v1, by rw [p_eq]; exact v2, k⟩

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p384p)).pre s) :
    ∃ t s', Exec isa addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv rfl (@addCore_core) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p384p)).pre s) :
    ∃ t s', Exec isa subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fnA_rv rfl (@subCore_core) hs.1.1 hs.2 (by rw [← p_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem mul_rv (s : State) (hs : (mulRV p384p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p384p).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (@mulCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v1, by rw [p_eq]; exact v2, k⟩

theorem add_rv (s : State) (hs : (addRV p384p).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@addCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

theorem sub_rv (s : State) (hs : (subRV p384p).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p384p).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@subCore_core) hs.1 (by rw [← p_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [p_eq]; exact v, k⟩

/-! ## Constant time -/

open VG.Proof.Ed25519.RISCV64 (mulAgreeLo mulZext_rel)

/-- `fn core` is constant time if the taint analysis finds `core` so, from the
pointers' and offsets' registers after the zero-extension. -/
theorem fn_ct {core : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂)
    (h : RelCT isa (VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]))
      (.seq (.block ptrs) (.ite (.zero .t0) core
        (.seq (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack .t4 SA 0 ++ unpack .t5 SB 0 ++
            ([.addi .t4 .a3 SA, .addi .t5 .a3 SB, .addi .t2 .a3 SO] : List Instr))) <|
          .seq core (.block (pack .t1 SO 0))))) fun _ _ => True) :
    ConstantTime isa Pre Pub (fn core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold fn
  refine RelCT.seq (mulZext_rel.mono (fun _ _ ⟨h₁, h₂, hp⟩ => hpub _ _ h₁ h₂ hp) fun _ _ h => h) ?_
  exact h.mono (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (by simpa using h)⟩) fun _ _ h => h

/-! ## The shared contracts -/

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

/-- A state satisfying the preconditions: `ws` at `0x1000`, every offset 0, memory zero. -/
def satWs : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

end VG.Proof.Weierstrass.RISCV64.P384Field
