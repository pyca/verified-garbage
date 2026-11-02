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
`keeps_of_frame`), which the shared contracts of `Proof/Weierstrass/MontContract.lean`
imply. They are constant time: the zero-extension is related by its
results (`mulZext_rel`), after which only `a0`–`a3` are public, and the
taint analysis finds every branch and address depends on them alone.
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
  simp only [Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p384p.k = 6 from rfl, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

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

theorem mulFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub mulFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem addFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub addFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem subFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub subFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem rvPub_agree : ∀ s₁ s₂ : State, rvPre p384p s₁ → rvPre p384p s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

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

theorem sat_pre : rvPre p384p satWs ∧ arg p384p satWs .a2 = 0 ∧ arg p384p satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes, satWs, offArg, p384p]

theorem mul_verified : Verified RISCV64.target mulFn (p384p.mulContract RISCV64.abi) :=
  Verified.of_correct mul_rv (mulFn_ct (Pre := (mulRV p384p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg,
        mulRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem add_verified : Verified RISCV64.target addFn (p384p.addContract RISCV64.abi) :=
  Verified.of_correct add_rv (addFn_ct (Pre := (addRV p384p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg,
        addRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem sub_verified : Verified RISCV64.target subFn (p384p.subContract RISCV64.abi) :=
  Verified.of_correct sub_rv (subFn_ct (Pre := (subRV p384p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg,
        subRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

end VG.Proof.Weierstrass.RISCV64.P384Field
