import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnB
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# P-521's product modulo `p` as a function, with BMI2 and ADX, on x86-64: verified

The facts of `p521p.mulContract` on x86-64, by register (`mulX64`: `ws` in
`rdi`, the offsets in `esi`, `edx` and `ecx`), which `mulFnX` meets
(`mulFnX_x64`, from `mulFnX_ok`), constant time by taint tracking (only the
stack pointer, `ws` and the offsets' low halves are public; `o`, kept in the
temporary area while the product runs, is a public slot there), and a state
satisfying it.
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Spec.Weierstrass.Mont (numAt Keeps Modulus p521p)

/-- What the precondition says of the registers. -/
def x64Pre (M : Modulus) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 8192⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩ ∧
    (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64 ∧
    M.Fit ((s.gpr .rsi).setWidth 32) ((s.gpr .rdx).setWidth 32) ((s.gpr .rcx).setWidth 32)

/-- The number at the offset in `r`. -/
abbrev argNum (M : Modulus) (m : Mem) (s : State) (r : Reg) : Nat :=
  numAt m (s.gpr .rdi) ((s.gpr r).setWidth 32) M.k

/-- What two runs agree on: the stack pointer, `ws` and the offsets. -/
def x64Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (s₁.gpr .rcx).setWidth 32 = (s₂.gpr .rcx).setWidth 32

/-- `vg_<curve>_mul_mod_<p|n>(ws = rdi, o = esi, a = edx, b = ecx)`. -/
def mulX64 (M : Modulus) : Contract isa where
  pre s := x64Pre M s ∧ argNum M s.mem s .rcx < M.m
  post s s' :=
    argNum M s'.mem s .rsi < M.m ∧
    argNum M s'.mem s .rsi * M.R % M.m = argNum M s.mem s .rdx * argNum M s.mem s .rcx % M.m ∧
    Keeps M.k (s.gpr .rdi) ((s.gpr .rsi).setWidth 32) s.mem s'.mem
  pub := x64Pub

theorem numAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) :
    numAt m ws o k = wordsVal m ws o.toNat k :=
  read_eq_wordsVal m ws k o.toNat

theorem p521p_m : p521p.m + 1 = 512 * (2 ^ 64) ^ 8 := by decide +kernel

theorem p521p_R : p521p.R = (2 ^ 64) ^ 9 :=
  (Nat.pow_mul 2 64 p521p.k).trans (congrArg (HPow.hPow (2 ^ 64)) (show p521p.k = 9 from rfl))

/-- The contract, from what `fnShape_ok` gives for `code`. -/
theorem fn_x64 {code : Prog isa} (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hok : ∀ {s : State} {base : Addr} {Z : Nat}, Scr s base Z → 4096 ≤ Z → ∀ {m : Nat}, m + 1 = 512 * (2 ^ 64) ^ 8 →
      argOf s .rsi + 72 ≤ 3520 → argOf s .rdx + 72 ≤ 3520 → argOf s .rcx + 72 ≤ 3520 →
      wordsVal s.mem base (argOf s .rcx) 9 < m →
      WP isa code s fun s' =>
        wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
        wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
          wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
        KeepRegs fnClob s s' ∧
        ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
          (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x)
    (s : State) (hs : (mulX64 p521p).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (mulX64 p521p).post s s' := by
  obtain ⟨⟨hrd, hwr, hret, hnw, ho, ha, hb⟩, hB⟩ := hs
  have hscr : Scr s (s.gpr .rdi) 8192 := ⟨rfl, by rw [hwr]; simp, hnw⟩
  simp only [Spec.Weierstrass.Mont.Fits, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes,
    p521p] at ho ha hb
  suffices hwp : WP isa code s fun s' => gprPreserved s s' ∧ (mulX64 p521p).post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  simp only [argNum, numAt_eq] at hB
  refine WP.mono (hok hscr (by decide) p521p_m ho ha hb hB) fun s' ⟨hlt, heq, k, hmem⟩ => ?_
  refine ⟨⟨fun r hr => k.gpr r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩,
    by simp only [argNum, numAt_eq]; exact hlt, by simp only [argNum, numAt_eq, p521p_R]; exact heq, ?_⟩
  · refine Mem.readW_congr fun i hi => hmem _ (Or.inr ?_) (Or.inr ?_) <;>
    · have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      simp only [Region.Contains, Nat.not_le] at hx
      simp only [ofs, argOf]; omega
  · intro i hi hown ho'
    have e1 : Spec.Weierstrass.Mont.wsBytes = 8192 := rfl
    have e2 : Spec.Weierstrass.Mont.ownAt p521p.k = 3520 := rfl
    have e3 : fnTmp = 4024 := rfl
    have e4 : p521p.k = 9 := rfl
    rw [e1] at hi
    rw [e2] at hown
    rw [e4] at ho'
    have h64 : i < 2 ^ 64 := by omega
    refine hmem _ ?_ ?_
    · rw [ofs_off0 _ h64]; exact ho'
    · rw [ofs_off0 _ h64, e3]; omega

theorem mulFnX_x64 : ∀ s, (mulX64 p521p).pre s →
    ∃ t s', Exec isa mulFnX s t s' ∧ abiPreserved s s' ∧ (mulX64 p521p).post s s' :=
  fn_x64 (by decide +kernel) mulFnX_ok

theorem mulFn_x64 : ∀ s, (mulX64 p521p).pre s →
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulX64 p521p).post s s' :=
  fn_x64 (by decide +kernel) mulFn_ok

/-! ## Constant time -/

/-- The state after the zero-extension of the offsets. -/
def zextState (s : State) : State :=
  ((s.setReg .rsi (((s.gpr .rsi).setWidth 32).setWidth 64)).setReg .rdx
    (((s.gpr .rdx).setWidth 32).setWidth 64)).setReg .rcx (((s.gpr .rcx).setWidth 32).setWidth 64)

theorem exec_zext {s s' : State} {t : List Leak} (h : Exec isa (.block zext) s t s') :
    t = [] ∧ s' = zextState s := by
  cases h with
  | block b =>
    simp only [zext, execBlock, exec, readSrc32, Option.map_some, State.setReg32, addrs, srcAddrs,
      List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq, RegUpd.gpr_setReg,
      reduceCtorEq, ite_false] at b
    exact ⟨b.2.symm, b.1.symm⟩

/-- After the zero-extension: the stack pointer, `ws` and the offsets public,
`rdi` the base of the working space. -/
def τ₁ : X86_64.Taint.T :=
  { regs := .ofList [.rsp, .rdi, .rsi, .rdx, .rcx], flags := false, lens := [8192], bases := [(.rdi, 0, 0)] }

/-- The zero-extension, then code that is constant time for states agreeing
as `τ₁` says: constant time for states agreeing on the stack pointer, `ws`
and the offsets' low halves. -/
theorem ct_zext {M : Modulus} {Pre : State → Prop} (hP : ∀ s, Pre s → x64Pre M s) {c : Prog isa}
    (h : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree τ₁) c) :
    ConstantTime isa Pre x64Pub (.seq (.block zext) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  have wf : ∀ s, x64Pre M s → X86_64.Taint.Wf τ₁ (zextState s) := by
    intro s hs
    obtain ⟨-, hw, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [zextState, RegUpd.wr_setReg, hw, τ₁], by simp [zextState, RegUpd.wr_setReg, hw],
      by simp [zextState, RegUpd.wr_setReg, hw]⟩, fun p hp => ?_⟩
    simp only [τ₁, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, zextState, RegUpd.wr_setReg, RegUpd.gpr_setReg, hw]
  cases e₁ with
  | seq z₁ c₁ =>
    cases e₂ with
    | seq z₂ c₂ =>
      obtain ⟨rfl, rfl⟩ := exec_zext z₁
      obtain ⟨rfl, rfl⟩ := exec_zext z₂
      have ag : X86_64.Taint.Agree τ₁ (zextState s₁) (zextState s₂) := by
        refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ (hP _ h₁), wf _ (hP _ h₂), ?_, ?_,
          X86_64.Taint.noLo, X86_64.Taint.noXr⟩
        · simp only [τ₁, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            simp only [zextState, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, p1, p2, p3, p4, p5]
        · simp only [zextState, RegUpd.wr_setReg]; rw [(hP _ h₁).2.1, (hP _ h₂).2.1, p2]
        · exact VG.X86_64.Taint.slotsOk_empty
        · exact VG.X86_64.Taint.slotsAgree_empty
      rw [h _ _ _ _ _ _ trivial trivial ag c₁ c₂]

theorem mulFnX_ct : ConstantTime isa (mulX64 p521p).pre (mulX64 p521p).pub mulFnX :=
  ct_zext (M := p521p) (fun _ h => h.1)
    (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))

theorem mulFn_ct : ConstantTime isa (mulX64 p521p).pre (mulX64 p521p).pub mulFn :=
  ct_zext (M := p521p) (fun _ h => h.1)
    (VG.Taint.constantTime (A := X86_64.taint) τ₁ (fun _ _ _ _ h => h) (by taint_decide))

/-! ## The contract -/

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

theorem numAt_zero (ws : Addr) (o : BitVec 32) (k : Nat) : numAt (fun _ => 0) ws o k = 0 :=
  read_zero _ _

/-- A state satisfying the precondition: `ws` at `0x1000`, the numbers at
offset 0, all zero, the stack at `0x10000`. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem fit_zero (M : Modulus) (hk : M.k ≤ 9) : M.Fit 0 0 0 := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Spec.Weierstrass.Mont.Fits, Spec.Weierstrass.Mont.ownAt,
    Spec.Weierstrass.Mont.ownBytes, h0] <;> omega

theorem mul_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.mulContract X86_64.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.Weierstrass.Mont.sig, X86_64.abi, X86_64.argRegs, sat]
    exact ⟨by decide, fit_zero M hk, by rw [numAt_zero]; exact hm⟩)

theorem mul_implies (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) :
    (mulX64 M).Implies (M.mulContract X86_64.abi) where
  pre := by sig_implies_pre [Modulus.mulContract, Spec.Weierstrass.Mont.sig, argNum, mulX64, x64Pre,
    x64Pub, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [Modulus.mulContract, Spec.Weierstrass.Mont.sig, argNum, mulX64, x64Pre,
    x64Pub, X86_64.abi, X86_64.argRegs]
  pub := by sig_implies_pub [Modulus.mulContract, Spec.Weierstrass.Mont.sig, argNum, mulX64, x64Pre,
    x64Pub, X86_64.abi, X86_64.argRegs]
  sat := ⟨sat, mul_sat M hk hm⟩

/-- `vg_p521_mul_mod_p` on x86-64. -/
theorem p521p_mul_verified : Verified X86_64.target mulFn (p521p.mulContract X86_64.abi) :=
  Verified.of_correct mulFn_x64 mulFn_ct (mul_implies p521p (by decide) (by decide +kernel))

/-- `vg_p521_mul_mod_p_adx` on x86-64. -/
theorem p521p_mulX_verified : Verified X86_64.target mulFnX (p521p.mulContract X86_64.abi) :=
  Verified.of_correct mulFnX_x64 mulFnX_ct (mul_implies p521p (by decide) (by decide +kernel))

end VG.Proof.Weierstrass.X86_64.Mont
