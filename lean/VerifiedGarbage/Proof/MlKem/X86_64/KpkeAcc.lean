module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodies
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: the pieces of `vg_mlkem*_{en,de}crypt_mul`

What `decryptMul` and `encryptMul` (`Impl/MlKem/X86_64/KpkeMul.lean`) need
of the code of a backend (`BodiesOk`): each piece meets a contract, around
an accumulator of a sum of products in a form of the backend's own
(`AccRep`), with whatever the products read from `scratch + 3328`
(`TabRep`). For SSE2 (`Bodies.sse`), the accumulator is the polynomial
itself (`PolyIs`), there is no table, and a product is computed to
`scratch + 2048` with `vg_mlkem_multiply_ntts`'s code and added with
`vg_mlkem_add`'s (`mulAccB`), whose contracts `WP.inline` runs them with.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The second working space of the products, at `scratch + 2048`. -/
abbrev tmpR (p : Addr) : Region := pR (p + BitVec.ofNat 64 2048)

/-- What the products read, at `scratch + 3328`. -/
abbrev tabR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 3328, 256⟩

/-- A form of a polynomial in the 1024 bytes at an address, which writes
elsewhere keep. -/
structure AccRep where
  is : Mem → Addr → Poly → Prop
  frame : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → ∀ {p : Addr} {f : Poly},
    (∀ r ∈ rs, (pR p).Disjoint r) → is m p f → is m' p f

/-- What the products need at `scratch + 3328`, which writes elsewhere keep. -/
structure TabRep where
  is : Mem → Addr → Prop
  frame : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → ∀ {p : Addr},
    (∀ r ∈ rs, (tabR p).Disjoint r) → is m p → is m' p

/-- The accumulator at `rdi` of the zero polynomial. -/
def zeroK (R : AccRep) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pR (s.gpr .rdi)] ∧ (retR s).Disjoint (pR (s.gpr .rdi))
  post s s' := R.is s'.mem (s.gpr .rdi) zero
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `NTT⁻¹` of the accumulator at `rdi`, to the polynomial at `rdi`, with the
working space at `rsi`. -/
def invAccK (R : AccRep) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ ∃ F, R.is s.mem (s.gpr .rdi) F
  post s s' := ∀ F, R.is s.mem (s.gpr .rdi) F → PolyIs s'.mem (s.gpr .rdi) (nttInv F)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The accumulator `o` at `rdi = rbp + 1024 o` plus `f = rsi ×_T g = rdx`, with
the working space at `scratch = rcx` (which `rbx` holds too) and at
`scratch + 2048`, and the table at `scratch + 3328`. -/
def mulAccK (R : AccRep) (T : TabRep) (o : Nat) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx), tabR (s.gpr .rcx)] ∧
    s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx), tmpR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdi)).Disjoint (tabR (s.gpr .rcx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdx)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rcx)).Disjoint (tmpR (s.gpr .rcx)) ∧ (pR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (tmpR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (tmpR (s.gpr .rcx)) ∧ (retR s).Disjoint (tabR (s.gpr .rcx)) ∧
    s.gpr .rbx = s.gpr .rcx ∧ s.gpr .rdi = s.gpr .rbp + BitVec.ofNat 64 (1024 * o) ∧ Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx) ∧
    T.is s.mem (s.gpr .rcx) ∧ ∃ A, R.is s.mem (s.gpr .rdi) A
  post s s' := ∀ A, R.is s.mem (s.gpr .rdi) A →
    R.is s'.mem (s.gpr .rdi) (add A (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The accumulator at `rdi` of `f = rsi ×_T g = rdx`, with what `mulAccK`
gives. -/
def mulSetK (R : AccRep) (T : TabRep) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx), tabR (s.gpr .rcx)] ∧
    s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx), tmpR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdi)).Disjoint (tabR (s.gpr .rcx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rdx)).Disjoint (tmpR (s.gpr .rcx)) ∧
    (pR (s.gpr .rcx)).Disjoint (tmpR (s.gpr .rcx)) ∧ (pR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (tmpR (s.gpr .rcx)).Disjoint (tabR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (tmpR (s.gpr .rcx)) ∧ (retR s).Disjoint (tabR (s.gpr .rcx)) ∧
    s.gpr .rbx = s.gpr .rcx ∧ Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx) ∧ T.is s.mem (s.gpr .rcx)
  post s s' := R.is s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The polynomial at `rdi` plus the accumulator at `rsi`, to `rdi`. -/
def finK (R : AccRep) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧
    ∃ F, R.is s.mem (s.gpr .rsi) F
  post s s' := ∀ F, R.is s.mem (s.gpr .rsi) F → PolyIs s'.mem (s.gpr .rdi) (add (polyAt s.mem (s.gpr .rdi)) F)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What `decryptMul`, `encryptMul` and `keygenMul` need of the code of a
backend: each piece meets its contract, and calls nothing. -/
structure BodiesOk (B : Bodies) (R : AccRep) (T : TabRep) : Prop where
  nttO : ∀ s, nttOK.pre s → ∃ t s', Exec isa B.nttO s t s' ∧ abiPreserved s s' ∧ nttOK.post s s'
  inv : ∀ s, (invAccK R).pre s → ∃ t s', Exec isa B.inv s t s' ∧ abiPreserved s s' ∧ (invAccK R).post s s'
  zero : ∀ s, (zeroK R).pre s → ∃ t s', Exec isa B.zero s t s' ∧ abiPreserved s s' ∧ (zeroK R).post s s'
  mulAcc : ∀ o, 1024 * o < 2 ^ 31 → ∀ s, (mulAccK R T o).pre s →
    ∃ t s', Exec isa (B.mulAcc o) s t s' ∧ abiPreserved s s' ∧ (mulAccK R T o).post s s'
  tab : ∀ s, InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 3328) 256 →
    WP isa (.block B.tab) s fun s' => T.is s'.mem (s.gpr .rcx) ∧ Frame [tabR (s.gpr .rcx)] s.mem s'.mem ∧
      Keep [.r9, .r10] s s'
  nc : B.nttO.noCalls = true ∧ B.inv.noCalls = true ∧ B.zero.noCalls = true ∧ ∀ o, (B.mulAcc o).noCalls = true
  fin : ∀ s, (finK R).pre s → ∃ t s', Exec isa B.fin s t s' ∧ abiPreserved s s' ∧ (finK R).post s s'
  ncFin : B.fin.noCalls = true
  mulSet : ∀ s, (mulSetK R T).pre s → ∃ t s', Exec isa B.mulSet s t s' ∧ abiPreserved s s' ∧ (mulSetK R T).post s s'
  ncSet : B.mulSet.noCalls = true

/-! ## SSE2 -/

/-- The accumulator of `Bodies.sse`: the polynomial. -/
def accSse : AccRep := ⟨PolyIs, fun hf _ _ hd h => polyIs_frame hf hd h⟩

/-- `Bodies.sse` reads no table. -/
def tabSse : TabRep := ⟨fun _ _ => True, fun _ _ _ _ => trivial⟩

namespace ZeroB

/-- After `i` stores of sixteen bytes. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x0 : s.xmm .xmm0 = 0
  keep : Keep [.rdi, .rcx] s₀ s
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  zero : ∀ k < 4 * i, coeffAt s.mem (s₀.gpr .rdi) k = 0

end ZeroB

theorem zeroB_wp {s : State} (hw : pR (s.gpr .rdi) ∈ s.wr) :
    WP isa zeroB s fun s' => PolyIs s'.mem (s.gpr .rdi) zero ∧ Frame [pR (s.gpr .rdi)] s.mem s'.mem ∧
      Keep [.rdi, .rcx] s s' := by
  unfold zeroB
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.xmm .xmm0 = 0 ∧ s1.mem = s.mem ∧ Keep [] s s1) (by
        vrunm
        exact ⟨by simp [XBinOp.eval], fun r _ => by simp only [RegUpd.gpr_setXmm], rfl, rfl⟩)
      fun s1 ⟨hx, hm, k1⟩ => ?_)
  refine WP.mono (wp_rcxLoop (N := 64) (by decide) (by decide) (ZeroB.Inv s) (fun u g _ => ?_)
    fun i hi u hI => ?_) fun u hI => ⟨polyIs_of_toNat fun k hk => ?_, hI.frame, hI.keep⟩
  · refine ⟨by rw [g.keep.gpr (by decide), k1.gpr (by decide)]; exact (BitVec.add_zero _).symm,
      by rw [g.keep.2.1, k1.2.1], by rw [g.keep.2.2, k1.2.2], by rw [g.xmm, hx], (k1.trans g.keep).mono (by decide),
      by rw [g.mem, hm]; exact Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  · have hc : InRegions u.wr (u.gpr .rdi) 16 := by
      rw [hI.wr, hI.rdi]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have hc' : InRegions (u.rd ++ u.wr) (u.gpr .rdi) 16 := let ⟨r, hr, h⟩ := hc; ⟨r, List.mem_append_right _ hr, h⟩
    vrunm [hc, hc']
    refine ⟨?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.rd,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.wr,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; exact hI.x0, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, fun k hk => ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
      rw [hI.rdi, show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_off, Nat.mul_succ]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
      exact hI.keep.gpr (by simp [hr])
    · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; exact hI.keep.2.1
    · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; exact hI.keep.2.2
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi]
      exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
      rw [hI.rdi, coeffAt_write128 _ _ (by omega) _ (by omega), hI.x0]
      split
      · simp [dword]
      · exact hI.zero k (by omega)
  · rw [n_eq] at hk
    rw [hI.zero k (by omega), zero, getElem!_pos _ k (by rw [n_eq]; exact hk)]
    simp

theorem zeroB_correct (s : State) (hs : (zeroK accSse).pre s) :
    ∃ t s', Exec isa zeroB s t s' ∧ abiPreserved s s' ∧ (zeroK accSse).post s s' := by
  obtain ⟨t, s', he, ⟨hP, hf, _⟩, hk⟩ := WP.keep [.rcx, .rdi] (zeroB_wp (s := s) (by rw [hs.2.1]; simp))
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2)), hP⟩

theorem nttInvB_acc (s : State) (hs : (invAccK accSse).pre s) :
    ∃ t s', Exec isa nttInvB s t s' ∧ abiPreserved s s' ∧ (invAccK accSse).post s s' := by
  obtain ⟨F, hF⟩ := hs.2.2.2.2.2
  obtain ⟨t, s', he, ha, hp⟩ := nttInvB_correct s ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hF.1⟩
  exact ⟨t, s', he, ha, fun F' hF' => by
    have e : polyAt s.mem (s.gpr .rdi) = F' := hF'.2
    simp only [inPlaceK, e] at hp
    exact hp⟩

theorem cov_mem {rs : List Region} {R : Region} (hR : R ∈ rs) : Covers [R] rs :=
  Covers.one ⟨R, hR, Region.contains_self _ _⟩

set_option linter.unusedSimpArgs false in
theorem mulAccB_correct (o : Nat) (ho : 1024 * o < 2 ^ 31) (s : State) (hs : (mulAccK accSse tabSse o).pre s) :
    ∃ t s', Exec isa (mulAccB o) s t s' ∧ abiPreserved s s' ∧ (mulAccK accSse tabSse o).post s s' := by
  obtain ⟨hrd, hwr, dAF, dAG, dAC, dAT, dAB, dFC, dFT, dGC, dGT, dCT, dCB, dTB,
    rA, rF, rG, rC, rT, rB, hbx, hbp, hRF, hRG, _, hAcc⟩ := hs
  generalize hA : s.gpr .rdi = A at *
  generalize hF : s.gpr .rsi = F at *
  generalize hG : s.gpr .rdx = G at *
  generalize hC : s.gpr .rcx = C at *
  have hW : WP isa (mulAccB o) s fun s' =>
      (∀ X, PolyIs s.mem A X → PolyIs s'.mem A (add X (multiplyNTTs (polyAt s.mem F) (polyAt s.mem G)))) ∧
      Frame [pR A, pR C, tmpR C] s.mem s'.mem := by
    unfold mulAccB
    -- `rdi = scratch + 2048`
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .rdi = C + BitVec.ofNat 64 2048 ∧
        s1.mem = s.mem ∧ Keep [.rdi] s s1) (by
          simp only [leaR]
          vrunm [hC]
          refine ⟨congrArg (C + ·) (by decide), fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h1di, hm1, k1⟩ => ?_)
    have g1 : ∀ r, r ∉ [Reg.rdi] → s1.gpr r = s.gpr r := fun r hr => k1.gpr hr
    -- the product to `scratch + 2048`
    refine WP.seq (WP.inline (k := mulK) mulB_correct (rd := [pR F, pR G]) (wr := [tmpR C, pR C]) ?_ ?_ ?_
      (fun s2 hrd2 hwr2 habi2 hf2 _ hpost2 => ?_))
    · simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        h1di, g1 .rsi (by decide), g1 .rdx (by decide), g1 .rcx (by decide), g1 .rsp (by decide), hF, hG, hC, hm1,
        retR]
      exact ⟨trivial, trivial, dFT.symm, dGT.symm, dCT.symm, dFC, dGC, rT, rF, rG, rC, hRF, hRG⟩
    · rw [k1.2.1, k1.2.2, hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons ((cov_mem (by simp)).cons
        ((cov_mem (by simp)).cons Covers.nil)))
    · rw [k1.2.2, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    simp only [mulK, State.withRegions_gpr, State.withRegions_mem, h1di, g1 .rsi (by decide),
      g1 .rdx (by decide), hF, hG, hm1] at hpost2
    have rbx_2 : s2.gpr .rbx = C := by rw [habi2.1 .rbx (by decide), g1 .rbx (by decide), hbx]
    have rbp_2 : s2.gpr .rbp = s.gpr .rbp := by rw [habi2.1 .rbp (by decide), g1 .rbp (by decide)]
    have rsp_2 : s2.gpr .rsp = s.gpr .rsp := by rw [habi2.1 .rsp (by decide), g1 .rsp (by decide)]
    -- the accumulator's address again, `rsi = scratch + 2048`
    refine WP.seq (WP.mono (Q := fun (s3 : State) => s3.gpr .rdi = A ∧ s3.gpr .rsi = C + BitVec.ofNat 64 2048 ∧
        s3.mem = s2.mem ∧ Keep [.rdi, .rsi] s2 s3) (by
          simp only [leaR, List.cons_append, List.nil_append]
          vrunm [rbx_2, rbp_2, sx_ofNat ho]
          refine ⟨hbp.symm, congrArg (C + ·) (by decide), fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s3 ⟨h3di, h3si, hm3, k3⟩ => ?_)
    have rsp_3 : s3.gpr .rsp = s.gpr .rsp := by rw [k3.gpr (by decide), rsp_2]
    have hfA : ∀ r ∈ [tmpR C, pR C], (pR A).Disjoint r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [dAT, dAC]
    rw [hm1] at hf2
    have hT3 : PolyIs s3.mem (C + BitVec.ofNat 64 2048) (multiplyNTTs (polyAt s.mem F) (polyAt s.mem G)) := by
      rw [hm3]; exact hpost2
    obtain ⟨X0, hX0⟩ := hAcc
    have hA3 : PolyIs s3.mem A (polyAt s.mem A) := by
      rw [hm3]; exact polyIs_frame hf2 hfA ⟨hX0.1, rfl⟩
    refine WP.inline (k := accK Spec.MlKem.add) add_correct (rd := [tmpR C]) (wr := [pR A]) ?_ ?_ ?_
      (fun s4 hrd4 hwr4 habi4 hf4 _ hpost4 => ?_)
    · simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        h3di, h3si, rsp_3, retR]
      exact ⟨trivial, trivial, dAT, rA, rT, hA3.1, hT3.1⟩
    · rw [k3.2.1, k3.2.2, hrd2, hwr2, k1.2.1, k1.2.2, hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    · rw [k3.2.2, hwr2, k1.2.2, hwr]
      exact (cov_mem (by simp)).cons Covers.nil
    simp only [accK, State.withRegions_gpr, State.withRegions_mem, h3di, h3si] at hpost4
    rw [hA3.2, hT3.2] at hpost4
    rw [hm3] at hf4
    refine ⟨fun X hX => ?_, ?_⟩
    · rw [← hX.2]; exact hpost4
    · refine (hf2.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans
        (hf4.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by rfl)
  refine ⟨t, s', he, abiPreserved_of_exec (by rfl) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨rA, rC, rT⟩)), fun X hX => ?_⟩
  rw [hA, hF, hG]
  rw [hA] at hX
  exact hP X hX

/-- `vg_mlkem_add`'s code adds the polynomial at `rsi`. -/
theorem finB_correct (s : State) (hs : (finK accSse).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.add s t s' ∧ abiPreserved s s' ∧ (finK accSse).post s s' := by
  obtain ⟨hrd, hwr, hd, rA, rF, hRA, F, hF⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := add_correct s ⟨hrd, hwr, hd, rA, rF, hRA, hF.1⟩
  exact ⟨t, s', he, ha, fun G hG => by rw [← hG.2]; exact hp⟩

/-- `vg_mlkem_multiply_ntts`'s code stores the product. -/
theorem mulB_set (s : State) (hs : (mulSetK accSse tabSse).pre s) :
    ∃ t s', Exec isa mulB s t s' ∧ abiPreserved s s' ∧ (mulSetK accSse tabSse).post s s' := by
  obtain ⟨hrd, hwr, dAF, dAG, dAC, _, _, dFC, _, dGC, _, _, _, _, rA, rF, rG, rC, _, _, _, hRF, hRG, _⟩ := hs
  have hW : WP isa mulB s fun s' =>
      PolyIs s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx))) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.inline (k := mulK) mulB_correct (rd := [pR (s.gpr .rsi), pR (s.gpr .rdx)])
      (wr := [pR (s.gpr .rdi), pR (s.gpr .rcx)]) ?_ ?_ ?_ (fun s2 _ _ _ hf2 _ hpost2 => ?_)
    · simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        retR]
      exact ⟨trivial, trivial, dAF, dAG, dAC, dFC, dGC, rA, rF, rG, rC, hRF, hRG⟩
    · rw [hrd, hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons ((cov_mem (by simp)).cons
        ((cov_mem (by simp)).cons Covers.nil)))
    · rw [hwr]
      exact (cov_mem (by simp)).cons ((cov_mem (by simp)).cons Covers.nil)
    simp only [mulK, State.withRegions_gpr, State.withRegions_mem] at hpost2
    exact ⟨hpost2, hf2⟩
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10] hW (by rfl)
  exact ⟨t, s', he, abiPreserved_of_exec (by rfl) he (gprPreserved_of hk (by decide) hf
    (by simpa using ⟨rA, rC⟩)), hP⟩

theorem BodiesOk.sse : BodiesOk .sse accSse tabSse :=
  ⟨nttOB_correct, nttInvB_acc, zeroB_correct, mulAccB_correct,
    fun _ _ => WP.block_nil_iff.mpr ⟨trivial, Frame.refl _ _, Keep.refl _ _⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl⟩, finB_correct, by decide +kernel,
    mulB_set, by decide +kernel⟩

end VG.Proof.MlKem.X86_64
