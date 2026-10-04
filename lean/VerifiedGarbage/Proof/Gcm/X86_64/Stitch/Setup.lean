import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Loop

/-!
# Interleaved counter mode and GHASH: the setup

`storesK_ok`: `storesK base rs j` stores the registers `rs` to
`base + 32 (j + i)`. `setupC_ok`: the end of the setup loads `Y`, and makes
the counter pair, the increment and the last round key's address. The
powers the setup computes before (`setupG_ok`) are in the field, in
`Stitch/Ok.lean`.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (storesK setupC)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.Vaes (extract_lo extract_hi)
open VG.Spec.Gcm (Block blockAt inc32)

theorem storesK_ok (base : Reg) : ∀ (rs : List XReg) (j : Nat) (s : State),
    (∀ k < rs.length, InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) →
    (s.gpr base).toNat + 32 * (j + rs.length) ≤ 2 ^ 64 →
    WP isa (.block (storesK base rs j)) s fun s' =>
      (∀ k (h : k < rs.length), ∀ l < 2,
        s'.mem.readW (s.gpr base + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 = s.lane rs[k] l) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * rs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l)
  | [], _, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | r :: rs, j, s, hin, hw => by
    simp only [List.length_cons] at hin hw
    have ha : s.gpr base + BitVec.ofInt 64 ((32 * j : Nat) : Int) = s.gpr base + BitVec.ofNat 64 (32 * j) := by
      rw [BitVec.ofInt_natCast]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero, ha] at hin0
    let s₁ := s.setMem (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r))
    rw [storesK, WP.block_cons_iff]
    refine ⟨s₁, by
      simp only [isa, exec, State.store256_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, ha, hin0, ite_true]; rfl, ?_⟩
    have hg₁ : s₁.gpr = s.gpr := by simp [s₁]
    refine WP.mono (storesK_ok base rs (j + 1) s₁ (fun k hk => by
        rw [hg₁, show s₁.wr = s.wr by simp [s₁], show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hg₁]; omega)) fun s' ⟨hv, hf, g, rd, wr, hl⟩ => ?_
    rw [hg₁] at hv hf
    refine ⟨fun k hk l hl => ?_, ?_, by rw [g, hg₁], by rw [rd]; simp [s₁], by rw [wr]; simp [s₁],
      fun r' l => by rw [hl]; simp [s₁, State.lane]⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (r := ⟨s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
        show (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r)).readW _ 128 = _
        rw [show s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l) =
          s.gpr base + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) by
            rw [BitVec.add_assoc, BitVec.ofNat_add], State.ymm_eq]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 0) (n := 16) (by decide) (by decide)
          rw [show 16 * 0 = 0 from rfl]
          exact e.trans (extract_lo _ _)
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 16) (n := 16) (by decide) (by decide)
          rw [show 16 * 1 = 16 from rfl, e, extract_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega, hv k (by simpa using hk) l hl]
        simp [s₁, State.lane]
    · refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * (rs.length + 1)⟩] s.mem)
        List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r' hr' => ⟨_, List.mem_cons_self, fun x hx => ?_⟩)
      simp only [List.mem_singleton] at hr'
      subst hr'
      exact (Offset.sub _ (by omega) (by omega)) x hx

/-! ## `Y`, the counter, the increment and the pointers -/

theorem setupC_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

end VG.Proof.Gcm.X86_64.Stitch
