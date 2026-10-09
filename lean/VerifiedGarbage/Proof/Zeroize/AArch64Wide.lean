import VerifiedGarbage.Impl.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.Zeroize.AArch64

namespace VG.Proof.Zeroize.AArch64
open VG VG.AArch64 VG.Impl.Zeroize.AArch64 RegUpd

def InvV (s₀ : State) (i : Nat) (s : State) : Prop :=
  Inv s₀ i s ∧ s.v .v0 = 0

/-- One vector store extends the erased prefix without changing registers. -/
theorem wideStore_ok (s₀ s : State) (hp : contract.pre s₀) (i off : Nat)
    (hoff : off % 16 = 0 ∧ off < 65536)
    (hi : i + off + 16 ≤ (s₀.gpr .x1).toNat)
    (hw : s.wr = s₀.wr) (hd : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 i)
    (hv : s.v .v0 = 0) (hz : Prefix s.mem (s₀.gpr .x0) (i + off))
    (hf : Frame s₀.wr s₀.mem s.mem) :
    WP isa (.block [.strq .v0 .x0 off]) s fun t =>
      Prefix t.mem (s₀.gpr .x0) (i + off + 16) ∧ Frame s₀.wr s₀.mem t.mem ∧
      t.gpr = s.gpr ∧ t.v = s.v ∧ t.wr = s.wr := by
  have hn := (s₀.gpr .x1).isLt
  have hc : (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (i + off)) 16 :=
    Offset.contains_base _ hi (by omega)
  have hm := List.mem_singleton_self (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region)
  rw [← hp.2] at hm
  have hs : InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (i + off)) 16 := ⟨_, hm, hc⟩
  have ha : s₀.gpr .x0 + BitVec.ofNat 64 i + BitVec.ofNat 64 off =
      s₀.gpr .x0 + BitVec.ofNat 64 (i + off) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  crun [hd, hv, hw, ha, hs, hoff, State.store]
  exact ⟨prefix_write hz (by omega), hf.write hm _ hc⟩

theorem wideStep_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + 128 ≤ (s₀.gpr .x1).toNat) (h : InvV s₀ i s) :
    WP isa (.block wideStep) s fun t =>
      InvV s₀ (i + 128) t ∧ t.gpr .x3 = s.gpr .x3 - 1 ∧ t.gpr .x1 = s.gpr .x1 := by
  obtain ⟨⟨hw, ha, hd, hz, hf⟩, hv⟩ := h
  have hn := (s₀.gpr .x1).isLt
  have hc : ∀ k, k ≤ 112 → (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (i + k)) 16 :=
    fun k hk => Offset.contains_base _ (by omega) (by omega)
  have hm := List.mem_singleton_self (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region)
  rw [← hp.2] at hm
  have hs : ∀ k, k ≤ 112 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (i + k)) 16 :=
    fun k hk => ⟨_, hm, hc k hk⟩
  have hadd (k : Nat) : s₀.gpr .x0 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .x0 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have s0 := hs 0 (by decide)
  have s16 := hs 16 (by decide)
  have s32 := hs 32 (by decide)
  have s48 := hs 48 (by decide)
  have s64 := hs 64 (by decide)
  have s80 := hs 80 (by decide)
  have s96 := hs 96 (by decide)
  have s112 := hs 112 (by decide)
  rw [Nat.add_zero] at s0
  unfold wideStep
  crun [hd, ha, hv, hw, hadd, s0, s16, s32, s48, s64, s80, s96, s112,
    InvV, Inv, State.store, Nat.add_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have h1 := prefix_write (k := 16) hz (by omega)
    have h2 := prefix_write (k := 16) h1 (by omega)
    have h3 := prefix_write (k := 16) h2 (by omega)
    have h4 := prefix_write (k := 16) h3 (by omega)
    have h5 := prefix_write (k := 16) h4 (by omega)
    have h6 := prefix_write (k := 16) h5 (by omega)
    have h7 := prefix_write (k := 16) h6 (by omega)
    have h8 := prefix_write (k := 16) h7 (by omega)
    simpa only [Nat.add_assoc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h8
  ·
    have f1 := hf.write hm 0 (hc 0 (by decide))
    have f2 := f1.write hm 0 (hc 16 (by decide))
    have f3 := f2.write hm 0 (hc 32 (by decide))
    have f4 := f3.write hm 0 (hc 48 (by decide))
    have f5 := f4.write hm 0 (hc 64 (by decide))
    have f6 := f5.write hm 0 (hc 80 (by decide))
    have f7 := f6.write hm 0 (hc 96 (by decide))
    have f8 := f7.write hm 0 (hc 112 (by decide))
    simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat] using f8
  · simpa only [State.write, BitVec.ofNat_eq_ofNat] using hv

theorem wideLoop_ok (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + 128 * n ≤ (s₀.gpr .x1).toNat)
    (h : InvV s₀ i s) (hc : s.gpr .x3 = BitVec.ofNat 64 n) :
    WP isa wideLoop s fun t =>
      InvV s₀ (i + 128 * n) t ∧ t.gpr .x1 = s.gpr .x1 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .x1).isLt
    omega
  unfold wideLoop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, State.read, hc]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .x1 = s.gpr .x1)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, hc, beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      InvV s₀ (i + 128 * j) t ∧ t.gpr .x3 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .x1 = s.gpr .x1) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (wideStep_ok s₀ t hp _ ?_ ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · omega
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + 128 * j + 128 =
          i + 128 * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [eval, State.read, BitVec.setWidth_eq, hcu, bne, beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega,
          j+1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩


theorem tail128 (x : BitVec 64) : x &&& 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (127 : BitVec 64).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

theorem wideCorrect (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroizeWide s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .x1).toNat
  have start : WP isa (.block [.movz .x .x2 0 0, .lsr .x .x3 .x1 7, .movz .x .x4 127 0,
      .logic .and .x .x1 .x1 .x4, .vop (.dup .d2 .v0 .x2)]) s₀ fun t =>
      InvV s₀ 0 t ∧ t.gpr .x3 = BitVec.ofNat 64 (n / 128) ∧
      t.gpr .x1 = BitVec.ofNat 64 (n % 128) := by
    crun [InvV, Inv, Prefix, shr64, tail128, VOp.eval, State.setV, ofVDwords,
      (show BitVec.setWidth 64 (127#16) = (127 : BitVec 64) from rfl)]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl, tail128 _⟩
  unfold zeroizeWide
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (wideLoop_ok s₀ t hp 0 (n / 128) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.lsr .x .x3 .x1 3, .movz .x .x4 7 0,
      .logic .and .x .x1 .x1 .x4]) u fun v =>
      Inv s₀ (128 * (n / 128)) v ∧
      v.gpr .x3 = BitVec.ofNat 64 ((n % 128) / 8) ∧
      v.gpr .x1 = BitVec.ofNat 64 (n % 8) := by
    have hu' : Inv s₀ (128 * (n / 128)) u := by simpa using hu.1
    have hsmall : (BitVec.ofNat 64 (n % 128)).toNat = n % 128 := by simp; omega
    crun [Inv, hsu, hs, count, tail, hsmall,
      (show BitVec.setWidth 64 (7#16) = (7 : BitVec 64) from rfl)]
    refine ⟨hu', ?_⟩
    have hh := tail (BitVec.ofNat 64 (n % 128))
    rw [hsmall] at hh
    have he : n % 128 % 8 = n % 8 := by omega
    simpa only [he, BitVec.ofNat_eq_ofNat] using hh
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hsv⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ v hp (128 * (n / 128)) ((n % 128) / 8)
    (by dsimp [n]; omega) hv hcv) fun w ⟨hw, hsw⟩ => ?_)
  have last : WP isa (.block [.addImm .x .x3 .x1 0]) w fun z =>
      Inv s₀ (128 * (n / 128) + 8 * ((n % 128) / 8)) z ∧
      z.gpr .x3 = BitVec.ofNat 64 (n % 8) := by
    crun [Inv, hsw, hsv]
    exact hw
  refine WP.seq (WP.mono last fun z ⟨hz, hcz⟩ => ?_)
  refine WP.mono (loop_ok false s₀ z hp _ (n % 8) (by dsimp [n]; omega) hz hcz)
    fun w ⟨hw, _⟩ => ?_
  have hn : 128 * (n / 128) + 8 * ((n % 128) / 8) + (if false then 8 else 1) * (n % 8) = n := by
    simp; omega
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.1, hw.2.2.2.2⟩

theorem wideVerified : Verified target zeroizeWide (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := wideCorrect s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, ho⟩
    intro r hr
    have hc := instrs_keeps (c := zeroizeWide) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs] [sat] using sat
end VG.Proof.Zeroize.AArch64
