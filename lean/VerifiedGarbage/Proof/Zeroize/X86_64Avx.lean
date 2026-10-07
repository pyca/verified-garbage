import VerifiedGarbage.Proof.Zeroize.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# `vg_zeroize_avx` on x86-64

`zeroizeAvx` (`Impl/Zeroize/X86_64.lean`): `zeroize`'s proof with 64 bytes
at a time from `ymm0`, which holds zero throughout the first loop (`InvY`),
and then `zeroize`'s word and byte loops.
-/

namespace VG.Proof.Zeroize.X86_64
open VG VG.X86_64 VG.Impl.Zeroize.X86_64 VG.Proof.MlKem.X86_64

/-- `Inv`, with `ymm0` zero. -/
def InvY (s₀ : State) (i : Nat) (s : State) : Prop := Inv s₀ i s ∧ s.ymm .xmm0 = 0

theorem wideStepY_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + 64 ≤ (s₀.gpr .rsi).toNat) (h : InvY s₀ i s) :
    WP isa (.block wideStepY) s fun t =>
      InvY s₀ (i + 64) t ∧ t.gpr .rdx = s.gpr .rdx - 1 ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (s.gpr .rdx - 1 == 0) := by
  obtain ⟨⟨hw, ha, hd, hz, hf⟩, hy⟩ := h
  have hn := (s₀.gpr .rsi).isLt
  have hc : ∀ k, k ≤ 32 → (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 (i + k)) 32 :=
    fun k hk => Offset.contains_base _ (by omega) (by omega)
  have hmem := List.mem_singleton_self (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region)
  rw [← hp.2.1] at hmem
  have hs : ∀ k, k ≤ 32 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 (i + k)) 32 :=
    fun k hk => ⟨_, hmem, hc k hk⟩
  have hadd (k : Nat) : s₀.gpr .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .rdi + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have s0 := hs 0 (by decide); have s32 := hs 32 (by decide)
  rw [Nat.add_zero] at s0
  unfold wideStepY
  simp only [State.ymm] at hy
  xrun [hd, ha, hy, s0, s32, InvY, Inv, hw, State.ea, State.store256, State.ymm, hadd,
    (show BitVec.ofInt 64 0 = 0 from rfl), (show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl),
    (show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 from rfl),
    (show ∀ a : Addr, a + 0 = a from BitVec.add_zero)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 := prefix_writeW (w := 256) hz (by omega)
    have h2 := prefix_writeW (w := 256) h1 (by omega)
    exact h2
  · have c0 : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains (s₀.gpr .rdi + BitVec.ofNat 64 i) (256 / 8) := by
      have := hc 0 (by decide); rwa [Nat.add_zero] at this
    exact (hf.writeW (w := 256) hmem _ c0).writeW hmem _ (hc 32 (by decide))
  · simp [State.setFlags, State.setReg, hy]

/-- `wideStepY` `n` times, each zeroing 64 more bytes. -/
theorem loopY_ok (s₀ s : State) (hp : contract.pre s₀) (i n : Nat) (hn : i + 64 * n ≤ (s₀.gpr .rsi).toNat)
    (h : InvY s₀ i s) (hc : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (loopOf wideStepY) s fun t => InvY s₀ (i + 64 * n) t ∧ t.gpr .rsi = s.gpr .rsi := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .rsi).isLt
    omega
  have start : WP isa (.block [.alu .cmp .rdx (.imm 0)]) s fun t =>
      InvY s₀ i t ∧ t.gpr .rdx = BitVec.ofNat 64 n ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (BitVec.ofNat 64 n == 0) := by
    obtain ⟨⟨hw, ha, hd, hz, hf⟩, hy⟩ := h
    simp only [State.ymm] at hy
    xrun [InvY, Inv, State.ymm, hy, hw, ha, hd, hc, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show ∀ a : Addr, a - 0 = a from BitVec.sub_zero)]
    exact ⟨⟨hz, hf⟩, by simpa [State.setFlags] using hy⟩
  unfold loopOf
  refine WP.seq (WP.mono start fun t ⟨ht, hct, hsi, hz⟩ => ?_)
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
  · refine WP.ite false (by simp only [eval, hz, ofNat64_beq_zero hlt, decide_eq_false he]) (by simp) (fun _ => ?_)
    apply wp_countdown hlt (by omega)
      (fun j u => InvY s₀ (i + 64 * j) u ∧ u.gpr .rsi = s.gpr .rsi)
      (cnt := .rdx)
    · intro j hj u ⟨hu, hsu⟩ _
      refine WP.mono (wideStepY_ok s₀ u hp _ (by
        have : 64 * (j + 1) ≤ 64 * n := Nat.mul_le_mul_left _ hj
        rw [Nat.mul_succ] at this; omega) hu) fun v ⟨hv, hcv, hsv, hzv⟩ => ?_
      exact ⟨⟨by rwa [Nat.mul_succ, ← Nat.add_assoc], hsv.trans hsu⟩, hcv, hzv⟩
    · exact fun _ h => h
    · simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
    · exact hct

theorem and7_64 (a : Nat) : BitVec.ofNat 64 a &&& 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

theorem correctAvx (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroizeAvx s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .rsi).toNat
  have hn := (s₀.gpr .rsi).isLt
  have start : WP isa (.block [.vop (.vbin .vpxor .l128 .xmm0 .xmm0 .xmm0), .mov .rax (.imm 0),
      .mov .rdx (.reg .rsi), .shift .shr .rdx 6]) s₀ fun t =>
      InvY s₀ 0 t ∧ t.gpr .rdx = BitVec.ofNat 64 (n / 64) ∧ t.gpr .rsi = s₀.gpr .rsi := by
    xrun [InvY, Inv, Prefix, shr64, State.ymm, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show ∀ p : Addr, p + BitVec.ofNat 64 0 = p from BitVec.add_zero), VOp.exec_gpr, VOp.exec_mem,
      VOp.exec_wr]
    refine ⟨⟨⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩, ?_⟩, rfl⟩
    simp only [State.setReg, State.setFlags, VOp.exec, State.setV, VBinOp.sse, XBinOp.eval, BitVec.xor_self,
      ite_true]
    rfl
  unfold zeroizeAvx
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loopY_ok s₀ t hp 0 (n / 64) (by dsimp [n]; omega) ht hc) fun u ⟨⟨hu, _⟩, hsu⟩ => ?_)
  have mid : WP isa (.block [.mov .rdx (.reg .rsi), .shift .shr .rdx 3, .alu .and .rdx (.imm 7)]) u fun v =>
      Inv s₀ (64 * (n / 64)) v ∧ v.gpr .rdx = BitVec.ofNat 64 (n / 8 % 8) ∧ v.gpr .rsi = s₀.gpr .rsi := by
    xrun [Inv, hsu, hs, shr64, (show BitVec.signExtend 64 (7 : BitVec 32) = 7 from rfl), and7_64]
    exact ⟨by simpa only [Nat.zero_add, Inv] using hu, rfl⟩
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hsv⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ v hp (64 * (n / 64)) (n / 8 % 8) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, hsw⟩ => ?_)
  have tl : WP isa (.block [.mov .rdx (.reg .rsi), .alu .and .rdx (.imm 7)]) w fun x =>
      Inv s₀ (64 * (n / 64) + 8 * (n / 8 % 8)) x ∧ x.gpr .rdx = BitVec.ofNat 64 (n % 8) := by
    xrun [Inv, hsw, hsv, tail, (show BitVec.signExtend 64 (7 : BitVec 32) = 7 from rfl)]
    exact ⟨by simpa only [↓reduceIte, Inv] using hw, rfl⟩
  refine WP.seq (WP.mono tl fun x ⟨hx, hcx⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok false s₀ x hp _ (n % 8) (by dsimp [n]; simp; omega) hx hcx) fun y ⟨hy, _⟩ => ?_)
  have he : 64 * (n / 64) + 8 * (n / 8 % 8) + (if false then 8 else 1) * (n % 8) = n := by simp; omega
  rw [he] at hy
  obtain ⟨hyw, _, _, hz, hf⟩ := hy
  xrun [hz, hf]
  exact ⟨prefix_spec hz, hf⟩

theorem verifiedAvx : Verified target zeroizeAvx (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ⟨ho, hf⟩, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rdx] (correctAvx s hp) (by rfl)
    refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ?_, ho⟩
    apply gprPreserved_of hk (by decide +kernel) hf
    intro r hr
    rw [hp.2.1] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.2.2
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
    intro s t _ _ h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs] [sat] using sat

end VG.Proof.Zeroize.X86_64
