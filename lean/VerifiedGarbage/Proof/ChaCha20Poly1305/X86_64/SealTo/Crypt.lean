import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.SealTo.Blocks
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorTo

/-!
# ChaCha20-Poly1305 encryption with part of the data read from elsewhere, x86-64: encrypting

`cryptTo` encrypts `PTat`: the data, but for its bytes `[mm, mm + PP)`,
read from `src` (`cryptTo_ok`). Its loop over the whole 1024-byte passes of
`src` is `vg_chacha20_xor_to_avx512`'s, run inline with the permissions
narrowed to its regions (`RegionModel.wp_narrow`), where its proof
(`ChaCha20.X86_64.Avx512To.loopFull_ok`) holds.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- A copy of 64 bytes holds the same ChaCha20 state. -/
theorem stateAt_copy (m : Mem) (a b : Addr) : stateAt (m.writeW a (m.readW b 512)) a = stateAt m b := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact (readW_writeW_inside m a _ (k := 4 * i) (n := 4) (by omega) (by decide)).trans
    (readW_extract m b (w := 512) (k := 4 * i) (n := 4) (by omega))

/-- The keystream for counter `1 + mm / 64`, as the prologue leaves it in
`ctx[64, 128)`. -/
abbrev KS1 (s₀ : State) : List Byte := keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)

/-- After `oop`: the arguments of the call for the data after its first
`mm + PP` bytes, those from `src` encrypted, the others as before. -/
structure OopPost (s₀ s₁ : State) (s : State) : Prop where
  args : XArgsM s₀ (mm s₀ + PP s₀) s
  cs : ∀ r ∈ calleeSaved, r ≠ .rbx → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  frame : Frame [sub s₀ 64 384, sub s₀ 608 64, dR s₀] s₁.mem s.mem
  out : ∀ k < L s₀, ¬ (mm s₀ ≤ k ∧ k < mm s₀ + PP s₀) → s.mem (dp s₀ + BitVec.ofNat 64 k) = s₁.mem (dp s₀ + BitVec.ofNat 64 k)
  inn : ∀ k, mm s₀ ≤ k → k < mm s₀ + PP s₀ →
    s.mem (dp s₀ + BitVec.ofNat 64 k) = s₁.mem (sp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
  st : stateAt s.mem (off (cx s₀) 64) =
    VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) ((mm s₀ + PP s₀) / 64)


theorem wrap_add {p : Addr} {n k j : Nat} (hw : p.toNat + n ≤ 2 ^ 64) (hk : k + j ≤ n) (hn : n < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat + j ≤ 2 ^ 64 := by
  have hp := p.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  by_cases hc : p.toNat + k < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc]; omega
  · rw [show p.toNat + k = 2 ^ 64 by omega, Nat.mod_self]; omega

/-- The loop of `vg_chacha20_xor_to_avx512` inline: the `P` bytes of `src`
from byte `mm` on, XORed with the keystream of the copy of the state in
`ctx[608, 672)`, written to the data from byte `mm` on. -/
theorem loopIn_ok {s₀ : State} (hT : ToPre s₀) {P : Nat} (hP : 1024 ∣ P) (hle : mm s₀ + P ≤ SL s₀)
    {s : State} (hrdi : s.gpr .rdi = off (cx s₀) 608) (hrsi : s.gpr .rsi = sp s₀ + BitVec.ofNat 64 (mm s₀))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 P) (hrcx : s.gpr .rcx = dp s₀ + BitVec.ofNat 64 (mm s₀))
    (hr9 : s.gpr .r9 = off (cx s₀) 128) (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    WP isa xorToLoop s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 608 64, ⟨dp s₀ + BitVec.ofNat 64 (mm s₀), P⟩, sub s₀ 128 320] s.mem s'.mem ∧
      ∀ k < P, s'.mem (dp s₀ + BitVec.ofNat 64 (mm s₀) + BitVec.ofNat 64 k) =
        s.mem (sp s₀ + BitVec.ofNat 64 (mm s₀) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (off (cx s₀) 608)) P).getD k 0 := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hSL := hT.le
  have hP' : P < 2 ^ 64 := by simp only [SL] at hle; have := (stackArg s₀ 3).isLt; omega
  have heL : (s.gpr .rdx).toNat = P := by rw [hrdx, toNat_ofNat_lt hP']
  have hmL : mm s₀ + P ≤ L s₀ := by omega
  -- The windows of the data and of `src`.
  have dw : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (mm s₀), P⟩ (dR s₀) := Offset.sub_base _ hmL
  have sw : Region.Sub ⟨sp s₀ + BitVec.ofNat 64 (mm s₀), P⟩ (spR s₀) := Offset.sub_base _ hle
  have c608 := sub_ctx s₀ (k := 608) (n := 64) (by lit_omega)
  have c128 := sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)
  have st : ChaCha20.X86_64.Avx512To.stR s = sub s₀ 608 64 := by simp only [ChaCha20.X86_64.Avx512To.stR, ChaCha20.X86_64.Avx512To.est, hrdi]
  have de : ChaCha20.X86_64.Avx512To.edR s = ⟨dp s₀ + BitVec.ofNat 64 (mm s₀), P⟩ := by
    simp only [ChaCha20.X86_64.Avx512To.edR, ChaCha20.X86_64.Avx512To.edp, ChaCha20.X86_64.Avx512To.eL, hrcx, heL]
  have bu : ChaCha20.X86_64.Avx512To.bufR s = sub s₀ 128 320 := by simp only [ChaCha20.X86_64.Avx512To.bufR, ChaCha20.X86_64.Avx512To.ebp, hr9]
  have sr : ChaCha20.X86_64.Avx512To.srR s = ⟨sp s₀ + BitVec.ofNat 64 (mm s₀), P⟩ := by
    simp only [ChaCha20.X86_64.Avx512To.srR, ChaCha20.X86_64.Avx512To.esp, ChaCha20.X86_64.Avx512To.eL, hrsi, heL]
  have er : ChaCha20.X86_64.Avx512To.eret s = retR s₀ := by simp only [ChaCha20.X86_64.Avx512To.eret, retR, hrsp]
  have ek : ChaCha20.X86_64.Avx512To.estk s = stkR s₀ := by simp only [ChaCha20.X86_64.Avx512To.estk, stkR, hrsp]
  have hA : ChaCha20.X86_64.Avx512To.APre (s.withRegions [ChaCha20.X86_64.Avx512To.srR s] (ChaCha20.X86_64.Avx512To.frR s)) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ChaCha20.X86_64.Avx512To.stR, ChaCha20.X86_64.Avx512To.edR, ChaCha20.X86_64.Avx512To.bufR, ChaCha20.X86_64.Avx512To.srR, ChaCha20.X86_64.Avx512To.eret, ChaCha20.X86_64.Avx512To.estk,
        ChaCha20.X86_64.Avx512To.est, ChaCha20.X86_64.Avx512To.edp, ChaCha20.X86_64.Avx512To.ebp, ChaCha20.X86_64.Avx512To.esp, ChaCha20.X86_64.Avx512To.eL, State.withRegions_gpr] <;>
      simp only [ChaCha20.X86_64.Avx512To.stR, ChaCha20.X86_64.Avx512To.edR, ChaCha20.X86_64.Avx512To.bufR, ChaCha20.X86_64.Avx512To.srR, ChaCha20.X86_64.Avx512To.eret, ChaCha20.X86_64.Avx512To.estk,
        ChaCha20.X86_64.Avx512To.est, ChaCha20.X86_64.Avx512To.edp, ChaCha20.X86_64.Avx512To.ebp, ChaCha20.X86_64.Avx512To.esp, ChaCha20.X86_64.Avx512To.eL] at st de bu sr er ek
    · rw [st, de]; exact (hp.c_d.sub_left c608).sub_right dw
    · rw [st, bu]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [de, bu]; exact (hp.c_d.symm.sub_right c128).sub_left dw
    · rw [sr, st]; exact (hT.s_c.sub_left sw).sub_right c608
    · rw [sr, de]; exact (hT.s_d.sub_left sw).sub_right dw
    · rw [sr, bu]; exact (hT.s_c.sub_left sw).sub_right c128
    · rw [er, st]; exact hp.ret_c.sub_right c608
    · rw [er, de]; exact hp.ret_d.sub_right dw
    · rw [er, bu]; exact hp.ret_c.sub_right c128
    · rw [ek, st]; exact hp.stk_sub (by lit_omega)
    · rw [ek, de]; exact hp.stk_d.sub_right dw
    · rw [ek, bu]; exact hp.stk_sub (by lit_omega)
    · rw [hrsi, heL]; exact wrap_add hT.wrap_s hle (stackArg s₀ 3).isLt
    · rw [hrcx, heL]; exact wrap_add hp.wrap_d hmL hL9
  have hW := ChaCha20.X86_64.Avx512To.loopFull_ok hA (by simp only [ChaCha20.X86_64.Avx512To.eL, State.withRegions_gpr, heL]; exact hP)
  have hcov : Covers ([ChaCha20.X86_64.Avx512To.srR s] ++ ChaCha20.X86_64.Avx512To.frR s) (s.rd ++ s.wr) := by
    rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [ChaCha20.X86_64.Avx512To.frR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [sr]; exact ⟨spR s₀, List.mem_append_left _ hT.s_rd, mm s₀, rfl, hle⟩
    · rw [st]; exact ⟨ctxR s₀, List.mem_append_right _ hp.ctx_wr, 608, by simp [off_eq], show 608 + 64 ≤ 1696 by omega⟩
    · rw [de]; exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, mm s₀, rfl, hmL⟩
    · rw [bu]; exact ⟨ctxR s₀, List.mem_append_right _ hp.ctx_wr, 128, by simp [off_eq], show 128 + 320 ≤ 1696 by omega⟩
  have hcw : Covers (ChaCha20.X86_64.Avx512To.frR s) s.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [ChaCha20.X86_64.Avx512To.frR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [st]; exact ⟨ctxR s₀, hp.ctx_wr, 608, by simp [off_eq], show 608 + 64 ≤ 1696 by omega⟩
    · rw [de]; exact ⟨dR s₀, hp.d_wr, mm s₀, rfl, hmL⟩
    · rw [bu]; exact ⟨ctxR s₀, hp.ctx_wr, 128, by simp [off_eq], show 128 + 320 ≤ 1696 by omega⟩
  refine regionModel.wp_narrow hW hcov hcw (by decide +kernel) (.inl (by decide +kernel))
    fun _ s' _ rd' wr' f' ⟨cs, _, _, _, data⟩ => ⟨fun r hr => cs r hr, rd', wr', ?_, fun k hk => ?_⟩
  · simp only [regionModel, ChaCha20.X86_64.Avx512To.frR] at f'
    rw [st, de, bu] at f'
    exact f'
  · have x := data k (by simp only [ChaCha20.X86_64.Avx512To.eL, State.withRegions_gpr, heL]; exact hk)
    simp only [ChaCha20.X86_64.Avx512To.edp, ChaCha20.X86_64.Avx512To.D0, ChaCha20.X86_64.Avx512To.esp, ChaCha20.X86_64.Avx512To.KS, ChaCha20.X86_64.Avx512To.S0, ChaCha20.X86_64.Avx512To.est,
      ChaCha20.X86_64.Avx512To.eL, State.withRegions_gpr, State.withRegions_mem, hrcx, hrsi, hrdi, heL] at x
    exact x

/-- `oop` changing nothing but `rax`, `rbx` and the flags: no bytes from
`src`. -/
theorem OopPost.skip {s₀ s₁ : State} (a₁ : XArgsM s₀ (mm s₀) s₁) (hPP : PP s₀ = 0)
    (st₁ : stateAt s₁.mem (off (cx s₀) 64) =
      VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (mm s₀ / 64))
    {s₂ : State} (g : ∀ q, q ≠ .rbx → q ≠ .rax → s₂.gpr q = s₁.gpr q) (rd : s₂.rd = s₁.rd)
    (wr : s₂.wr = s₁.wr) (m : s₂.mem = s₁.mem) : OopPost s₀ s₁ s₂ := by
  have a₂ : XArgsM s₀ (mm s₀) s₂ :=
    ⟨by rw [g _ (by decide) (by decide)]; exact a₁.rdi, by rw [g _ (by decide) (by decide)]; exact a₁.rsi,
      by rw [g _ (by decide) (by decide)]; exact a₁.rdx, by rw [g _ (by decide) (by decide)]; exact a₁.rcx,
      by rw [g _ (by decide) (by decide)]; exact a₁.rsp, by rw [g _ (by decide) (by decide)]; exact a₁.r13,
      by rw [g _ (by decide) (by decide)]; exact a₁.r14, by rw [g _ (by decide) (by decide)]; exact a₁.r12,
      by rw [wr]; exact a₁.wr, a₁.le⟩
  refine ⟨by rw [hPP, Nat.add_zero]; exact a₂, fun r hr hb => g r hb (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), rd, by rw [m]; exact Frame.refl _ _,
    fun k _ _ => by rw [m], fun k h₁ h₂ => by omega, by rw [m, hPP, Nat.add_zero]; exact st₁⟩

theorem PP_eq {s₀ : State} (hbig : 960 < L s₀) (hle : mm s₀ ≤ SL s₀) :
    (SL s₀ - mm s₀) / 1024 * 1024 = PP s₀ := by
  simp only [PP]
  by_cases h : mm s₀ < SL s₀
  · rw [ite_eq_left ⟨hbig, h⟩]
  · rw [ite_eq_right (fun h' => h h'.2), show SL s₀ - mm s₀ = 0 by omega]

theorem oop_eq : oop =
    .seq (.block [.mov .rbx (.reg .r13), .alu .sub .rbx (.reg .rdx), .mov .rax (.mem (at_ .rsp 32)),
      .alu .cmp .rax (.reg .rbx)])
    (.ite .b (.block [])
      (.seq (.block [.alu .sub .rax (.reg .rbx), .shift .shr .rax 10, .shift .shl .rax 10,
          .alu .test .rax (.reg .rax)])
        (.ite .e (.block [])
          (.seq (.block (([.vmovdqu32Load .xmm0 (at_ .r15 64), .vmovdqu32Store (at_ .r15 608) .xmm0] : List Instr) ++
            (([.mov .rsi (.mem (at_ .rsp 24)), .alu .add .rsi (.reg .rbx), .mov .rcx (.reg .r14),
              .alu .add .rcx (.reg .rbx), .mov .rdx (.reg .rax)] : List Instr) ++ ptr .rdi .r15 608 ++
              ptr .r9 .r15 128 ++ ([.alu .add .rbx (.reg .rax)] : List Instr))))
            (.seq xorToLoop (.block restArgs)))))) := rfl

/-- The keystream from block `a` on (`64 ∣ c`). -/
theorem ks_ctr (S : Spec.ChaCha20.State) {c n P j : Nat} (hc : 64 ∣ c) (hj : j < P) (hn : c + j < n) :
    (keystream (VG.Proof.ChaCha20.ctr S (c / 64)) P).getD j 0 = (keystream S n).getD (c + j) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hj, VG.Proof.ChaCha20.keystream_getD _ hn, ctr_ctr']
  obtain ⟨a, rfl⟩ := hc
  rw [show 64 * a / 64 + j / 64 = (64 * a + j) / 64 by omega, show j % 64 = (64 * a + j) % 64 by omega]

/-- `oop`: the whole 1024-byte passes of `src` from byte `mm` on, if any,
encrypted into the data, and the arguments of the call for the rest. -/
theorem oop_ok {s₀ : State} (hT : ToPre s₀) (hbig : 960 < L s₀) {s₁ : State} (a₁ : XArgsM s₀ (mm s₀) s₁)
    (hrd₁ : s₁.rd = s₀.rd) (hr15 : s₁.gpr .r15 = cx s₀)
    (hS2 : s₁.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s₁.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3)
    (hst : stateAt s₁.mem (off (cx s₀) 64) =
      (Spec.ChaCha20.initState (K s₀) 0 (N s₀)).set 12 (BitVec.ofNat 32 (mm s₀ / 64 + 1))) :
    WP isa oop s₁ (OopPost s₀ s₁) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hSL := hT.le
  have hM := mOf_le 960 1024 (L s₀)
  have hML := mOf_le_len 960 1024 (L s₀)
  have hdvd := mm_dvd hbig
  have st₁ : stateAt s₁.mem (off (cx s₀) 64) =
      VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (mm s₀ / 64) := by
    rw [hst, set12_ctr]
  rw [oop_eq]
  refine WP.seq (WP.mono (oop1_ok hT a₁ hrd₁ hS3) fun s₂ ⟨rbx₂, rax₂, g₂, rd₂, wr₂, m₂, cf₂⟩ => ?_)
  refine WP.ite (decide (SL s₀ < mm s₀)) (by simp [eval, cf₂]) (fun hc => ?_) (fun hc => ?_)
  · have hc' := of_decide_eq_true hc
    have hPP : PP s₀ = 0 := by simp only [PP]; rw [ite_eq_right (fun h => by omega)]
    exact WP.block_nil (M := isa) (OopPost.skip a₁ hPP st₁ g₂ rd₂ wr₂ m₂)
  have hc' : mm s₀ ≤ SL s₀ := by have := of_decide_eq_false hc; omega
  refine WP.seq (WP.mono (oop2_ok hc' (stackArg s₀ 3).isLt rax₂ rbx₂) fun s₃ ⟨rax₃, g₃, rd₃, wr₃, m₃, zf₃⟩ => ?_)
  rw [PP_eq hbig hc'] at rax₃ zf₃
  have g₃₂ : ∀ q, q ≠ .rbx → q ≠ .rax → s₃.gpr q = s₁.gpr q := fun q h₁ h₂ => by rw [g₃ q h₂, g₂ q h₁ h₂]
  refine WP.ite (decide (PP s₀ = 0)) (by simp [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · exact WP.block_nil (M := isa) (OopPost.skip a₁ (of_decide_eq_true hz) st₁ g₃₂ (by rw [rd₃, rd₂])
      (by rw [wr₃, wr₂]) (by rw [m₃, m₂]))
  have hPP0 : PP s₀ ≠ 0 := of_decide_eq_false hz
  have hPPle : mm s₀ + PP s₀ ≤ SL s₀ := by
    rw [← PP_eq hbig hc']; have := Nat.div_mul_le_self (SL s₀ - mm s₀) 1024; omega
  have hmL : mm s₀ + PP s₀ ≤ L s₀ := by omega
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, a₁.wr]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃₂ _ (by decide) (by decide), hr15]
  -- The copy of the state, and the loop's arguments.
  have i₂ : InRegions (s₃.rd ++ s₃.wr) (stackArgAddr s₀ 2) 8 :=
    ⟨arg2R s₀, by rw [hrd₃]; simp [hT.g2], by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  have i₆₄ : InRegions (s₃.rd ++ s₃.wr) (off (cx s₀) 64) 64 := by
    rw [hrd₃, hwr₃]; exact hp.in_ctx' (by lit_omega)
  have o₆₀₈ : InRegions s₃.wr (off (cx s₀) 608) 64 := by
    rw [hwr₃]; exact hp.in_ctx (by lit_omega)
  have F₄ : ∀ m', m' = s₁.mem.writeW (off (cx s₀) 608) (s₁.mem.readW (off (cx s₀) 64) 512) →
      Frame [sub s₀ 608 64] s₁.mem m' := fun m' e => by
    rw [e]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have a2c : (arg2R s₀).Contains (stackArgAddr s₀ 2) (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine WP.seq (WP.block_append (WP.mono (zcopy_ok r15₃ i₆₄ o₆₀₈)
    fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => WP.mono (oopG_ok (s₀ := s₀) (m := mm s₀) (P := PP s₀)
      (by rw [g₄]; exact r15₃) (by rw [g₄, g₃₂ _ (by decide) (by decide)]; exact a₁.r14)
      (by rw [g₄, g₃ _ (by decide)]; exact rbx₂) (by rw [g₄]; exact rax₃)
      (by rw [g₄, g₃₂ _ (by decide) (by decide)]; exact a₁.rsp)
      (by
        rw [(F₄ s₄.mem (by rw [m₄, m₃, m₂])).readW a2c (by
          simpa using hT.g_c.sub_right (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega))) (by decide), hS2])
      (by rw [rd₄, wr₄]; exact i₂)) fun s₅ ⟨rsi₅, rcx₅, rdx₅, rdi₅, r9₅, rbx₅, g₅, m₅, rd₅, wr₅⟩ => ?_))
  have g₅₁ : ∀ q, q ≠ .rsi → q ≠ .rcx → q ≠ .rdx → q ≠ .rdi → q ≠ .r9 → q ≠ .rbx → q ≠ .rax →
      s₅.gpr q = s₁.gpr q := fun q a b c d e f g => by rw [g₅ q a b c d e f, g₄, g₃₂ q f g]
  have mem₅ : s₅.mem = s₁.mem.writeW (off (cx s₀) 608) (s₁.mem.readW (off (cx s₀) 64) 512) := by
    rw [m₅, m₄, m₃, m₂]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄, hrd₃]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, hwr₃]
  -- The loop.
  refine WP.seq (WP.mono (loopIn_ok hT (PP_dvd s₀) hPPle rdi₅ rsi₅ rdx₅ rcx₅ r9₅
    (by rw [g₅₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a₁.rsp)
    rd₅' wr₅') fun s₆ ⟨cs₆, rd₆, wr₆, f₆, d₆⟩ => ?_)
  have k₆ : ∀ r ∈ calleeSaved, r ≠ .rbx → s₆.gpr r = s₁.gpr r := fun r hr hb => by
    have hne : r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rdi ∧ r ≠ .r9 ∧ r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨a, b, c, d, e, f⟩ := hne
    rw [cs₆ r hr, g₅₁ r a b c d e hb f]
  -- The arguments of the call.
  refine WP.mono (restArgs_ok hp (m := mm s₀ + PP s₀) hmL (by rw [cs₆ _ (by simp [calleeSaved]), rbx₅])
    (by rw [k₆ _ (by simp [calleeSaved]) (by decide)]; exact hr15)
    (by rw [k₆ _ (by simp [calleeSaved]) (by decide)]; exact a₁.r14)
    (by rw [k₆ _ (by simp [calleeSaved]) (by decide)]; exact a₁.r13)
    (by rw [wr₆, wr₅']))
    fun s₇ ⟨m₇, rdi₇, rsi₇, rdx₇, rcx₇, cs₇, rd₇, wr₇⟩ => ?_
  have k₇ : ∀ r ∈ calleeSaved, r ≠ .rbx → s₇.gpr r = s₁.gpr r := fun r hr hb => by rw [cs₇ r hr, k₆ r hr hb]
  -- Memory.
  have Fw₇ : Frame [sub s₀ 64 64] s₆.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have F₅ : Frame [sub s₀ 608 64] s₁.mem s₅.mem := F₄ s₅.mem mem₅
  have dw : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (mm s₀), PP s₀⟩ (dR s₀) := Offset.sub_base _ hmL
  have nctx : ∀ {k a n : Nat}, k < L s₀ → a + n ≤ 1696 → ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk ha hc => hp.c_d _ (sub_ctx s₀ ha _ hc) (byte_dR hk)
  have st₆ : stateAt s₆.mem (off (cx s₀) 64) = stateAt s₁.mem (off (cx s₀) 64) := by
    rw [stateAt_frame f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dw
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      stateAt_frame F₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  refine ⟨⟨rdi₇, rsi₇, rdx₇, rcx₇, by rw [k₇ _ calleeSaved_rsp (by decide)]; exact a₁.rsp,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide)]; exact a₁.r13,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide)]; exact a₁.r14,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide)]; exact a₁.r12, by rw [wr₇, wr₆, wr₅'], hmL⟩,
    k₇, by rw [rd₇, rd₆, rd₅', hrd₁], ?_, fun k hk hout => ?_, fun k h₁ h₂ => ?_, ?_⟩
  · refine (F₅.sub fun r hr => ?_).trans ((f₆.sub fun r hr => ?_).trans (Fw₇.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, dw⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · have nw : ¬ (⟨dp s₀ + BitVec.ofNat 64 (mm s₀), PP s₀⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
      fun hc => Offset.disjoint (dp s₀) (d := k) (n := 1) (e := mm s₀) (k := PP s₀) (by omega)
        (by simp only [L] at hk; omega) (by simp only [L] at hmL; omega) _ (Region.contains_self _ _) hc
    rw [Fw₇ _ (by simpa using nctx hk (by lit_omega)), f₆ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨nctx hk (by lit_omega), nw, nctx hk (by lit_omega)⟩),
      F₅ _ (by simpa using nctx hk (by lit_omega))]
  · have hk : k < L s₀ := by omega
    have ea : dp s₀ + BitVec.ofNat 64 k = dp s₀ + BitVec.ofNat 64 (mm s₀) + BitVec.ofNat 64 (k - mm s₀) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h₁]
    have es : sp s₀ + BitVec.ofNat 64 (mm s₀) + BitVec.ofNat 64 (k - mm s₀) = sp s₀ + BitVec.ofNat 64 k := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h₁]
    have nsc : ¬ (sub s₀ 608 64).Contains (sp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hT.s_c _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) (sub_ctx s₀ (by lit_omega) _ hc)
    rw [Fw₇ _ (by simpa using nctx hk (by lit_omega)), ea, d₆ _ (by omega), es, F₅ _ (by simpa using nsc),
      mem₅, stateAt_copy, st₁, ks_ctr _ hdvd (by omega) (show mm s₀ + (k - mm s₀) < L s₀ by omega),
      Nat.add_sub_cancel' h₁]
  · rw [m₇, stateAt_ctrW, st₆, hst, Vector.set_set, set12_ctr]


/-! ## The bytes encrypted -/

theorem length_PTat (s₀ : State) (m : Mem) : (PTat s₀ m).length = L s₀ := by simp [PTat]

theorem PTat_getD {s₀ : State} (m : Mem) {k : Nat} (hk : k < L s₀) :
    (PTat s₀ m).getD k 0 = if mm s₀ ≤ k ∧ k < mm s₀ + PP s₀ then m (sp s₀ + BitVec.ofNat 64 k)
      else m (dp s₀ + BitVec.ofNat 64 k) := by
  simp [PTat, List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- With no bytes from `src`, the data. -/
theorem PTat_zero {s₀ : State} (hPP : PP s₀ = 0) (m : Mem) : PTat s₀ m = bytesAt m (dp s₀) (L s₀) := by
  simp only [PTat, bytesAt, hPP, Nat.add_zero]
  apply List.map_congr_left
  intro k _
  rw [ite_eq_right (fun h => by omega)]

theorem bytesAt_eq_zip {m : Mem} {p : Addr} {n : Nat} {xs ks : List Byte} (hx : xs.length = n)
    (hk : ks.length = n) (h : ∀ k < n, m (p + BitVec.ofNat 64 k) = xs.getD k 0 ^^^ ks.getD k 0) :
    bytesAt m p n = List.zipWith (· ^^^ ·) xs ks := by
  apply List.ext_getElem (by simp [bytesAt, hx, hk])
  intro k h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith, h k h₁]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `Inv.step`, for code that may write `rbx`, which `Inv` does not keep. -/
theorem Inv.stepB {s₀ s s' : State} (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, r ≠ .rbx → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 0 48).Disjoint r) : Inv s₀ s' where
  r15 := by rw [cs _ (by simp [calleeSaved]) (by decide), h.r15]
  r14 := by rw [cs _ (by simp [calleeSaved]) (by decide), h.r14]
  r13 := by rw [cs _ (by simp [calleeSaved]) (by decide), h.r13]
  r12 := by rw [cs _ (by simp [calleeSaved]) (by decide), h.r12]
  rsp := by rw [cs _ calleeSaved_rsp (by decide), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

/-- After `PTat` is encrypted, before the keystream is wiped. -/
structure CryptedTo (s₀ s : State) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → r ≠ .rbx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 384, sub s₀ 608 64, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (PTat s₀ s.mem)

/-! ## More than `fold` bytes -/

theorem arg_frame {s₀ : State} {j : Nat} (hj : j = 2 ∨ j = 3) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (arg2R s₀).Disjoint r) :
    m'.readW (stackArgAddr s₀ j) 64 = m.readW (stackArgAddr s₀ j) 64 := by
  refine hf.readW ?_ hd (by decide)
  rcases hj with rfl | rfl
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · show (arg2R s₀).Contains (s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1))) (64 / 8)
    rw [show s₀.gpr .rsp + BitVec.ofNat 64 (8 * (3 + 1)) = s₀.gpr .rsp + BitVec.ofNat 64 (8 * (2 + 1)) +
      BitVec.ofNat 64 8 by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact Offset.contains_base _ (by lit_omega) (by lit_omega)

theorem cryptBigTo_ok {s₀ : State} (hT : ToPre s₀) {s : State} (h : Inv s₀ s) (hbig : 960 < L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mm s₀, s.mem (off (cx s₀) (736 + k)) = (KS1 s₀).getD k 0)
    (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa (cryptBigTo Impl.ChaCha20.X86_64.Callee.avx512) s (CryptedTo s₀ s) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hM := mOf_le 960 1024 (L s₀)
  have hML := mOf_le_len 960 1024 (L s₀)
  have hdvd := mm_dvd hbig
  have hPPl := PP_le s₀ hT.le
  have hdvd' : 64 ∣ mm s₀ + PP s₀ := Nat.dvd_add hdvd (Nat.dvd_trans (by decide) (PP_dvd s₀))
  refine WP.seq (WP.mono (cryptPre_ok Proof.ChaCha20.X86_64.XorImpl.avx512 hp h)
    fun s₁ ⟨a₁, cs₁, rd₁, mx, fx, dx, m₁⟩ => ?_)
  change XArgsM s₀ (mm s₀) s₁ at a₁
  change Frame [⟨dp s₀, mm s₀⟩] s.mem mx at fx
  change ∀ k < mm s₀, _ at dx
  change s₁.mem = mx.writeW (off (cx s₀) 112) (BitVec.ofNat 32 (mm s₀ / 64 + 1)) at m₁
  have fw : Frame [sub s₀ 64 64] mx s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have dpre : ∀ r ∈ [(⟨dp s₀, mm s₀⟩ : Region)], (sub s₀ 64 64).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hML)
  have hpre : ∀ r ∈ [(⟨dp s₀, mm s₀⟩ : Region)], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_d.sub_right (Region.sub_prefix hML)
  have harg : ∀ r ∈ [sub s₀ 64 64], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_c.sub_right (sub_ctx s₀ (by lit_omega))
  refine WP.seq (WP.mono (oop_ok hT hbig a₁ (by rw [rd₁, h.rd]) (by rw [cs₁ _ (by simp [calleeSaved]), h.r15])
    (by rw [arg_frame (.inl rfl) fw harg, arg_frame (.inl rfl) fx hpre, hS2])
    (by rw [arg_frame (.inr rfl) fw harg, arg_frame (.inr rfl) fx hpre, hS3])
    (by rw [m₁, stateAt_ctrW, stateAt_frame fx dpre, hst])) fun s₂ o₂ => ?_)
  refine o₂.args.call hp Proof.ChaCha20.X86_64.XorImpl.avx512 fun s₃ rd₃ wr₃ cs₃ f₃ rsi₃ data₃ => ?_
  -- A byte of the data, or of `src`, is in none of the other regions.
  have nctx : ∀ {k a n : Nat}, k < L s₀ → a + n ≤ 1696 → ¬ (sub s₀ a n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk ha hc => hp.c_d _ (sub_ctx s₀ ha _ hc) (byte_dR hk)
  have nstk : ∀ {k : Nat}, k < L s₀ → ¬ (stkR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk hc => hp.stk_d _ hc (byte_dR hk)
  have sctx : ∀ {k a n : Nat}, k < SL s₀ → a + n ≤ 1696 → ¬ (sub s₀ a n).Contains (sp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk ha hc => hT.s_c _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) (sub_ctx s₀ ha _ hc)
  have sdR : ∀ {k : Nat}, k < SL s₀ → ¬ (dR s₀).Contains (sp s₀ + BitVec.ofNat 64 k) 1 :=
    fun hk hc => hT.s_d _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) hc
  -- Bytes outside the call's: as after `oop`.
  have out₃ : ∀ k < mm s₀ + PP s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₂.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₃ _ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact nctx (by omega) (by lit_omega)
      · exact fun hc => Offset.disjoint (dp s₀) (d := k) (n := 1) (e := mm s₀ + PP s₀) (k := L s₀ - (mm s₀ + PP s₀))
          (Or.inl (by omega)) (by have := hk; simp only [L] at hPPl; omega) (by simp only [L] at hPPl ⊢; omega) _
          (Region.contains_self _ _) (by simpa only [dRm, off_eq] using hc)
      · exact nctx (by omega) (by lit_omega)
      · exact nstk (by omega)
  refine ⟨rsi₃, fun r hr _ hb => by rw [cs₃ r hr, o₂.cs r hr hb, cs₁ r hr], by rw [rd₃, o₂.rd, rd₁],
    by rw [wr₃, o₂.args.wr, h.wr], ?_, ?_⟩
  · refine (fx.sub fun r hr => ?_).trans ((fw.sub fun r hr => ?_).trans ((o₂.frame.sub fun r hr => ?_).trans
      (f₃.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, Region.sub_prefix hML⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, dRm_sub s₀ hPPl⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [encrypt_eq, length_PTat]
    apply bytesAt_eq_zip (length_PTat _ _) (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [PTat_getD _ hk]
    have m₁k : ∀ {x : Addr}, ¬ (sub s₀ 64 64).Contains x 1 → s₁.mem x = mx x :=
      fun hx => fw _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx
    by_cases hkm : k < mm s₀
    · rw [ite_eq_right (fun h => by omega), out₃ k (by omega), o₂.out k hk (fun h => by omega),
        m₁k (nctx hk (by lit_omega)), dx k hkm, hks k hkm]
    by_cases hkp : k < mm s₀ + PP s₀
    · have hS := PP_le_SL s₀ (by omega)
      rw [ite_eq_left ⟨by omega, hkp⟩, out₃ k hkp, o₂.inn k (by omega) hkp,
        m₁k (sctx (by omega) (by lit_omega)), fx _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact fun hc => sdR (by omega) (Region.sub_prefix hML _ hc))]
    · rw [ite_eq_right (fun h => by omega)]
      have e₃ := bytesAt_xor_get (VG.Proof.ChaCha20.length_keystream _ _) data₃
        (k := k - (mm s₀ + PP s₀)) (by omega)
      have ea : off (dp s₀) (mm s₀ + PP s₀) + BitVec.ofNat 64 (k - (mm s₀ + PP s₀)) = dp s₀ + BitVec.ofNat 64 k := by
        rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      rw [ea, o₂.out k hk (fun h => by omega), m₁k (nctx hk (by lit_omega)),
        fx _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact fun hc => Offset.disjoint_base (dp s₀) (d := k) (n := 1) (by omega)
            (by simp only [L] at hk; omega) _ (Region.contains_self _ _) hc), o₂.st] at e₃
      rw [e₃]
      obtain ⟨a, ha⟩ := hdvd'
      rw [ha, Nat.mul_div_cancel_left _ (by decide), keystream_skip _ (by omega) hk]

/-! ## The data encrypted, and the keystream wiped -/

theorem cryptTo_ok {s₀ : State} (hT : ToPre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mm s₀, s.mem (off (cx s₀) (736 + k)) = (KS1 s₀).getD k 0)
    (hS2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2)
    (hS3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3) :
    WP isa (cryptTo Impl.ChaCha20.X86_64.Callee.avx512) s fun s' => Inv s₀ s' ∧
      Frame [sub s₀ 64 384, sub s₀ 608 64, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (PTat s₀ s.mem) := by
  have hp := hT.hp
  have hL9 := (s₀.gpr .r9).isLt
  have hm : mm s₀ ≤ 960 := mOf_le 960 1024 (L s₀)
  unfold cryptTo
  refine WP.seq (WP.mono (cmpFold_ok (fold := 960) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := CryptedTo s₀ s₁) ?_ fun s₂ c₂ => ?_)
  · refine WP.ite (decide (L s₀ < 960 + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      have hPP : PP s₀ = 0 := by simp only [PP]; rw [ite_eq_right (fun h => by omega)]
      refine WP.mono (cryptSmall_ok (fold := 960) (pass := 1024) (by lit_omega) (.inr (.inr rfl)) hp h₁
        (by omega_using [hc]) (by rw [m₁]; exact hks)) fun s' c => ⟨c.rsi, fun r hr h15 _ => c.cs r hr h15,
          c.rd, c.wr, c.frame.sub fun r hr => ?_, by rw [PTat_zero hPP]; exact c.data⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [decide_eq_false_iff_not] at hc
      exact cryptBigTo_ok hT h₁ (by omega_using [hc]) (by rw [m₁]; exact hst) (by rw [m₁]; exact hks)
        (by rw [m₁]; exact hS2) (by rw [m₁]; exact hS3)
  refine WP.seq (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, r ≠ .rbx → s₃.gpr r = s.gpr r := fun r hr hb => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ r h15, c₂.cs r hr h15 hb, g₁]
  have i₃ : Inv s₀ s₃ := h.stepB cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁])
    (by rw [m₃, ← m₁]; exact c₂.frame) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  -- The keystream wiped.
  refine WP.seq (WP.mono (foldM_ok (fold := 960) (pass := 1024) (len := L s₀) (by lit_omega) (.inr rfl) hL9
    (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (add64_ok (n := mm s₀) d₄) fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ => ?_)
  refine WP.mono (zeroKs_ok (w := 6) (.inr (.inr rfl)) hp (n := 64 + mm s₀) (by omega_using []) (by lit_omega) d₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ => ?_
  have cs₆ : ∀ r ∈ calleeSaved, s₆.gpr r = s₃.gpr r := fun r hr => by
    have h' := calleeSaved_ne hr
    rw [g₆ r h'.1 h'.2.1, g₅ r h'.2.2.1, g₄ r h'.2.2.1]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  refine ⟨i₃.step cs₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    ?_, ?_⟩
  · have fc : Frame [sub s₀ 64 384, sub s₀ 608 64, dR s₀, stkR s₀] s.mem s₃.mem := by
      rw [m₃, ← m₁]; exact c₂.frame
    refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt hL9), m₃, c₂.data, ← m₁]

end VG.Proof.ChaCha20Poly1305.X86_64
