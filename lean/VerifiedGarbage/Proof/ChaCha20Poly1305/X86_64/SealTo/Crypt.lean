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

end VG.Proof.ChaCha20Poly1305.X86_64
