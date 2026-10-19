module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Short.Rounds
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Loop
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Out3
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Prologue
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.StoreRow

/-!
# ChaCha20-Poly1305 for short records (x86-64): `sealShort` and `openShort`

One module, so that few modules import the Poly1305 proofs' algebra through
`CT`: the keystream (`ksShort_ok`), the registers and the keystream after the
prologue (`shortPre_ok`), the padded blocks (`padAad_ok`, `padData_ok`), the
tag (`mac_ok`), and `seal` and `open` from them (`sealShort_ok`,
`openShort_ok`).
-/

@[expose] public section

/-!
# ChaCha20-Poly1305 for short records (x86-64): the keystream

`Stitch.ksShort` computes the first `64 n` bytes of keystream from the state
at `ctx + 608` (counter 0) into `ctx + 672` (`KsOut`): two blocks for up to
64 bytes of data (`twoKsR`, `twoKsS_ok`), four up to 192 (`fourKsR`,
`fourKsS_ok`), six up to 320 (`threeKs`), and the kernel's eight up to 448
(`eightKs`), each with its rounds looped (`Short/Rounds.lean`). They write
only `ctx[64, 448)` and `ctx[608, 1184)` and, among the general-purpose
registers, `rax`, `rcx`, `r9` and `rsi`.
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch (twoKsRN_ok fourKsRN_ok xCtr xCtr_eq ctr_toNat)
open VG.Proof.ChaCha20.X86_64.Avx2 (stR bufR)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt serialize)

variable {e : Bool}

/-- The first `64 n` bytes of keystream from the state at `ctx + 608` in `s`,
at `ctx + 672` in `s'`, and what else `s'` keeps of `s`. -/
def KsOut (s₀ s : State) (n : Nat) (s' : State) : Prop :=
  (∀ k < 64 * n, s'.mem (off (cx s₀) (672 + k)) =
    (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (off (cx s₀) 608)) (k / 64)))).getD (k % 64) 0) ∧
  (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
  Frame [sub s₀ 64 384, sub s₀ 608 576] s.mem s'.mem

section
variable {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀)
  (hrdi : s.gpr .rdi = off (cx s₀) 608) (hwr : s.wr = s₀.wr)

theorem eS : Stitch.stA (cx s₀ + BitVec.ofNat 64 544) = off (cx s₀) 608 := by
  rw [off_eq]; simp only [Stitch.stA, Offset.add_add]

theorem eB : Stitch.bfA (cx s₀ + BitVec.ofNat 64 544) = off (cx s₀) 672 := by
  rw [off_eq]; simp only [Stitch.bfA, Offset.add_add]

theorem eA (k : Nat) : Stitch.bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k = off (cx s₀) (672 + k) := by
  rw [off_eq]; simp only [Stitch.bfA, Offset.add_add]

/-- The regions `twoKsR` and `fourKsR` write: the state's copy and `buf`. -/
abbrev wKs (s₀ : State) : List Region :=
  [stR (Stitch.stA (cx s₀ + BitVec.ofNat 64 544)), bufR (Stitch.bfA (cx s₀ + BitVec.ofNat 64 544))]

include hp hwr in
theorem wKs_covers : Covers (wKs s₀) s.wr := covers_sub hp hwr _ (by
  intro r hr
  simp only [wKs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨608, by rw [eS], by show 608 + 64 ≤ 1696; omega⟩
  · exact ⟨672, by rw [eB], by show 672 + 320 ≤ 1696; omega⟩)

theorem wKs_frame {m m' : Mem} (h : Frame (wKs s₀) m m') : Frame [sub s₀ 64 384, sub s₀ 608 576] m m' :=
  h.sub fun r hr => by
    simp only [wKs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 608 576, by simp, by rw [eS]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨sub s₀ 608 576, by simp, by rw [eB]; exact sub_sub s₀ (by omega) (by lit_omega) (by lit_omega)⟩

include hp hr15 hrdi hwr in
/-- `twoKsR` with looped rounds: two blocks, for fewer than 512 bytes. -/
theorem twoKsS_ok (vl : Bool) (hL : (s.gpr .r13).toNat < 512) :
    WP isa (twoKsR (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 1 1))) s (KsOut s₀ s 2) := by
  have hw := wKs_covers hp hwr
  have hn : (twoKsR (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 1 1))).noCalls = true := by
    cases vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := wKs s₀)
    (twoKsRN_ok (rounds10S_roundsOk vl (.inl rfl)) (s := s.withRegions [] (wKs s₀)) (c := cx s₀) hr15
      (by rw [State.withRegions_gpr, hrdi, eS]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, -, g₀, -, -⟩ := hP
  refine ⟨fun k hk => ?_, fun r h₁ h₂ h₃ h₄ => ?_, rd', wr', wKs_frame f'⟩
  · have ks' : ∀ k < 128, s'.mem (Stitch.bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] (wKs s₀)).mem
          (Stitch.stA (cx s₀ + BitVec.ofNat 64 544)))
          (VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf (xCtr ((s.withRegions [] (wKs s₀)).gpr .r13)).toNat
            (k / 64))))).getD (k % 64) 0 := ks₀
    have := ks' k (by omega)
    rw [eA, State.withRegions_mem, eS, State.withRegions_gpr, xCtr_eq,
      show (s.gpr .r13).toNat / 512 = 0 by omega] at this
    have hc : VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf (BitVec.ofNat 32 (1 + 8 * 0)).toNat (k / 64) = k / 64 := by
      simp only [VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf, Nat.mul_zero, Nat.add_zero,
        show (BitVec.ofNat 32 1).toNat = 1 from rfl]
      split <;> omega
    rw [hc] at this
    exact this
  · have := (g₀ r h₁ h₂ h₃ h₄ : s'.gpr r = (s.withRegions [] (wKs s₀)).gpr r)
    rwa [State.withRegions_gpr] at this

include hp hr15 hrdi hwr in
/-- `fourKsR` with looped rounds: four blocks, for fewer than 512 bytes. -/
theorem fourKsS_ok (vl : Bool) (hL : (s.gpr .r13).toNat < 512) :
    WP isa (fourKsR (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 2 1))) s (KsOut s₀ s 4) := by
  have hw := wKs_covers hp hwr
  have hn : (fourKsR (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 2 1))).noCalls = true := by
    cases vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := wKs s₀)
    (fourKsRN_ok (rounds10S_roundsOk vl (.inr rfl)) (s := s.withRegions [] (wKs s₀)) (c := cx s₀) hr15
      (by rw [State.withRegions_gpr, hrdi, eS]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, -, g₀, -, -⟩ := hP
  refine ⟨fun k hk => ?_, fun r h₁ h₂ h₃ h₄ => ?_, rd', wr', wKs_frame f'⟩
  · have ks' : ∀ k < 256, s'.mem (Stitch.bfA (cx s₀ + BitVec.ofNat 64 544) + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] (wKs s₀)).mem
          (Stitch.stA (cx s₀ + BitVec.ofNat 64 544)))
          (VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4 (1 + 8 * (((s.withRegions [] (wKs s₀)).gpr .r13).toNat / 512))
            (k / 64))))).getD (k % 64) 0 := ks₀
    have := ks' k (by omega)
    rw [eA, State.withRegions_mem, eS, State.withRegions_gpr, show (s.gpr .r13).toNat / 512 = 0 by omega] at this
    have hc : VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4 (1 + 8 * 0) (k / 64) = k / 64 := by
      simp only [VG.Proof.ChaCha20.X86_64.Avx2Tail.cOf4]
      split <;> omega
    rw [hc] at this
    exact this
  · have := (g₀ r h₁ h₂ h₃ h₄ : s'.gpr r = (s.withRegions [] (wKs s₀)).gpr r)
    rwa [State.withRegions_gpr] at this

end

/-! ## Six blocks -/

section
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts pairs_ok pairsCode constPairs constPairs_le tPairs tPairs_le
  tconsts_eq consts_eq consts_mem tincs_mem storeAll storeAll_frame plus plus_block vz_ok)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM3 Incs)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx regn baseR bsize S0)
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch (setup3_ok0 out3_ok movReg_ok)

/-- The regions `threeKs` writes, from `c`: the state's copy, `buf`, and the
six blocks. -/
abbrev w3 (c : Addr) : List Region :=
  [stR (c + BitVec.ofNat 64 608), bufR (c + BitVec.ofNat 64 128), ⟨c + BitVec.ofNat 64 672, 384⟩]

/-- Where `Avx2Tail`'s code for three sets runs in `threeKs`: the state at
`rdi`, `buf` at `r9`, and up to 384 bytes at `rsi`. -/
theorem ctx3 {c : Addr} {D : Nat} (hD : D ≤ 96) {s : State} (hrdi : s.gpr .rdi = c + BitVec.ofNat 64 608)
    (hr9 : s.gpr .r9 = c + BitVec.ofNat 64 128) (hrsi : s.gpr .rsi = c + BitVec.ofNat 64 672)
    (hwr : s.wr = w3 c) : Ctx D s := by
  have r0 : regn D s 0 = stR (c + BitVec.ofNat 64 608) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn D s 1 = bufR (c + BitVec.ofNat 64 128) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : regn D s 2 = ⟨c + BitVec.ofNat 64 672, 4 * D⟩ := by simp only [regn, baseR, bsize, hrsi]
  have d01 : (regn D s 0).Disjoint (regn D s 1) := by
    rw [r0, r1]; exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
  have d02 : (regn D s 0).Disjoint (regn D s 2) := by
    rw [r0, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by omega)
  have d12 : (regn D s 1).Disjoint (regn D s 2) := by
    rw [r1, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by omega)
  refine ⟨fun b i n hb3 h hn => ?_, fun b b' hb hb' ne => ?_, by omega⟩
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨stR (c + BitVec.ofNat 64 608), by rw [hwr]; simp,
        Offset.contains_base _ (by omega) (by lit_omega)⟩
    · rw [r1]; exact ⟨bufR (c + BitVec.ofNat 64 128), by rw [hwr]; simp,
        Offset.contains_base _ (by omega) (by lit_omega)⟩
    · rw [r2]; exact ⟨⟨c + BitVec.ofNat 64 672, 384⟩, by rw [hwr]; simp,
        Offset.contains_base _ (by omega) (by omega)⟩
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · exact absurd rfl ne
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl ne
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl ne

theorem threeKs_eq (vl : Bool) : threeKs vl =
    .seq (.block (ptr .rcx .r15 128 ++ (ptr .rsi .r15 672 ++ (pairsCode tPairs ++ (pairsCode constPairs ++
      (([.mov .r9 (.reg .rcx)] : List Instr) ++ Impl.ChaCha20.X86_64.Avx2Tail.setup3))))))
    (.seq (rounds10 (Impl.ChaCha20.X86_64.Avx2Tail.roundsS vl 3 1))
      (.block ((Impl.ChaCha20.X86_64.Avx2Tail.addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++
        (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++ storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256))) ++
        ([.vop .vzeroupper] : List Instr)))) := by
  simp only [threeKs, tconsts_eq, VG.Proof.ChaCha20.X86_64.Avx2.consts_eq, List.append_assoc]

/-- `threeKs` on its own regions: six blocks from the state at `c + 608`
into `c + 672`. -/
theorem threeKsN_ok (vl : Bool) {c : Addr} {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = c + BitVec.ofNat 64 608) (hwr : s.wr = w3 c) :
    WP isa (threeKs vl) s fun t =>
      (∀ k < 384, t.mem (c + BitVec.ofNat 64 672 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (c + BitVec.ofNat 64 608)) (k / 64)))).getD
          (k % 64) 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb : bufR (c + BitVec.ofNat 64 128) ∈ s.wr := by rw [hwr]; simp
  rw [threeKs_eq]
  refine WP.seq (WP.block_append (WP.mono (ptr_ok .rcx .r15 (k := 128) (by lit_omega) s)
    fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_))
  refine WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := 672) (by lit_omega) s₁)
    fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  have rcx₂ : s₂.gpr .rcx = c + BitVec.ofNat 64 128 := by rw [g₂ _ (by decide), e₁, hr15, off_eq]
  refine WP.block_append (WP.mono (pairs_ok tPairs tPairs_le rcx₂ (by rw [wr₂, wr₁]; exact hb))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := c + BitVec.ofNat 64 128) constPairs constPairs_le (s := s₃)
    (by rw [g₃ _ (by decide), rcx₂]) (by rw [wr₃, wr₂, wr₁]; exact hb)) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.block_append (WP.mono (movReg_ok .r9 .rcx s₄) fun s₅ ⟨r9₅, g₅, x₅, y₅, m₅, rd₅, wr₅⟩ => ?_)
  have rdi₅ : s₅.gpr .rdi = c + BitVec.ofNat 64 608 := by
    rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hrdi]
  have r9₅' : s₅.gpr .r9 = c + BitVec.ofNat 64 128 := by rw [r9₅, g₄ _ (by decide), g₃ _ (by decide), rcx₂]
  have rsi₅ : s₅.gpr .rsi = c + BitVec.ofNat 64 672 := by
    rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), e₂, g₁ _ (by decide), hr15, off_eq]
  have wr₅' : s₅.wr = w3 c := by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hwr]
  have mm : s₅.mem = storeAll (c + BitVec.ofNat 64 128) constPairs (storeAll (c + BitVec.ofNat 64 128) tPairs s.mem) := by
    rw [m₅, m₄, m₃, m₂, m₁]
  have F₅ : Frame [bufR (c + BitVec.ofNat 64 128)] s.mem s₅.mem := by
    rw [mm]
    exact (storeAll_frame (List.mem_singleton_self _) _ tPairs_le _).trans
      (storeAll_frame (List.mem_singleton_self _) _ constPairs_le _)
  have S₅ : S0 s₅ = stateAt s.mem (c + BitVec.ofNat 64 608) := by
    simp only [S0, rdi₅]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame F₅ (by
      simpa using (Offset.disjoint c (d := 608) (n := 64) (e := 128) (k := 320) (Or.inr (by decide))
        (by decide) (by decide)))
  refine WP.mono (setup3_ok0 (ctx3 (by decide) rdi₅ r9₅' rsi₅ wr₅') (by rw [mm, r9₅']; exact consts_mem _ _)
    (by rw [mm, r9₅']; exact tincs_mem _ _)) fun s₆ ⟨hz₆, ym₆, m₆, g₆, rd₆, wr₆⟩ => ?_
  refine WP.seq (WP.mono (rounds10S3_ok vl hz₆ ym₆) fun s₇ ⟨hz₇, _, g₇, m₇, rd₇, wr₇⟩ => ?_)
  have g₇' : ∀ r, r ≠ .rax → s₇.gpr r = s₅.gpr r := fun r h => by rw [g₇ r h, g₆]
  have m₇' : s₇.mem = s₅.mem := by rw [m₇, m₆]
  refine WP.block_append (WP.mono (out3_ok (ctx3 (by decide) (by rw [g₇' _ (by decide), rdi₅])
    (by rw [g₇' _ (by decide), r9₅']) (by rw [g₇' _ (by decide), rsi₅]) (by rw [wr₇, wr₆, wr₅']))
    (by rw [m₇', g₇' _ (by decide), mm, r9₅']; exact tincs_mem _ _) hz₇) fun s₈ ⟨ks₈, _, g₈, rd₈, wr₈⟩ => ?_)
  refine WP.mono (vz_ok s₈) fun s₉ ⟨g₉, m₉, rd₉, wr₉⟩ => ⟨fun k hk => ?_, fun r h₁ h₂ h₃ h₄ => ?_,
    by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · have S₇ : S0 s₇ = S0 s₅ := by simp only [S0, g₇' .rdi (by decide), m₇']
    rw [m₉, ← rsi₅, ← g₇' _ (by decide), ks₈ k hk, S₇, S₅, ← S₅]
    simp only [S₅]
    rfl
  · rw [g₉, g₈, g₇' r h₁, g₅ r h₃, g₄ r h₁, g₃ r h₁, g₂ r h₄, g₁ r h₂]

end

/-! ## Eight blocks -/

section
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts pairs_ok pairsCode constPairs constPairs_le consts_mem storeAll
  storeAll_frame plus plus_block vz_ok setup_ok Holds RI M16 W2_frame slotsR incs_frame hiR_slots slotsR_sub
  Incs)
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch (finishK_ok)

/-- The regions `eightKs` writes, from `c`: the state's copy, `buf` at
`c + 64`, and the eight blocks at `c + 672`. -/
abbrev w8 (c : Addr) : List Region :=
  [stR (c + BitVec.ofNat 64 608), bufR (c + BitVec.ofNat 64 64), Stitch.kR (c + BitVec.ofNat 64 64)]

theorem eightKs_eq (vl : Bool) : eightKs vl =
    .seq (.block (ptr .rcx .r15 64 ++ (pairsCode constPairs ++ Impl.ChaCha20.X86_64.Avx2.setup)))
    (.seq (roundsK vl) (.block (Impl.ChaCha20.X86_64.Avx2.finishWith (storeRow kOff) ++
      ([.vop .vzeroupper] : List Instr)))) := by
  simp only [eightKs, VG.Proof.ChaCha20.X86_64.Avx2.consts_eq, List.append_assoc]; rfl

/-- `eightKs` on its own regions: the kernel's eight blocks from the state at
`c + 608` into `c + 672`. -/
theorem eightKsN_ok (vl : Bool) {c : Addr} {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = c + BitVec.ofNat 64 608) (hwr : s.wr = w8 c) :
    WP isa (eightKs vl) s fun t =>
      (∀ k < 512, t.mem (c + BitVec.ofNat 64 672 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt s.mem (c + BitVec.ofNat 64 608)) (k / 64)))).getD
          (k % 64) 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have buf : c + BitVec.ofNat 64 64 + BitVec.ofNat 64 608 = c + BitVec.ofNat 64 672 := by rw [Offset.add_add]
  have hst : stR (c + BitVec.ofNat 64 608) ∈ s.wr := by rw [hwr]; simp
  have hb : bufR (c + BitVec.ofNat 64 64) ∈ s.wr := by rw [hwr]; simp
  have hk : Stitch.kR (c + BitVec.ofNat 64 64) ∈ s.wr := by rw [hwr]; simp
  have dsb : (stR (c + BitVec.ofNat 64 608)).Disjoint (bufR (c + BitVec.ofNat 64 64)) :=
    Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
  have dsk : (stR (c + BitVec.ofNat 64 608)).Disjoint (Stitch.kR (c + BitVec.ofNat 64 64)) := by
    simp only [Stitch.kR, Stitch.kA, buf]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dbk : (bufR (c + BitVec.ofNat 64 64)).Disjoint (Stitch.kR (c + BitVec.ofNat 64 64)) := by
    simp only [Stitch.kR, Stitch.kA, buf]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  rw [eightKs_eq]
  refine WP.seq (WP.block_append (WP.mono (ptr_ok .rcx .r15 (k := 64) (by lit_omega) s)
    fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_))
  have rcx₁ : s₁.gpr .rcx = c + BitVec.ofNat 64 64 := by rw [e₁, hr15, off_eq]
  refine WP.block_append (WP.mono (pairs_ok (buf := c + BitVec.ofNat 64 64) constPairs constPairs_le rcx₁
    (by rw [wr₁]; exact hb)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  have rcx₂ : s₂.gpr .rcx = c + BitVec.ofNat 64 64 := by rw [g₂ _ (by decide), rcx₁]
  have rdi₂ : s₂.gpr .rdi = c + BitVec.ofNat 64 608 := by rw [g₂ _ (by decide), g₁ _ (by decide), hrdi]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have c₂ : Consts s₂.mem (c + BitVec.ofNat 64 64) := by rw [m₂, m₁]; exact consts_mem _ _
  refine WP.mono (setup_ok rdi₂ rcx₂ (by rw [wr₂']; exact hst) (by rw [wr₂']; exact hb) c₂)
    fun s₃ ⟨hh, h15, g₃, rd₃, wr₃, y₁, y₂, m₃⟩ => ?_
  have c₃ : Consts s₃.mem (c + BitVec.ofNat 64 64) := by rw [m₃]; exact c₂.w2 (by decide) y₁ y₂
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  refine WP.seq (WP.mono (Short.roundsK_ok vl hh h15 (by rw [g₃, rcx₂]) (by rw [wr₃']; exact hb) c₃.m8
    ⟨c₃.lo16, c₃.hi16⟩) fun s₄ ⟨v, h₄⟩ => ?_)
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₂.gpr r := fun r hr => by
    rw [h₄.gpr, RegUpd.gpr_setReg]; simp only [hr, ite_false]; rw [g₃]
  have wr₄ : s₄.wr = s.wr := by rw [h₄.wr, RegUpd.wr_setReg, wr₃']
  have F₄ : Frame [slotsR (c + BitVec.ofNat 64 64)] s₂.mem s₄.mem := by
    have f := h₄.frame
    rw [RegUpd.mem_setReg, m₃] at f
    exact (W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)).trans f
  have inc₄ : Incs (c + BitVec.ofNat 64 64) s₄.mem := incs_frame c₂.inc F₄ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.block_append (WP.mono (finishK_ok h₄.holds (st := c + BitVec.ofNat 64 608)
    (by rw [g₄ _ (by decide), rdi₂]) (by rw [g₄ _ (by decide), rcx₂]) (by rw [wr₄]; exact hst)
    (by rw [wr₄]; exact hb) (by rw [wr₄]; exact hk) inc₄ dsb dsk dbk) fun s₅ ⟨d₅, _, g₅, rd₅, wr₅⟩ => ?_)
  refine WP.mono (vz_ok s₅) fun s₆ ⟨g₆, m₆, rd₆, wr₆⟩ => ⟨fun k hk' => ?_, fun r h₁ h₂ h₃ h₄' => ?_,
    by rw [rd₆, rd₅, h₄.rd, RegUpd.rd_setReg, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄]⟩
  · have F₂ : Frame [bufR (c + BitVec.ofNat 64 64)] s.mem s₂.mem := by
      rw [m₂, m₁]; exact storeAll_frame (List.mem_singleton_self _) _ constPairs_le _
    have F : Frame [bufR (c + BitVec.ofNat 64 64)] s.mem s₄.mem := F₂.trans (F₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, slotsR_sub _⟩)
    have hS : stateAt s₄.mem (c + BitVec.ofNat 64 608) = stateAt s.mem (c + BitVec.ofNat 64 608) :=
      Proof.ChaCha20.X86_64.Xor.stateAt_frame F (by simpa using dsb)
    have hS₂ : stateAt s₂.mem (c + BitVec.ofNat 64 608) = stateAt s.mem (c + BitVec.ofNat 64 608) :=
      Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb)
    have := d₅ k hk'
    rw [Stitch.kA, buf, hS, hS₂, plus_block] at this
    rw [m₆, this]
  · rw [g₆, g₅, g₄ r h₁, g₂ r h₁, g₁ r h₂]

end

/-! ## The choice -/

section
variable {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀)
  (hrdi : s.gpr .rdi = off (cx s₀) 608) (hwr : s.wr = s₀.wr)

/-- Regions of `ctx[64, 448)` and `ctx[608, 1184)`. -/
abbrev KsRegs (s₀ : State) (w : List Region) : Prop :=
  ∀ r ∈ w, ∃ k n, r = sub s₀ k n ∧ ((64 ≤ k ∧ k + n ≤ 448) ∨ (608 ≤ k ∧ k + n ≤ 1184))

theorem frame_ks {m m' : Mem} {w : List Region} (hw : KsRegs s₀ w) (h : Frame w m m') :
    Frame [sub s₀ 64 384, sub s₀ 608 576] m m' :=
  h.sub fun r hr => by
    obtain ⟨k, n, rfl, h₁ | h₂⟩ := hw r hr
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ h₁.1 (by omega) (by lit_omega)⟩
    · exact ⟨sub s₀ 608 576, by simp, sub_sub s₀ h₂.1 (by omega) (by lit_omega)⟩

include hp hwr in
theorem covers_ks {w : List Region} (hw : KsRegs s₀ w) : Covers w s.wr :=
  covers_sub hp hwr _ fun r hr => by
    obtain ⟨k, n, rfl, h | h⟩ := hw r hr <;> exact ⟨k, rfl, by show k + n ≤ 1696; omega⟩

theorem w3_sub : KsRegs s₀ (w3 (cx s₀)) := by
  intro r hr
  simp only [w3, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨608, 64, by simp only [sub, off_eq], .inr ⟨by decide, by decide⟩⟩
  · exact ⟨128, 320, by simp only [sub, off_eq], .inl ⟨by decide, by decide⟩⟩
  · exact ⟨672, 384, by simp only [sub, off_eq], .inr ⟨by decide, by decide⟩⟩

theorem w8_sub : KsRegs s₀ (w8 (cx s₀)) := by
  intro r hr
  simp only [w8, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨608, 64, by simp only [sub, off_eq], .inr ⟨by decide, by decide⟩⟩
  · exact ⟨64, 320, by simp only [sub, off_eq], .inl ⟨by decide, by decide⟩⟩
  · exact ⟨672, 512, by simp only [Stitch.kR, Stitch.kA, sub, off_eq, Offset.add_add], .inr ⟨by decide, by decide⟩⟩

include hp hr15 hrdi hwr in
theorem threeKsS_ok (vl : Bool) : WP isa (threeKs vl) s (KsOut s₀ s 6) := by
  have hw : Covers (w3 (cx s₀)) s.wr := covers_ks hp hwr w3_sub
  have hn : (threeKs vl).noCalls = true := by cases vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := w3 (cx s₀))
    (threeKsN_ok vl (s := s.withRegions [] (w3 (cx s₀))) (c := cx s₀) hr15
      (by rw [State.withRegions_gpr, hrdi, off_eq]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, g₀, -, -⟩ := hP
  refine ⟨fun k hk => ?_, fun r h₁ h₂ h₃ h₄ => ?_, rd', wr', frame_ks w3_sub f'⟩
  · have this : s'.mem (cx s₀ + BitVec.ofNat 64 672 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] (w3 (cx s₀))).mem
          (cx s₀ + BitVec.ofNat 64 608)) (k / 64)))).getD (k % 64) 0 := ks₀ k (by omega)
    rw [Offset.add_add, State.withRegions_mem] at this
    rw [off_eq, this, off_eq]
  · have := (g₀ r h₁ h₂ h₃ h₄ : s'.gpr r = (s.withRegions [] (w3 (cx s₀))).gpr r)
    rwa [State.withRegions_gpr] at this

include hp hr15 hrdi hwr in
theorem eightKsS_ok (vl : Bool) : WP isa (eightKs vl) s (KsOut s₀ s 8) := by
  have hw : Covers (w8 (cx s₀)) s.wr := covers_ks hp hwr w8_sub
  have hn : (eightKs vl).noCalls = true := by cases vl <;> decide +kernel
  refine regionModel.wp_narrow (r := []) (w := w8 (cx s₀))
    (eightKsN_ok vl (s := s.withRegions [] (w8 (cx s₀))) (c := cx s₀) hr15
      (by rw [State.withRegions_gpr, hrdi, off_eq]) rfl)
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ rd' wr' f' hP => ?_
  obtain ⟨ks₀, g₀, -, -⟩ := hP
  refine ⟨fun k hk => ?_, fun r h₁ h₂ h₃ h₄ => ?_, rd', wr', frame_ks w8_sub f'⟩
  · have this : s'.mem (cx s₀ + BitVec.ofNat 64 672 + BitVec.ofNat 64 k) =
        (serialize (Spec.ChaCha20.block (ctr (stateAt (s.withRegions [] (w8 (cx s₀))).mem
          (cx s₀ + BitVec.ofNat 64 608)) (k / 64)))).getD (k % 64) 0 := ks₀ k (by omega)
    rw [Offset.add_add, State.withRegions_mem] at this
    rw [off_eq, this, off_eq]
  · have := (g₀ r h₁ h₂ h₃ h₄ : s'.gpr r = (s.withRegions [] (w8 (cx s₀))).gpr r)
    rwa [State.withRegions_gpr] at this

/-- `KsOut` from a state differing from `s` only in the flags. -/
theorem KsOut.of_flags {s₀ s t s' : State} {n : Nat} (h : KsOut s₀ t n s') (hg : t.gpr = s.gpr)
    (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : KsOut s₀ s n s' :=
  ⟨fun k hk => by rw [h.1 k hk, hm], fun r h₁ h₂ h₃ h₄ => by rw [h.2.1 r h₁ h₂ h₃ h₄, hg],
    by rw [h.2.2.1, hrd], by rw [h.2.2.2.1, hwr], by rw [← hm]; exact h.2.2.2.2⟩

set_option simprocs false in
/-- `cmp r13, n`: `CF` set below `n`, nothing else written. -/
theorem cmp13n_ok {n : Nat} (hn : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n)
    (hn64 : n < 2 ^ 64) (s : State) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      isa.eval .b t = some (decide ((s.gpr .r13).toNat < n)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  have en : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hn,
    Option.bind_some, RegUpd.cf_arithFlags, eval, en, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

include hp hr15 hrdi hwr in
/-- `ksShort` for 1 to 448 bytes: at least `64 + len` bytes of keystream. -/
theorem ksShort_ok (vl : Bool) (hr13 : s.gpr .r13 = s₀.gpr .r9) (hL : L s₀ ≤ 448) :
    WP isa (ksShort vl) s fun s' => ∃ n, 64 + L s₀ ≤ 64 * n ∧ KsOut s₀ s n s' := by
  have hl : (s.gpr .r13).toNat = L s₀ := by rw [hr13]
  unfold ksShort
  refine WP.seq (WP.mono (cmp13n_ok (n := 193) (by decide) (by decide) s) fun t ⟨c₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.ite _ c₁ (fun h => ?_) (fun h => ?_)
  · have h193 : L s₀ < 193 := by rw [← hl]; simpa using h
    refine WP.seq (WP.mono (cmp13n_ok (n := 65) (by decide) (by decide) t) fun u ⟨c₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have r15u : u.gpr .r15 = cx s₀ := by rw [g₂, g₁, hr15]
    have rdiu : u.gpr .rdi = off (cx s₀) 608 := by rw [g₂, g₁, hrdi]
    have wru : u.wr = s₀.wr := by rw [wr₂, wr₁, hwr]
    have r13u : (u.gpr .r13).toNat < 512 := by rw [g₂, g₁, hl]; omega
    refine WP.ite _ c₂ (fun h => ?_) (fun h => ?_)
    · have h65 : L s₀ < 65 := by rw [← hl, ← g₁]; simpa using h
      exact WP.mono (twoKsS_ok hp r15u rdiu wru vl r13u) fun s' h' =>
        ⟨2, by omega, h'.of_flags (by rw [g₂, g₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩
    · exact WP.mono (fourKsS_ok hp r15u rdiu wru vl r13u) fun s' h' =>
        ⟨4, by omega, h'.of_flags (by rw [g₂, g₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩
  · refine WP.seq (WP.mono (cmp13n_ok (n := 321) (by decide) (by decide) t) fun u ⟨c₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have r15u : u.gpr .r15 = cx s₀ := by rw [g₂, g₁, hr15]
    have rdiu : u.gpr .rdi = off (cx s₀) 608 := by rw [g₂, g₁, hrdi]
    have wru : u.wr = s₀.wr := by rw [wr₂, wr₁, hwr]
    refine WP.ite _ c₂ (fun h => ?_) (fun h => ?_)
    · have h321 : L s₀ < 321 := by rw [← hl, ← g₁]; simpa using h
      exact WP.mono (threeKsS_ok hp r15u rdiu wru vl) fun s' h' =>
        ⟨6, by omega, h'.of_flags (by rw [g₂, g₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩
    · exact WP.mono (eightKsS_ok hp r15u rdiu wru vl) fun s' h' =>
        ⟨8, by omega, h'.of_flags (by rw [g₂, g₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩

end

end VG.Proof.ChaCha20Poly1305.X86_64.Short

/-!
# ChaCha20-Poly1305 for short records (x86-64): the registers and the keystream

`Stitch.shortPre` saves the registers, moves the arguments, stores the
ChaCha20 state for counter 0 at `ctx + 608` and computes the keystream
(`ksShort_ok`): after it (`SP`) the one-time key is at `ctx + 672` and the
data's keystream at `ctx + 736`, and nothing but the context is written.
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt serialize keystream)
open VG.Spec.Poly1305 (bytesAt)

variable {e : Bool}

/-- After `shortPre`: the arguments where `moves` put them, the registers
saved, only the context written, and the keystream at `ctx + 672`. -/
structure SP (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rcx
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀] s₀.mem s.mem
  key : bytesAt s.mem (off (cx s₀) 672) 32 = otk s₀
  ks : ∀ k < L s₀, s.mem (off (cx s₀) (736 + k)) =
    (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0

theorem shortPre_eq (vl : Bool) : shortPre vl =
    .seq (.block ((save ++ moves) ++ (initStateQ 608 ++ ptr .rdi .r15 608))) (ksShort vl) := by
  simp only [shortPre, List.append_assoc]

theorem frame_work {s₀ : State} {k n : Nat} (h : k + n ≤ 1696) {m m' : Mem} (hf : Frame [sub s₀ k n] m m') :
    Frame [workR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s₀, by simp, sub_sub s₀ (Nat.zero_le _) (by lit_omega) (by lit_omega)⟩

theorem shortPre_ok (vl : Bool) {s₀ : State} (hp : APre e s₀) (hL : L s₀ ≤ 448) :
    WP isa (shortPre vl) (entryS s₀) (SP s₀) := by
  rw [shortPre_eq]
  refine WP.seq (WP.block_append (WP.mono (saveMoves_ok hp)
    fun s₁ ⟨e15, e12, ebx, ebp, e14, e13, g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_))
  have edi : s₁.gpr .rdi = kp s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have esi : s₁.gpr .rsi = np s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ersp : s₁.gpr .rsp = s₀.gpr .rsp := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hc₁ : CtxOk (cx s₀) (kp s₀) (np s₀) s₁ := by
    refine ⟨fun a w h => by rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩, fun a w ha => ?_, fun a w ha => ?_⟩
    · rw [rd₁, wr₁]
      exact ⟨kR s₀, by simp [hp.k_rd], by rw [off_eq]; exact Offset.contains_base _ ha (by lit_omega)⟩
    · rw [rd₁, wr₁]
      exact ⟨nR s₀, by simp [hp.n_rd], by rw [off_eq]; exact Offset.contains_base _ ha (by lit_omega)⟩
  refine WP.block_append (WP.mono (initStateQ_ok (o := 608) (by lit_omega) e15 edi esi hc₁
    (hp.c_k.sub_left (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega)))
    (hp.c_n.sub_left (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega))))
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  refine WP.mono (ptr_ok .rdi .r15 (k := 608) (by lit_omega) s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  have g₃' : ∀ r, r ≠ .rax → r ≠ .rdi → s₃.gpr r = s₁.gpr r := fun r h₁ h₂ => by rw [g₃ r h₂, g₂ r h₁]
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃' _ (by decide) (by decide), e15]
  have st₃ : stateAt s₃.mem (off (cx s₀) 608) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) :=
    stateAt_initState hp f₁ fun i hi => by rw [m₃]; exact w₂ i hi
  refine WP.mono (ksShort_ok hp r15₃ (by rw [e₃, g₂ _ (by decide), e15]) (by rw [wr₃, wr₂, wr₁]) vl
    (by rw [g₃' _ (by decide) (by decide), e13]) hL) fun s₄ ⟨n, hn, ks₄, g₄, rd₄, wr₄, f₄⟩ => ?_
  have g₄' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → r ≠ .rsi → r ≠ .rdi → s₄.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₄ r h₁ h₂ h₃ h₄, g₃' r h₁ h₅]
  have f₂' : Frame [sub s₀ 608 64] s₁.mem s₃.mem := by rw [m₃]; exact f₂
  -- The keystream from counter 0, byte by byte.
  have hks : ∀ k < 64 + L s₀, s₄.mem (off (cx s₀) (672 + k)) =
      (keystream (Spec.ChaCha20.initState (K s₀) 0 (N s₀)) (64 + L s₀)).getD k 0 := fun k hk => by
    rw [ks₄ k (by omega), st₃, VG.Proof.ChaCha20.keystream_getD _ hk]
  refine ⟨by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), e15],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), e12],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), ebx],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), ebp],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), e14],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), e13],
    by rw [g₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), ersp],
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], ?_, ?_, ?_, fun k hk => ?_⟩
  · refine (sv₁.frame f₂' ?_).frame f₄ ?_
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega),
        sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · refine (frame_work (k := 0) (n := 48) (by lit_omega) f₁).trans
      ((frame_work (k := 608) (n := 64) (by lit_omega) f₂').trans (f₄.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub_sub s₀ (Nat.zero_le _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub_sub s₀ (Nat.zero_le _) (by lit_omega) (by lit_omega)⟩
  · show _ = Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
    rw [← keystream_otk (K s₀) (N s₀) (n := 64 + L s₀) (by omega)]
    apply List.ext_getElem
    · simp [bytesAt, VG.Proof.ChaCha20.length_keystream]; omega
    · intro i h₁ h₂
      simp only [bytesAt, List.length_map, List.length_range] at h₁
      simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take]
      rw [show off (cx s₀) 672 + BitVec.ofNat 64 i = off (cx s₀) (672 + i) by
        rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], hks i (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
          rw [VG.Proof.ChaCha20.length_keystream]; omega), Option.getD_some]
      rfl
  · rw [show 736 + k = 672 + (64 + k) by omega, hks _ (by omega), keystream_shift _ _ hk (by omega)]

end VG.Proof.ChaCha20Poly1305.X86_64.Short

/-!
# ChaCha20-Poly1305 for short records (x86-64): the padded blocks

`Stitch.padBuild o` builds the `rdx` (1 to 15) bytes at `rsi`, padded with
zeros, in `r9:rax` as `padTail` does (`padInit_ok`, `padIte_ok`), and stores
them at `ctx + o` (`padBuild_ok`): `padAad` for the additional data at
`ctx + 576`, `padData` for the data's last bytes at `ctx + 624`.
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)
open VG.Impl.ChaCha20.X86_64 (at_)

variable {e : Bool}

/-- `pad16` of 1 to 15 bytes. -/
theorem pad16_short {xs : List Byte} {t : Nat} (hl : xs.length = t) (ht0 : 0 < t) (ht : t < 16) :
    pad16 xs = List.replicate (16 - t) 0 := by
  rw [pad16, ite_eq_right (by omega), hl, Nat.mod_eq_of_lt ht]

theorem padBuild_eq (o : Nat) : padBuild o =
    .seq (.block [.alu32 .xor .r9 (.reg .r9), .alu .cmp .rdx (.imm 8)])
      (.seq padIte (.block (ptr .rsi .r15 o ++ ([.store (at_ .rsi 0) .rax, .store (at_ .rsi 8) .r9] : List Instr)))) :=
  rfl

/-- The `t` (1 to 15) bytes at `Q`, padded, at `ctx + o`. -/
theorem padBuild_ok {s₀ : State} (hp : APre e s₀) (o o8 : Nat) (h8 : o8 = o + 8) (ho : o + 16 ≤ 1696)
    {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16) (hrsi : s.gpr .rsi = Q)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s.gpr .r15 = cx s₀) (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hsrc8 : 8 ≤ t → InRegions (s.rd ++ s.wr) Q 8) :
    WP isa (padBuild o) s fun s' =>
      bytesAt s'.mem (off (cx s₀) o) 16 = bytesAt s.mem Q t ++ pad16 (bytesAt s.mem Q t) ∧
      Frame [sub s₀ o 16] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [padBuild_eq]
  refine WP.seq (WP.mono (padInit_ok ht hrdx) fun s₁ ⟨r9₁, cf₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = Q := by rw [g₁ _ (by decide), hrsi]
  have rdx₁ : s₁.gpr .rdx = BitVec.ofNat 64 t := by rw [g₁ _ (by decide), hrdx]
  refine WP.seq (WP.mono (padIte_ok ht0 ht r9₁ cf₁ rsi₁ rdx₁
    (by rw [rd₁, wr₁]; exact hsrc) (fun h => by rw [rd₁, wr₁]; exact hsrc8 h)) fun s₃ h₃ => ?_)
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → s₃.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃' h₄ h₅ => by rw [h₃.keep r h₁ h₂ h₃' h₄ h₅, g₁ r h₄]
  have r15₃ : s₃.gpr .r15 = cx s₀ := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr15]
  refine WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := o) (by omega) s₃) fun s₄ ⟨e₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.mono (padStore_ok hp o o8 h8 ho (by rw [e₄, r15₃]) (by rw [wr₄, h₃.wr, wr₁, hwr]))
    fun s₅ ⟨g₅, rd₅, wr₅, m₅⟩ => ⟨?_, ?_, fun r h₁ h₂ h₃' h₄ h₅' => by rw [g₅, g₄ r h₅', g₃ r h₁ h₂ h₃' h₄ h₅'],
      by rw [rd₅, rd₄, h₃.rd, rd₁], by rw [wr₅, wr₄, h₃.wr, wr₁]⟩
  · have mm : s₅.mem = (s.mem.writeW (off (cx s₀) o) (s₃.gpr .rax)).writeW (off (cx s₀) o8) (s₃.gpr .r9) := by
      rw [m₅, m₄, h₃.mem, m₁, g₄ .rax (by decide), g₄ .r9 (by decide)]
    rw [pad16_short (VG.Proof.Poly1305.length_bytesAt _ _ _) ht0 ht]
    refine padded_bytes (s₀ := s₀) ht fun j hj => ?_
    apply BitVec.eq_of_toNat_eq
    have hlo : (s₃.gpr .rax).toNat = tv (tb s.mem Q) 0 t % 2 ^ 64 := by rw [h₃.lo, m₁]
    have hhi : (s₃.gpr .r9).toNat = tv (tb s.mem Q) 0 t / 2 ^ 64 := by rw [h₃.hi, m₁]
    rw [mm, stored_bytes (tb_lt s.mem Q) s.mem (cx s₀) o o8 h8 (by omega) hlo hhi hj]
    split <;> rfl
  · have mm : s₅.mem = (s.mem.writeW (off (cx s₀) o) (s₃.gpr .rax)).writeW (off (cx s₀) o8) (s₃.gpr .r9) := by
      rw [m₅, m₄, h₃.mem, m₁, g₄ .rax (by decide), g₄ .r9 (by decide)]
    rw [mm]
    subst h8
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by omega) ho)
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) ho)

set_option simprocs false in
theorem movTest_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .rbp), .alu .test .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr .rdx = s.gpr .rbp ∧ isa.eval .e s' = some (s.gpr .rbp == 0) ∧
      (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, eval,
    BitVec.and_self, ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', true_and,
    and_true]
  exact fun q hq => by simp only [hq, ite_false]

theorem beq_zero_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact h0 this

/-- The additional data, if any, padded at `ctx + 576`. -/
theorem padAad_ok {s₀ : State} (hp : APre e s₀) (hA : AL s₀ < 16) {s : State} (hr15 : s.gpr .r15 = cx s₀)
    (hrbx : s.gpr .rbx = ad s₀) (hrbp : s.gpr .rbp = s₀.gpr .rcx) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa padAad s fun s' =>
      (AL s₀ ≠ 0 → bytesAt s'.mem (off (cx s₀) 576) 16 =
        bytesAt s.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s.mem (ad s₀) (AL s₀))) ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hAL : AL s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  refine WP.seq (WP.mono (movTest_ok s) fun t ⟨rdx₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hrbp, show s₀.gpr .rcx = BitVec.ofNat 64 (AL s₀) by simp [AL], beq_zero_ofNat hAL] at z₁
  refine WP.ite _ z₁ (fun h => ?_) (fun h => ?_)
  · have h0 : AL s₀ = 0 := by simpa using h
    exact WP.block_nil ⟨fun h' => absurd h0 h', by rw [m₁]; exact Frame.refl _ _,
      fun r _ _ h₃ _ _ => g₁ r h₃, rd₁, wr₁⟩
  · have h0 : AL s₀ ≠ 0 := by simpa using h
    refine WP.seq (WP.mono (Stitch.movReg_ok .rsi .rbx t) fun u ⟨rsi₂, g₂, x₂, y₂, m₂, rd₂, wr₂⟩ => ?_)
    refine WP.mono (padBuild_ok hp 576 584 rfl (by decide) (t := AL s₀) (Q := ad s₀) (Nat.pos_of_ne_zero h0) hA
      (by rw [rsi₂, g₁ _ (by decide), hrbx]) (by rw [g₂ _ (by decide), rdx₁, hrbp]; simp [AL])
      (by rw [g₂ _ (by decide), g₁ _ (by decide), hr15]) (by rw [wr₂, wr₁, hwr])
      (fun j hj => by
        rw [rd₂, wr₂, rd₁, wr₁, hrd]
        exact ⟨aR s₀, List.mem_append_left _ hp.a_rd, Offset.contains_base _ (by omega) (by omega)⟩)
      (fun h8 => by
        rw [rd₂, wr₂, rd₁, wr₁, hrd]
        exact ⟨aR s₀, List.mem_append_left _ hp.a_rd, by
          have := Offset.contains_base (ad s₀) (d := 0) (n := 8) (k := AL s₀) (by omega) (by decide)
          simpa using this⟩))
      fun s' ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ⟨fun _ => by rw [b₃, m₂, m₁], by rw [m₂, m₁] at f₃; exact f₃,
        fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, g₂ r h₅, g₁ r h₃], by rw [rd₃, rd₂, rd₁],
        by rw [wr₃, wr₂, wr₁]⟩

/-- The data's last bytes past its whole blocks, if any, padded at `ctx + 624`. -/
theorem padData_ok {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀)
    (hr14 : s.gpr .r14 = dp s₀) (hr13 : s.gpr .r13 = s₀.gpr .r9) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa padData s fun s' =>
      (L s₀ % 16 ≠ 0 → bytesAt s'.mem (off (cx s₀) 624) 16 =
        bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
          pad16 (bytesAt s.mem (dp s₀) (L s₀))) ∧
      Frame [sub s₀ 624 16] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hr : MacRegs .r14 .r13 := ⟨.inr rfl, .inr rfl⟩
  refine WP.seq (WP.mono (macTail_ok hr hL (by rw [hr13]; simp [L])) fun t ⟨rdx₁, z₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.ite (decide (L s₀ % 16 = 0)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_)
  · have h0 : L s₀ % 16 = 0 := by simpa using h
    exact WP.block_nil ⟨fun h' => absurd h0 h', by rw [m₁]; exact Frame.refl _ _,
      fun r _ _ h₃ _ _ => g₁ r h₃, rd₁, wr₁⟩
  · have h0 : L s₀ % 16 ≠ 0 := by simpa using h
    refine WP.seq (WP.mono (macD_ok hr t) fun u ⟨rsi₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
    have hQ : u.gpr .rsi = dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16)) := by
      rw [rsi₂, rdx₁, g₁ _ (by decide), g₁ _ (by decide), hr13, hr14]
      have e : L s₀ = 16 * (L s₀ / 16) + L s₀ % 16 := (Nat.div_add_mod _ _).symm
      have e' : s₀.gpr .r9 = BitVec.ofNat 64 (16 * (L s₀ / 16)) + BitVec.ofNat 64 (L s₀ % 16) := by
        rw [← BitVec.ofNat_add, ← e]; simp [L]
      rw [e', BitVec.add_sub_cancel, BitVec.add_comm]
    have hin : ∀ j, j + 1 ≤ L s₀ % 16 → InRegions (u.rd ++ u.wr) (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16) + j)) 1 :=
      fun j hj => by
        rw [rd₂, wr₂, rd₁, wr₁, hrd, hwr]
        exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (padBuild_ok hp 624 632 rfl (by decide) (t := L s₀ % 16)
      (Q := dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ (by decide)) hQ
      (by rw [g₂ _ (by decide), rdx₁]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hr15]) (by rw [wr₂, wr₁, hwr])
      (fun j hj => by rw [Offset.add_add]; exact hin j (by omega))
      (fun h8 => by
        rw [rd₂, wr₂, rd₁, wr₁, hrd, hwr]
        exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s' ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ⟨fun _ => ?_, by rw [m₂, m₁] at f₃; exact f₃,
        fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, g₂ r h₅, g₁ r h₃], by rw [rd₃, rd₂, rd₁],
        by rw [wr₃, wr₂, wr₁]⟩
    rw [b₃, m₂, m₁, pad16_short (VG.Proof.Poly1305.length_bytesAt _ _ _) (Nat.pos_of_ne_zero h0)
      (Nat.mod_lt _ (by decide)), pad16, ite_eq_right (by rw [VG.Proof.Poly1305.length_bytesAt]; exact h0),
      VG.Proof.Poly1305.length_bytesAt]

end VG.Proof.ChaCha20Poly1305.X86_64.Short

/-!
# ChaCha20-Poly1305 for short records (x86-64): the tag

`Stitch.macSetup` and `Stitch.macBody` compute the tag of the padded
additional data, the data's whole blocks, its padded last bytes and the
lengths into `r11:rbx` (`mac_ok`), with the scalar Poly1305's code
(`absorbAt`, `reduce`): each block absorbed keeps `Acc` with the message so
far (`absorbAt_acc`, from `absorbAt_ok`), the data's blocks in a loop counted
in `rdi` (`cntLoop_ok`).
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20Poly1305.X86_64.Stitch (Acc Key rN mod_step cntLoop_ok addImm_ok Only)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs absorbAt_ok Keeps ofInt_natCast)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (absorbAll)
open VG.Impl.ChaCha20.X86_64 (at_)

/-- Absorbing the 16 bytes at `b + d`: `Acc` with them appended. -/
theorem absorbAt_acc {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {s : State} (h : Acc R0 R1 X s)
    {b : Reg} (hb : b ≠ .r11) {d : Nat}
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 d) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (Impl.Poly1305.X86_64.absorbAt b d 1)) s fun s' =>
      Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem (s.gpr b + BitVec.ofNat 64 d) 16)) s' ∧
        Keeps absorbRegs s s' := by
  have hq : R1.toNat / 4 < 2 ^ 58 := by have := hk.r1; omega
  rw [← ofInt_natCast] at h0 h8
  refine WP.mono (absorbAt_ok s hb (.inr rfl) (q := R1.toNat / 4) (by rw [h.r8]; exact hk.r0)
    (by rw [h.r9]; have := hk.r1_mod; omega) hq h.r10 h0 h8) fun s' ⟨hv, k⟩ => ?_
  obtain ⟨hv, h2⟩ := hv h.h2
  refine ⟨⟨by rw [k.1 _ (by decide), h.r8], by rw [k.1 _ (by decide), h.r9],
    by rw [k.1 _ (by decide)]; exact h.r10, h2, ?_⟩, k⟩
  have eM : Proof.Poly1305.X86_64.word s.mem (s.gpr b) d +
      2 ^ 64 * Proof.Poly1305.X86_64.word s.mem (s.gpr b) (d + 8) + 2 ^ 128 * (1 : BitVec 32).toNat =
      leNum (bytesAt s.mem (s.gpr b + BitVec.ofNat 64 d) 16 ++ [0x01]) := by
    rw [VG.Proof.Poly1305.leNum_append, VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.leNum_bytesAt_16,
      show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    simp only [Proof.Poly1305.X86_64.word, ofInt_natCast]
    rfl
  rw [VG.Proof.Poly1305.absorbAll_block (by rw [VG.Proof.Poly1305.length_bytesAt]; decide)
    (by rw [VG.Proof.Poly1305.length_bytesAt]), hv, h.r8, h.r9, eM]
  exact mod_step h.val

/-- `Acc` reads only Poly1305's registers. -/
theorem acc_keep6 {R0 R1 : BitVec 64} {X : Nat} {s s' : State} (h : Acc R0 R1 X s)
    (e8 : s'.gpr .r8 = s.gpr .r8) (e9 : s'.gpr .r9 = s.gpr .r9) (e10 : s'.gpr .r10 = s.gpr .r10)
    (e11 : s'.gpr .r11 = s.gpr .r11) (ebx : s'.gpr .rbx = s.gpr .rbx) (ebp : s'.gpr .rbp = s.gpr .rbp) :
    Acc R0 R1 X s' :=
  ⟨by rw [e8]; exact h.r8, by rw [e9]; exact h.r9, by rw [e10]; exact h.r10, by rw [ebp]; exact h.h2,
    by simp only [hval, e11, ebx, ebp]; exact h.val⟩

/-- The bytes after the first `16 i` absorbed: the first `16 (i + 1)`. -/
theorem absorbAll_next (r X : Nat) (m : Mem) (q : Addr) (i : Nat) :
    absorbAll r (absorbAll r X (bytesAt m q (16 * i))) (bytesAt m (q + BitVec.ofNat 64 (16 * i)) 16) =
      absorbAll r X (bytesAt m q (16 * (i + 1))) := by
  rw [Nat.mul_add, Nat.mul_one, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]

/-- The `n` whole blocks at `q` (`rsi`), counted in `rdi`. -/
theorem blocks_acc {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {q : Addr} {n : Nat} (hn : 0 < n)
    (hn64 : n < 2 ^ 64) {s : State} (h : Acc R0 R1 X s) (hq : s.gpr .rsi = q)
    (hd : s.gpr .rdi = BitVec.ofNat 64 n)
    (hin : ∀ k w, k + w ≤ 16 * n → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 k) w) :
    WP isa (cntLoop (.block (Impl.Poly1305.X86_64.absorbAt .rsi 0 1)) [.alu .add .rsi (.imm 16)]) s fun s' =>
      Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * n))) s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r := by
  let I : Nat → State → Prop := fun i t =>
    Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * i))) t ∧ t.gpr .rsi = q + BitVec.ofNat 64 (16 * i) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → t.gpr r = s.gpr r
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide
  refine WP.mono (cntLoop_ok I hn hn64 (fun i hi t ⟨ha, hr, hm, hrd, hwr, hg⟩ => ?_)
    (fun i t t' ⟨ha, hr, hm, hrd, hwr, hg⟩ g x y m rd wr => ⟨?_, by rw [g _ (by decide), hr],
      by rw [m, hm], by rw [rd, hrd], by rw [wr, hwr], fun r h₁ h₂ h₃ => by rw [g r h₃, hg r h₁ h₂ h₃]⟩)
    ⟨by rw [Nat.mul_zero, show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]; exact h, by rw [hq, Nat.mul_zero, BitVec.add_zero], rfl, rfl, rfl, fun _ _ _ _ => rfl⟩ hd)
    fun t ⟨⟨ha, _, hm, hrd, hwr, hg⟩, _⟩ => ⟨ha, hm, hrd, hwr, hg⟩
  · have i0 : InRegions (t.rd ++ t.wr) (t.gpr .rsi + BitVec.ofNat 64 0) 8 := by
      rw [hrd, hwr, hr, Offset.add_add]; exact hin _ _ (by omega)
    have i8 : InRegions (t.rd ++ t.wr) (t.gpr .rsi + BitVec.ofNat 64 (0 + 8)) 8 := by
      rw [hrd, hwr, hr, Offset.add_add]; exact hin _ _ (by omega)
    refine WP.seq (WP.mono (absorbAt_acc hk ha (by decide) i0 i8) fun t₁ ⟨a₁, k₁⟩ => ?_)
    refine WP.mono (addImm_ok .rsi 16 t₁) fun t₂ ⟨r₂, o₂⟩ => ?_
    have g₂ : ∀ r, r ∉ absorbRegs → r ≠ .rsi → t₂.gpr r = t.gpr r := fun r h₁ h₂ => by
      rw [o₂.1 r h₂, k₁.1 r h₁]
    rw [hm, hr, Offset.add_add, Nat.add_zero, absorbAll_next] at a₁
    refine ⟨⟨acc_keep6 a₁ (o₂.1 .r8 (by decide)) (o₂.1 .r9 (by decide)) (o₂.1 .r10 (by decide))
      (o₂.1 .r11 (by decide)) (o₂.1 .rbx (by decide)) (o₂.1 .rbp (by decide)), ?_,
      by rw [o₂.2.2.2.1, k₁.2.1, hm], by rw [o₂.2.2.2.2.1, k₁.2.2.1, hrd],
      by rw [o₂.2.2.2.2.2, k₁.2.2.2, hwr], fun r h₁ h₂ h₃ => by rw [g₂ r h₁ h₂, hg r h₁ h₂ h₃]⟩,
      g₂ _ (by decide) (by decide)⟩
    rw [r₂, k₁.1 _ (by decide), hr, e16, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega]
  · exact acc_keep6 ha (g .r8 (by decide)) (g .r9 (by decide)) (g .r10 (by decide)) (g .r11 (by decide))
      (g .rbx (by decide)) (g .rbp (by decide))

section
variable {e : Bool}

/-- The memory `macSetup` leaves: the lengths block and the stashed registers. -/
def setupMem (c : Addr) (s : State) : Mem :=
  (((((s.mem.writeW (off c 592) (s.gpr .rbp)).writeW (off c 600) (s.gpr .r13)).writeW (off c 520)
    (s.gpr .r12)).writeW (off c 528) (s.gpr .r13)).writeW (off c 536) (s.gpr .r14)).writeW (off c 544) (s.gpr .rbp)

set_option simprocs false in
theorem macSetup_ok {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block macSetup) s fun s' =>
      s'.gpr .rcx = cx s₀ ∧ s'.gpr .rsi = s.gpr .r14 ∧ s'.gpr .rdi = s.gpr .r13 >>> 4 ∧
      s'.gpr .r8 = s.mem.readW (off (cx s₀) 672) 64 &&& Proof.Poly1305.X86_64.M0 ∧
      s'.gpr .r9 = s.mem.readW (off (cx s₀) 680) 64 &&& Proof.Poly1305.X86_64.M1 ∧
      s'.gpr .r10 = ((s.mem.readW (off (cx s₀) 680) 64 &&& Proof.Poly1305.X86_64.M1) >>> 2) +
        (s.mem.readW (off (cx s₀) 680) 64 &&& Proof.Poly1305.X86_64.M1) ∧
      s'.gpr .r11 = 0 ∧ s'.gpr .rbx = 0 ∧ s'.gpr .rbp = 0 ∧
      (∀ r, r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = setupMem (cx s₀) s := by
  have o : ∀ a, a + 8 ≤ 1696 → InRegions s.wr (off (cx s₀) a) 8 := fun a h => by
    rw [hwr]; exact hp.in_ctx h
  have i : ∀ a, a + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have o0 := o 592 (by lit_omega); have o1 := o 600 (by lit_omega); have o2 := o 520 (by lit_omega)
  have o3 := o 528 (by lit_omega); have o4 := o 536 (by lit_omega); have o5 := o 544 (by lit_omega)
  have i0 := i 672 (by lit_omega); have i1 := i 680 (by lit_omega)
  simp only [off] at o0 o1 o2 o3 o4 o5 i0 i1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [macSetup, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, readSrc32, execAlu, execShift, State.store64, State.load64, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hr15, o0, o1, o2, o3, o4, o5, i0, i1, readW64_off, setupMem, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', true_and, and_true]
  intro r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ite_false]

set_option simprocs false in
/-- `s` added to the accumulator's low 128 bits. -/
theorem addS_ok (s : State) {c : Addr} (hrcx : s.gpr .rcx = c)
    (i0 : InRegions (s.rd ++ s.wr) (off c 688) 8) (i1 : InRegions (s.rd ++ s.wr) (off c 696) 8) :
    WP isa (.block [.alu .add .r11 (.mem (at_ .rcx 688)), .alu .adc .rbx (.mem (at_ .rcx 696))]) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat =
        ((s.gpr .r11).toNat + (s.mem.readW (off c 688) 64).toNat +
          2 ^ 64 * ((s.gpr .rbx).toNat + (s.mem.readW (off c 696) 64).toNat)) % 2 ^ 128 ∧
      (∀ r, r ≠ .r11 → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [off] at i0 i1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    execAlu, State.load64,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    hrcx, i0, i1,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [and_true]
  refine ⟨Proof.Poly1305.X86_64.add_adc_mod _ _ _ _, fun r h₁ h₂ => by simp only [h₁, h₂, ite_false]⟩

set_option simprocs false in
/-- `ZF` set if the quadword at `rcx + o` is 0. -/
theorem testMem_ok (s : State) {c : Addr} (hrcx : s.gpr .rcx = c) {o : Nat}
    (i0 : InRegions (s.rd ++ s.wr) (off c o) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rcx o)), .alu .test .rax (.reg .rax)]) s fun s' =>
      isa.eval .e s' = some (s.mem.readW (off c o) 64 == 0) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [off] at i0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    execAlu, State.load64,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, hrcx, i0,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', eval,
    BitVec.and_self, true_and, and_true]
  exact fun r h₁ => by simp only [h₁, ite_false]

set_option simprocs false in
/-- `ZF` set if `rdi` is 0. -/
theorem testRdi_ok (s : State) :
    WP isa (.block [.alu .test .rdi (.reg .rdi)]) s fun s' =>
      isa.eval .e s' = some (s.gpr .rdi == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', eval, BitVec.and_self]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

set_option simprocs false in
/-- `ZF` set if the quadword at `rcx + o` is a multiple of 16. -/
theorem andMem_ok (s : State) {c : Addr} (hrcx : s.gpr .rcx = c) {o : Nat}
    (i0 : InRegions (s.rd ++ s.wr) (off c o) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rcx o)), .alu .and .rax (.imm 15)]) s fun s' =>
      isa.eval .e s' = some (s.mem.readW (off c o) 64 &&& 15 == 0) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have x15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
  simp only [off] at i0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    execAlu, State.load64,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg, hrcx, i0, x15,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', eval, true_and, and_true]
  exact fun r h₁ => by simp only [h₁, ite_false]

/-- The lengths block at `c + 592` absorbed, the accumulator reduced, and `s`
(at `c + 688`) added: the tag's low 128 bits in `r11:rbx`. -/
theorem final_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {s : State} (h : Acc R0 R1 X s) {c : Addr}
    (hrcx : s.gpr .rcx = c) (hin : ∀ a, a = 592 ∨ a = 600 ∨ a = 688 ∨ a = 696 →
      InRegions (s.rd ++ s.wr) (off c a) 8) :
    WP isa (.block (Impl.Poly1305.X86_64.absorbAt .rcx 592 1 ++ Impl.Poly1305.X86_64.reduce ++
      ([.alu .add .r11 (.mem (at_ .rcx 688)), .alu .adc .rbx (.mem (at_ .rcx 696))] : List Instr))) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat =
        (absorbAll (rN R0 R1) X (bytesAt s.mem (off c 592) 16) +
          ((s.mem.readW (off c 688) 64).toNat + 2 ^ 64 * (s.mem.readW (off c 696) 64).toNat)) % 2 ^ 128 ∧
      s'.gpr .rcx = c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 592) 8 := by
    rw [hrcx, ← off_eq]; exact hin _ (.inl rfl)
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 (592 + 8)) 8 := by
    rw [hrcx, ← off_eq]; exact hin _ (.inr (.inl rfl))
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (absorbAt_acc hk h (by decide) i0 i8) fun s₁ ⟨a₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₁) fun s₂ ⟨hr, k₂⟩ => ?_)
  have rcx₂ : s₂.gpr .rcx = c := by rw [k₂.1 _ (by decide), k₁.1 _ (by decide), hrcx]
  have rd₂ : s₂.rd = s.rd := by rw [k₂.2.2.1, k₁.2.2.1]
  have wr₂ : s₂.wr = s.wr := by rw [k₂.2.2.2, k₁.2.2.2]
  have m₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  refine WP.mono (addS_ok s₂ rcx₂ (by rw [rd₂, wr₂]; exact hin _ (.inr (.inr (.inl rfl))))
    (by rw [rd₂, wr₂]; exact hin _ (.inr (.inr (.inr rfl))))) fun s₃ ⟨hv, g₃, m₃, rd₃, wr₃⟩ =>
    ⟨?_, by rw [g₃ _ (by decide) (by decide), rcx₂],
      by rw [g₃ _ (by decide) (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)],
      by rw [m₃, m₂], by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
  rw [hrcx, ← off_eq] at a₁
  have hV : absorbAll (rN R0 R1) X (bytesAt s.mem (off c 592) 16) < P := by
    rw [VG.Proof.Poly1305.absorbAll_block (by rw [VG.Proof.Poly1305.length_bytesAt]; decide)
      (by rw [VG.Proof.Poly1305.length_bytesAt])]
    exact Nat.mod_lt _ (by decide)
  have e₂ : hval s₂ = absorbAll (rN R0 R1) X (bytesAt s.mem (off c 592) 16) := by
    rw [hr a₁.h2, a₁.val, Nat.mod_eq_of_lt hV]
  simp only [hval] at e₂
  rw [hv, m₂]
  omega

/-- `setupMem` changes only the lengths block and the stash. -/
theorem setupMem_frame {s₀ : State} (s : State) :
    Frame [sub s₀ 520 32, sub s₀ 592 16] s.mem (setupMem (cx s₀) s) := by
  have c : ∀ k n d, k ≤ d → d + 8 ≤ k + n → k + n ≤ 1696 → (sub s₀ k n).Contains (off (cx s₀) d) (64 / 8) :=
    fun k n d h₁ h₂ h₃ => contains_sub s₀ h₁ h₂ h₃
  exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (c 592 16 592 (by decide) (by decide) (by decide))
    |>.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 592 16 600 (by decide) (by decide) (by decide))
    |>.writeW (List.mem_cons_self) _ (c 520 32 520 (by decide) (by decide) (by decide))
    |>.writeW (List.mem_cons_self) _ (c 520 32 528 (by decide) (by decide) (by decide))
    |>.writeW (List.mem_cons_self) _ (c 520 32 536 (by decide) (by decide) (by decide))
    |>.writeW (List.mem_cons_self) _ (c 520 32 544 (by decide) (by decide) (by decide))

/-- What `setupMem` stores. -/
theorem setupMem_read {s₀ : State} (s : State) :
    (setupMem (cx s₀) s).readW (off (cx s₀) 592) 64 = s.gpr .rbp ∧
    (setupMem (cx s₀) s).readW (off (cx s₀) 600) 64 = s.gpr .r13 ∧
    (setupMem (cx s₀) s).readW (off (cx s₀) 520) 64 = s.gpr .r12 ∧
    (setupMem (cx s₀) s).readW (off (cx s₀) 528) 64 = s.gpr .r13 ∧
    (setupMem (cx s₀) s).readW (off (cx s₀) 536) 64 = s.gpr .r14 ∧
    (setupMem (cx s₀) s).readW (off (cx s₀) 544) 64 = s.gpr .rbp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [setupMem, Mem.readW_writeW_self64, readW64_off]

theorem keeps_refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- An optional padded block at `c + d`: `B` absorbed, which is the block
there if `ZF` is clear and empty if it is set. -/
theorem blockIte_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {t : State} (h : Acc R0 R1 X t)
    {c : Addr} (hrcx : t.gpr .rcx = c) {d : Nat} {b : Bool} (hz : isa.eval .e t = some b) {B : List Byte}
    (hB : b = false → bytesAt t.mem (off c d) 16 = B) (hB0 : b = true → B = [])
    (i0 : b = false → InRegions (t.rd ++ t.wr) (off c d) 8)
    (i8 : b = false → InRegions (t.rd ++ t.wr) (off c (d + 8)) 8) :
    WP isa (.ite .e (.block []) (.block (Impl.Poly1305.X86_64.absorbAt .rcx d 1))) t fun t' =>
      Acc R0 R1 (absorbAll (rN R0 R1) X B) t' ∧ Keeps absorbRegs t t' := by
  refine WP.ite b hz (fun hb => ?_) (fun hb => ?_)
  · rw [hB0 hb, VG.Proof.Poly1305.absorbAll_nil]; exact WP.block_nil ⟨h, keeps_refl _ _⟩
  · refine WP.mono (absorbAt_acc hk h (by decide) (by rw [hrcx, ← off_eq]; exact i0 hb)
      (by rw [hrcx, ← off_eq]; exact i8 hb)) fun t' ⟨a, k⟩ => ⟨?_, k⟩
    rw [hrcx, ← off_eq, hB hb] at a
    exact a

/-- The data's `n` whole blocks at `q`, if any. -/
theorem dataIte_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {t : State} (h : Acc R0 R1 X t) {q : Addr}
    {n : Nat} (hn64 : n < 2 ^ 64) (hrsi : t.gpr .rsi = q) (hrdi : t.gpr .rdi = BitVec.ofNat 64 n)
    (hz : isa.eval .e t = some (BitVec.ofNat 64 n == 0))
    (hin : ∀ k w, k + w ≤ 16 * n → InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 k) w) :
    WP isa (.ite .e (.block [])
      (cntLoop (.block (Impl.Poly1305.X86_64.absorbAt .rsi 0 1)) [.alu .add .rsi (.imm 16)])) t fun t' =>
      Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt t.mem q (16 * n))) t' ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
        t'.wr = t.wr ∧ ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → t'.gpr r = t.gpr r := by
  have e0 : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at this
      exact h0 this
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · rw [e0, decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, show bytesAt t.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    exact WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  · rw [e0, decide_eq_false_iff_not] at hb
    exact blocks_acc hk (Nat.pos_of_ne_zero hb) hn64 h hrsi hrdi hin

open VG.Spec.ChaCha20Poly1305 (pad16) in
/-- The data padded: its whole blocks, then its last bytes padded. -/
theorem split_tail (m : Mem) (p : Addr) (L : Nat) :
    bytesAt m p L ++ pad16 (bytesAt m p L) = bytesAt m p (16 * (L / 16)) ++
      (bytesAt m (p + BitVec.ofNat 64 (16 * (L / 16))) (L % 16) ++ pad16 (bytesAt m p L)) := by
  have e : bytesAt m p L = bytesAt m p (16 * (L / 16)) ++ bytesAt m (p + BitVec.ofNat 64 (16 * (L / 16))) (L % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  calc _ = (bytesAt m p (16 * (L / 16)) ++ bytesAt m (p + BitVec.ofNat 64 (16 * (L / 16))) (L % 16)) ++
        pad16 (bytesAt m p L) := by rw [← e]
    _ = _ := List.append_assoc _ _ _

open VG.Spec.ChaCha20Poly1305 (pad16) in
theorem tail_len (m : Mem) (p q : Addr) (L : Nat) :
    (bytesAt m q (L % 16) ++ pad16 (bytesAt m p L)).length % 16 = 0 := by
  simp only [List.length_append, VG.Proof.Poly1305.length_bytesAt, pad16]
  split <;> simp only [List.length_replicate, List.length_nil] <;> omega

open VG.Spec.ChaCha20Poly1305 (pad16) in
/-- `macBody` from the key and an empty accumulator: the padded additional
data `B` (empty with none), the data's whole blocks, its padded last bytes
and the lengths block absorbed, and `s` added. -/
theorem macBody_ok {s₀ : State} (hp : APre e s₀) {R0 R1 : BitVec 64} (hk : Key R0 R1) {s : State}
    (h : Acc R0 R1 0 s) (hrcx : s.gpr .rcx = cx s₀) (hrsi : s.gpr .rsi = dp s₀)
    (hrdi : s.gpr .rdi = BitVec.ofNat 64 (L s₀ / 16)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h544 : s.mem.readW (off (cx s₀) 544) 64 = s₀.gpr .rcx) (h528 : s.mem.readW (off (cx s₀) 528) 64 = s₀.gpr .r9)
    {B : List Byte} (hB0 : AL s₀ = 0 → B = []) (hB : AL s₀ ≠ 0 → bytesAt s.mem (off (cx s₀) 576) 16 = B)
    (hT : L s₀ % 16 ≠ 0 → bytesAt s.mem (off (cx s₀) 624) 16 =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) :
    WP isa macBody s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat =
        (absorbAll (rN R0 R1) (absorbAll (rN R0 R1) 0 B)
            (bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀)) ++
              bytesAt s.mem (off (cx s₀) 592) 16) +
          ((s.mem.readW (off (cx s₀) 688) 64).toNat + 2 ^ 64 * (s.mem.readW (off (cx s₀) 696) 64).toNat)) %
          2 ^ 128 ∧
      s'.gpr .rcx = cx s₀ ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have ic : ∀ a, a + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have id : ∀ k w, k + w ≤ L s₀ → InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 k) w := fun k w h => by
    rw [hrd, hwr]
    exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ h (by omega)⟩
  -- The additional data.
  refine WP.seq (WP.mono (testMem_ok s hrcx (ic 544 (by lit_omega))) fun s₁ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [h544] at z₁
  have h₁ : Acc R0 R1 0 s₁ := acc_keep6 h (g₁ _ (by decide)) (g₁ _ (by decide)) (g₁ _ (by decide))
    (g₁ _ (by decide)) (g₁ _ (by decide)) (g₁ _ (by decide))
  have ez : (s₀.gpr .rcx == 0) = decide (AL s₀ = 0) := by
    by_cases h0 : AL s₀ = 0
    · simp only [h0, decide_true, beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
    · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact fun h' => h0 (by rw [AL, h']; rfl)
  rw [ez] at z₁
  refine WP.seq (WP.mono (blockIte_ok hk h₁ (by rw [g₁ _ (by decide), hrcx]) (d := 576) z₁ (B := B)
    (fun hb => by rw [m₁]; exact hB (by simpa using hb)) (fun hb => hB0 (by simpa using hb))
    (fun _ => by rw [rd₁, wr₁]; exact ic 576 (by lit_omega)) (fun _ => by rw [rd₁, wr₁]; exact ic 584 (by lit_omega)))
    fun s₂ ⟨a₂, k₂⟩ => ?_)
  have g₂ : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.1 r hr, g₁ r (by intro h; subst h; exact hr (by decide))]
  have m₂ : s₂.mem = s.mem := by rw [k₂.2.1, m₁]
  have rd₂ : s₂.rd = s.rd := by rw [k₂.2.2.1, rd₁]
  have wr₂ : s₂.wr = s.wr := by rw [k₂.2.2.2, wr₁]
  -- The whole blocks.
  refine WP.seq (WP.mono (testRdi_ok s₂) fun s₃ ⟨z₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  rw [g₂ _ (by decide), hrdi] at z₃
  refine WP.seq (WP.mono (dataIte_ok hk (acc_keep6 a₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃])
    (by rw [g₃]) (by rw [g₃])) (q := dp s₀) (by omega) (by rw [g₃, g₂ _ (by decide), hrsi])
    (by rw [g₃, g₂ _ (by decide), hrdi]) z₃ (fun k w h => by rw [rd₃, wr₃, rd₂, wr₂]; exact id k w (by omega)))
    fun s₄ ⟨a₄, m₄, rd₄, wr₄, g₄⟩ => ?_)
  rw [m₃, m₂] at a₄
  -- The last bytes.
  have rcx₄ : s₄.gpr .rcx = cx s₀ := by
    rw [g₄ _ (by decide) (by decide) (by decide), g₃, g₂ _ (by decide), hrcx]
  have m₄' : s₄.mem = s.mem := by rw [m₄, m₃, m₂]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂]
  refine WP.seq (WP.mono (andMem_ok s₄ rcx₄ (by rw [rd₄', wr₄']; exact ic 528 (by lit_omega)))
    fun s₅ ⟨z₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  rw [m₄', h528] at z₅
  have e15 : (s₀.gpr .r9 &&& 15 == 0) = decide (L s₀ % 16 = 0) := by
    have : (s₀.gpr .r9 &&& 15).toNat = L s₀ % 16 := by
      rw [BitVec.toNat_and, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    by_cases h0 : L s₀ % 16 = 0
    · simp only [h0, decide_true, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [this, h0]; rfl)
    · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact fun h' => h0 (by rw [← this, h']; rfl)
  rw [e15] at z₅
  let Tb : List Byte := bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
    pad16 (bytesAt s.mem (dp s₀) (L s₀))
  refine WP.seq (WP.mono (blockIte_ok hk (acc_keep6 a₄ (g₅ _ (by decide)) (g₅ _ (by decide)) (g₅ _ (by decide))
    (g₅ _ (by decide)) (g₅ _ (by decide)) (g₅ _ (by decide))) (by rw [g₅ _ (by decide), rcx₄]) (d := 624) z₅
    (B := Tb) (fun hb => by rw [m₅, m₄']; exact hT (by simpa using hb)) (fun hb => ?_)
    (fun _ => by rw [rd₅, wr₅, rd₄', wr₄']; exact ic 624 (by lit_omega))
    (fun _ => by rw [rd₅, wr₅, rd₄', wr₄']; exact ic 632 (by lit_omega))) fun s₆ ⟨a₆, k₆⟩ => ?_)
  · have h0 : L s₀ % 16 = 0 := by simpa using hb
    simp only [Tb, h0, VG.Spec.ChaCha20Poly1305.pad16, VG.Proof.Poly1305.length_bytesAt, ite_true,
      List.append_nil]
    rfl
  -- The lengths and `s`.
  have rcx₆ : s₆.gpr .rcx = cx s₀ := by rw [k₆.1 _ (by decide), g₅ _ (by decide), rcx₄]
  have m₆ : s₆.mem = s.mem := by rw [k₆.2.1, m₅, m₄']
  have rd₆ : s₆.rd = s.rd := by rw [k₆.2.2.1, rd₅, rd₄']
  have wr₆ : s₆.wr = s.wr := by rw [k₆.2.2.2, wr₅, wr₄']
  refine WP.mono (final_ok hk a₆ rcx₆ fun a ha => by
    rw [rd₆, wr₆]; exact ic a (by rcases ha with rfl | rfl | rfl | rfl <;> decide))
    fun s₇ ⟨v₇, rcx₇, rsp₇, m₇, rd₇, wr₇⟩ => ⟨?_, rcx₇, ?_, by rw [m₇, m₆], by rw [rd₇, rd₆], by rw [wr₇, wr₆]⟩
  · rw [v₇, m₆, split_tail, List.append_assoc,
      VG.Proof.Poly1305.absorbAll_append (x := bytesAt s.mem (dp s₀) (16 * (L s₀ / 16)))
        (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
      VG.Proof.Poly1305.absorbAll_append (x := Tb) (tail_len _ _ _ _)]
  · rw [rsp₇, k₆.1 _ (by decide), g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide), g₃,
      g₂ _ (by decide)]

open VG.Spec.ChaCha20Poly1305 (pad16) in
theorem pad_len (AA : List Byte) : (AA ++ pad16 AA).length % 16 = 0 := by
  simp only [List.length_append, pad16]
  split <;> simp only [List.length_replicate, List.length_nil] <;> omega

open VG.Spec.ChaCha20Poly1305 (pad16 macData) in
/-- The tag of the padded additional data `AA` and the data, under the
one-time key at `ctx + 672`, into `r11:rbx` (`mac`'s number before
`leBytes 16`, modulo `2¹²⁸`): `macSetup` stores the lengths and stashes the
registers, `macBody` absorbs. -/
theorem mac_ok {s₀ : State} (hp : APre e s₀) {s : State}
    (hr15 : s.gpr .r15 = cx s₀) (hr14 : s.gpr .r14 = dp s₀) (hr13 : s.gpr .r13 = s₀.gpr .r9)
    (hrbp : s.gpr .rbp = s₀.gpr .rcx) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {AA : List Byte} (hAl : AA.length = AL s₀)
    (hAA : AL s₀ ≠ 0 → bytesAt s.mem (off (cx s₀) 576) 16 = AA ++ pad16 AA)
    (hT : L s₀ % 16 ≠ 0 → bytesAt s.mem (off (cx s₀) 624) 16 =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) :
    WP isa macShort s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .rbx).toNat =
        (Spec.Poly1305.accumulate (Spec.Poly1305.clamp (leNum ((bytesAt s.mem (off (cx s₀) 672) 32).take 16)))
            (macData AA (bytesAt s.mem (dp s₀) (L s₀))) +
          leNum (((bytesAt s.mem (off (cx s₀) 672) 32).drop 16).take 16)) % 2 ^ 128 ∧
      s'.gpr .rcx = cx s₀ ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = setupMem (cx s₀) s := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (macSetup_ok hp hr15 hrd hwr)
    fun s₁ ⟨rcx₁, rsi₁, rdi₁, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (cx s₀) 672) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (cx s₀) 680) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  rw [hR1] at r9₁ r10₁
  rw [hR0] at r8₁
  have ha : Acc R0 R1 0 s₁ := by
    refine ⟨r8₁, r9₁, ?_, by rw [rbp₁]; decide, by simp only [hval, r11₁, rbx₁, rbp₁]; rfl⟩
    have h1 := hk.r1; have h2 := hk.r1_mod
    rw [r10₁, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have f₁ : Frame [sub s₀ 520 32, sub s₀ 592 16] s.mem s₁.mem := by rw [m₁]; exact setupMem_frame s
  have rd₁' := setupMem_read (s₀ := s₀) s
  rw [← m₁] at rd₁'
  obtain ⟨l0, l1, -, l3, -, l5⟩ := rd₁'
  have hC : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := bytesAt_frame f₁ (by rdisj_all) (by omega)
  have dD : ∀ {k n a m : Nat}, k + n ≤ L s₀ → a + m ≤ 1696 →
      (⟨dp s₀ + BitVec.ofNat 64 k, n⟩ : Region).Disjoint (sub s₀ a m) := fun h1 h2 =>
    (hp.c_d.sub_left (sub_ctx s₀ h2)).symm.sub_left (Offset.sub_base _ h1)
  refine WP.mono (macBody_ok hp hk ha rcx₁ (by rw [rsi₁, hr14]) (by
      rw [rdi₁, hr13]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (by rw [l5, hrbp]) (by rw [l3, hr13]) (B := AA ++ pad16 AA)
    (fun h0 => by
      rw [List.eq_nil_of_length_eq_zero (hAl.trans h0)]; rfl)
    (fun h0 => by rw [bytesAt_frame f₁ (by rdisj_all) (by decide)]; exact hAA h0)
    (fun h0 => by
      rw [bytesAt_frame f₁ (by rdisj_all) (by decide), hC,
        bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dD (by omega) (by decide)) (by omega)]
      exact hT h0))
    fun s' ⟨v', rcx', rsp', m', rd', wr'⟩ => ⟨?_, rcx', by rw [rsp', g₁ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)],
      by rw [rd', rd₁], by rw [wr', wr₁], by rw [m', m₁]⟩
  rw [v', hC]
  -- The key: `r` and `s`.
  have hK : bytesAt s.mem (off (cx s₀) 672) 32 =
      bytesAt s.mem (off (cx s₀) 672) 16 ++ bytesAt s.mem (off (cx s₀) 688) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, VG.Proof.Poly1305.bytesAt_add, off_eq, off_eq, Offset.add_add]
  have hr : Spec.Poly1305.clamp (leNum ((bytesAt s.mem (off (cx s₀) 672) 32).take 16)) = rN R0 R1 := by
    have e680 : off (cx s₀) 672 + 8 = off (cx s₀) 680 := by
      rw [off_eq, off_eq, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    rw [hK, List.take_left' (VG.Proof.Poly1305.length_bytesAt _ _ _), VG.Proof.Poly1305.leNum_bytesAt_16, e680,
      VG.Proof.Poly1305.clamp_words, ← hR0, ← hR1]
  have hs : leNum (((bytesAt s.mem (off (cx s₀) 672) 32).drop 16).take 16) =
      (s₁.mem.readW (off (cx s₀) 688) 64).toNat + 2 ^ 64 * (s₁.mem.readW (off (cx s₀) 696) 64).toNat := by
    rw [hK, List.drop_left' (VG.Proof.Poly1305.length_bytesAt _ _ _),
      List.take_of_length_le (by rw [VG.Proof.Poly1305.length_bytesAt]), VG.Proof.Poly1305.leNum_bytesAt_16,
      f₁.readW (r := ⟨off (cx s₀) 688, 8⟩) (Region.contains_self _ _) (by rdisj_all) (by decide),
      f₁.readW (r := ⟨off (cx s₀) 696, 8⟩) (Region.contains_self _ _) (by rdisj_all) (by decide),
      show off (cx s₀) 696 = off (cx s₀) 688 + 8 by rw [off_eq, off_eq, show (8 : Addr) = BitVec.ofNat 64 8 from rfl,
        Offset.add_add]]
  -- The lengths.
  have hl : bytesAt s₁.mem (off (cx s₀) 592) 16 = Spec.Poly1305.leBytes 8 AA.length ++
      Spec.Poly1305.leBytes 8 (bytesAt s.mem (dp s₀) (L s₀)).length := by
    rw [bytesAt_16, off_off, l0, l1, hrbp, hr13, hAl, VG.Proof.Poly1305.length_bytesAt]
  rw [hl, hr, hs, Spec.ChaCha20Poly1305.macData, VG.Proof.Poly1305.accumulate_eq,
    show AA ++ pad16 AA ++ bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀)) ++
      Spec.Poly1305.leBytes 8 AA.length ++ Spec.Poly1305.leBytes 8 (bytesAt s.mem (dp s₀) (L s₀)).length =
      (AA ++ pad16 AA) ++ (bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀)) ++
        (Spec.Poly1305.leBytes 8 AA.length ++ Spec.Poly1305.leBytes 8 (bytesAt s.mem (dp s₀) (L s₀)).length))
      by simp only [List.append_assoc],
    VG.Proof.Poly1305.absorbAll_append (pad_len AA)]

end

end VG.Proof.ChaCha20Poly1305.X86_64.Short

/-!
# ChaCha20-Poly1305 for short records (x86-64): `seal`

`Stitch.sealShort`, from its parts: the keystream (`shortPre_ok`), the
padded additional data (`padAad_ok`), the data encrypted from the keystream
at `ctx + 736` (`xorBufX_ok`), its padded last bytes (`padData_ok`), the tag
(`mac_ok`), stored at `tag` (`tagStore_ok`), the keystream wiped
(`zeroKs_ok`) and the registers restored (`restoreLoads_ok`).
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (bytesAt leNum leBytes mac)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Impl.ChaCha20.X86_64 (at_)

variable {e : Bool}

/-- The tag block: the tag from `r11:rbx` stored at the `tag` stashed at
`ctx + 520`. -/
abbrev tagStore : List Instr :=
  [.mov .rax (.mem (at_ .rcx 520)), .store (at_ .rax 0) .r11, .store (at_ .rax 8) .rbx,
   .mov .r15 (.reg .rcx), .mov32 .rdx (.imm 512)]

set_option simprocs false in
theorem tagStore_ok {s₀ : State} (hp : APre true s₀) {s : State} (hrcx : s.gpr .rcx = cx s₀)
    (h520 : s.mem.readW (off (cx s₀) 520) 64 = tp s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block tagStore) s fun s' =>
      s'.mem = (s.mem.writeW (off (tp s₀) 0) (s.gpr .r11)).writeW (off (tp s₀) 8) (s.gpr .rbx) ∧
      s'.gpr .r15 = cx s₀ ∧ s'.gpr .rdx = BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 : InRegions (s.rd ++ s.wr) (off (cx s₀) 520) 8 := by rw [hrd, hwr]; exact hp.in_ctx' (by lit_omega)
  have o : ∀ d, d + 8 ≤ 16 → InRegions s.wr (off (tp s₀) d) 8 := fun d h => by
    rw [hwr]; exact ⟨tR s₀, hp.t_wr, by rw [off_eq]; exact Offset.contains_base _ h (by lit_omega)⟩
  have o0 := o 0 (by decide)
  have o8 := o 8 (by decide)
  simp only [off] at i0 h520
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hrcx, i0, h520, o0, o8, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp only [h₁, h₂, h₃, ite_false], trivial⟩

/-- The 16 bytes of two words stored next to each other. -/
theorem tag_bytes (m : Mem) (p : Addr) (lo hi : BitVec 64) :
    bytesAt ((m.writeW (off p 0) lo).writeW (off p 8) hi) p 16 = leBytes 16 (lo.toNat + 2 ^ 64 * hi.toNat) := by
  have e0 : off p 0 = p := by rw [off_eq]; exact BitVec.add_zero _
  refine VG.Proof.Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [show ∀ X : Mem, X.readW p 64 = X.readW (off p 0) 64 from fun X => by rw [e0],
      readW64_off _ _ _ (d := 0) (e := 8) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
    omega
  · rw [← off_eq, Mem.readW_writeW_self64]
    have := lo.isLt
    omega

abbrev allR (s₀ : State) : List Region := [workR s₀, dR s₀, tR s₀]

theorem sub_all (s₀ : State) {k n : Nat} (h : k + n ≤ 1696) : ∃ r' ∈ allR s₀, Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ (Nat.zero_le _) (by lit_omega) (by lit_omega)⟩

theorem d_all (s₀ : State) : ∃ r' ∈ allR s₀, Region.Sub (dR s₀) r' := ⟨dR s₀, by simp, fun _ h => h⟩

theorem t_all (s₀ : State) : ∃ r' ∈ allR s₀, Region.Sub (tR s₀) r' := ⟨tR s₀, by simp, fun _ h => h⟩

theorem sealShort_eq (x : Impl.ChaCha20.X86_64.Callee) : sealShort x =
    .seq (shortPre x.vl) (.seq padAad (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX x.wide .r14) (.seq padData (.seq macShort (.seq (.block tagStore)
        (.seq (zeroKs x.wide) (.block restoreLoads)))))))) := rfl

/-- `sealShort`, from the state after `entry`: the registers restored, only
the context, the data and the tag written, and the ciphertext and tag. -/
theorem sealShort_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 4 ∨ x.wide = 5 ∨ x.wide = 6)
    {s₀ : State} (hp : APre true s₀) (hLe : L s₀ ≤ 448) (hA : AL s₀ < 16) :
    WP isa (sealShort x) (entryS s₀) fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ Frame (allR s₀) s₀.mem s'.mem ∧
      Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
        (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16) := by
  have hL' : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  rw [sealShort_eq]
  refine WP.seq (WP.mono (shortPre_ok x.vl hp hLe) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (padAad_ok hp hA h₁.r15 h₁.rbx h₁.rbp h₁.rd h₁.wr) fun s₂ ⟨a₂, f₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := 736) (by lit_omega) s₂)
    fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_))
  refine WP.mono (Q := fun (s' : State) => s'.gpr .rdx = s₀.gpr .r9 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s₃.gpr q) ∧
      s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧ s'.mem = s₃.mem) ?_ fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, Option.map_some,
      Option.some.injEq, exists_eq_left', ite_true]
    exact ⟨by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r13],
      fun q hq => by simp [hq], trivial, trivial, trivial⟩
  have m₄₂ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, h₁.wr]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, h₁.rd]
  have rsi₄ : s₄.gpr .rsi = off (cx s₀) 736 := by
    rw [g₄ _ (by decide), e₃, g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r15]
  have r14₄ : s₄.gpr .r14 = dp s₀ := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      h₁.r14]
  have dB : (dR s₀).Disjoint ⟨off (cx s₀) 736, L s₀⟩ :=
    hp.c_d.symm.sub_right (sub_ctx s₀ (k := 736) (n := L s₀) (by omega))
  refine WP.seq (WP.mono (XorBufX.xorBufX_ok hw (d := .r14) (by decide)
    r14₄ rsi₄ (by rw [d₄]; exact hL s₀) hL' dB
    ⟨dR s₀, by rw [wr₄']; exact hp.d_wr, Region.contains_self _ _⟩
    ⟨ctxR s₀, by rw [rd₄', wr₄']; simp [hp.ctx_wr], by
      rw [off_eq]; exact Offset.contains_base _ (show 736 + L s₀ ≤ 1696 by omega) (by lit_omega)⟩)
    fun s₅ h₅ => ?_)
  -- The registers the rest reads, from `shortPre`.
  have K₅ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → r ≠ .r8 → r ≠ .rdi →
      s₅.gpr r = s₁.gpr r := fun r a c d n9 si r8 di => by
    rw [h₅.keep r a r8 c d si di, g₄ r d, g₃ r si, g₂ r a c d n9 si]
  have r15₅ : s₅.gpr .r15 = cx s₀ := by
    rw [K₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r15]
  have r14₅ : s₅.gpr .r14 = dp s₀ := by
    rw [K₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r14]
  have r13₅ : s₅.gpr .r13 = s₀.gpr .r9 := by
    rw [K₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r13]
  have wr₅ : s₅.wr = s₀.wr := by rw [h₅.wr, wr₄']
  have rd₅ : s₅.rd = s₀.rd := by rw [h₅.rd, rd₄']
  refine WP.seq (WP.mono (padData_ok hp r15₅ r14₅ r13₅ rd₅ wr₅) fun s₆ ⟨t₆, f₆, g₆, rd₆, wr₆⟩ => ?_)
  have K₆ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → r ≠ .r8 → r ≠ .rdi →
      s₆.gpr r = s₁.gpr r := fun r a c d n9 si r8 di => by rw [g₆ r a c d n9 si, K₅ r a c d n9 si r8 di]
  have k6 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rsi → r ≠ .r8 → r ≠ .rdi →
      ∀ v, s₁.gpr r = v → s₆.gpr r = v := fun r a c d n9 si r8 di v h => (K₆ r a c d n9 si r8 di).trans h
  have dec := fun (r : Reg) (h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r9 ∧ r ≠ .rsi ∧ r ≠ .r8 ∧ r ≠ .rdi) =>
    k6 r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅]
  -- What the tag reads: the additional data, padded, and the data's last bytes, padded.
  have hM : L s₀ ≤ 960 := by omega
  have ks₄ : ∀ k < L s₀, s₄.mem (off (cx s₀) (736 + k)) =
      (Spec.ChaCha20.keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0 := by
    rw [m₄₂]; exact ks_frame f₂ (by rdisj_all) hM h₁.ks
  have D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by
    rw [m₄₂, bytesAt_frame f₂ (by rdisj_all) hL'.le, bytesAt_frame h₁.frame (by rdisj_all) hL'.le]
  have C₅ : bytesAt s₅.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [← D₄, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
    apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [h₅.data k hk, show off (cx s₀) 736 + BitVec.ofNat 64 k = off (cx s₀) (736 + k) by
      rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], ks₄ k hk]
  have C₆ : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₅.mem (dp s₀) (L s₀) :=
    bytesAt_frame f₆ (by rdisj_all) hL'.le
  have A₁ : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  have hAA : AL s₀ ≠ 0 → bytesAt s₆.mem (off (cx s₀) 576) 16 = A s₀ ++ pad16 (A s₀) := fun h => by
    rw [bytesAt_frame f₆ (by rdisj_all) (by decide), bytesAt_frame h₅.frame (by rdisj_all) (by decide), m₄₂,
      a₂ h, A₁]
  have tB0 : (sub s₀ 624 16).Disjoint (dR s₀) := hp.c_d.sub_left (sub_ctx s₀ (by decide))
  have tB : (⟨dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16)), L s₀ % 16⟩ : Region).Disjoint (sub s₀ 624 16) :=
    (Src.disj_sub tB0 (a := 16 * (L s₀ / 16)) (n := L s₀ % 16) (by omega)).dsymm
  have hT : L s₀ % 16 ≠ 0 → bytesAt s₆.mem (off (cx s₀) 624) 16 =
      bytesAt s₆.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
        pad16 (bytesAt s₆.mem (dp s₀) (L s₀)) := fun h => by
    rw [t₆ h, C₆, bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact tB) (by omega)]
  have key₆ : bytesAt s₆.mem (off (cx s₀) 672) 32 = otk s₀ := by
    rw [bytesAt_frame f₆ (by rdisj_all) (by decide), bytesAt_frame h₅.frame (by rdisj_all) (by decide), m₄₂,
      bytesAt_frame f₂ (by rdisj_all) (by decide), h₁.key]
  refine WP.seq (WP.mono (mac_ok hp (dec .r15 (by decide) _ h₁.r15) (dec .r14 (by decide) _ h₁.r14)
    (dec .r13 (by decide) _ h₁.r13) (dec .rbp (by decide) _ h₁.rbp) rd₆' wr₆'
    (VG.Proof.Poly1305.length_bytesAt _ _ _) hAA hT) fun s₇ ⟨t₇, rcx₇, rsp₇, rd₇, wr₇, m₇⟩ => ?_)
  rw [key₆, C₆, C₅] at t₇
  have r12₆ := dec .r12 (by decide) _ h₁.r12
  refine WP.seq (WP.mono (tagStore_ok hp rcx₇ (by rw [m₇, (setupMem_read (s₀ := s₀) s₆).2.2.1, r12₆])
    (by rw [rd₇, rd₆']) (by rw [wr₇, wr₆'])) fun s₈ ⟨m₈, r15₈, rdx₈, g₈, rd₈, wr₈⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.X86_64.zeroKs_ok hw hp (n := 512) (by decide) (by decide) rdx₈ r15₈
    (by rw [wr₈, wr₇, wr₆'])) fun s₉ ⟨g₉, rd₉, wr₉, f₉, _⟩ => ?_)
  have f₇ : Frame [sub s₀ 520 32, sub s₀ 592 16] s₆.mem s₇.mem := by rw [m₇]; exact setupMem_frame s₆
  have c0 : (tR s₀).Contains (off (tp s₀) 0) (64 / 8) := by
    rw [off_eq]; exact Offset.contains_base _ (by decide) (by decide)
  have c8 : (tR s₀).Contains (off (tp s₀) 8) (64 / 8) := by
    rw [off_eq]; exact Offset.contains_base _ (by decide) (by decide)
  have f₈ : Frame [tR s₀] s₇.mem s₈.mem := by
    rw [m₈]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  have sv₉ : Saved s₀ s₉.mem :=
    ((((((h₁.saved.frame f₂ (by rdisj_all)).frame (m₄₂ ▸ h₅.frame) (by rdisj_all)).frame f₆
      (by rdisj_all)).frame f₇ (by rdisj_all)).frame f₈ (by rdisj_all)).frame f₉ (by rdisj_all))
  have rsp₉ : s₉.gpr .rsp = s₀.gpr .rsp := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide), rsp₇,
      dec .rsp (by decide) _ h₁.rsp]
  have r15₉ : s₉.gpr .r15 = cx s₀ := by rw [g₉ _ (by decide) (by decide), r15₈]
  refine WP.mono (restoreLoads_ok hp r15₉ sv₉ rsp₉ (by rw [rd₉, rd₈, rd₇, rd₆'])
    (by rw [wr₉, wr₈, wr₇, wr₆'])) fun s' ⟨cs', _, m'⟩ => ?_
  refine ⟨cs', ?_, ?_⟩
  · rw [m']
    have f₅ : Frame [dR s₀] s₂.mem s₅.mem := by rw [← m₄₂]; exact h₅.frame
    have l₁ : Frame (allR s₀) s₀.mem s₁.mem := h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₂ : Frame (allR s₀) s₁.mem s₂.mem := f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₅ : Frame (allR s₀) s₂.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_all s₀
    have l₆ : Frame (allR s₀) s₅.mem s₆.mem := f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₇ : Frame (allR s₀) s₆.mem s₇.mem := f₇.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst h <;> exact sub_all s₀ (by decide)
    have l₈ : Frame (allR s₀) s₇.mem s₈.mem := f₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact t_all s₀
    have l₉ : Frame (allR s₀) s₈.mem s₉.mem := f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    exact ((((((l₁.trans l₂).trans l₅).trans l₆).trans l₇).trans l₈).trans l₉)
  · have C' : bytesAt s'.mem (dp s₀) (L s₀) = bytesAt s₅.mem (dp s₀) (L s₀) := by
      rw [m', bytesAt_frame f₉ (by rdisj_all) hL'.le, bytesAt_frame f₈ (by rdisj_all) hL'.le,
        bytesAt_frame f₇ (by rdisj_all) hL'.le, C₆]
    have T' : bytesAt s'.mem (tp s₀) 16 = mac (otk s₀) (macData (A s₀) (bytesAt s₅.mem (dp s₀) (L s₀))) := by
      rw [m', bytesAt_frame f₉ (by rdisj_all) (by decide), m₈, tag_bytes, t₇,
        show (2 : Nat) ^ 128 = 256 ^ 16 from rfl, VG.Proof.Poly1305.leBytes_mod, C₅]
      rfl
    rw [C', T', C₅]
    rfl

end VG.Proof.ChaCha20Poly1305.X86_64.Short

/-!
# ChaCha20-Poly1305 for short records (x86-64): `open`

`Stitch.openShort`, from its parts: the keystream (`shortPre_ok`), the
padded additional data and data (`padAad_ok`, `padData_ok`), the tag
(`mac_ok`), stored at `ctx + 48` (`openStore_ok`), the data decrypted from
the keystream at `ctx + 736` (`xorBufX_ok`), the keystream wiped
(`zeroKs_ok`), the tags compared (`compare_ok`) and the registers restored
(`restoreLoads_ok`).
-/


namespace VG.Proof.ChaCha20Poly1305.X86_64.Short

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (bytesAt leNum leBytes mac)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Impl.ChaCha20.X86_64 (at_)

/-- The tag from `r11:rbx` stored at `ctx + 48`, and the data's registers
reloaded from their stash. -/
abbrev openStore : List Instr :=
  [.store (at_ .rcx 48) .r11, .store (at_ .rcx 56) .rbx, .mov .r15 (.reg .rcx),
   .mov .r14 (.mem (at_ .r15 536)), .mov .r13 (.mem (at_ .r15 528)), .mov .r12 (.mem (at_ .r15 520))]

set_option simprocs false in
theorem openStore_ok {e : Bool} {s₀ : State} (hp : APre e s₀) {s : State} (hrcx : s.gpr .rcx = cx s₀)
    (h536 : s.mem.readW (off (cx s₀) 536) 64 = dp s₀) (h528 : s.mem.readW (off (cx s₀) 528) 64 = s₀.gpr .r9)
    (h520 : s.mem.readW (off (cx s₀) 520) 64 = tp s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block openStore) s fun s' =>
      s'.mem = (s.mem.writeW (off (cx s₀) 48) (s.gpr .r11)).writeW (off (cx s₀) 56) (s.gpr .rbx) ∧
      s'.gpr .r15 = cx s₀ ∧ s'.gpr .r14 = dp s₀ ∧ s'.gpr .r13 = s₀.gpr .r9 ∧ s'.gpr .r12 = tp s₀ ∧
      (∀ r, r ≠ .r15 → r ≠ .r14 → r ≠ .r13 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ a, a + 8 ≤ 1696 → InRegions s.wr (off (cx s₀) a) 8 := fun a h => by
    rw [hwr]; exact hp.in_ctx h
  have i : ∀ a, a + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have o0 := o 48 (by lit_omega); have o1 := o 56 (by lit_omega)
  have i0 := i 536 (by lit_omega); have i1 := i 528 (by lit_omega); have i2 := i 520 (by lit_omega)
  have r0 : ((s.mem.writeW (off (cx s₀) 48) (s.gpr .r11)).writeW (off (cx s₀) 56) (s.gpr .rbx)).readW
      (off (cx s₀) 536) 64 = dp s₀ := by
    rw [readW64_off _ _ _ (by decide) (by decide) (by decide), readW64_off _ _ _ (by decide) (by decide)
      (by decide), h536]
  have r1 : ((s.mem.writeW (off (cx s₀) 48) (s.gpr .r11)).writeW (off (cx s₀) 56) (s.gpr .rbx)).readW
      (off (cx s₀) 528) 64 = s₀.gpr .r9 := by
    rw [readW64_off _ _ _ (by decide) (by decide) (by decide), readW64_off _ _ _ (by decide) (by decide)
      (by decide), h528]
  have r2 : ((s.mem.writeW (off (cx s₀) 48) (s.gpr .r11)).writeW (off (cx s₀) 56) (s.gpr .rbx)).readW
      (off (cx s₀) 520) 64 = tp s₀ := by
    rw [readW64_off _ _ _ (by decide) (by decide) (by decide), readW64_off _ _ _ (by decide) (by decide)
      (by decide), h520]
  simp only [off] at o0 o1 i0 i1 i2 r0 r1 r2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hrcx, o0, o1, i0, i1, i2, r0, r1, r2, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ => by simp only [h₁, h₂, h₃, h₄, ite_false],
    trivial⟩

theorem tag_bytes48 (m : Mem) (c : Addr) (lo hi : BitVec 64) :
    bytesAt ((m.writeW (off c 48) lo).writeW (off c 56) hi) (off c 48) 16 =
      leBytes 16 (lo.toNat + 2 ^ 64 * hi.toNat) := by
  have := tag_bytes m (off c 48) lo hi
  simp only [off_off] at this
  exact this

theorem openShort_eq (x : Impl.ChaCha20.X86_64.Callee) : openShort x =
    .seq (shortPre x.vl) (.seq padAad (.seq padData (.seq macShort
      (.seq (.block ((openStore ++ ptr .rsi .r15 736) ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX x.wide .r14) (.seq (.block [.mov32 .rdx (.imm 512)]) (.seq (zeroKs x.wide)
        (.block ((ptr .rcx .r15 48 ++ compare) ++ restoreLoads))))))))) := rfl

/-- `openShort`, from the state after `entry`: the registers restored but
`rax`, only the context and the data written, and the contract's result. -/
theorem openShort_ok (x : Impl.ChaCha20.X86_64.Callee) (hw : x.wide = 4 ∨ x.wide = 5 ∨ x.wide = 6)
    {s₀ : State} (hp : APre false s₀) (hLe : L s₀ ≤ 448) (hA : AL s₀ < 16) :
    WP isa (openShort x) (entryS s₀) fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ Frame (allR s₀) s₀.mem s'.mem ∧ openX86_64.post s₀ s' := by
  have hL' : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  rw [openShort_eq]
  refine WP.seq (WP.mono (shortPre_ok x.vl hp hLe) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (padAad_ok hp hA h₁.r15 h₁.rbx h₁.rbp h₁.rd h₁.wr) fun s₂ ⟨a₂, f₂, g₂, rd₂, wr₂⟩ => ?_)
  have G₂ := fun (r : Reg) (h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r9 ∧ r ≠ .rsi) =>
    g₂ r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  refine WP.seq (WP.mono (padData_ok hp ((G₂ .r15 (by decide)).trans h₁.r15) ((G₂ .r14 (by decide)).trans h₁.r14)
    ((G₂ .r13 (by decide)).trans h₁.r13) (by rw [rd₂, h₁.rd]) (by rw [wr₂, h₁.wr]))
    fun s₃ ⟨t₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have G₃ := fun (r : Reg) (h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r9 ∧ r ≠ .rsi) =>
    (g₃ r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).trans (G₂ r h)
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  -- What the tag reads.
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL'.le, bytesAt_frame h₁.frame (by rdisj_all) hL'.le]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame f₃ (by rdisj_all) hL'.le, D₂]
  have A₁ : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  have hAA : AL s₀ ≠ 0 → bytesAt s₃.mem (off (cx s₀) 576) 16 = A s₀ ++ pad16 (A s₀) := fun h => by
    rw [bytesAt_frame f₃ (by rdisj_all) (by decide), a₂ h, A₁]
  have tB0 : (sub s₀ 624 16).Disjoint (dR s₀) := hp.c_d.sub_left (sub_ctx s₀ (by decide))
  have tB : (⟨dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16)), L s₀ % 16⟩ : Region).Disjoint (sub s₀ 624 16) :=
    (Src.disj_sub tB0 (a := 16 * (L s₀ / 16)) (n := L s₀ % 16) (by omega)).dsymm
  have hT : L s₀ % 16 ≠ 0 → bytesAt s₃.mem (off (cx s₀) 624) 16 =
      bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ % 16) ++
        pad16 (bytesAt s₃.mem (dp s₀) (L s₀)) := fun h => by
    rw [t₃ h, bytesAt_frame f₃ (by rdisj_all) hL'.le, bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact tB) (by omega)]
  have key₃ : bytesAt s₃.mem (off (cx s₀) 672) 32 = otk s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) (by decide), bytesAt_frame f₂ (by rdisj_all) (by decide), h₁.key]
  refine WP.seq (WP.mono (mac_ok hp ((G₃ .r15 (by decide)).trans h₁.r15) ((G₃ .r14 (by decide)).trans h₁.r14)
    ((G₃ .r13 (by decide)).trans h₁.r13) ((G₃ .rbp (by decide)).trans h₁.rbp) rd₃' wr₃'
    (VG.Proof.Poly1305.length_bytesAt _ _ _) hAA hT) fun s₄ ⟨t₄, rcx₄, rsp₄, rd₄, wr₄, m₄⟩ => ?_)
  rw [key₃, D₃] at t₄
  have sr := setupMem_read (s₀ := s₀) s₃
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (openStore_ok hp rcx₄
    (by rw [m₄, sr.2.2.2.2.1, (G₃ .r14 (by decide)).trans h₁.r14])
    (by rw [m₄, sr.2.2.2.1, (G₃ .r13 (by decide)).trans h₁.r13])
    (by rw [m₄, sr.2.2.1, (G₃ .r12 (by decide)).trans h₁.r12]) (by rw [rd₄, rd₃']) (by rw [wr₄, wr₃']))
    fun s₅ ⟨m₅, r15₅, r14₅, r13₅, r12₅, g₅, rd₅, wr₅⟩ => ?_)))
  refine WP.mono (ptr_ok .rsi .r15 (k := 736) (by lit_omega) s₅) fun s₆ ⟨e₆, g₆, rd₆, wr₆, m₆⟩ => ?_
  refine WP.mono (Q := fun (s' : State) => s'.gpr .rdx = s₀.gpr .r9 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s₆.gpr q) ∧
      s'.rd = s₆.rd ∧ s'.wr = s₆.wr ∧ s'.mem = s₆.mem) ?_ fun s₇ ⟨d₇, g₇, rd₇, wr₇, m₇⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, Option.map_some,
      Option.some.injEq, exists_eq_left', ite_true]
    exact ⟨by rw [g₆ _ (by decide), r13₅], fun q hq => by simp [hq], trivial, trivial, trivial⟩
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃']
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃']
  have rsi₇ : s₇.gpr .rsi = off (cx s₀) 736 := by rw [g₇ _ (by decide), e₆, r15₅]
  have r14₇ : s₇.gpr .r14 = dp s₀ := by rw [g₇ _ (by decide), g₆ _ (by decide), r14₅]
  have dB : (dR s₀).Disjoint ⟨off (cx s₀) 736, L s₀⟩ :=
    hp.c_d.symm.sub_right (sub_ctx s₀ (k := 736) (n := L s₀) (by omega))
  refine WP.seq (WP.mono (XorBufX.xorBufX_ok hw (d := .r14) (by decide)
    r14₇ rsi₇ (by rw [d₇]; exact hL s₀) hL' dB
    ⟨dR s₀, by rw [wr₇']; exact hp.d_wr, Region.contains_self _ _⟩
    ⟨ctxR s₀, by rw [rd₇', wr₇']; simp [hp.ctx_wr], by
      rw [off_eq]; exact Offset.contains_base _ (show 736 + L s₀ ≤ 1696 by omega) (by lit_omega)⟩)
    fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (mov32_rdx_ok 512 s₈) fun s₉ ⟨d₉, g₉, rd₉, wr₉, m₉⟩ => ?_)
  have r15₉ : s₉.gpr .r15 = cx s₀ := by
    rw [g₉ _ (by decide), h₈.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₇ _ (by decide), g₆ _ (by decide), r15₅]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.X86_64.zeroKs_ok hw hp (n := 512) (by decide) (by decide)
    (by rw [d₉]; rfl) r15₉ (by rw [wr₉, h₈.wr, wr₇'])) fun s₁₀ ⟨g₁₀, rd₁₀, wr₁₀, f₁₀, _⟩ => ?_)
  -- The frames so far.
  have f₄ : Frame [sub s₀ 520 32, sub s₀ 592 16] s₃.mem s₄.mem := by rw [m₄]; exact setupMem_frame s₃
  have c0 : (sub s₀ 48 16).Contains (off (cx s₀) 48) (64 / 8) := contains_sub s₀ (by decide) (by decide) (by decide)
  have c8 : (sub s₀ 48 16).Contains (off (cx s₀) 56) (64 / 8) := contains_sub s₀ (by decide) (by decide) (by decide)
  have f₅ : Frame [sub s₀ 48 16] s₄.mem s₅.mem := by
    rw [m₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  have m₇₅ : s₇.mem = s₅.mem := by rw [m₇, m₆]
  have f₈ : Frame [dR s₀] s₅.mem s₈.mem := by rw [← m₇₅]; exact h₈.frame
  have f₉ : Frame [sub s₀ 672 1024] s₈.mem s₁₀.mem := by rw [← m₉]; exact f₁₀
  have r15₁₀ : s₁₀.gpr .r15 = cx s₀ := by rw [g₁₀ _ (by decide) (by decide), r15₉]
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, h₈.rd, rd₇']
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, h₈.wr, wr₇']
  have r12₁₀ : s₁₀.gpr .r12 = tp s₀ := by
    rw [g₁₀ _ (by decide) (by decide), g₉ _ (by decide),
      h₈.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₇ _ (by decide), g₆ _ (by decide), r12₅]
  refine WP.block_append (WP.block_append (WP.mono (ptr_ok .rcx .r15 (k := 48) (by lit_omega) s₁₀)
    fun s₁₂ ⟨e₁₂, g₁₂, rd₁₂, wr₁₂, m₁₂⟩ => ?_))
  refine WP.mono (compare_ok hp (by rw [e₁₂, r15₁₀])
    (by rw [g₁₂ _ (by decide), r12₁₀]) (by rw [rd₁₂, rd₁₀']) (by rw [wr₁₂, wr₁₀']))
    fun s₁₃ ⟨rax₁₃, g₁₃, m₁₃, rd₁₃, wr₁₃⟩ => ?_
  have m₁₂' : s₁₂.mem = s₁₀.mem := m₁₂
  have sv : Saved s₀ s₁₃.mem := by
    rw [m₁₃, m₁₂']
    exact (((((h₁.saved.frame f₂ (by rdisj_all)).frame f₃ (by rdisj_all)).frame f₄ (by rdisj_all)).frame f₅
      (by rdisj_all)).frame f₈ (by rdisj_all)).frame f₉ (by rdisj_all)
  have rsp₁₃ : s₁₃.gpr .rsp = s₀.gpr .rsp := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide), g₁₀ _ (by decide) (by decide),
      g₉ _ (by decide), h₈.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide), rsp₄,
      G₃ .rsp (by decide), h₁.rsp]
  refine WP.mono (restoreLoads_ok hp (by rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide),
    r15₁₀]) sv rsp₁₃ (by rw [rd₁₃, rd₁₂, rd₁₀']) (by rw [wr₁₃, wr₁₂, wr₁₀']))
    fun s' ⟨cs', rax', m'⟩ => ?_
  refine ⟨cs', ?_, ?_⟩
  · rw [m', m₁₃, m₁₂']
    have l₁ : Frame (allR s₀) s₀.mem s₁.mem := h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₂ : Frame (allR s₀) s₁.mem s₂.mem := f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₃ : Frame (allR s₀) s₂.mem s₃.mem := f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₄ : Frame (allR s₀) s₃.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst h <;> exact sub_all s₀ (by decide)
    have l₅ : Frame (allR s₀) s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    have l₈ : Frame (allR s₀) s₅.mem s₈.mem := f₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d_all s₀
    have l₉ : Frame (allR s₀) s₈.mem s₁₀.mem := f₉.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_all s₀ (by decide)
    exact ((((((l₁.trans l₂).trans l₃).trans l₄).trans l₅).trans l₈).trans l₉)
  · -- The tags, and the plaintext.
    have hM : L s₀ ≤ 960 := by omega
    have ks₇ : ∀ k < L s₀, s₇.mem (off (cx s₀) (736 + k)) =
        (Spec.ChaCha20.keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0 := by
      rw [m₇₅]
      exact ks_frame f₅ (by rdisj_all) hM (ks_frame f₄ (by rdisj_all) hM (ks_frame f₃ (by rdisj_all) hM
        (ks_frame f₂ (by rdisj_all) hM h₁.ks)))
    have D₅ : bytesAt s₅.mem (dp s₀) (L s₀) = D s₀ := by
      rw [bytesAt_frame f₅ (by rdisj_all) hL'.le, bytesAt_frame f₄ (by rdisj_all) hL'.le, D₃]
    have P₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
      rw [← D₅, ← m₇₅, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
      apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
      intro k hk
      rw [h₈.data k hk, show off (cx s₀) 736 + BitVec.ofNat 64 k = off (cx s₀) (736 + k) by
        rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], ks₇ k hk]
    have P' : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
      rw [m', m₁₃, m₁₂', bytesAt_frame f₉ (by rdisj_all) hL'.le, P₈]
    have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₁₂.mem (off (cx s₀) 48) 16 := by
      rw [m₁₂', bytesAt_frame f₉ (by rdisj_all) (by decide), bytesAt_frame f₈ (by rdisj_all) (by decide), m₅,
        tag_bytes48, t₄, show (2 : Nat) ^ 128 = 256 ^ 16 from rfl, VG.Proof.Poly1305.leBytes_mod]
      rfl
    have T0₁₂ : bytesAt s₁₂.mem (tp s₀) 16 = T0 s₀ := by
      rw [m₁₂', bytesAt_frame f₉ (by rdisj_all) (by decide), bytesAt_frame f₈ (by rdisj_all) (by decide),
        bytesAt_frame f₅ (by rdisj_all) (by decide), bytesAt_frame f₄ (by rdisj_all) (by decide),
        bytesAt_frame f₃ (by rdisj_all) (by decide), bytesAt_frame f₂ (by rdisj_all) (by decide),
        bytesAt_frame h₁.frame (by rdisj_all) (by decide)]
    rw [openX86_64, Contract.post_mk, rax', rax₁₃]
    split
    next pt hpt =>
      obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
      exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₁₂.symm)), P'⟩
    next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₁₂)

end VG.Proof.ChaCha20Poly1305.X86_64.Short
