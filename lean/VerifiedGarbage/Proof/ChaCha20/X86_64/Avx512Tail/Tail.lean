import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Out
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes

`tail`, from the state after the sixteen-block loop of
`vg_chacha20_xor_avx512` (`TInv`: the first `p` bytes of data done, `p` a
multiple of 64, fewer than 1024 left), to the end of the function.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (APre est edp eL ebp edR eret estk D0 KS frR eL_lt xorAvx2X86_64
  add_ofNat in_dR calleeSaved_ne vz_ok ctr_ctr ctr_add plus plus_block)

/-! ## The invariant -/

/-- The first `p` bytes of the data done. -/
structure TInv (s₀ : State) (p : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)
  le : p ≤ eL s₀
  dvd : 64 ∣ p
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (Avx2.S0 s₀) (p / 64)
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) =
    if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  incs : Incs s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-- All the data done. -/
structure Done (s₀ : State) (s : State) : Prop where
  r9 : s.gpr .r9 = ebp s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  frame : Frame (frR s₀) s₀.mem s.mem

/-- At the end of the last bytes: as `Done`, but memory outside the
function's regions is known only at the return address (`vg_chacha20_xor`
uses the stack below it). -/
structure Fin (s₀ : State) (s : State) : Prop where
  r9 : s.gpr .r9 = ebp s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

theorem r9_not_calleeSaved {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .r9 ∧ r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Regions -/

section
variable {s₀ : State}

/-- `n` bytes of data from byte `p`. -/
abbrev win (s₀ : State) (p n : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 p, n⟩

theorem win_sub {p n : Nat} (h : p + n ≤ eL s₀) : Region.Sub (win s₀ p n) (edR s₀) :=
  Offset.sub_base _ (by omega)

theorem not_win {p n k : Nat} (h : p + n ≤ eL s₀) (hk : k < eL s₀) (ho : k < p ∨ p + n ≤ k) :
    ¬ (win s₀ p n).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem win_byte {p k : Nat} : edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) =
    edp s₀ + BitVec.ofNat 64 k ∨ k < p := by
  by_cases h : p ≤ k
  · exact .inl (by rw [add_ofNat, Nat.add_sub_cancel' h])
  · exact .inr (by omega)

theorem ea_win {p k : Nat} (h : p ≤ k) : edp s₀ + BitVec.ofNat 64 k =
    edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) := by
  rw [add_ofNat, Nat.add_sub_cancel' h]

/-- The keystream of byte `k`, from block `p / 64` on. -/
theorem ks_at {p k : Nat} (hp : 64 ∣ p) (hpk : p ≤ k) (hk : k < eL s₀) :
    (KS s₀).getD k 0 =
      (serialize (plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (ctr (Avx2.S0 s₀) (p / 64)) j))
        (ctr (Avx2.S0 s₀) (p / 64)) ((k - p) / 64))).getD ((k - p) % 64) 0 := by
  rw [plus_block, ctr_ctr, keystream_getD _ hk]
  obtain ⟨c, rfl⟩ := hp
  rw [show 64 * c / 64 + (k - 64 * c) / 64 = k / 64 by omega, show (k - 64 * c) % 64 = k % 64 by omega]

end

/-- Where the code around the rounds runs, `D` doublewords of data from byte
`p`. -/
theorem ctx_of {s₀ : State} (hp : APre s₀) {D p : Nat} (hw : p + 4 * D ≤ eL s₀) (hD : D ≤ 128) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hr9 : s.gpr .r9 = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hwr : s.wr = s₀.wr) : Ctx D s := by
  have hL := eL_lt s₀
  have r0 : regn D s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn D s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : regn D s 2 = win s₀ p (4 * D) := by simp only [regn, baseR, bsize, hrsi]
  refine ⟨fun b i n hb h _ => ?_, fun b b' hb hb' ne => ?_, hD⟩
  · rw [hwr, hp.wr]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]
      exact ⟨Avx2.stR (est s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [r1]
      exact ⟨Avx2.bufR (ebp s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [r2, add_ofNat]
      exact ⟨edR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · have d01 := hp.st_b
    have d02 := hp.st_d.sub_right (win_sub (s₀ := s₀) (p := p) (n := 4 * D) hw)
    have d12 := hp.d_b.symm.sub_right (win_sub (s₀ := s₀) (p := p) (n := 4 * D) hw)
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | with_reducible assumption | exact d01.symm | exact d02.symm | exact d12.symm

/-! ## The start -/

theorem start_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) :
    WP isa (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 512)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 512)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨⟨by simp [h.rdi], by simp [h.rcx],
    by simp [h.rsi], by simp [h.rdx], h.le,
    h.dvd, fun r hr => by simp [(r9_not_calleeSaved hr).1, h.keep r hr], h.rd, h.wr, h.cnt, h.data,
    h.incs, h.frame⟩, by simp [h.rcx], ?_⟩
  simp only [h.rdx]
  rw [toNat_ofNat_lt (by omega)]
  rfl

/-! ## Eight blocks into the data -/

set_option simprocs false in
theorem adv_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hge : 512 ≤ eL s₀ - p) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
      .alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512)]) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 512) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 512)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 8) ∧
      Frame [Avx2.stR (est s₀)] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by simp [hrd, hwr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [Avx2.stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 8)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, by simp⟩

/-- Data byte `k`, after the data from byte `p` changed (`hw`) and nothing
else (`hf`). -/
theorem data_step {s₀ : State} {p n : Nat} {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ k < eL s₀, k < p ∨ p + n ≤ k →
      ¬ r.Contains (edp s₀ + BitVec.ofNat 64 k) 1)
    (hw : ∀ k < n, m' (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) =
      m (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) ^^^ (KS s₀).getD (p + k) 0)
    (hm : ∀ k < eL s₀, m (edp s₀ + BitVec.ofNat 64 k) =
      if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k) :
    ∀ k < eL s₀, m' (edp s₀ + BitVec.ofNat 64 k) =
      if k < p + n then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  by_cases hin : p ≤ k ∧ k < p + n
  · have x := hw (k - p) (by omega)
    rw [← ea_win hin.1, Nat.add_sub_cancel' hin.1, hm k hk, ite_eq_right (by omega)] at x
    rw [x, ite_eq_left hin.2]
  · rw [hf _ (fun r hr => hd r hr k hk (by omega)), hm k hk]
    by_cases hlt : k < p
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Incs m (ebp s₀)) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ : Region).Disjoint r) : Incs m' (ebp s₀) := by
  intro k hk p hp
  rw [← h k hk p hp]
  refine hf.readW (r := ⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩) ?_ hd (by decide)
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simp only [incB]
    rw [show 4 * (64 + p) = 192 + (4 * (p + 16)) by omega, ← add_ofNat]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [incB]
    rw [show 4 * (48 + p) = 192 + 4 * p by omega, ← add_ofNat]
    exact Offset.contains_base _ (by omega) (by omega)

theorem full_eq : full = .seq (.block setup2) (.seq (rounds2 10)
    (.block ((finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256) ++
      ([.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
        .alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512)] : List Instr)))) := by
  simp only [full, List.append_assoc]

/-- The state, the data from byte `p` and the first 256 bytes of `buf` are
disjoint. -/
theorem regions_disj {s₀ : State} (hp : APre s₀) {p n : Nat} (hn : p + n ≤ eL s₀) :
    (Avx2.stR (est s₀)).Disjoint (win s₀ p n) ∧ (Avx2.stR (est s₀)).Disjoint ⟨ebp s₀, 256⟩ ∧
    (win s₀ p n).Disjoint ⟨ebp s₀, 256⟩ ∧
    (⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ : Region).Disjoint (Avx2.stR (est s₀)) ∧
    (⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ : Region).Disjoint (win s₀ p n) := by
  have sb : Region.Sub ⟨ebp s₀, 256⟩ (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega)
  have si : Region.Sub ⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ (Avx2.bufR (ebp s₀)) := Offset.sub_base _ (by omega)
  exact ⟨hp.st_d.sub_right (win_sub hn), hp.st_b.sub_right sb, (hp.d_b.sub_left (win_sub hn)).sub_right sb,
    (hp.st_b.sub_right si).symm, (hp.d_b.sub_left (win_sub hn)).sub_right si |>.symm⟩

theorem fullT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hge : 512 ≤ eL s₀ - p) {s : State}
    (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa full s fun s' => TInv s₀ (p + 512) s' ∧ s'.gpr .r9 = ebp s₀ := by
  have hL := eL_lt s₀
  have hw : p + 4 * 128 ≤ eL s₀ := by omega
  have hc : Ctx 128 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.incs
  obtain ⟨dsw, dsb, dwb, dis, diw⟩ := regions_disj hp (p := p) (n := 512) (by omega)
  rw [full_eq]
  refine WP.seq (WP.mono (setup2_ok (Or.inl rfl) hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx 128 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (full_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (rd₃.trans (rd₂.trans h.rd)) (wr₃.trans (wr₂.trans h.wr)))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄⟩ => ?_
  have ws : wregs 128 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 512] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.reduceMul]
  rw [ws, m₂] at f₃
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  -- The state before the rounds, in the terms of the code.
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by
    simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dsb
      · exact dsw)
  refine ⟨⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂, by omega,
    Nat.dvd_add h.dvd ⟨8, rfl⟩, fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr],
    ?_, ?_, ?_, ?_⟩, by rw [gk _ (by decide) (by decide) (by decide)]; exact hr9⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show (p + 512) / 64 = p / 64 + 8 by omega]
    exact ctr_add _ _ 8
  · have F : Frame [⟨ebp s₀, 256⟩, win s₀ p 512, Avx2.stR (est s₀)] s.mem s₄.mem :=
      (f₃.mono (by simp)).trans (f₄.mono (by simp))
    refine data_step F (fun r hr k hk ho => ?_) (fun k hk => ?_) h.data
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun hc => hp.d_b _ (in_dR hk) (Region.sub_prefix (by omega) _ hc)
      · exact not_win (by omega) hk ho
      · exact fun hc => hp.st_d _ hc (in_dR hk)
    · have hk' : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) 1 :=
        fun hc => dsw _ hc (Offset.contains_base _ (by omega) (by omega))
      rw [f₄ _ (by simpa using hk')]
      have x := d₃ k hk
      rw [g₂, h.rsi, m₂, hS] at x
      rw [x, ks_at h.dvd (by omega) (by omega), Nat.add_sub_cancel_left, ← hS']
  · have I₃ : Incs s₃.mem (ebp s₀) := fun k hk q hq => by
      have x := b₃ (incB k + q) (by rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp only [incB] <;> omega)
      rw [g₂, hr9, m₂] at x
      rw [x]; exact h.incs k hk q hq
    exact incs_frame I₃ f₄ (by simpa using dis)
  · refine h.frame.trans ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨edR s₀, by simp, win_sub (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## The last bytes, from `buf` -/

/-- `xorBuf` of the `n` bytes left, from `buf`, where the data from byte `p`
holds bytes `p … p + n` of the keystream: then all the data is done. -/
theorem fromBuf_ok {s₀ : State} (hp : APre s₀) {p n : Nat} (hn : p + n = eL s₀) (hn256 : n ≤ 256) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hr9 : s.gpr .r9 = ebp s₀)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hkeep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r)
    (hdone : ∀ k < p, s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0)
    (hrest : ∀ k < n, s.mem (edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) = D0 s₀ (p + k))
    (hks : ∀ k < n, s.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0)
    (hframe : Frame (frR s₀) s₀.mem s.mem) :
    WP isa fromBuf s (Done s₀) := by
  have hL := eL_lt s₀
  have sb : Region.Sub ⟨ebp s₀, n⟩ (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega)
  have hdb : (win s₀ p n).Disjoint ⟨ebp s₀, n⟩ := (hp.d_b.sub_left (win_sub (by omega))).sub_right sb
  refine WP.mono (XorBuf.xorBuf_ok (by decide) (by decide) hrsi hr9 hrdx (by omega) hdb
    ⟨edR s₀, by simp [hwr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
    ⟨Avx2.bufR (ebp s₀), by simp [hrd, hwr, hp.rd, hp.wr], by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega⟩)
    fun s' hq => ⟨?_, fun r hr => ?_, hq.rd.trans hrd, hq.wr.trans hwr, fun k hk => ?_, ?_⟩
  · rw [hq.keep _ (by decide) (by decide) (by decide), hr9]
  · obtain ⟨_, a, b, c⟩ := r9_not_calleeSaved hr
    rw [hq.keep r a b c]; exact hkeep r hr
  · by_cases hkp : k < p
    · rw [hq.frame _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact not_win (by omega) hk (.inl hkp)), hdone k hkp]
    · rw [ea_win (p := p) (by omega), hq.data (k - p) (by omega), hrest _ (by omega), hks _ (by omega),
        Nat.add_sub_cancel' (by omega)]
  · refine hframe.trans (hq.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨edR s₀, by simp, win_sub (by omega)⟩

theorem lastT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hpos : 0 < eL s₀ - p) (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa last s (Done s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 0 ≤ eL s₀ := by omega
  have hc : Ctx 0 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.incs
  obtain ⟨_, dsb, _, _, _⟩ := regions_disj hp (p := p) (n := 0) (by omega)
  refine WP.seq (WP.mono (setup_ok hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have hc₂ : Ctx 0 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (finish_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have ws : wregs 0 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 0] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.mul_zero]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have nd : ∀ k < eL s₀, ∀ r ∈ [(⟨ebp s₀, 256⟩ : Region), win s₀ p 0],
      ¬ r.Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hp.d_b _ (in_dR hk) (Region.sub_prefix (by omega) _ hc)
    · simp only [Region.Contains]; omega
  refine fromBuf_ok hp (p := p) (n := eL s₀ - p) (by omega) hle (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact hr9) (by rw [g₃']; exact h.rdx) (rd₃.trans (rd₂.trans h.rd))
    (wr₃.trans (wr₂.trans h.wr)) (fun r hr => by rw [g₃']; exact h.keep r hr) (fun k hk => ?_)
    (fun k hk => ?_) (fun k hk => ?_) ?_
  · rw [f₃ _ (nd k (by omega)), h.data k (by omega), ite_eq_left hk]
  · rw [add_ofNat, f₃ _ (nd _ (by omega)), h.data _ (by omega), ite_eq_right (by omega)]
  · rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega),
      hS, ks_at h.dvd (by omega) (by omega), Nat.add_sub_cancel_left, ← hS']
  · refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨edR s₀, by simp, win_sub (by omega)⟩

theorem part_eq : part = .seq (.block setup2) (.seq (rounds2 10) (.seq
    (.block ((finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) fromBuf)) := by
  simp only [part, List.append_assoc]

theorem adv256_ok {s₀ : State} {p : Nat} (hge : 256 ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block [.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)]) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 256) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 256)) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ => by simp [h₁, h₂], by simp⟩

theorem partT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hgt : 256 < eL s₀ - p) (hlt : eL s₀ - p < 512)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa part s (Done s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega
  have hc : Ctx 64 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.incs
  rw [part_eq]
  refine WP.seq (WP.mono (setup2_ok (Or.inr rfl) hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have hc₂ : Ctx 64 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (part_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv256_ok (s₀ := s₀) (p := p) (by omega) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx)) fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have g₄ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  have ws : wregs 64 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 256] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.reduceMul]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have nb : ∀ k < eL s₀, ¬ (⟨ebp s₀, 256⟩ : Region).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (in_dR hk) (Region.sub_prefix (by omega) _ hc)
  refine fromBuf_ok hp (p := p + 256) (n := eL s₀ - (p + 256)) (by omega) (by omega) e₁
    (by rw [g₄ _ (by decide) (by decide)]; exact hr9) e₂ (rd₄.trans (rd₃.trans (rd₂.trans h.rd)))
    (wr₄.trans (wr₃.trans (wr₂.trans h.wr)))
    (fun r hr => by obtain ⟨_, a, b⟩ := calleeSaved_ne hr; rw [g₄ r a b]; exact h.keep r hr)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_
  · rw [m₄]
    by_cases hkp : k < p
    · rw [f₃ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nb k (by omega)
        · exact not_win (by omega) (by omega) (.inl hkp)), h.data k (by omega), ite_eq_left hkp]
    · have x := d₃ (k - p) (by omega)
      rw [g₂, h.rsi, m₂, hS, ← ea_win (by omega)] at x
      rw [x, h.data k (by omega), ite_eq_right hkp, ks_at h.dvd (by omega) (by omega), ← hS']
  · rw [m₄, add_ofNat, f₃ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact nb _ (by omega)
      · exact not_win (by omega) (by omega) (.inr (by omega))), h.data _ (by omega), ite_eq_right (by omega)]
  · rw [m₄, show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega),
      hS, ks_at h.dvd (by omega) (by omega), ← hS',
      show (p + 256 + k - p) / 64 = 4 + k / 64 by omega, show (p + 256 + k - p) % 64 = k % 64 by omega]
  · rw [m₄]
    refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨edR s₀, by simp, win_sub (by omega)⟩

/-! ## The whole tail -/

set_option simprocs false in
theorem cmp_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .cmp .rdx (.imm 257)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 257)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (257 : BitVec 32) = 257 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.incs, h.frame⟩,
    hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega)]
  rfl

set_option simprocs false in
theorem test_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.zf = some (decide (eL s₀ - p = 0)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.incs, h.frame⟩,
    hr9, ?_⟩
  rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := eL s₀ - p) (y := 0) (by omega) (by omega)]
  simp

theorem done_of {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀)
    (he : eL s₀ - p = 0) : Done s₀ s :=
  ⟨hr9, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega)], h.frame⟩

theorem ret_frR {s₀ : State} (hp : APre s₀) : ∀ r ∈ frR s₀, (eret s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.ret_st
  · exact hp.ret_d
  · exact hp.ret_b

/-! ## At most 64 bytes, by `vg_chacha20_xor` -/

theorem cmp65_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .cmp .rdx (.imm 65)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 65)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (65 : BitVec 32) = 65 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.incs, h.frame⟩,
    hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega)]
  rfl

section
variable {s₀ : State} {p : Nat}

/-- The data left for `vg_chacha20_xor`. -/
abbrev pR (s₀ : State) (p : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 p, eL s₀ - p⟩

theorem pR_sub (hp : p ≤ eL s₀) : Region.Sub (pR s₀ p) (edR s₀) :=
  Offset.sub_base _ (by have := eL_lt s₀; omega)

theorem not_pR {k : Nat} (hk : k < p) (hp : p ≤ eL s₀) :
    ¬ (pR s₀ p).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

end

/-- What `vg_chacha20_xor` needs of `TInv` (and of `Avx2Tail.TInv`): all
but the constants in `buf`. -/
structure SInv (s₀ : State) (p : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)
  le : p ≤ eL s₀
  dvd : 64 ∣ p
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (Avx2.S0 s₀) (p / 64)
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) =
    if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame (frR s₀) s₀.mem s.mem

theorem TInv.sinv {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) : SInv s₀ p s :=
  ⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.frame⟩

/-- `vg_chacha20_xor` XORs the last bytes into the data, and returns with
`rsi` pointing at `buf`. -/
theorem scalarT_ok {s₀ : State} (hp : APre s₀) {p : Nat} {s : State} (h : SInv s₀ p s) :
    WP isa Impl.ChaCha20.X86_64.Avx2Tail.scalar s (Fin s₀) := by
  have hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hn : (BitVec.ofNat 64 (eL s₀ - p)).toNat = eL s₀ - p := toNat_ofNat_lt (by omega)
  have hwr : s₁.wr = frR s₀ := by rw [wr₁, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have ts := pR_sub (s₀ := s₀) hle
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rsi = ebp s₀ ∧ (∀ r ∈ calleeSaved, s₂.gpr r = s₀.gpr r) ∧
      s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧
      (∀ k < eL s₀, s₂.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0) ∧
      s₂.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64) ?_
    fun s₂ ⟨r₂, k₂, rd₂, wr₂, d₂, ret₂⟩ => ?_)
  · refine WP.call (k := xorStack 8) Xor.xor_rsi Avx2.xor_nosp (by rw [Avx2.xor_depth]; decide)
      (rd := []) (wr := [Avx2.stR (est s₀), pR s₀ p, Avx2.bufR (ebp s₀)]) ?_ ?_ ?_ ?_
    · rw [xorStack_pre8]
      simp only [xorX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
        hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp), g₁, h.rdi, h.rsi,
        h.rdx, h.rcx, hsp, hn]
      exact ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts,
        hp.stk_st.sub_left (Avx2.stk_ret s₀), (hp.stk_d.sub_left (Avx2.stk_ret s₀)).sub_right ts,
        hp.stk_b.sub_left (Avx2.stk_ret s₀), hp.stk_st.sub_left (Avx2.stk_stk s₀),
        (hp.stk_d.sub_left (Avx2.stk_stk s₀)).sub_right ts, hp.stk_b.sub_left (Avx2.stk_stk s₀),
        by have := hp.nowrap; bv_omega⟩
    · rw [hrd, hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
      · exact ⟨edR s₀, by simp, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega⟩
      · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
    · rw [hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
      · exact ⟨edR s₀, by simp, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega⟩
      · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
    · intro s₂ rd₂ wr₂ hcs hf _ ⟨s₃, hm₃, hg₃, hpost, hrsi₃⟩
      rw [Avx2.xor_depth, hsp] at hf
      have hce : stateAt s₁.callEntry.mem (est s₀) = stateAt s₁.mem (est s₀) := by
        rw [State.callEntry_mem]
        exact Xor.stateAt_frame (rs := [estk s₀])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
            rw [hsp]; exact below_call _ (by omega) (by omega)))
          (by simpa using hp.stk_st.symm)
      have Fce : Frame [estk s₀] s₁.mem s₁.callEntry.mem := by
        rw [State.callEntry_mem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
          rw [hsp]; exact below_call _ (by omega) (by omega))
      simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
        hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
        hne _ (by decide : Reg.rdx ≠ .rsp), g₁, h.rdi, h.rsi, h.rdx, hce, hm₃, m₁, h.cnt] at hpost
      rw [hn] at hpost
      refine ⟨?_, fun r hr => by rw [hcs r hr, g₁]; exact h.keep r hr, by rw [rd₂, rd₁, h.rd],
        by rw [wr₂, wr₁, h.wr], fun k hk => ?_, ?_⟩
      · rw [← hg₃ .rsi (by decide), hrsi₃, State.withRegions_gpr, hne _ (by decide), g₁, h.rcx]
      · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.st_d _ hc (in_dR hk)
        have n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.d_b _ (in_dR hk) hc
        have n_sk : ¬ (estk s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.stk_d _ hc (in_dR hk)
        by_cases hk' : k < p
        · rw [hf _ (by
            intro r hr
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact n_st
            · exact not_pR hk' hle
            · exact n_b
            · exact n_sk), m₁, h.data k hk, ite_eq_left hk']
        · have ea : edp s₀ + BitVec.ofNat 64 k =
              edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) := by
            rw [add_ofNat, Nat.add_sub_cancel' (by omega)]
          have x := Avx2.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - p) (by omega)
          rw [← ea, Fce _ (by simpa using n_sk), m₁, h.data k hk, ite_eq_right hk',
            keystream_getD _ (by omega)] at x
          rw [x, keystream_getD _ hk, ctr_ctr]
          obtain ⟨c, rfl⟩ := h.dvd
          rw [show 64 * c / 64 + (k - 64 * c) / 64 = k / 64 by omega,
            show (k - 64 * c) % 64 = k % 64 by omega]
      · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
        · intro r hr
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact hp.ret_st
          · exact hp.ret_d.sub_right ts
          · exact hp.ret_b
          · exact Avx2.ret_stk s₀
        · rw [m₁]
          exact h.frame.readW (Region.contains_self _ _) (ret_frR hp) (by decide)
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rd₂, wr₂, d₂, ret₂⟩
    · simp only [State.setReg, ite_true, r₂]
    · simp only [State.setReg, (r9_not_calleeSaved hr).1, ite_false]
      exact k₂ r hr

theorem Done.fin {s₀ : State} (hp : APre s₀) {s : State} (h : Done s₀ s) : Fin s₀ s :=
  ⟨h.r9, h.keep, h.rd, h.wr, h.data, h.frame.readW (Region.contains_self _ _) (ret_frR hp) (by decide)⟩

theorem smallT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hpos : 0 < eL s₀ - p) (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa small s (Fin s₀) := by
  refine WP.seq (WP.mono (cmp65_ok h hr9) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 65)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · exact scalarT_ok hp h₁.sinv
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (lastT_ok hp hpos hle h₁ r₁) fun _ d => d.fin hp

theorem tail_eq : tail =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 512)])
    (.seq (.ite .b (.block []) full)
    (.seq (.block [.alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) part)
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))) := rfl

theorem rest_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 512) {s : State} (h : TInv s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) (hc : s.cf = some (decide (eL s₀ - p < 257))) :
    WP isa (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) part) s
      (Fin s₀) := by
  refine WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, hc]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h hr9) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · simp only [decide_eq_false_iff_not] at he
      exact smallT_ok hp (by omega) (by omega) h₂ r₂
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (partT_ok hp (by omega) hlt h hr9) fun _ d => d.fin hp

theorem fin_ok {s₀ s : State} (h : Fin s₀ s) :
    WP isa (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]) s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  show WP isa (.block (([.vop .vzeroupper] : List Instr) ++ [.mov .rsi (.reg .r9)])) s _
  refine WP.block_append (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, _, _⟩ => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [State.setReg, (calleeSaved_ne hr).2.1, ite_false, g₁]
    exact h.keep r hr
  · simp only [State.setReg, m₁]
    exact h.ret
  · simp only [State.setReg, m₁]
    show bytesAt s.mem _ _ = _
    exact bytesAt_xor (length_keystream _ _) fun k hk => by rw [h.data k hk]
  · simp only [State.setReg, ite_true, g₁, h.r9]

theorem tail_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 1024) {s : State}
    (h : TInv s₀ p s) :
    WP isa tail s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [tail_eq]
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => ∃ p', eL s₀ - p' < 512 ∧ TInv s₀ p' s ∧
      s.gpr .r9 = ebp s₀) ?_
    fun s₂ ⟨p', hp', h₂, r₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ - p < 512)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (M := isa) ⟨p, hs, h₁, r₁⟩
    · simp only [decide_eq_false_iff_not] at hs
      exact WP.mono (fullT_ok hp (by omega) h₁ r₁) fun s' ⟨h', r'⟩ => ⟨p + 512, by omega, h', r'⟩
  · refine WP.seq (WP.mono (cmp_ok h₂ r₂) fun s₃ ⟨h₃, r₃, c₃⟩ => ?_)
    exact WP.seq (WP.mono (rest_ok hp hp' h₃ r₃ c₃) fun s₄ d => fin_ok d)

end VG.Proof.ChaCha20.X86_64.Avx512Tail
