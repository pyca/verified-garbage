import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes

`tail`, from the state after the eight-block loop of `vg_chacha20_xor_avx2`
(`TInv`: the first `p` bytes of data done, `p` a multiple of 64, fewer than
512 left), to the end of the function. What does not depend on the code
(`Done`, the last bytes from `buf`, the end) is `Avx512Tail.Tail`'s.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (APre est edp eL ebp edR eret estk D0 KS frR eL_lt xorAvx2X86_64
  add_ofNat in_dR calleeSaved_ne ctr_add plus hiR hiR_contains hiR_sub Consts)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Done win win_sub not_win ea_win ks_at ctx_of Ctx wregs S0
  r9_not_calleeSaved data_step fromBuf_ok fin_ok Fin SInv Done.fin scalarT_ok)

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
  consts : Consts s.mem (ebp s₀)
  incs : Incs s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-- The constants survive a memory whose bytes of `buf` are unchanged. -/
theorem consts_of_bytes {buf : Addr} {m m' : Mem} (h : ∀ i < 80, m'.readW (buf + BitVec.ofNat 64 (4 * i)) 32 =
    m.readW (buf + BitVec.ofNat 64 (4 * i)) 32) (hc : Consts m buf) (hi : Incs m buf) :
    Consts m' buf ∧ Incs m' buf := by
  have hb : ∀ k < 320, m' (buf + BitVec.ofNat 64 k) = m (buf + BitVec.ofNat 64 k) := fun k hk => by
    rw [Avx512.byte_dword m', Avx512.byte_dword m, h _ (by omega)]
  have hr : ∀ d n, d + n / 8 ≤ 320 → m'.readW (buf + BitVec.ofNat 64 d) n = m.readW (buf + BitVec.ofNat 64 d) n :=
    fun d n hdn => Mem.readW_congr fun i hi => by rw [add_ofNat, hb _ (by omega)]
  refine ⟨⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩, fun k hk p hp => ?_⟩
  · rw [hr 128 256 (by omega)]; exact hc.lo16
  · rw [hr 128 256 (by omega)]; exact hc.hi16
  · rw [hr 160 256 (by omega)]; exact hc.m8.1
  · rw [hr 160 256 (by omega)]; exact hc.m8.2
  · intro l q hl hq; rw [hr _ 32 (by omega)]; exact hc.inc l q hl hq
  · rw [hr _ 32 (by omega)]; exact hi k hk p hp

theorem TInv.cst {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    Consts s.mem (s.gpr .r9) ∧ Incs s.mem (s.gpr .r9) := by
  rw [hr9]; exact ⟨h.consts, h.incs⟩

/-! ## The steps -/

theorem start_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) :
    WP isa (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 257)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (257 : BitVec 32) = 257 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨⟨by simp [h.rdi], by simp [h.rcx], by simp [h.rsi], by simp [h.rdx], h.le,
    h.dvd, fun r hr => by simp [(r9_not_calleeSaved hr).1, h.keep r hr], h.rd, h.wr, h.cnt, h.data,
    h.consts, h.incs, h.frame⟩, by simp [h.rcx], ?_⟩
  simp only [h.rdx]
  rw [toNat_ofNat_lt (by omega)]
  rfl

theorem cmp_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .cmp .rdx (.imm 129)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 129)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (129 : BitVec 32) = 129 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.consts, h.incs,
    h.frame⟩, hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega)]
  rfl

theorem cmp65_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .cmp .rdx (.imm 65)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < 65)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (65 : BitVec 32) = 65 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.consts, h.incs,
    h.frame⟩, hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega)]
  rfl

theorem TInv.sinv {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) : SInv s₀ p s :=
  ⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.frame⟩

theorem test_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.zf = some (decide (eL s₀ - p = 0)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.rdx, h.le, h.dvd, h.keep, h.rd, h.wr, h.cnt, h.data, h.consts, h.incs,
    h.frame⟩, hr9, ?_⟩
  rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := eL s₀ - p) (y := 0) (by omega) (by omega)]
  simp

theorem done_of {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀)
    (he : eL s₀ - p = 0) : Done s₀ s :=
  ⟨hr9, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega)], h.frame⟩

set_option simprocs false in
theorem adv_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hge : 256 ≤ eL s₀ - p) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 4), .store32 (at_ .rdi 48) .rax,
      .alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)]) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 256) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 256)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 4) ∧
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
      ((stateAt s.mem (est s₀))[12] + 4)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, by simp⟩

theorem full_eq : full = .seq (.block setup) (.seq (rounds2 10)
    (.block ((addIn ++ xorSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSet .xmm4 .xmm5 .xmm6 .xmm7 128) ++
      ([.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 4), .store32 (at_ .rdi 48) .rax,
        .alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr)))) := by
  simp only [full, List.append_assoc]

theorem fullT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hge : 257 ≤ eL s₀ - p) {s : State}
    (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa full s fun s' => TInv s₀ (p + 256) s' ∧ s'.gpr .r9 = ebp s₀ := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega
  have hc : Ctx 64 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  obtain ⟨dsw, dsb, dwb, _, _⟩ := Avx512Tail.regions_disj hp (p := p) (n := 256) (by omega)
  rw [full_eq]
  refine WP.seq (WP.mono (setup_ok (Or.inl rfl) hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx 64 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (full_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv_ok hp (p := p) (by omega) (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (rd₃.trans (rd₂.trans h.rd)) (wr₃.trans (wr₂.trans h.wr)))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄⟩ => ?_
  have ws : wregs 64 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 256] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.reduceMul]
  rw [ws, m₂] at f₃
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dsb
      · exact dsw)
  have C₃ : Consts s₃.mem (ebp s₀) ∧ Incs s₃.mem (ebp s₀) :=
    consts_of_bytes (by rw [g₂, hr9, m₂] at b₃; exact b₃) h.consts h.incs
  have hsi : ∀ r ∈ [Avx2.stR (est s₀)], (hiR (ebp s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_b.sub_right (hiR_sub _)).symm
  refine ⟨⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂, by omega,
    Nat.dvd_add h.dvd ⟨4, rfl⟩, fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr],
    ?_, ?_, C₃.1.frame f₄ hsi, incs_frame C₃.2 f₄ hsi, ?_⟩, by rw [gk _ (by decide) (by decide) (by decide)]; exact hr9⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show (p + 256) / 64 = p / 64 + 4 by omega]
    exact ctr_add _ _ 4
  · have F : Frame [⟨ebp s₀, 256⟩, win s₀ p 256, Avx2.stR (est s₀)] s.mem s₄.mem :=
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
  · refine h.frame.trans ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨edR s₀, by simp, win_sub (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## The last bytes, from `buf` -/

/-- After the keystream of `n ≤ 256` bytes is in `buf`, written by the code
from `s` (`hb`, `hf`): the data from there. -/
theorem fromBufT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hn : eL s₀ - p ≤ 256) {s s₃ : State}
    (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) (g₃ : s₃.gpr = s.gpr) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (f₃ : Frame [⟨ebp s₀, 256⟩, win s₀ p 0] s.mem s₃.mem)
    (hb : ∀ k < eL s₀ - p, s₃.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0) :
    WP isa fromBuf s₃ (Done s₀) := by
  have hL := eL_lt s₀
  have hpL := h.le
  have nd : ∀ k < eL s₀, ∀ r ∈ [(⟨ebp s₀, 256⟩ : Region), win s₀ p 0],
      ¬ r.Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hp.d_b _ (in_dR hk) (Region.sub_prefix (by omega) _ hc)
    · simp only [Region.Contains]; omega
  refine fromBuf_ok hp (p := p) (n := eL s₀ - p) (by have := h.le; omega) hn (by rw [g₃]; exact h.rsi)
    (by rw [g₃]; exact hr9) (by rw [g₃]; exact h.rdx) (rd₃.trans h.rd) (wr₃.trans h.wr)
    (fun r hr => by rw [g₃]; exact h.keep r hr) (fun k hk => ?_) (fun k hk => ?_) hb ?_
  · rw [f₃ _ (nd k (by omega)), h.data k (by omega), ite_eq_left hk]
  · rw [add_ofNat, f₃ _ (nd _ (by omega)), h.data _ (by omega), ite_eq_right (by omega)]
  · refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨edR s₀, by simp, win_sub (by have := h.le; omega)⟩

theorem lastT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa last s (Done s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 0 ≤ eL s₀ := by have := h.le; omega
  have hc : Ctx 0 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  refine WP.seq (WP.mono (setup_ok (Or.inr rfl) hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [sm₂.wr.trans wr₁]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : wregs 0 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 0] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.mul_zero]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  refine fromBufT_ok hp hle h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃ fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega),
    hS, ks_at h.dvd (by omega) (by omega), Nat.add_sub_cancel_left, ← hS']

theorem last1T_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa last1 s (Done s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 0 ≤ eL s₀ := by have := h.le; omega
  have hc : Ctx 0 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  refine WP.seq (WP.mono (setup1_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds1_ok hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [sm₂.wr.trans wr₁]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last1_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : wregs 0 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 0] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.mul_zero]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  refine fromBufT_ok hp (by omega) h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃ fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega),
    hS, ks_at h.dvd (by omega) (by omega), Nat.add_sub_cancel_left, ← hS']

/-! ## The whole tail -/

theorem smallT_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa small s (Fin s₀) := by
  refine WP.seq (WP.mono (cmp65_ok h hr9) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 65)) (by simp [eval, c₁]) (fun _ => ?_) (fun _ => ?_)
  · exact scalarT_ok hp h₁.sinv
  · exact WP.mono (last1T_ok hp hle h₁ r₁) fun _ d => d.fin hp

theorem tail_eq : tail =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b (.block []) full)
    (.seq (.block [.alu .cmp .rdx (.imm 129)])
    (.seq (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) last)
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))) := rfl

theorem rest_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 257) {s : State} (h : TInv s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) (hc : s.cf = some (decide (eL s₀ - p < 129))) :
    WP isa (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) last) s
      (Fin s₀) := by
  refine WP.ite (decide (eL s₀ - p < 129)) (by simp [eval, hc]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h hr9) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · exact smallT_ok hp (by omega) h₂ r₂
  · exact WP.mono (lastT_ok hp (by omega) h hr9) fun _ d => d.fin hp

theorem tail_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 512) {s : State}
    (h : TInv s₀ p s) :
    WP isa tail s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [tail_eq]
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => ∃ p', eL s₀ - p' < 257 ∧ TInv s₀ p' s ∧
      s.gpr .r9 = ebp s₀) ?_ fun s₂ ⟨p', hp', h₂, r₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (M := isa) ⟨p, hs, h₁, r₁⟩
    · simp only [decide_eq_false_iff_not] at hs
      exact WP.mono (fullT_ok hp (by omega) h₁ r₁) fun s' ⟨h', r'⟩ => ⟨p + 256, by omega, h', r'⟩
  · refine WP.seq (WP.mono (cmp_ok h₂ r₂) fun s₃ ⟨h₃, r₃, c₃⟩ => ?_)
    exact WP.seq (WP.mono (rest_ok hp hp' h₃ r₃ c₃) fun s₄ d => fin_ok d)

end VG.Proof.ChaCha20.X86_64.Avx2Tail
