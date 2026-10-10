import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
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
  refine WP.seq (WP.mono (setup_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
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

theorem adv3_ok {s₀ : State} {p : Nat} (hge : 256 ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr)) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 256) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 256)) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨by simp only [reduceCtorEq, ↓reduceIte]; rw [hrsi]; bv_omega,
    by simp only [reduceCtorEq, ↓reduceIte]; rw [hrdx]; bv_omega,
    fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

theorem last3_eq : last3 = .seq (.block setup3) (.seq (rounds3 10) (.seq (.block
    ((addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) fromBuf)) := rfl

theorem last3T_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hge : 257 ≤ eL s₀ - p) (hle : eL s₀ - p ≤ 384)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa last3 s (Done s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega
  have hc : Ctx 64 s := ctx_of hp hw (by decide) h.rdi hr9 h.rsi h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  rw [last3_eq]
  refine WP.seq (WP.mono (setup3_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds3_ok hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx 64 s₂ := ctx_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (last3_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv3_ok (s₀ := s₀) (p := p) (by omega) (by rw [g₃']; exact h.rsi) (by rw [g₃']; exact h.rdx))
    fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have ws : wregs 64 s₂ = [⟨ebp s₀, 256⟩, win s₀ p 256] := by
    simp only [wregs, win, g₂, hr9, h.rsi, Nat.reduceMul]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  have D₄ : ∀ k < eL s₀, s₄.mem (edp s₀ + BitVec.ofNat 64 k) =
      if k < p + 256 then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
    rw [m₄]
    refine data_step f₃ (fun r hr k hk ho => ?_) (fun k hk => ?_) h.data
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun hc => hp.d_b _ (in_dR hk) (Region.sub_prefix (by omega) _ hc)
      · exact not_win (by omega) hk ho
    · have x := d₃ k hk
      rw [g₂, h.rsi, m₂, hS] at x
      rw [x, ks_at h.dvd (by omega) (by omega), Nat.add_sub_cancel_left, ← hS']
  refine fromBuf_ok hp (p := p + 256) (n := eL s₀ - (p + 256)) (by omega) (by omega) e₁
    (by rw [gk _ (by decide) (by decide)]; exact hr9) e₂ (by rw [rd₄, rd₃, rd₂, h.rd])
    (by rw [wr₄, wr₃, wr₂, h.wr]) (fun r hr => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_
  · obtain ⟨_, b, c⟩ := calleeSaved_ne hr
    rw [gk r b c]; exact h.keep r hr
  · rw [D₄ k (by omega), ite_eq_left hk]
  · rw [add_ofNat, D₄ _ (by omega), ite_eq_right (by omega)]
  · rw [m₄, show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9],
      b₃ k (by omega), hS, ks_at h.dvd (by omega) (by omega),
      show (p + 256 + k - p) / 64 = 4 + k / 64 by omega, show (p + 256 + k - p) % 64 = k % 64 by omega,
      ← hS']
  · rw [m₄]
    refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨edR s₀, by simp, win_sub (by omega)⟩

theorem tail_eq : tail =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b rest last3)
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])) := rfl

theorem rest_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 257) {s : State} (h : TInv s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) : WP isa rest s (Fin s₀) := by
  refine WP.seq (WP.mono (cmp_ok h hr9) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 129)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h₁ r₁) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · exact smallT_ok hp (by omega) h₂ r₂
  · exact WP.mono (lastT_ok hp (by omega) h₁ r₁) fun _ d => d.fin hp

theorem tail_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hlt : eL s₀ - p < 385) {s : State}
    (h : TInv s₀ p s) :
    WP isa tail s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [tail_eq]
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := Fin s₀) (WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, c₁])
    (fun hs => ?_) (fun hs => ?_)) fun s₂ d => fin_ok d)
  · simp only [decide_eq_true_eq] at hs
    exact rest_ok hp hs h₁ r₁
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (last3T_ok hp (by omega) (by omega) h₁ r₁) fun _ d => d.fin hp

end VG.Proof.ChaCha20.X86_64.Avx2Tail
