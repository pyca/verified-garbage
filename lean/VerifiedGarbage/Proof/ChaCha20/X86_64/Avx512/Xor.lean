module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Setup
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20 keystream XOR on x86-64 with AVX-512

The loop over 1024-byte chunks (`Setup`, `Rounds`, `Finish`), the rest
(`Avx512Last.last16_ok` for 769 to 1023 bytes, `Avx512Tail.part3T_ok` for
513 to 768, `Avx512Tail.tail_ok` for fewer), constant time and the calling
convention, from the source to the destination (`xorTo 16`, `Avx2.TPre`),
with 16 bytes of stack below the return address, which this implementation
does not use. The in-place facts the sixteen blocks of
`vg_chacha20_xor_split` need are here too (`next_ok`, `ctx_of`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre est edp edq eL ebp edR eqR eret estk S0 D0 Q0 KS frT eL_lt
  add_ofNat in_dR in_eqR)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (DoneT winS winQ winS_sub winQ_sub not_winQ)

/-! ## The loop invariant -/

/-- Before chunk `t`: the destination done before it, the source from it on
intact (`LInv.src`). -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)
  r11 : s.gpr .r11 = edq s₀ - edp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)
  le : 1024 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (16 * t)
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) =
    if k < 1024 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k
  incs : Incs s.mem (ebp s₀)
  tincs : Avx512Tail.Incs s.mem (ebp s₀)
  frame : Frame (frT s₀) s₀.mem s.mem

theorem LInv.src {s₀ : State} (hp : TPre s₀) {t : Nat} {s : State} (h : LInv s₀ t s) {k : Nat}
    (hpk : 1024 * t ≤ k) (hk : k < eL s₀) : s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k :=
  hp.src_of h.data h.frame hpk hk

/-- The keystream from block `16 t` on. -/
theorem ks_shift (S : CState) {L t k : Nat} (hk : k < L) (ht : 1024 * t ≤ k) :
    (keystream S L).getD k 0 =
      (serialize (Spec.ChaCha20.block (ctr (ctr S (16 * t)) ((k - 1024 * t) / 64)))).getD
        ((k - 1024 * t) % 64) 0 := by
  rw [keystream_getD _ hk, Avx2.ctr_ctr, show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega_arith,
    show (k - 1024 * t) % 64 = k % 64 by omega_arith]

/-! ## The end of a chunk -/

set_option simprocs false in
theorem next_ok {s₀ : State} (hst : Avx2.stR (est s₀) ∈ s₀.wr) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t)
    {s : State} (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 16) ∧
      Frame [Avx2.stR (est s₀)] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega_arith) (by omega_arith)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by rw [hrd, hwr]; exact List.mem_append_right _ hst, c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by rw [hwr]; exact hst, c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [Avx2.stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  have e : (s.gpr .rdx - 1024).toNat = eL s₀ - 1024 * (t + 1) := by rw [hrdx]; bv_omega
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk of data -/

section
variable {s₀ : State} {t : Nat}

/-- The 1024 bytes of chunk `t`. -/
abbrev wR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), 1024⟩

/-- The counter increments in `buf`. -/
abbrev incR (s₀ : State) : Region := ⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩

/-- The saved registers in `buf`. -/
abbrev saveR (s₀ : State) : Region := ⟨ebp s₀, 128⟩

theorem win_sub (hw : 1024 * t + 1024 ≤ eL s₀) : Region.Sub (wR s₀ t) (edR s₀) :=
  Offset.sub_base _ hw

theorem out_win (hw : 1024 * t + 1024 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 1024 * t ∨ 1024 * t + 1024 ≤ k) :
    ¬ (wR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
  split <;> omega_arith

theorem save_sub (s₀ : State) : Region.Sub (saveR s₀) (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega_arith)

theorem inc_sub (s₀ : State) : Region.Sub (incR s₀) (Avx2.bufR (ebp s₀)) := Offset.sub_base _ (by omega_arith)

theorem inc_save (s₀ : State) : (incR s₀).Disjoint (saveR s₀) :=
  Offset.base_disjoint _ (by omega_arith) (by omega_arith) |>.symm

end

/-- Where a chunk of `vg_chacha20_xor_split` runs, in place (the destination
the source): the regions of `Sym`, from the loop's. -/
theorem ctx_of {s₀ : State} (hp : TPre s₀) (he : edq s₀ = edp s₀) {t : Nat} (hw : 1024 * t + 1024 ≤ eL s₀)
    {s : State} (hrdi : s.gpr .rdi = est s₀) (hrcx : s.gpr .rcx = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)) (hwr : s.wr = s₀.wr) : Ctx s := by
  have hL := eL_lt s₀
  have r0 : regn s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi]
  have r1 : regn s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hrcx]
  have r2 : regn s 2 = wR s₀ t := by simp only [regn, baseR, bsize, hrsi]
  have eq : eqR s₀ = edR s₀ := by simp only [eqR, edR, he]
  have hd : edR s₀ ∈ s₀.wr := eq ▸ hp.w_q
  refine ⟨fun b i n hb h => ?_, fun b b' hb hb' ne => ?_⟩
  · rw [hwr]
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨Avx2.stR (est s₀), hp.w_st, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r1]; exact ⟨Avx2.bufR (ebp s₀), hp.w_b, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r2, add_ofNat]; exact ⟨edR s₀, hd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · have d01 := hp.st_b
    have d02 := hp.st_d.sub_right (win_sub hw)
    have d12 := hp.d_b.symm.sub_right (win_sub hw)
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | with_reducible assumption | exact d01.symm | exact d02.symm | exact d12.symm

/-- Where a chunk runs, from the source to the destination: the regions of
`Sym`, from the loop's. -/
theorem ctxT_of {s₀ : State} (hp : TPre s₀) {t : Nat} (hw : 1024 * t + 4 * 256 ≤ eL s₀) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrcx : s.gpr .rcx = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)) (h11 : s.gpr .r11 = edq s₀ - edp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : CtxT true s := by
  have hL := eL_lt s₀
  have r0 : regn s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi]
  have r1 : regn s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hrcx]
  have r2 : regn s 2 = winS s₀ (1024 * t) (4 * 256) := by simp only [regn, baseR, bsize, hrsi]
  have r3 : dstR 256 s = winQ s₀ (1024 * t) (4 * 256) := by
    simp only [dstR, hrsi, h11]; rw [BitVec.add_comm, XorBuf.sub_add_add]
  have sS := winS_sub (s₀ := s₀) hw
  have sQ := winQ_sub (s₀ := s₀) hw
  refine ⟨⟨fun b i n hb h => ?_, by rw [r0, r1]; exact hp.st_b⟩,
    ⟨fun i n h _ => ?_, fun i n h _ => ?_, fun b hb => ?_, ?_⟩⟩
  · rw [hwr]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨Avx2.stR (est s₀), hp.w_st, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r1]; exact ⟨Avx2.bufR (ebp s₀), hp.w_b, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [r2, hrd, hwr, add_ofNat]
    exact ⟨edR s₀, hp.rd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [r3, hwr, add_ofNat]
    exact ⟨eqR s₀, hp.w_q, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [r2, r3]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl
    · rw [r0]; exact ⟨hp.st_q.sub_right sQ, hp.st_d.sub_right sS⟩
    · rw [r1]; exact ⟨hp.q_b.symm.sub_right sQ, hp.d_b.symm.sub_right sS⟩
  · rcases hp.alias with he | hdis
    · left; rw [h11]; simp only [edq, edp] at he ⊢; rw [he, BitVec.sub_self]; rfl
    · right; rw [r2, r3]; exact (hdis.sub_left sS).sub_right sQ

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Incs m (ebp s₀))
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (incR s₀).Disjoint r) : Incs m' (ebp s₀) := by
  intro j hj
  rw [← h j hj]
  refine hf.readW (r := incR s₀) ?_ hd (by decide)
  rw [show 4 * (32 + j) = 128 + 4 * j by omega_arith, ← add_ofNat]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx :=
  Avx2.calleeSaved_ne hr

theorem body_eq : body = .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next))) := rfl

theorem body_ok {s₀ : State} (hp : TPre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (h : LInv s₀ t s) :
    WP isa body s fun s' =>
      LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have hw : 1024 * t + 4 * 256 ≤ eL s₀ := by omega_arith
  have hi : Incs s.mem (s.gpr .rcx) := by rw [h.rcx]; exact h.incs
  rw [body_eq]
  refine WP.seq (WP.mono (setup_ok (ctxT_of hp hw h.rdi h.rcx h.rsi h.r11 h.rd h.wr) hi)
    fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : CtxT true s₂ := ctxT_of hp hw (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx)
    (by rw [g₂]; exact h.rsi) (by rw [g₂]; exact h.r11) (by rw [rd₂]; exact h.rd) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .rcx) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (finish_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have hd3 : (dstR 256 s₂).base = edq s₀ + BitVec.ofNat 64 (1024 * t) := by
    simp only [dstR, g₂, h.rsi, h.r11]; rw [BitVec.add_comm, XorBuf.sub_add_add]
  have ws : wregsT true s₂ = [saveR s₀, winQ s₀ (1024 * t) (4 * 256)] := by
    simp only [wregsT, g₂, h.rcx, List.cons.injEq, and_true, true_and]
    exact congrArg (fun a => (⟨a, 4 * 256⟩ : Region)) hd3
  rw [ws, m₂] at f₃
  rw [hd3] at d₃
  simp only [g₂, m₂, h.rsi, h.rdi] at d₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (next_ok hp.w_st hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have sQ := winQ_sub (s₀ := s₀) hw
  have dss : (Avx2.stR (est s₀)).Disjoint (saveR s₀) := hp.st_b.sub_right (save_sub _)
  have FA : Frame [saveR s₀, winQ s₀ (1024 * t) (4 * 256), Avx2.stR (est s₀)] s.mem s₄.mem :=
    (f₃.mono (by simp)).trans (f₄.mono (by simp))
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact hp.st_q.sub_right sQ)
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.r11, e₂, by omega_arith,
    fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 16 * (t + 1) = 16 * t + 16 by omega_arith]
    exact Avx2.ctr_add _ _ 16
  · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.st_q _ hc (in_eqR hk)
    have n_sv : ¬ (saveR s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.q_b _ (in_eqR hk) (save_sub _ _ hc)
    by_cases hin : 1024 * t ≤ k ∧ k < 1024 * t + 1024
    · have x₃ := d₃ (k - 1024 * t) (by omega_arith)
      rw [add_ofNat, add_ofNat, Nat.add_sub_cancel' hin.1, h.src hp hin.1 hk] at x₃
      rw [f₄ _ (by simpa using n_st), x₃, ite_eq_left (by omega_arith : k < 1024 * (t + 1)),
        Avx2.plus_block, h.cnt, ks_shift _ hk hin.1]
    · rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sv
          · exact not_winQ hw hk (by omega_arith)
          · exact n_st), h.data k hk]
      by_cases hlt : k < 1024 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega_arith : k < 1024 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_arith : ¬ k < 1024 * (t + 1))]
  · refine incs_frame h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact inc_save _
    · exact (hp.q_b.symm.sub_right sQ).sub_left (inc_sub _)
    · exact (hp.st_b.sub_right (inc_sub _)).symm
  · refine Avx512Tail.incs_frame h.tincs FA ?_
    have ti : Region.Sub ⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ (Avx2.bufR (ebp s₀)) := Offset.sub_base _ (by omega_arith)
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by omega_arith) (by omega_arith) |>.symm
    · exact (hp.q_b.symm.sub_right sQ).sub_left ti
    · exact (hp.st_b.sub_right ti).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, save_sub _⟩
    · exact ⟨eqR s₀, by simp, sQ⟩
    · exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## The prologue -/

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1024)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 1024)) := by
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

set_option simprocs false in
theorem cmp513_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 513)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 513)) := by
  have se : BitVec.signExtend 64 (513 : BitVec 32) = 513 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

theorem cmp769_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 769)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 769)) := by
  have se : BitVec.signExtend 64 (769 : BitVec 32) = 769 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

/-- The offsets in `buf` and values of the quadwords the prologue stores. -/
def incPairs : List (Nat × BitVec 64) :=
  [(128, 0x0000000100000000), (136, 0x0000000300000002), (144, 0x0000000500000004),
   (152, 0x0000000700000006), (160, 0x0000000900000008), (168, 0x0000000b0000000a),
   (176, 0x0000000d0000000c), (184, 0x0000000f0000000e)]

theorem consts_eq : consts = Avx2.pairsCode incPairs := rfl

theorem incPairs_le : ∀ p ∈ incPairs, p.1 + 8 ≤ 320 := by decide

theorem incs_mem (m : Mem) (buf : Addr) : Incs (Avx2.storeAll buf incPairs m) buf := by
  have H : ∀ j < 16, Avx2.readsTo [] incPairs (32 + j) (BitVec.ofNat 32 j) = true := by decide +kernel
  intro j hj
  exact Avx2.storeAll_readW32 (H j hj) m

/-- The offsets in `buf` and values of the quadwords of the lane increments of
the last bytes (`Impl.ChaCha20.X86_64.Avx512Tail.consts`). -/
def tPairs : List (Nat × BitVec 64) :=
  [(256, 0), (264, 0), (272, 1), (280, 0), (288, 2), (296, 0), (304, 3), (312, 0),
   (192, 4), (200, 0), (208, 5), (216, 0), (224, 6), (232, 0), (240, 7), (248, 0)]

theorem tconsts_eq : Impl.ChaCha20.X86_64.Avx512Tail.consts = Avx2.pairsCode tPairs := rfl

theorem tPairs_le : ∀ p ∈ tPairs, p.1 + 8 ≤ 320 := by decide

theorem tincs_mem (m : Mem) (buf : Addr) :
    Avx512Tail.Incs (Avx2.storeAll buf incPairs (Avx2.storeAll buf tPairs m)) buf := by
  have H : ∀ k < 2, ∀ j < 16, Avx2.readsTo tPairs incPairs (Avx512Tail.incB k + j)
      (if j % 4 = 0 then BitVec.ofNat 32 (4 * k + j / 4) else 0) = true := by decide +kernel
  intro k hk j hj
  exact Avx2.storeAll_readW32 (H k hk j hj) m

theorem prologue_ok {s₀ : State} (hp : TPre s₀) :
    WP isa (.block (Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++ Impl.ChaCha20.X86_64.XorBuf.delta ++
      ([.alu .cmp .rdx (.imm 1024)] : List Instr))) s₀ fun s =>
      LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 1024)) := by
  have hL := eL_lt s₀
  rw [tconsts_eq, consts_eq]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono (Avx2.pairs_ok tPairs tPairs_le (s := s₀) rfl hp.w_b)
    fun s₀' ⟨m₀, g₀, rd₀, wr₀⟩ => WP.mono (Avx2.pairs_ok (buf := ebp s₀) incPairs incPairs_le (s := s₀')
      (by rw [g₀ _ (by decide)]) (by rw [wr₀]; exact hp.w_b))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (Avx2.delta_ok s₁) fun s₁' ⟨d₁, gd, md, rdd, wrd, _⟩ =>
      WP.mono (cmp_ok s₁') fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)))
  have F : Frame [Avx2.bufR (ebp s₀)] s₀.mem s₂.mem := by
    rw [m₂, md, m₁, m₀]
    exact (Avx2.storeAll_frame (List.mem_singleton_self _) _ tPairs_le _).trans
      (Avx2.storeAll_frame (List.mem_singleton_self _) _ incPairs_le _)
  have gk : ∀ r, r ≠ .rax → r ≠ .r11 → s₂.gpr r = s₀.gpr r := fun r hr h11 => by
    rw [g₂, gd r h11, g₁ r hr, g₀ r hr]
  refine ⟨⟨gk _ (by decide) (by decide), gk _ (by decide) (by decide),
    by rw [gk _ (by decide) (by decide)]; simp,
    by rw [g₂, d₁, g₁ _ (by decide), g₁ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)],
    by rw [gk _ (by decide) (by decide)]; simp, by omega_arith,
    fun r hr => gk r (calleeSaved_ne hr).1 (by intro h; subst h; simp [calleeSaved] at hr),
    by rw [rd₂, rdd, rd₁, rd₀], by rw [wr₂, wrd, wr₁, wr₀], ?_, fun k hk => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.q_b _ (in_eqR hk) hc)]
    simp
  · rw [m₂, md, m₁, m₀]; exact incs_mem _ _
  · rw [m₂, md, m₁, m₀]; exact tincs_mem _ _
  · exact F.mono (by simp)
  · rw [cf₂, gd _ (by decide), g₁ _ (by decide), g₀ _ (by decide)]

/-! ## The rest -/

/-- The loop's invariant, as the tail's. -/
theorem tinv_of {s₀ : State} {t : Nat} {s : State} (h : LInv s₀ t s) :
    Avx512Tail.TInv (Avx512Tail.XI s₀) s₀ (1024 * t) s :=
  ⟨h.rdi, h.rcx, h.rsi, h.r11, h.rdx, h.le, ⟨16 * t, by omega_arith⟩, h.keep, h.rd, h.wr,
    by rw [h.cnt, show 1024 * t / 64 = 16 * t by omega_arith], h.data, h.tincs, h.frame⟩

/-- The last 513 to 768 bytes, by twelve blocks. -/
theorem last12_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hgt : 512 < eL s₀ - p) (hle : eL s₀ - p ≤ 768)
    {s : State} (h : Avx512Tail.TInv (Avx512Tail.XI s₀) s₀ p s) :
    WP isa last12 s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  unfold last12
  refine WP.seq (WP.mono (Avx512Last.mov_ok s) fun s₁ ⟨r9₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  exact WP.seq (WP.mono (Avx512Tail.part3T_ok hp hgt hle (h.of g₁ m₁ rd₁ wr₁) (by rw [r9₁, h.rcx])) fun _ d =>
    Avx2Tail.fin_ok (d.fin hp))

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Avx512.xor =
    .seq (.block (Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++ Impl.ChaCha20.X86_64.XorBuf.delta ++
      ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body .ae))
    (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b Impl.ChaCha20.X86_64.Avx512Tail.tail
      (.seq (.block [.alu .cmp .rdx (.imm 769)]) (.ite .b last12 last16))))) := rfl

/-- After the loop: the last pass of twelve or sixteen blocks, or the tail. -/
theorem rest_ok {s₀ : State} (hp : TPre s₀) {t : Nat} (ht : eL s₀ - 1024 * t < 1024) {s : State}
    (h : LInv s₀ t s) :
    WP isa (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b Impl.ChaCha20.X86_64.Avx512Tail.tail
      (.seq (.block [.alu .cmp .rdx (.imm 769)]) (.ite .b last12 last16)))) s
      fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  have hL := eL_lt s₀
  have cong : ∀ {s s' : State}, LInv s₀ t s → s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → LInv s₀ t s' := fun h g m rd wr =>
    ⟨by rw [g]; exact h.rdi, by rw [g]; exact h.rcx, by rw [g]; exact h.rsi, by rw [g]; exact h.r11,
      by rw [g]; exact h.rdx, h.le, fun r hr => by rw [g]; exact h.keep r hr, rd.trans h.rd,
      wr.trans h.wr, by rw [m]; exact h.cnt, fun k hk => by rw [m]; exact h.data k hk,
      by rw [m]; exact h.incs, by rw [m]; exact h.tincs, by rw [m]; exact h.frame⟩
  refine WP.seq (WP.mono (cmp513_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, c₁⟩ => ?_)
  have h₁ : LInv s₀ t s₁ := cong h g₁ m₁ rd₁ wr₁
  have hr : (s.gpr .rdx).toNat = eL s₀ - 1024 * t := by rw [h.rdx, toNat_ofNat_lt (by omega_arith)]
  refine WP.ite (decide (eL s₀ - 1024 * t < 513)) (by simp [eval, c₁, hr]) (fun hs => ?_) (fun hs => ?_)
  · exact Avx512Tail.tail_ok hp ht (tinv_of h₁)
  · simp only [decide_eq_false_iff_not] at hs
    refine WP.seq (WP.mono (cmp769_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, c₂⟩ => ?_)
    have h₂ : LInv s₀ t s₂ := cong h₁ g₂ m₂ rd₂ wr₂
    have hr₁ : (s₁.gpr .rdx).toNat = eL s₀ - 1024 * t := by rw [g₁]; exact hr
    refine WP.ite (decide (eL s₀ - 1024 * t < 769)) (by simp [eval, c₂, hr₁]) (fun hs' => ?_) (fun hs' => ?_)
    · simp only [decide_eq_true_eq] at hs'
      exact last12_ok hp (by omega_arith) (by omega_arith) (tinv_of h₂)
    · simp only [decide_eq_false_iff_not] at hs'
      exact Avx512Last.last16_ok hp (by omega_arith) ht (tinv_of h₂) h₂.incs

theorem correct {s₀ : State} (hp : TPre s₀) :
    WP isa Impl.ChaCha20.X86_64.Avx512.xor s₀ fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => rest_ok hp ht h₂)
  refine WP.ite (decide (eL s₀ < 1024)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega_arith, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = eL s₀ - 1024 * t ∧ 1024 ≤ eL s₀ - 1024 * t ∧ LInv s₀ t s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s') ∨
        (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (body_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : eL s₀ - 1024 * (t + 1) < 1024
      · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 1024 * (t + 1), by omega_arith, t + 1, rfl, by omega_arith, h'⟩
    exact WP.loop (M := isa) Inv hstep (eL s₀ - 1024 * 0) s₁ ⟨0, rfl, by omega_arith, h₁⟩

/-! ## Constant time and the contract -/

/-- `vg_chacha20_xor_avx512` from the source to the destination, returning
with `rsi` pointing at `buf`, as `vg_chacha20_xor` does. -/
theorem xor_to (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx512.xor s t s' ∧ abiPreserved s s' ∧ (xorTo 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct (Avx2.TPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

theorem xor_ctTo : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Avx512.xor :=
  VG.Taint.constantTime (A := taint) Xor.τ₀ (fun _ _ h₁ h₂ hp => Xor.agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.ChaCha20.X86_64.Avx512
