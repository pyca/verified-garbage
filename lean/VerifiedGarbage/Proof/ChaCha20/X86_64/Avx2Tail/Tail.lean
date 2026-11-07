module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.FromBuf
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Sym
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes

`tail`, from the state after the eight-block loop of `vg_chacha20_xor_avx2`
(`TInv`: the first `p` bytes of the destination done, `p` a multiple of 64,
fewer than 512 left), to the end of the function, from the source at `rsi`
to the destination at `rsi + r11`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre est edp edq eL ebp edR eqR eret estk D0 Q0 KS frT eL_lt
  add_ofNat in_dR in_eqR calleeSaved_ne ctr_add ctr_ctr plus hiR hiR_contains hiR_sub Consts vz_ok pS pQ pS_sub
  pQ_sub not_pQ ret_frT)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (ks_at Ctx wregs S0 r9_not_calleeSaved regn baseR bsize)

/-! ## The invariant -/

/-- The first `p` bytes of the destination done, the source from there on
intact (`TInv.src`). -/
structure TInv (s₀ : State) (p : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p
  r11 : s.gpr .r11 = edq s₀ - edp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)
  le : p ≤ eL s₀
  dvd : 64 ∣ p
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (Avx2.S0 s₀) (p / 64)
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) =
    if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k
  consts : Consts s.mem (ebp s₀)
  incs : Incs s.mem (ebp s₀)
  frame : Frame (frT s₀) s₀.mem s.mem

theorem TInv.src {s₀ : State} (hp : TPre s₀) {p : Nat} {s : State} (h : TInv s₀ p s) {k : Nat}
    (hpk : p ≤ k) (hk : k < eL s₀) : s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k :=
  hp.src_of h.data h.frame hpk hk

theorem TInv.of {s₀ : State} {p : Nat} {s s' : State} (h : TInv s₀ p s) (hg : ∀ r, r ≠ .r9 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : TInv s₀ p s' :=
  ⟨by rw [hg _ (by decide), h.rdi], by rw [hg _ (by decide), h.rcx], by rw [hg _ (by decide), h.rsi],
    by rw [hg _ (by decide), h.r11], by rw [hg _ (by decide), h.rdx], h.le, h.dvd,
    fun r hr' => by rw [hg r (r9_not_calleeSaved hr').1, h.keep r hr'], by rw [hr, h.rd], by rw [hw, h.wr],
    by rw [hm]; exact h.cnt, fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.consts,
    by rw [hm]; exact h.incs, by rw [hm]; exact h.frame⟩

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
  refine ⟨h.of (fun r hr => by simp [hr]) rfl rfl rfl, by simp [h.rcx], ?_⟩
  simp only [h.rdx]
  rw [toNat_ofNat_lt (by omega_arith)]
  rfl

set_option simprocs false in
theorem cmpN_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) {N : Nat}
    (hN : N < 2 ^ 31) (se : BitVec.signExtend 64 (BitVec.ofNat 32 N) = BitVec.ofNat 64 N) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < N)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨h.of (fun _ _ => rfl) rfl rfl rfl, hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]

theorem test_ok {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      TInv s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.zf = some (decide (eL s₀ - p = 0)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨h.of (fun _ _ => rfl) rfl rfl rfl, hr9, ?_⟩
  rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := eL s₀ - p) (y := 0) (by omega_arith) (by omega_arith)]
  simp

theorem done_of {s₀ : State} {p : Nat} {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀)
    (he : eL s₀ - p = 0) : DoneT s₀ s :=
  ⟨hr9, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega_arith)], h.frame⟩

/-! ## Regions -/

/-- The state and `buf`, as the code around the rounds sees them. -/
theorem ctx0_of {s₀ : State} (hp : TPre s₀) {s : State} (hrdi : s.gpr .rdi = est s₀) (hr9 : s.gpr .r9 = ebp s₀)
    (hwr : s.wr = s₀.wr) : Ctx 0 s := by
  have r0 : regn 0 s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn 0 s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  refine ⟨fun b i n hb h hn => ?_, fun b b' hb hb' ne => ?_, by decide⟩
  · rw [hwr, hp.wr]
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]
      exact ⟨Avx2.stR (est s₀), by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r1]
      exact ⟨Avx2.bufR (ebp s₀), by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · omega_arith
  · have z : ∀ r : Region, (regn 0 s 2).Disjoint r := fun r x hx => by
      simp only [Region.Contains, regn, bsize, Nat.mul_zero] at hx; omega_arith
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl ne
      | (rw [r0, r1]; exact hp.st_b)
      | (rw [r1, r0]; exact hp.st_b.symm)
      | exact z _
      | exact (z _).symm

/-- The source and the destination of the `D` doublewords from byte `p`. -/
theorem ctx3_of {s₀ : State} (hp : TPre s₀) {D p : Nat} (hw : p + 4 * D ≤ eL s₀) (hD : D ≤ 128) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hr9 : s.gpr .r9 = ebp s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (h11 : s.gpr .r11 = edq s₀ - edp s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : Ctx3 D s := by
  have hL := eL_lt s₀
  have r0 : regn D s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn D s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : regn D s 2 = winS s₀ p (4 * D) := by simp only [regn, baseR, bsize, hrsi]
  have r3 : dstR D s = winQ s₀ p (4 * D) := by
    simp only [dstR, hrsi, h11]; rw [BitVec.add_comm, XorBuf.sub_add_add]
  have sS := winS_sub (s₀ := s₀) hw
  have sQ := winQ_sub (s₀ := s₀) hw
  refine ⟨fun i n h _ => ?_, fun i n h _ => ?_, fun b hb => ?_, ?_, hD⟩
  · rw [r2, hrd, hwr, add_ofNat]
    exact ⟨edR s₀, hp.r_d, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [r3, hwr, add_ofNat]
    exact ⟨eqR s₀, hp.w_q, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [r2, r3]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl
    · rw [r0]; exact ⟨hp.st_q.sub_right sQ, hp.st_d.sub_right sS⟩
    · rw [r1]; exact ⟨hp.q_b.symm.sub_right sQ, hp.d_b.symm.sub_right sS⟩
  · rcases hp.alias with he | hdis
    · left; rw [h11]; simp only [edq, edp] at he ⊢; rw [he, BitVec.sub_self]; rfl
    · right; rw [r2, r3]; exact (hdis.sub_left sS).sub_right sQ

/-! ## The last bytes, from `buf` -/

/-- After the keystream of `n ≤ 256` bytes is in `buf`, written by the code
from `s` (`hb`, `hf`): the destination from there. -/
theorem fromBufT_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hn : eL s₀ - p ≤ 256) {s s₃ : State}
    (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) (g₃ : s₃.gpr = s.gpr) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (f₃ : Frame [⟨ebp s₀, 256⟩] s.mem s₃.mem)
    (hb : ∀ k < eL s₀ - p, s₃.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0) :
    WP isa (fromBuf vl) s₃ (DoneT s₀) := by
  have hL := eL_lt s₀
  have hpL := h.le
  have nb : ∀ (a : Addr) (R : Region), R ∈ [edR s₀, eqR s₀] → (R.Disjoint (Avx2.bufR (ebp s₀))) →
      R.Contains a 1 → ∀ r ∈ [(⟨ebp s₀, 256⟩ : Region)], ¬ r.Contains a 1 := by
    intro a R _ hd hc r hr hc'
    simp only [List.mem_singleton] at hr; subst hr
    exact hd _ hc (Region.sub_prefix (by omega_arith) _ hc')
  refine fromBufY_ok vl hp (p := p) (n := eL s₀ - p) (by omega_arith) hn (by rw [g₃]; exact h.rsi)
    (by rw [g₃]; exact h.r11) (by rw [g₃]; exact hr9) (by rw [g₃]; exact h.rdx) (rd₃.trans h.rd) (wr₃.trans h.wr)
    (fun r hr => by rw [g₃]; exact h.keep r hr) (fun k hk => ?_) (fun k hk => ?_) hb ?_
  · rw [f₃ _ (nb _ (eqR s₀) (by simp) hp.q_b (in_eqR (by omega_arith))), h.data k (by omega_arith),
      ite_eq_left hk]
  · rw [add_ofNat, f₃ _ (nb _ (edR s₀) (by simp) hp.d_b (in_dR (by omega_arith))),
      h.src hp (by omega_arith) (by omega_arith)]
  · refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega_arith)⟩

/-- `wregs 0`, the regions the code around the rounds writes into `buf`. -/
theorem wregs0 {s₀ s : State} (hr9 : s.gpr .r9 = ebp s₀) {s₂ : State}
    (g₂ : s₂.gpr = s.gpr) {m m' : Mem} (f : Frame (wregs 0 s₂) m m') : Frame [⟨ebp s₀, 256⟩] m m' := by
  refine f.sub fun r hr => ?_
  simp only [wregs, g₂, hr9, Nat.mul_zero, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  · exact ⟨⟨ebp s₀, 256⟩, List.mem_singleton_self _, fun x hx => by
      simp only [Region.Contains] at hx; omega_arith⟩

theorem lastT_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hc : Ctx 0 s := ctx0_of hp h.rdi hr9 h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  refine WP.seq (WP.mono (setup_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inr rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx0_of hp (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [sm₂.wr.trans wr₁]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  refine fromBufT_ok vl hp hle h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    hS, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left, ← hS']

theorem last1T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last1 vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hc : Ctx 0 s := ctx0_of hp h.rdi hr9 h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  refine WP.seq (WP.mono (setup1_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inl rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hc₂ : Ctx 0 s₂ := ctx0_of hp (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9)
    (by rw [sm₂.wr.trans wr₁]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last1_ok hc₂ hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  refine fromBufT_ok vl hp (by omega_arith) h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    hS, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left, ← hS']

/-! ## At most 64 bytes, by `vg_chacha20_xor` -/

/-- `vg_chacha20_xor` XORs the last bytes of the source into the
destination, and returns with `rsi` pointing at `buf`. -/
theorem scalarT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} {s : State} (h : TInv s₀ p s) :
    WP isa scalar s (FinT s₀) := by
  have hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  have hsp' : (toR8 s₁).gpr .rsp = s₀.gpr .rsp := by rw [X86_64.RegUpd.gpr_setReg_of_ne _ _ (by decide), hsp]
  have hne : ∀ r : Reg, r ≠ .rsp → r ≠ .r8 → (toR8 s₁).callEntry.gpr r = s.gpr r := fun r h h8 => by
    rw [State.callEntry_gpr _ h, X86_64.RegUpd.gpr_setReg_of_ne _ _ h8, g₁]
  have h8 : (toR8 s₁).callEntry.gpr .r8 = edq s₀ + BitVec.ofNat 64 p := by
    rw [State.callEntry_gpr _ (by decide), X86_64.RegUpd.gpr_setReg_self, g₁, h.r11, h.rsi, XorBuf.sub_add_add]
  have hn : (BitVec.ofNat 64 (eL s₀ - p)).toNat = eL s₀ - p := toNat_ofNat_lt (by omega_arith)
  have hwr : s₁.wr = frT s₀ := by rw [wr₁, h.wr, hp.wr]
  have hrd : s₁.rd = [edR s₀] := by rw [rd₁, h.rd, hp.rd]
  have ts := pS_sub (s₀ := s₀) hle
  have tq := pQ_sub (s₀ := s₀) hle
  have Fce : Frame [estk s₀] s₁.mem (toR8 s₁).callEntry.mem := by
    rw [State.callEntry_mem, X86_64.RegUpd.mem_setReg, hsp']
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega_arith) (by omega_arith))
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rsi = ebp s₀ ∧ (∀ r ∈ calleeSaved, s₂.gpr r = s₀.gpr r) ∧
      s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧
      (∀ k < eL s₀, s₂.mem (edq s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0) ∧
      s₂.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64) ?_
    fun s₂ ⟨r₂, k₂, rd₂, wr₂, d₂, ret₂⟩ => ?_)
  · refine Proof.ChaCha20.wpCallTo Xor.xor_to Avx2.xor_nosp (by rw [Avx2.xor_depth]; decide)
      (rd := [pS s₀ p]) (wr := [Avx2.stR (est s₀), pQ s₀ p, Avx2.bufR (ebp s₀)]) ?_ ?_ ?_ ?_
    · simp only [xorTo, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp) (by decide), hne _ (by decide : Reg.rsi ≠ .rsp) (by decide),
        hne _ (by decide : Reg.rdx ≠ .rsp) (by decide), hne _ (by decide : Reg.rcx ≠ .rsp) (by decide), h8, h.rdi,
        h.rsi, h.rdx, h.rcx, hsp', hn]
      refine ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_q.sub_right tq, hp.st_b, hp.d_b.sub_left ts,
        hp.q_b.sub_left tq, ?_,
        hp.stk_st.sub_left (Avx2.stk_ret s₀), (hp.stk_q.sub_left (Avx2.stk_ret s₀)).sub_right tq,
        hp.stk_b.sub_left (Avx2.stk_ret s₀), hp.stk_st.sub_left (Avx2.stk_stk s₀),
        (hp.stk_d.sub_left (Avx2.stk_stk s₀)).sub_right ts,
        (hp.stk_q.sub_left (Avx2.stk_stk s₀)).sub_right tq, hp.stk_b.sub_left (Avx2.stk_stk s₀),
        by have := hp.nowrap; bv_omega, by have := hp.nowrap_q; bv_omega⟩
      rcases hp.alias with he | hdis
      · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
      · exact .inr ((hdis.sub_left ts).sub_right tq)
    · rw [hwr, hrd]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨edR s₀, by simp, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega_arith⟩
      · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨eqR s₀, by simp, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega_arith⟩
      · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩
    · rw [hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨eqR s₀, by simp, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega_arith⟩
      · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩
    · intro s₂ rd₂ wr₂ hcs hf _ ⟨s₃, hm₃, hg₃, hpost, hrsi₃⟩
      rw [Avx2.xor_depth, hsp] at hf
      have hce : stateAt (toR8 s₁).callEntry.mem (est s₀) = stateAt s₁.mem (est s₀) :=
        Xor.stateAt_frame Fce (by simpa using hp.stk_st.symm)
      simp only [State.withRegions_gpr, State.withRegions_mem,
        hne _ (by decide : Reg.rdi ≠ .rsp) (by decide), hne _ (by decide : Reg.rsi ≠ .rsp) (by decide),
        hne _ (by decide : Reg.rdx ≠ .rsp) (by decide), h8, h.rdi, h.rsi, h.rdx, hce, hm₃, m₁, h.cnt] at hpost
      rw [hn] at hpost
      refine ⟨?_, fun r hr => by rw [hcs r hr, g₁]; exact h.keep r hr, by rw [rd₂, rd₁, h.rd],
        by rw [wr₂, wr₁, h.wr], fun k hk => ?_, ?_⟩
      · rw [← hg₃ .rsi (by decide), hrsi₃, State.withRegions_gpr, hne _ (by decide) (by decide), h.rcx]
      · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.st_q _ hc (in_eqR hk)
        have n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.q_b _ (in_eqR hk) hc
        have n_sk : ¬ (estk s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.stk_q _ hc (in_eqR hk)
        by_cases hk' : k < p
        · rw [hf _ (by
            intro r hr
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact n_st
            · exact not_pQ hk' hle
            · exact n_b
            · exact n_sk), m₁, h.data k hk, ite_eq_left hk']
        · have ea : edq s₀ + BitVec.ofNat 64 k =
              edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) := by
            rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)]
          have ea' : edp s₀ + BitVec.ofNat 64 k =
              edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) := by
            rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)]
          have x := Avx2.bytes_of_bytesAt_to (length_keystream _ _) hpost (k := k - p) (by omega_arith)
          rw [← ea, ← ea', Fce _ (by simpa using fun hc => hp.stk_d _ hc (in_dR hk)), m₁,
            h.src hp (k := k) (by omega_arith) hk, keystream_getD _ (by omega_arith)] at x
          rw [x, keystream_getD _ hk, ctr_ctr]
          obtain ⟨c, rfl⟩ := h.dvd
          rw [show 64 * c / 64 + (k - 64 * c) / 64 = k / 64 by omega_arith,
            show (k - 64 * c) % 64 = k % 64 by omega_arith]
      · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
        · intro r hr
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact hp.ret_st
          · exact hp.ret_q.sub_right tq
          · exact hp.ret_b
          · exact Avx2.ret_stk s₀
        · rw [m₁]
          exact h.frame.readW (Region.contains_self _ _) (ret_frT hp) (by decide)
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rd₂, wr₂, d₂, ret₂⟩
    · simp only [State.setReg, ite_true, r₂]
    · simp only [State.setReg, (r9_not_calleeSaved hr).1, ite_false]
      exact k₂ r hr

/-! ## The whole tail -/

theorem smallT_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (small vl) s (FinT s₀) := by
  refine WP.seq (WP.mono (cmpN_ok h hr9 (N := 65) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 65)) (by simp [eval, c₁]) (fun _ => ?_) (fun _ => ?_)
  · exact scalarT_ok hp h₁
  · exact WP.mono (last1T_ok vl hp hle h₁ r₁) fun _ d => d.fin hp

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

theorem last3_eq (vl : Bool) : last3 vl = .seq (.block setup3) (.seq (roundsS vl 3 10) (.seq (.block
    ((addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) (fromBuf vl))) := rfl

theorem last3T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hge : 257 ≤ eL s₀ - p) (hle : eL s₀ - p ≤ 384)
    {s : State} (h : TInv s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last3 vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega_arith
  have hc : Ctx 0 s := ctx0_of hp h.rdi hr9 h.wr
  obtain ⟨hm, hi⟩ := h.cst hr9
  rw [last3_eq vl]
  refine WP.seq (WP.mono (setup3_ok hc hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS3_ok vl hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx 0 s₂ ∧ Ctx3 64 s₂ :=
    ⟨ctx0_of hp (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9) (by rw [wr₂]; exact h.wr),
     ctx3_of hp hw (by decide) (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact hr9) (by rw [g₂]; exact h.rsi)
      (by rw [g₂]; exact h.r11) (by rw [rd₂]; exact h.rd) (by rw [wr₂]; exact h.wr)⟩
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (last3_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv3_ok (s₀ := s₀) (p := p) (by omega_arith) (by rw [g₃']; exact h.rsi) (by rw [g₃']; exact h.rdx))
    fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have hd3 : (dstR 64 s₂).base = edq s₀ + BitVec.ofNat 64 p := by
    simp only [dstR, g₂, h.rsi, h.r11]; rw [BitVec.add_comm, XorBuf.sub_add_add]
  have ws : wregsT true 64 s₂ = [⟨ebp s₀, 256⟩, winQ s₀ p 256] := by
    simp only [wregsT, dstR, g₂, hr9, h.rsi, h.r11, Nat.reduceMul]
    rw [BitVec.add_comm (edp s₀ + _), XorBuf.sub_add_add]
  rw [ws, m₂] at f₃
  have hS : S0 s₂ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, g₂, m₂, h.rdi]; exact h.cnt
  have hS' : S0 s = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, h.rdi]; exact h.cnt
  have gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  have nbuf : ∀ (a : Addr) (R : Region), R.Disjoint (Avx2.bufR (ebp s₀)) → R.Contains a 1 →
      ¬ (⟨ebp s₀, 256⟩ : Region).Contains a 1 := fun a R hd hc hc' =>
    hd _ hc (Region.sub_prefix (by omega_arith) _ hc')
  -- The source outside the 256 bytes the code wrote is intact.
  have nS : ∀ k < eL s₀, (k < p ∨ p + 256 ≤ k) → ¬ (winQ s₀ p 256).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk ho
    rcases hp.alias with he | hdis
    · have := not_winQ (s₀ := s₀) (p := p) (n := 256) (by omega_arith) hk ho
      simp only [edq, edp] at he this ⊢; rwa [he] at this
    · exact fun hc => hdis _ (in_dR hk) (winQ_sub (by omega_arith) _ hc)
  refine fromBufY_ok vl hp (p := p + 256) (n := eL s₀ - (p + 256)) (by omega_arith) (by omega_arith) e₁
    (by rw [gk _ (by decide) (by decide)]; exact h.r11) (by rw [gk _ (by decide) (by decide)]; exact hr9) e₂
    (by rw [rd₄, rd₃, rd₂, h.rd]) (by rw [wr₄, wr₃, wr₂, h.wr]) (fun r hr => ?_) (fun k hk => ?_)
    (fun k hk => ?_) (fun k hk => ?_) ?_
  · obtain ⟨_, b, c⟩ := calleeSaved_ne hr
    rw [gk r b c]; exact h.keep r hr
  · rw [m₄]
    by_cases hkp : k < p
    · rw [f₃ _ (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nbuf _ _ hp.q_b (in_eqR (by omega_arith))
        · exact not_winQ (by omega_arith) (by omega_arith) (.inl hkp)), h.data k (by omega_arith),
        ite_eq_left hkp]
    · have x := d₃ (k - p) (by omega_arith)
      rw [hd3, g₂, h.rsi, m₂, add_ofNat, add_ofNat, Nat.add_sub_cancel' (by omega_arith), hS,
        h.src hp (k := k) (by omega_arith) (by omega_arith)] at x
      rw [x, ks_at h.dvd (by omega_arith) (by omega_arith), ← hS']
  · rw [m₄, add_ofNat, f₃ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact nbuf _ _ hp.d_b (in_dR (by omega_arith))
      · exact nS _ (by omega_arith) (.inr (by omega_arith))), h.src hp (by omega_arith) (by omega_arith)]
  · rw [m₄, show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9],
      b₃ k (by omega_arith), hS, ks_at h.dvd (by omega_arith) (by omega_arith),
      show (p + 256 + k - p) / 64 = 4 + k / 64 by omega_arith, show (p + 256 + k - p) % 64 = k % 64 by omega_arith,
      ← hS']
  · rw [m₄]
    refine h.frame.trans (f₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩

theorem tail_eq (vl : Bool) : tail vl =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b (rest vl) (last3 vl))
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])) := rfl

theorem rest_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 257) {s : State} (h : TInv s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) : WP isa (rest vl) s (FinT s₀) := by
  refine WP.seq (WP.mono (cmpN_ok h hr9 (N := 129) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 129)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h₁ r₁) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · exact smallT_ok vl hp (by omega_arith) h₂ r₂
  · exact WP.mono (lastT_ok vl hp (by omega_arith) h₁ r₁) fun _ d => d.fin hp

/-- The end: `rsi` pointing at `buf`. -/
theorem fin_ok {s₀ s : State} (h : FinT s₀ s) :
    WP isa (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]) s fun s' =>
      gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  show WP isa (.block (([.vop .vzeroupper] : List Instr) ++ [.mov .rsi (.reg .r9)])) s _
  refine WP.block_append (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, _, _⟩ => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [State.setReg, (calleeSaved_ne hr).2.1, ite_false, g₁]
    exact h.keep r hr
  · simp only [State.setReg, m₁]
    exact h.ret
  · simp only [State.setReg, m₁]
    exact bytesAt_xor_to (length_keystream _ _) fun k hk => by rw [h.data k hk]
  · simp only [State.setReg, ite_true, g₁, h.r9]

theorem tail_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 385) {s : State}
    (h : TInv s₀ p s) :
    WP isa (tail vl) s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  rw [tail_eq vl]
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := FinT s₀) (WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, c₁])
    (fun hs => ?_) (fun hs => ?_)) fun s₂ d => fin_ok d)
  · simp only [decide_eq_true_eq] at hs
    exact rest_ok vl hp hs h₁ r₁
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (last3T_ok vl hp (by omega_arith) (by omega_arith) h₁ r₁) fun _ d => d.fin hp

end VG.Proof.ChaCha20.X86_64.Avx2Tail
