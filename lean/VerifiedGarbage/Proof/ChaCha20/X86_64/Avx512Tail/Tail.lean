module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.FromBuf
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Out
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes

`tail`, from the state after the sixteen-block loop of
`vg_chacha20_xor_avx512` (`TInv`: the first `p` bytes of the destination
done, `p` a multiple of 64, fewer than 1024 left), to the end of the
function, from the source at `rsi` to the destination at `rsi + r11`.

The invariant and its steps serve the last bytes of
`vg_chacha20_xor_avx2` too (`Avx2Tail/Tail.lean`): `TInv X` holds `X` of
memory, the constants each keeps in `buf`; the rest from `buf`, after the
code wrote the destination's first bytes, is `restT_ok`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre est edp edq eL ebp edR eqR eret estk D0 Q0 KS frT eL_lt
  add_ofNat in_dR in_eqR calleeSaved_ne ctr_ctr ctr_add plus plus_block)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (DoneT FinT winS winQ winS_sub winQ_sub not_winQ fromBufY_ok
  r9_not_calleeSaved)
open VG.Proof.ChaCha20.X86_64.Avx512 (dstR Ctx3)

/-! ## The invariant -/

/-- The first `p` bytes of the destination done, the source from there on
intact (`TInv.src`), and `X` of memory. -/
structure TInv (X : Mem → Prop) (s₀ : State) (p : Nat) (s : State) : Prop where
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
  x : X s.mem
  frame : Frame (frT s₀) s₀.mem s.mem

section
variable {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State}

theorem TInv.src (hp : TPre s₀) (h : TInv X s₀ p s) {k : Nat} (hpk : p ≤ k) (hk : k < eL s₀) :
    s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k :=
  hp.src_of h.data h.frame hpk hk

theorem TInv.of (h : TInv X s₀ p s) {s' : State} (hg : ∀ r, r ≠ .r9 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : TInv X s₀ p s' :=
  ⟨by rw [hg _ (by decide), h.rdi], by rw [hg _ (by decide), h.rcx], by rw [hg _ (by decide), h.rsi],
    by rw [hg _ (by decide), h.r11], by rw [hg _ (by decide), h.rdx], h.le, h.dvd,
    fun r hr' => by rw [hg r (r9_not_calleeSaved hr').1, h.keep r hr'], by rw [hr, h.rd], by rw [hw, h.wr],
    by rw [hm]; exact h.cnt, fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.x,
    by rw [hm]; exact h.frame⟩

/-- The state as the code around the rounds has it, from the state at `s`. -/
theorem TInv.cntAt (h : TInv X s₀ p s) {s' : State} (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) :
    S0 s' = ctr (Avx2.S0 s₀) (p / 64) := by
  simp only [S0, hg, hm, h.rdi]; exact h.cnt

end

/-! ## The steps -/

theorem startN_ok {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State} (h : TInv X s₀ p s) {N : Nat}
    (hN : N < 2 ^ 31) (se : BitVec.signExtend 64 (BitVec.ofNat 32 N) = BitVec.ofNat 64 N) :
    WP isa (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      TInv X s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < N)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨h.of (fun r hr => by simp [hr]) rfl rfl rfl, by simp [h.rcx], ?_⟩
  simp only [h.rdx]
  rw [toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]

set_option simprocs false in
theorem cmpN_ok {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State} (h : TInv X s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) {N : Nat} (hN : N < 2 ^ 31)
    (se : BitVec.signExtend 64 (BitVec.ofNat 32 N) = BitVec.ofNat 64 N) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      TInv X s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.cf = some (decide (eL s₀ - p < N)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨h.of (fun _ _ => rfl) rfl rfl rfl, hr9, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]

theorem test_ok {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State} (h : TInv X s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      TInv X s₀ p s' ∧ s'.gpr .r9 = ebp s₀ ∧ s'.zf = some (decide (eL s₀ - p = 0)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨h.of (fun _ _ => rfl) rfl rfl rfl, hr9, ?_⟩
  rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := eL s₀ - p) (y := 0) (by omega_arith) (by omega_arith)]
  simp

theorem done_of {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State} (h : TInv X s₀ p s)
    (hr9 : s.gpr .r9 = ebp s₀) (he : eL s₀ - p = 0) : DoneT s₀ s :=
  ⟨hr9, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega_arith)], h.frame⟩

/-- The source and the destination on by `N` bytes. -/
theorem advN_ok {s₀ : State} {p N : Nat}
    (se : BitVec.signExtend 64 (BitVec.ofNat 32 N) = BitVec.ofNat 64 N) (hge : N ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block [.alu .add .rsi (.imm (BitVec.ofNat 32 N)), .alu .sub .rdx (.imm (BitVec.ofNat 32 N))]) s
      fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + N) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + N)) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨by rw [hrsi]; exact Offset.add_add _ _ _,
    by rw [hrdx, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub],
    fun r h₁ h₂ => by simp [h₁, h₂], by simp⟩

/-! ## Regions -/

section
variable {s₀ : State}

/-- The keystream of byte `k`, from block `p / 64` on. -/
theorem ks_at {p k : Nat} (hp : 64 ∣ p) (hpk : p ≤ k) (hk : k < eL s₀) :
    (KS s₀).getD k 0 =
      (serialize (plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (ctr (Avx2.S0 s₀) (p / 64)) j))
        (ctr (Avx2.S0 s₀) (p / 64)) ((k - p) / 64))).getD ((k - p) % 64) 0 := by
  rw [plus_block, ctr_ctr, keystream_getD _ hk]
  obtain ⟨c, rfl⟩ := hp
  rw [show 64 * c / 64 + (k - 64 * c) / 64 = k / 64 by omega_arith, show (k - 64 * c) % 64 = k % 64 by omega_arith]

end

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
theorem ctx3_of {s₀ : State} (hp : TPre s₀) {D p : Nat} (hw : p + 4 * D ≤ eL s₀) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hr9 : s.gpr .r9 = ebp s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (h11 : s.gpr .r11 = edq s₀ - edp s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : Ctx3 (regn D s) D s := by
  have hL := eL_lt s₀
  have r0 : regn D s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn D s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : regn D s 2 = winS s₀ p (4 * D) := by simp only [regn, baseR, bsize, hrsi]
  have r3 : dstR D s = winQ s₀ p (4 * D) := by
    simp only [dstR, hrsi, h11]; rw [BitVec.add_comm, XorBuf.sub_add_add]
  have sS := winS_sub (s₀ := s₀) hw
  have sQ := winQ_sub (s₀ := s₀) hw
  refine ⟨fun i n h _ => ?_, fun i n h _ => ?_, fun b hb => ?_, ?_⟩
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

section
variable {X : Mem → Prop} {s₀ : State} {p : Nat} {s : State}

/-- The state and `buf` around the rounds, from the state at `s`. -/
theorem TInv.ctx0 (hp : TPre s₀) (h : TInv X s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) {s' : State}
    (hg : s'.gpr = s.gpr) (hwr : s'.wr = s.wr) : Ctx 0 s' :=
  ctx0_of hp (by rw [hg]; exact h.rdi) (by rw [hg]; exact hr9) (by rw [hwr]; exact h.wr)

/-- The regions around the rounds, the source and the destination of `D`
doublewords from byte `p`, from the state at `s`. -/
theorem TInv.ctxT (hp : TPre s₀) (h : TInv X s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) {D : Nat}
    (hw : p + 4 * D ≤ eL s₀) (hD : D ≤ 128) {s' : State} (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CtxT true D s' :=
  ⟨h.ctx0 hp hr9 hg hwr, ctx3_of hp hw (by rw [hg]; exact h.rdi) (by rw [hg]; exact hr9)
    (by rw [hg]; exact h.rsi) (by rw [hg]; exact h.r11) (by rw [hrd]; exact h.rd) (by rw [hwr]; exact h.wr), hD⟩

/-- Where the destination is, from the state at `s`. -/
theorem TInv.dst (h : TInv X s₀ p s) {D : Nat} {s' : State} (hg : s'.gpr = s.gpr) :
    (dstR D s').base = edq s₀ + BitVec.ofNat 64 p := by
  simp only [dstR, hg, h.rsi, h.r11]; rw [BitVec.add_comm, XorBuf.sub_add_add]

/-- The regions the code around the rounds writes, from the state at `s`. -/
theorem TInv.wregs (h : TInv X s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) {D : Nat} {s' : State}
    (hg : s'.gpr = s.gpr) : wregsT true D s' = [⟨ebp s₀, 256⟩, winQ s₀ p (4 * D)] := by
  simp only [wregsT, hg, hr9, List.cons.injEq, and_true, true_and]
  exact congrArg (fun a => (⟨a, 4 * D⟩ : Region)) (h.dst (D := D) hg)

end

/-! ## The last bytes, from `buf` -/

/-- After the code from `s` (`TInv X s₀ p s`) wrote the destination's `w`
bytes from byte `p` (`hd`), `buf`'s first 256 bytes with the keystream from
byte `p + w` on (`hb`) and nothing else (`f₄`), and the source and the
destination are on by `w` bytes: the rest, from `buf`. -/
theorem restT_ok (vl : Bool) {X : Mem → Prop} {s₀ : State} (hp : TPre s₀) {p w : Nat} (hpw : p + w ≤ eL s₀)
    (hle : eL s₀ - (p + w) ≤ 256) {s s₄ : State} (h : TInv X s₀ p s)
    (rsi₄ : s₄.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + w)) (r11₄ : s₄.gpr .r11 = edq s₀ - edp s₀)
    (r9₄ : s₄.gpr .r9 = ebp s₀) (rdx₄ : s₄.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + w)))
    (rd₄ : s₄.rd = s.rd) (wr₄ : s₄.wr = s.wr) (keep₄ : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r)
    (f₄ : Frame [⟨ebp s₀, 256⟩, winQ s₀ p w] s.mem s₄.mem)
    (hd : ∀ k < w, s₄.mem (edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) =
      D0 s₀ (p + k) ^^^ (KS s₀).getD (p + k) 0)
    (hb : ∀ k < eL s₀ - (p + w), s₄.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + w + k) 0) :
    WP isa (Impl.ChaCha20.X86_64.Avx2Tail.fromBuf vl) s₄ (DoneT s₀) := by
  have hL := eL_lt s₀
  have nbuf : ∀ (a : Addr) (R : Region), R.Disjoint (Avx2.bufR (ebp s₀)) → R.Contains a 1 →
      ¬ (⟨ebp s₀, 256⟩ : Region).Contains a 1 := fun a R hd hc hc' =>
    hd _ hc (Region.sub_prefix (by omega_arith) _ hc')
  -- The source outside the destination's `w` bytes is intact.
  have nS : ∀ k < eL s₀, (k < p ∨ p + w ≤ k) → ¬ (winQ s₀ p w).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk ho
    rcases hp.alias with he | hdis
    · have := not_winQ (s₀ := s₀) (p := p) (n := w) (by omega_arith) hk ho
      simp only [edq, edp] at he this ⊢; rwa [he] at this
    · exact fun hc => hdis _ (in_dR hk) (winQ_sub (by omega_arith) _ hc)
  refine fromBufY_ok vl hp (p := p + w) (n := eL s₀ - (p + w)) (by omega_arith) hle rsi₄ r11₄ r9₄ rdx₄
    (by rw [rd₄, h.rd]) (by rw [wr₄, h.wr]) (fun r hr => by rw [keep₄ r hr]; exact h.keep r hr)
    (fun k hk => ?_) (fun k hk => ?_) hb ?_
  · by_cases hkp : k < p
    · rw [f₄ _ (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nbuf _ _ hp.q_b (in_eqR (by omega_arith))
        · exact not_winQ (by omega_arith) (by omega_arith) (.inl hkp)), h.data k (by omega_arith),
        ite_eq_left hkp]
    · have x := hd (k - p) (by omega_arith)
      rwa [add_ofNat, Nat.add_sub_cancel' (by omega_arith)] at x
  · rw [add_ofNat, f₄ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact nbuf _ _ hp.d_b (in_dR (by omega_arith))
      · exact nS _ (by omega_arith) (.inr (by omega_arith))), h.src hp (by omega_arith) (by omega_arith)]
  · refine h.frame.trans (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩

/-- After the code from `s` wrote `buf`'s first 256 bytes with the keystream
from byte `p` on and nothing else: the rest, from `buf`. -/
theorem fromBufT_ok (vl : Bool) {X : Mem → Prop} {s₀ : State} (hp : TPre s₀) {p : Nat} (hn : eL s₀ - p ≤ 256)
    {s s₃ : State} (h : TInv X s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) (g₃ : s₃.gpr = s.gpr) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (f₃ : Frame [⟨ebp s₀, 256⟩] s.mem s₃.mem)
    (hb : ∀ k < eL s₀ - p, s₃.mem (ebp s₀ + BitVec.ofNat 64 k) = (KS s₀).getD (p + k) 0) :
    WP isa (Impl.ChaCha20.X86_64.Avx2Tail.fromBuf vl) s₃ (DoneT s₀) :=
  restT_ok vl hp (w := 0) (by have := h.le; omega_arith) hn h (by rw [g₃]; exact h.rsi) (by rw [g₃]; exact h.r11)
    (by rw [g₃]; exact hr9) (by rw [g₃]; exact h.rdx) rd₃ wr₃ (fun r _ => by rw [g₃])
    (f₃.mono (by simp)) (fun k hk => absurd hk (by omega_arith)) hb

/-- `wregs 0`, the regions the code around the rounds writes into `buf`. -/
theorem wregs0 {s₀ s : State} (hr9 : s.gpr .r9 = ebp s₀) {s₂ : State}
    (g₂ : s₂.gpr = s.gpr) {m m' : Mem} (f : Frame (wregs 0 s₂) m m') : Frame [⟨ebp s₀, 256⟩] m m' := by
  refine f.sub fun r hr => ?_
  simp only [wregs, g₂, hr9, Nat.mul_zero, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  · exact ⟨⟨ebp s₀, 256⟩, List.mem_singleton_self _, fun x hx => by
      simp only [Region.Contains] at hx; omega_arith⟩

/-! ## Eight blocks into the destination -/

/-- What `vg_chacha20_xor_avx512` keeps in `buf` for its last bytes: the
lane increments. -/
abbrev XI (s₀ : State) (m : Mem) : Prop := Incs m (ebp s₀)

set_option simprocs false in
theorem adv_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hge : 512 ≤ eL s₀ - p) {s : State}
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
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega_arith) (by omega_arith)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by rw [hrd, hwr]; exact List.mem_append_right _ hp.w_st, c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by rw [hwr]; exact hp.w_st, c₁⟩
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
  refine ⟨by rw [hrsi]; exact Offset.add_add _ _ _,
    by rw [hrdx, show (512 : BitVec 64) = BitVec.ofNat 64 512 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      Nat.sub_sub],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], Xor.stateAt_writeW_counter _ _ _, hfs, by simp⟩

/-- Destination byte `k`, after the destination from byte `p` was written
(`hw`) and nothing else (`hf`). -/
theorem data_step {s₀ : State} {p n : Nat} {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ k < eL s₀, k < p ∨ p + n ≤ k →
      ¬ r.Contains (edq s₀ + BitVec.ofNat 64 k) 1)
    (hw : ∀ k < n, m' (edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) =
      D0 s₀ (p + k) ^^^ (KS s₀).getD (p + k) 0)
    (hm : ∀ k < eL s₀, m (edq s₀ + BitVec.ofNat 64 k) =
      if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k) :
    ∀ k < eL s₀, m' (edq s₀ + BitVec.ofNat 64 k) =
      if k < p + n then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k := by
  intro k hk
  by_cases hin : p ≤ k ∧ k < p + n
  · have x := hw (k - p) (by omega_arith)
    rw [add_ofNat, Nat.add_sub_cancel' hin.1] at x
    rw [x, ite_eq_left hin.2]
  · rw [hf _ (fun r hr => hd r hr k hk (by omega_arith)), hm k hk]
    by_cases hlt : k < p
    · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Incs m (ebp s₀)) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩ : Region).Disjoint r) : Incs m' (ebp s₀) := by
  intro k hk p hp
  rw [← h k hk p hp]
  refine hf.readW (r := ⟨ebp s₀ + BitVec.ofNat 64 192, 128⟩) ?_ hd (by decide)
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · simp only [incB]
    rw [show 4 * (64 + p) = 192 + (4 * (p + 16)) by omega_arith, ← add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · simp only [incB]
    rw [show 4 * (48 + p) = 192 + 4 * p by omega_arith, ← add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem full_eq : full = .seq (.block setup2) (.seq (rounds2 10)
    (.block ((finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256) ++
      ([.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
        .alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512)] : List Instr)))) := by
  simp only [full, List.append_assoc]

theorem fullT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hge : 512 ≤ eL s₀ - p) {s : State}
    (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa full s fun s' => TInv (XI s₀) s₀ (p + 512) s' ∧ s'.gpr .r9 = ebp s₀ := by
  have hL := eL_lt s₀
  have hw : p + 4 * 128 ≤ eL s₀ := by omega_arith
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.x
  rw [full_eq]
  refine WP.seq (WP.mono (setup2_ok (h.ctx0 hp hr9 rfl rfl) hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (full_ok (h.ctxT hp hr9 hw (by decide) g₂ rd₂ wr₂) hi₂ hz₂)
    fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (adv_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (rd₃.trans (rd₂.trans h.rd)) (wr₃.trans (wr₂.trans h.wr)))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄⟩ => ?_
  rw [h.wregs hr9 g₂, m₂] at f₃
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_b.sub_right (Region.sub_prefix (by omega_arith))
      · exact hp.st_q.sub_right (winQ_sub (by omega_arith)))
  refine ⟨⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.r11, e₂, by omega_arith,
    Nat.dvd_add h.dvd ⟨8, rfl⟩, fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr],
    ?_, ?_, ?_, ?_⟩, by rw [gk _ (by decide) (by decide) (by decide)]; exact hr9⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show (p + 512) / 64 = p / 64 + 8 by omega_arith]
    exact ctr_add _ _ 8
  · have F : Frame [⟨ebp s₀, 256⟩, winQ s₀ p (4 * 128), Avx2.stR (est s₀)] s.mem s₄.mem :=
      (f₃.mono (by simp)).trans (f₄.mono (by simp))
    refine data_step (n := 512) F (fun r hr k hk ho => ?_) (fun k hk => ?_) h.data
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun hc => hp.q_b _ (in_eqR hk) (Region.sub_prefix (by omega_arith) _ hc)
      · exact not_winQ (by omega_arith) hk ho
      · exact fun hc => hp.st_q _ hc (in_eqR hk)
    · have hk' : ¬ (Avx2.stR (est s₀)).Contains (edq s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 k) 1 :=
        fun hc => hp.st_q _ hc (by rw [add_ofNat]; exact in_eqR (by omega_arith))
      rw [f₄ _ (by simpa using hk')]
      have x := d₃ k hk
      rw [h.dst g₂, g₂, h.rsi, m₂, add_ofNat (edp s₀), h.src hp (by omega_arith) (by omega_arith),
        h.cntAt g₂ m₂, h.cntAt rfl rfl] at x
      rw [x, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]
  · have I₃ : Incs s₃.mem (ebp s₀) := fun k hk q hq => by
      have x := b₃ (incB k + q) (by rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;> simp only [incB] <;> omega_arith)
      rw [g₂, hr9, m₂] at x
      rw [x]; exact h.x k hk q hq
    exact incs_frame I₃ f₄ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_b.sub_right (Offset.sub_base _ (by omega_arith))).symm)
  · refine h.frame.trans ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## Four blocks, into `buf` -/

theorem lastT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa last s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.x
  refine WP.seq (WP.mono (setup_ok (h.ctx0 hp hr9 rfl rfl) hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (finish_ok (h.ctx0 hp hr9 g₂ (sm₂.wr.trans wr₁)) hi₂ hz₂)
    fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  refine fromBufT_ok true hp hle h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    h.cntAt g₂ m₂, h.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]

/-! ## Eight blocks, four into the destination and four into `buf` -/

theorem part_eq : part = .seq (.block setup2) (.seq (rounds2 10) (.seq
    (.block ((finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) fromBuf)) := by
  simp only [part, List.append_assoc]

theorem partT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hgt : 256 < eL s₀ - p) (hlt : eL s₀ - p < 512)
    {s : State} (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa part s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega_arith
  have hi : Incs s.mem (s.gpr .r9) := by rw [hr9]; exact h.x
  rw [part_eq]
  refine WP.seq (WP.mono (setup2_ok (h.ctx0 hp hr9 rfl rfl) hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds2_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (part_ok (h.ctxT hp hr9 hw (by decide) g₂ rd₂ wr₂) hi₂ hz₂)
    fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (advN_ok (s₀ := s₀) (p := p) (N := 256) (by decide) (by omega_arith)
    (by rw [g₃']; exact h.rsi) (by rw [g₃']; exact h.rdx)) fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  rw [h.wregs hr9 g₂, m₂] at f₃
  refine restT_ok true hp (w := 256) (by omega_arith) (by omega_arith) h e₁
    (by rw [gk _ (by decide) (by decide)]; exact h.r11) (by rw [gk _ (by decide) (by decide)]; exact hr9) e₂
    (rd₄.trans (rd₃.trans rd₂)) (wr₄.trans (wr₃.trans wr₂))
    (fun r hr => by obtain ⟨_, b, c⟩ := calleeSaved_ne hr; exact gk r b c) (by rw [m₄]; exact f₃)
    (fun k hk => ?_) (fun k hk => ?_)
  · have x := d₃ k hk
    rw [h.dst g₂, g₂, h.rsi, m₂, add_ofNat (edp s₀), h.src hp (by omega_arith) (by omega_arith), h.cntAt g₂ m₂,
      h.cntAt rfl rfl] at x
    rw [m₄, x, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]
  · rw [m₄, show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9],
      b₃ k (by omega_arith), h.cntAt g₂ m₂, h.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith),
      show (p + 256 + k - p) / 64 = 4 + k / 64 by omega_arith, show (p + 256 + k - p) % 64 = k % 64 by omega_arith]

/-! ## Twelve blocks -/

/-- The offsets in `buf` and values of the quadwords of the third set's lane
increments (`inc3Q`). -/
def p3Pairs : List (Nat × BitVec 64) :=
  [(0, 8), (8, 0), (16, 9), (24, 0), (32, 10), (40, 0), (48, 11), (56, 0)]

theorem p3_eq : Impl.ChaCha20.X86_64.Avx2.storeQ inc3Off inc3Q = Avx2.pairsCode p3Pairs := rfl

theorem p3Pairs_le : ∀ p ∈ p3Pairs, p.1 + 8 ≤ 64 := by decide

/-- Stores into `buf[0, 64)` keep the rest of memory. -/
theorem storeLo_frame {buf : Addr} (ps : List (Nat × BitVec 64)) (hps : ∀ p ∈ ps, p.1 + 8 ≤ 64) (m : Mem) :
    Frame [⟨buf, 64⟩] m (Avx2.storeAll buf ps m) := by
  induction ps generalizing m with
  | nil => exact Frame.refl _ _
  | cons p ps ih =>
    rw [Avx2.storeAll, List.foldl_cons, ← Avx2.storeAll]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base buf (hps p (List.mem_cons_self ..)) (by have := hps p (List.mem_cons_self ..); omega))).trans
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _)

theorem incs3_mem {s₀ : State} {m : Mem} (h : Incs m (ebp s₀)) :
    Incs3 (Avx2.storeAll (ebp s₀) p3Pairs m) (ebp s₀) := by
  intro k hk p hp
  rcases (by omega : k < 2 ∨ k = 2) with hk2 | rfl
  · exact incs_frame h (storeLo_frame p3Pairs p3Pairs_le m) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by decide) (by decide)) k hk2 p hp
  · have H : ∀ j < 16, Avx2.readsTo [] p3Pairs (incB 2 + j)
        (if j % 4 = 0 then BitVec.ofNat 32 (4 * 2 + j / 4) else 0) = true := by decide +kernel
    exact Avx2.storeAll_readW32 (H p hp) m

theorem part3_eq : part3 = .seq (.block (Avx2.pairsCode p3Pairs ++ setup3)) (.seq (rounds3 10) (.seq
    (.block (finish3 ++ ([.alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512)] : List Instr))) fromBuf)) := by
  rw [part3, p3_eq]

theorem part3T_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hgt : 512 < eL s₀ - p) (hle : eL s₀ - p ≤ 768)
    {s : State} (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa part3 s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 128 ≤ eL s₀ := by omega_arith
  rw [part3_eq]
  -- The third set's increments, then the input states.
  refine WP.seq (WP.block_append (WP.mono (Avx2.pairs_ok (buf := ebp s₀) p3Pairs
    (fun q hq => by have := p3Pairs_le q hq; omega_arith) (s := s) h.rcx (by rw [h.wr]; exact hp.w_b))
    fun s₀' ⟨m₀, g₀, rd₀, wr₀⟩ => ?_))
  have gk₀ : ∀ r, r ≠ .rax → s₀'.gpr r = s.gpr r := g₀
  have nst : ∀ r ∈ [Avx2.bufR (ebp s₀)], (Avx2.stR (est s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.st_b
  have F₀ : Frame [Avx2.bufR (ebp s₀)] s.mem s₀'.mem := by
    rw [m₀]; exact Avx2.storeAll_frame (List.mem_singleton_self _) _ (fun q hq => by have := p3Pairs_le q hq; omega_arith) _
  have nB : ∀ (a : Addr) (R : Region), R.Disjoint (Avx2.bufR (ebp s₀)) → R.Contains a 1 →
      ∀ r ∈ [Avx2.bufR (ebp s₀)], ¬ r.Contains a 1 := fun a R hd hc r hr hc' => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd _ hc hc'
  -- The invariant after the increments, but for them.
  have h₀ : TInv (fun _ => True) s₀ p s₀' :=
    ⟨by rw [gk₀ _ (by decide)]; exact h.rdi, by rw [gk₀ _ (by decide)]; exact h.rcx,
      by rw [gk₀ _ (by decide)]; exact h.rsi, by rw [gk₀ _ (by decide)]; exact h.r11,
      by rw [gk₀ _ (by decide)]; exact h.rdx, h.le, h.dvd,
      fun r hr => by rw [gk₀ r (calleeSaved_ne hr).1]; exact h.keep r hr, by rw [rd₀, h.rd], by rw [wr₀, h.wr],
      by rw [Xor.stateAt_frame F₀ nst]; exact h.cnt,
      fun k hk => by rw [F₀ _ (nB _ _ hp.q_b (in_eqR hk)), h.data k hk], trivial,
      h.frame.trans (F₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨Avx2.bufR (ebp s₀), by simp, fun _ h => h⟩)⟩
  have r9₀ : s₀'.gpr .r9 = ebp s₀ := by rw [gk₀ _ (by decide)]; exact hr9
  have hi₀ : Incs3 s₀'.mem (s₀'.gpr .r9) := by rw [m₀, r9₀]; exact incs3_mem h.x
  refine WP.mono (setup3_ok (h₀.ctx0 hp r9₀ rfl rfl) hi₀) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_
  refine WP.seq (WP.mono (rounds3_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s₀'.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s₀'.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s₀'.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s₀'.wr := sm₂.wr.trans wr₁
  have hi₂ : Incs3 s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi₀
  refine WP.seq (WP.block_append (WP.mono (part3_ok (h₀.ctxT hp r9₀ hw (by decide) g₂ rd₂ wr₂) hi₂ hz₂)
    fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s₀'.gpr := g₃.trans g₂
  refine WP.mono (advN_ok (s₀ := s₀) (p := p) (N := 512) (by decide) (by omega_arith)
    (by rw [g₃']; exact h₀.rsi) (by rw [g₃']; exact h₀.rdx)) fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s₀'.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  rw [h₀.wregs r9₀ g₂, m₂] at f₃
  refine restT_ok true hp (w := 512) (by omega_arith) (by omega_arith) h₀ e₁
    (by rw [gk _ (by decide) (by decide)]; exact h₀.r11) (by rw [gk _ (by decide) (by decide)]; exact r9₀) e₂
    (rd₄.trans (rd₃.trans rd₂)) (wr₄.trans (wr₃.trans wr₂))
    (fun r hr => by obtain ⟨_, b, c⟩ := calleeSaved_ne hr; exact gk r b c) (by rw [m₄]; exact f₃)
    (fun k hk => ?_) (fun k hk => ?_)
  · have x := d₃ k hk
    rw [h₀.dst g₂, g₂, h₀.rsi, m₂, add_ofNat (edp s₀), h₀.src hp (by omega_arith) (by omega_arith), h₀.cntAt g₂ m₂,
      h₀.cntAt rfl rfl] at x
    rw [m₄, x, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]
  · rw [m₄, show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, r9₀],
      b₃ k (by omega_arith), h₀.cntAt g₂ m₂, h₀.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith),
      show (p + 512 + k - p) / 64 = 8 + k / 64 by omega_arith, show (p + 512 + k - p) % 64 = k % 64 by omega_arith]

/-! ## The whole tail -/

theorem smallT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa small s (FinT s₀) :=
  WP.mono (lastT_ok hp hle h hr9) fun _ d => d.fin hp

theorem tail_eq : tail =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 512)])
    (.seq (.ite .b (.block []) full)
    (.seq (.block [.alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) part)
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))) := rfl

theorem rest_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 512) {s : State}
    (h : TInv (XI s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) (hc : s.cf = some (decide (eL s₀ - p < 257))) :
    WP isa (.ite .b (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) small)) part) s
      (FinT s₀) := by
  refine WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, hc]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h hr9) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · exact smallT_ok hp (by omega_arith) h₂ r₂
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (partT_ok hp (by omega_arith) hlt h hr9) fun _ d => d.fin hp

theorem tail_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 1024) {s : State}
    (h : TInv (XI s₀) s₀ p s) :
    WP isa tail s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  rw [tail_eq]
  refine WP.seq (WP.mono (startN_ok h (N := 512) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => ∃ p', eL s₀ - p' < 512 ∧ TInv (XI s₀) s₀ p' s ∧
      s.gpr .r9 = ebp s₀) ?_
    fun s₂ ⟨p', hp', h₂, r₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ - p < 512)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (M := isa) ⟨p, hs, h₁, r₁⟩
    · simp only [decide_eq_false_iff_not] at hs
      exact WP.mono (fullT_ok hp (by omega_arith) h₁ r₁) fun s' ⟨h', r'⟩ => ⟨p + 512, by omega_arith, h', r'⟩
  · refine WP.seq (WP.mono (cmpN_ok h₂ r₂ (N := 257) (by decide) (by decide)) fun s₃ ⟨h₃, r₃, c₃⟩ => ?_)
    exact WP.seq (WP.mono (rest_ok hp hp' h₃ r₃ c₃) fun s₄ d => Avx2Tail.fin_ok d)

end VG.Proof.ChaCha20.X86_64.Avx512Tail
