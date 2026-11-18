module

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.FromBuf
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.FromBuf
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `ChaCha20.X86_64.Avx2.Last8`, which this module and modules that import it used -/

section

/-! ### `ChaCha20.X86_64.Avx2Tail.Tail`, which this module and modules that import it used -/

section

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes

`tail`, from the state after the eight-block loop of `vg_chacha20_xor_avx2`
(`Avx512Tail.TInv (XA s₀)`: the first `p` bytes of the destination done,
`p` a multiple of 64, fewer than 512 left, the masks and the lane
increments in `buf`), to the end of the function, from the source at `rsi`
to the destination at `rsi + r11`. The invariant's steps and the rest from
`buf` are `Avx512Tail`'s.
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
open VG.Proof.ChaCha20.X86_64.Avx512Tail (ks_at Ctx wregs S0 regn baseR bsize TInv startN_ok cmpN_ok test_ok
  done_of advN_ok restT_ok fromBufT_ok wregs0)

/-! ## The invariant -/

/-- What `vg_chacha20_xor_avx2` keeps in `buf` for its last bytes: the
masks and the lane increments. -/
abbrev XA (s₀ : State) (m : Mem) : Prop := Consts m (ebp s₀) ∧ Incs m (ebp s₀)

theorem cst_of {s₀ : State} {p : Nat} {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    Consts s.mem (s.gpr .r9) ∧ Incs s.mem (s.gpr .r9) := by
  rw [hr9]; exact h.x

/-! ## Four or two blocks, into `buf` -/

theorem lastT_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 256)
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last vl) s (DoneT s₀) := by
  obtain hL := eL_lt s₀
  obtain ⟨hm, hi⟩ := cst_of h hr9
  refine WP.seq (WP.mono (setup_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inr rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  obtain g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  obtain m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  obtain hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last_ok (h.ctx0 hp hr9 g₂ (sm₂.wr.trans wr₁)) hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  refine fromBufT_ok vl hp hle h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    h.cntAt g₂ m₂, h.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]

theorem last1T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last1 vl) s (DoneT s₀) := by
  obtain hL := eL_lt s₀
  obtain ⟨hm, hi⟩ := cst_of h hr9
  refine WP.seq (WP.mono (setup1_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inl rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  obtain g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  obtain m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  obtain hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last1_ok (h.ctx0 hp hr9 g₂ (sm₂.wr.trans wr₁)) hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  refine fromBufT_ok vl hp (by omega_arith) h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    h.cntAt g₂ m₂, h.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]

/-! ## At most 64 bytes, by `vg_chacha20_xor` -/

/-- `vg_chacha20_xor` XORs the last bytes of the source into the
destination, and returns with `rsi` pointing at `buf`. -/
theorem scalarT_ok {s₀ : State} (hp : TPre s₀) {p : Nat} {s : State} (h : TInv (XA s₀) s₀ p s) :
    WP isa scalar s (FinT s₀) := by
  obtain hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  obtain hsp' : (toR8 s₁).gpr .rsp = s₀.gpr .rsp := by rw [X86_64.RegUpd.gpr_setReg_of_ne _ _ (by decide), hsp]
  obtain hne : ∀ r : Reg, r ≠ .rsp → r ≠ .r8 → (toR8 s₁).callEntry.gpr r = s.gpr r := fun r h h8 => by
    rw [State.callEntry_gpr _ h, X86_64.RegUpd.gpr_setReg_of_ne _ _ h8, g₁]
  obtain h8 : (toR8 s₁).callEntry.gpr .r8 = edq s₀ + BitVec.ofNat 64 p := by
    rw [State.callEntry_gpr _ (by decide), X86_64.RegUpd.gpr_setReg_self, g₁, h.r11, h.rsi, XorBuf.sub_add_add]
  obtain hn : (BitVec.ofNat 64 (eL s₀ - p)).toNat = eL s₀ - p := toNat_ofNat_lt (by omega_arith)
  obtain hwr : s₁.wr = frT s₀ := by rw [wr₁, h.wr, hp.wr]
  obtain hrd : edR s₀ ∈ s₁.rd ++ frT s₀ := by rw [← hwr, rd₁, wr₁, h.rd, h.wr]; exact hp.rd
  obtain ts := pS_sub (s₀ := s₀) hle
  obtain tq := pQ_sub (s₀ := s₀) hle
  obtain Fce : Frame [estk s₀] s₁.mem (toR8 s₁).callEntry.mem := by
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
        Avx2.nowrap_at hp.nowrap hle (eL_lt s₀), Avx2.nowrap_at hp.nowrap_q hle (eL_lt s₀)⟩
      rcases hp.alias with he | hdis
      · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
      · exact .inr ((hdis.sub_left ts).sub_right tq)
    · rw [hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨edR s₀, hrd, p, rfl, show p + (eL s₀ - p) ≤ eL s₀ by omega_arith⟩
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
      obtain hce : stateAt (toR8 s₁).callEntry.mem (est s₀) = stateAt s₁.mem (est s₀) :=
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
        obtain n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
          hp.q_b _ (in_eqR hk) hc
        obtain n_sk : ¬ (estk s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
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
          obtain ea' : edp s₀ + BitVec.ofNat 64 k =
              edp s₀ + BitVec.ofNat 64 p + BitVec.ofNat 64 (k - p) := by
            rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)]
          obtain x := Avx2.bytes_of_bytesAt_to (length_keystream _ _) hpost (k := k - p) (by omega_arith)
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
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (small vl) s (FinT s₀) := by
  cases vl with
  | true => exact WP.mono (last1T_ok true hp hle h hr9) fun _ d => d.fin hp
  | false =>
  refine WP.seq (WP.mono (cmpN_ok h hr9 (N := 65) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 65)) (by simp [eval, c₁]) (fun _ => ?_) (fun _ => ?_)
  · exact scalarT_ok hp h₁
  · exact WP.mono (last1T_ok false hp hle h₁ r₁) fun _ d => d.fin hp

theorem last3_eq (vl : Bool) : last3 vl = .seq (.block setup3) (.seq (roundsS vl 3 10) (.seq (.block
    ((addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) (fromBuf vl))) := rfl

theorem last3T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hge : 257 ≤ eL s₀ - p) (hle : eL s₀ - p ≤ 384)
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last3 vl) s (DoneT s₀) := by
  obtain hL := eL_lt s₀
  obtain hw : p + 4 * 64 ≤ eL s₀ := by omega_arith
  obtain ⟨hm, hi⟩ := cst_of h hr9
  rw [last3_eq vl]
  refine WP.seq (WP.mono (setup3_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS3_ok vl hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  obtain g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  obtain m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  obtain rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  obtain wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  obtain hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (last3_ok (h.ctxT hp hr9 hw (by decide) g₂ rd₂ wr₂) hi₂ hz₂)
    fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  obtain g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (advN_ok (s₀ := s₀) (p := p) (N := 256) (by decide) (by omega_arith) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx)) fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  obtain gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
  rw [h.wregs hr9 g₂, m₂] at f₃
  refine restT_ok vl hp (w := 256) (by omega_arith) (by omega_arith) h e₁
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

theorem tail_eq (vl : Bool) : tail vl =
    .seq (.block [.mov .r9 (.reg .rcx), .alu .cmp .rdx (.imm 257)])
    (.seq (.ite .b (rest vl) (last3 vl))
      (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])) := rfl

theorem rest_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 257) {s : State}
    (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) : WP isa (rest vl) s (FinT s₀) := by
  refine WP.seq (WP.mono (cmpN_ok h hr9 (N := 129) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 129)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    refine WP.seq (WP.mono (test_ok h₁ r₁) fun s₂ ⟨h₂, r₂, z₂⟩ => ?_)
    refine WP.ite (decide (eL s₀ - p = 0)) (by simp [eval, z₂]) (fun he => ?_) (fun he => ?_)
    · simp only [decide_eq_true_eq] at he
      exact WP.block_nil (M := isa) ((done_of h₂ r₂ he).fin hp)
    · exact smallT_ok vl hp (by omega_arith) h₂ r₂
  · exact WP.mono (lastT_ok vl hp (by omega_arith) h₁ r₁) fun _ d => d.fin hp

theorem tail_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hlt : eL s₀ - p < 385) {s : State}
    (h : TInv (XA s₀) s₀ p s) :
    WP isa (tail vl) s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  rw [tail_eq vl]
  refine WP.seq (WP.mono (startN_ok h (N := 257) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := FinT s₀) (WP.ite (decide (eL s₀ - p < 257)) (by simp [eval, c₁])
    (fun hs => ?_) (fun hs => ?_)) fun s₂ d => fin_ok d)
  · simp only [decide_eq_true_eq] at hs
    exact rest_ok vl hp hs h₁ r₁
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (last3T_ok vl hp (by omega_arith) (by omega_arith) h₁ r₁) fun _ d => d.fin hp

end VG.Proof.ChaCha20.X86_64.Avx2Tail

end

end

/-!
# ChaCha20 on x86-64 with AVX2: the last 385 to 511 bytes

`last8` computes eight blocks as the loop does (`setup`, `rounds`) and
writes them out with `finishWith xorRow8` (`Finish.lean`): blocks 0 to 5
XORed into the 384 bytes of data at `rsi`, and blocks 6 and 7 stored to
`buf` (`b67Off`). `move67` then moves those two to `buf[0, 128)`, from
which `Avx2Tail.fromBuf` XORs the rest of the data.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512Tail (ks_at)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (r9_not_calleeSaved)

/-- Bytes outside the destination's 384 bytes from `p`. -/
theorem out_winQ' {s₀ : State} {p k : Nat} (hw : p + 384 ≤ eL s₀) (hk : k < eL s₀) (ho : k < p ∨ p + 384 ≤ k) :
    ¬ (⟨edq s₀ + BitVec.ofNat 64 p, 384⟩ : Region).Contains (edq s₀ + BitVec.ofNat 64 k) 1 :=
  Avx2Tail.not_winQ hw hk ho

/-! ## Writing out a row -/

/-- The first six blocks' 384 bytes of data. -/
abbrev dR3 (a : Addr) : Region := ⟨a, 384⟩

/-- Every access within the 384 bytes at `a` is permitted by `ws`. -/
def DWin3 (ws : List Region) (a : Addr) : Prop :=
  ∀ off n, off + n ≤ 384 → InRegions ws (a + BitVec.ofNat 64 off) n

/-- Where block `6 + j` is stored in `buf`. -/
abbrev bR (buf : Addr) (j : Nat) : Region := ⟨buf + BitVec.ofNat 64 (b67Off j), 64⟩

/-- The source's bytes outside what a frame of the destination changed are
intact: in place, as the destination's; apart, outside the frame. -/
theorem src_keep3 {a b : Addr} (al : b = a ∨ (dR3 a).Disjoint (dR3 b)) {rs : List Region}
    (hrs : ∀ r ∈ rs, (dR3 a).Disjoint r) {m m' : Mem} (hf : Frame (dR3 b :: rs) m m') {c : Nat → Prop}
    (hd : ∀ k < 384, ¬ c k → m' (b + BitVec.ofNat 64 k) = m (b + BitVec.ofNat 64 k))
    {k : Nat} (hk : k < 384) (hc : ¬ c k) : m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k) := by
  rcases al with rfl | hdis
  · exact hd k hk hc
  · exact hf.bytes (R := dR3 a) (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hdis
      · exact hrs r hr) (show 384 ≤ 2 ^ 64 by decide) hk

/-- What the output of the first six blocks needs of the source at `a` and
the destination at `b` (`rsi` and `rsi + r11`). -/
structure Out3 (a b : Addr) (s : State) : Prop where
  rsi : s.gpr .rsi = a
  dst : XorBuf.DstAt true s.gpr a b
  rd : DWin3 (s.rd ++ s.wr) a
  wr : DWin3 s.wr b
  al : b = a ∨ (dR3 a).Disjoint (dR3 b)

theorem Out3.of {a b : Addr} {s s' : State} (h : Out3 a b s) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : Out3 a b s' :=
  ⟨by rw [hg]; exact h.rsi, h.dst.congr hg, by rw [hr, hw]; exact h.rd, by rw [hw]; exact h.wr, h.al⟩

theorem xor16_3_ok {x : XReg} (_hx : x ≠ .xmm12) {off : Nat} (ho : off + 16 ≤ 384) {a b : Addr}
    {s : State} (hc : Out3 a b s) :
    WP isa (.block (xor16 true x off)) s fun s' =>
      (∀ k < 384, s'.mem (b + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k - off) else s.mem (b + BitVec.ofNat 64 k)) ∧
      (∀ k < 384, ¬ (off ≤ k ∧ k < off + 16) → s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR3 b] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain c : (dR3 b).Contains (b + BitVec.ofNat 64 off) 16 := Offset.contains_base b ho (by lit_omega)
  obtain o1 : InRegions s.wr (b + BitVec.ofNat 64 off) 16 := hc.wr off 16 ho
  obtain i1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 := hc.rd off 16 ho
  obtain e : s.ea (Impl.ChaCha20.X86_64.Avx2Tail.dst true off) = b + BitVec.ofNat 64 off :=
    XorBuf.DstAt.ea hc.rsi hc.dst off
  apply WP.of_runBlock
  simp only [xor16, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hc.rsi, State.load128,
    State.store128_eq, State.setV_ea, e, i1, o1, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, State.xmm_lane, State.lane_setV128,
    VBinOp.sse, reduceXBinOpEval]
  obtain hdat : ∀ k < 384, (s.mem.writeW (b + BitVec.ofNat 64 off) (s.lane x 0 ^^^
      s.mem.readW (a + BitVec.ofNat 64 off) 128)) (b + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k - off) else s.mem (b + BitVec.ofNat 64 k) := by
    intro k hk
    rw [byte_write16 _ _ _ (by lit_omega) (by lit_omega)]
    by_cases h : off ≤ k ∧ k < off + 16
    · simp only [h.1, h.2, and_self, ite_true, byte]
      rw [BitVec.xor_comm, BitVec.extractLsb'_xor, byte_readW _ _ (by lit_omega), add_ofNat,
        Nat.add_sub_cancel' h.1]
    · simp only [h, ite_false]
  obtain F : Frame [dR3 b] s.mem (s.mem.writeW (b + BitVec.ofNat 64 off)
      (s.lane x 0 ^^^ s.mem.readW (a + BitVec.ofNat 64 off) 128)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c
  refine ⟨hdat, fun k hk hn => src_keep3 hc.al (rs := []) (by simp) F
    (fun k hk hn => by rw [hdat k hk, ite_eq_right hn]) hk hn, F, fun r l hr => ?_, trivial, trivial, trivial⟩
  simp only [State.setMem_lane, State.lane_setV128, hr, ite_false]

/-- `piece`, for blocks `i` and `i + 4` of the first six. -/
theorem piece3_ok {row i : Nat} (hrow : row < 4) (hi : i < 2) {x : XReg} (hx12 : x ≠ .xmm12)
    {a b : Addr} {s : State} (hc : Out3 a b s) :
    WP isa (.block (piece true row x i)) s fun s' =>
      (∀ k < 384, s'.mem (b + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (b + BitVec.ofNat 64 k)) ∧
      (∀ k < 384, ¬ ((k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row) →
        s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dR3 b] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.block_append (WP.mono (xor16_3_ok hx12 (by lit_omega) hc)
    fun s₁ ⟨m₁, a₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine WP.mono (xor16_3_ok (x := .xmm13) (by decide) (off := 64 * (i + 4) + 16 * row) (a := a) (b := b)
    (by lit_omega) ((hc.of g₁ r₁ w₁).of (by rw [VOp.exec_gpr]) (by rw [VOp.exec_rd]) (by rw [VOp.exec_wr])))
    fun s₃ ⟨m₃, a₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12] at m₃ a₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, fun k hk hn => ?_, f₁.trans f₃, fun r l h12 h13 => ?_, g₃.trans g₁, r₃.trans r₁,
    w₃.trans w₁⟩
  · rw [m₃ k hk]
    by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
    · have h2 : ¬ (64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16) := by omega_arith
      obtain hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega_arith
      rw [ite_eq_right h2, m₁ k hk, ite_eq_left h1, ite_eq_left hc, show k / 64 / 4 = 0 by omega_arith,
        show k - (64 * i + 16 * row) = k % 16 by omega_arith]
    · by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
      · have hc : (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row := by omega_arith
        rw [ite_eq_left h2, a₁ k hk h1, ite_eq_left hc, show k / 64 / 4 = 1 by omega_arith,
          show k - (64 * (i + 4) + 16 * row) = k % 16 by omega_arith]
      · have hc : ¬ ((k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row) := by omega_arith
        rw [ite_eq_right h2, m₁ k hk, ite_eq_right h1, ite_eq_right hc]
  · rw [a₃ k hk (by omega_arith), a₁ k hk (by omega_arith)]
  · rw [l₃ r l h12, ite_eq_right h13, l₁ r l h12]

/-- Row `row` of block `2 + j` from lane 0 of `x` into the destination, and
of block `6 + j` from lane 1 to `buf`. -/
def pieceS (row : Nat) (x : XReg) (j : Nat) : List Instr :=
  xor16 true x (64 * (2 + j) + 16 * row) ++
    [.vop (.vextracti128 .xmm13 x 1), .vmovdquStore .l128 (at_ .rcx (b67Off j + 16 * row)) .xmm13]

theorem b67Off_le {j : Nat} : b67Off j + 64 ≤ 288 := by
  simp only [b67Off]; split <;> omega_arith

theorem pieceS_ok {row j : Nat} (hrow : row < 4) (hj : j < 2) {x : XReg} (hx12 : x ≠ .xmm12)
    {a b buf : Addr} {s : State} (hc : Out3 a b s) (hrcx : s.gpr .rcx = buf)
    (hb : bufR buf ∈ s.wr) (hd : (dR3 b).Disjoint (bufR buf)) (hda : (dR3 a).Disjoint (bufR buf)) :
    WP isa (.block (pieceS row x j)) s fun s' =>
      (∀ k < 384, s'.mem (b + BitVec.ofNat 64 k) =
        if 64 * (2 + j) + 16 * row ≤ k ∧ k < 64 * (2 + j) + 16 * row + 16 then
          s.mem (a + BitVec.ofNat 64 k) ^^^ byte (s.lane x 0) (k % 16)
        else s.mem (b + BitVec.ofNat 64 k)) ∧
      (∀ k < 384, ¬ (64 * (2 + j) + 16 * row ≤ k ∧ k < 64 * (2 + j) + 16 * row + 16) →
        s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        if k / 16 = row then byte (s.lane x 1) (k % 16)
        else s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [dR3 b, bR buf j] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hbo := b67Off_le (j := j)
  refine WP.block_append (WP.mono (xor16_3_ok hx12 (by lit_omega) hc)
    fun s₁ ⟨m₁, a₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  obtain o : InRegions s₁.wr (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) 16 := by
    rw [w₁]; exact out_buf hb (by lit_omega)
  obtain c : (bR buf j).Contains (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) 16 :=
    Offset.contains buf (by lit_omega) (by lit_omega) (by lit_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, VOp.exec_gpr, VOp.exec_wr, g₁, hrcx,
    State.store128_eq, o, ite_true, Option.some.injEq, exists_eq_left']
  simp only [VOp.exec_mem, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, State.setMem_mem, State.setMem_gpr,
    State.setMem_rd, State.setMem_wr, State.setMem_lane, State.xmm_lane, lane_vextracti128_1, ite_true,
    l₁ x 1 hx12]
  obtain W : Frame [bR buf j] s₁.mem
      (s₁.mem.writeW (buf + BitVec.ofNat 64 (b67Off j + 16 * row)) (s.lane x 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c
  obtain hbuf : ∀ k < 64, s₁.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
      s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) := fun k hk => by
    rw [add_ofNat]
    exact f₁ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hd _ hc (bufR_contains buf (by lit_omega))
  obtain nW : ∀ (p : Addr), (dR3 p).Disjoint (bufR buf) → ∀ k < 384, ∀ r ∈ [bR buf j],
      ¬ r.Contains (p + BitVec.ofNat 64 k) 1 := fun p hp k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact fun hc => hp _ (Offset.contains_base p (d := k) (n := 1) (by omega_arith) (by lit_omega))
      (Offset.sub_base buf (k := 320) (by lit_omega) _ hc)
  refine ⟨fun k hk => ?_, fun k hk hn => ?_, fun k hk => ?_, (f₁.mono (by simp)).trans (W.mono (by simp)),
    fun r l h12 h13 => ?_, g₁, r₁, w₁⟩
  · rw [W _ (nW b hd k hk), m₁ k hk]
    by_cases h : 64 * (2 + j) + 16 * row ≤ k ∧ k < 64 * (2 + j) + 16 * row + 16
    · rw [ite_eq_left h, ite_eq_left h, show k - (64 * (2 + j) + 16 * row) = k % 16 by omega_arith]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [W _ (nW a hda k hk), a₁ k hk hn]
  · rw [← add_ofNat, byte_write16 _ _ _ (by lit_omega) (by lit_omega)]
    by_cases h : 16 * row ≤ k ∧ k < 16 * row + 16
    · rw [ite_eq_left h, ite_eq_left (by omega_arith), show k - 16 * row = k % 16 by omega_arith]
    · rw [ite_eq_right h, ite_eq_right (by omega_arith), hbuf k hk]
  · rw [ite_eq_right h13, l₁ r l h12]


theorem xorRow8_eq (row : Nat) (x0 x1 x2 x3 : XReg) : xorRow8 row [x0, x1, x2, x3] =
    piece true row x0 0 ++ (piece true row x1 1 ++ (pieceS row x2 0 ++ pieceS row x3 1)) := rfl

section
variable {a buf : Addr}

theorem bR_dR3 (hd : (dR3 a).Disjoint (bufR buf)) (j : Nat) : (bR buf j).Disjoint (dR3 a) :=
  (hd.sub_right (Offset.sub_base buf (k := 320) (by have := b67Off_le (j := j); omega_arith))).symm

theorem bR_01 : (bR buf 0).Disjoint (bR buf 1) := Offset.disjoint buf (by decide) (by decide) (by decide)

end

theorem xorRow8_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13) (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13) (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13) {a b buf : Addr} {s : State}
    (hc : Out3 a b s) (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr)
    (hd : (dR3 b).Disjoint (bufR buf)) (hda : (dR3 a).Disjoint (bufR buf)) :
    WP isa (.block (xorRow8 row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 384, s'.mem (b + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then
          s.mem (a + BitVec.ofNat 64 k) ^^^
            byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (b + BitVec.ofNat 64 k)) ∧
      (∀ k < 384, k % 64 / 16 ≠ row → s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k)) ∧
      (∀ j < 2, ∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        if k / 16 = row then byte (s.lane ([x2, x3].getD j .xmm0) 1) (k % 16)
        else s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [dR3 b, bR buf 0, bR buf 1] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm12 → r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [xorRow8_eq]
  refine WP.block_append (WP.mono (piece3_ok hrow (i := 0) (by decide) h0.1 hc)
    fun s₁ ⟨m₁, a₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (piece3_ok hrow (i := 1) (by decide) h1.1 (hc.of g₁ r₁ w₁))
    fun s₂ ⟨m₂, a₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (pieceS_ok hrow (j := 0) (buf := buf) (by decide) h2.1
    ((hc.of g₁ r₁ w₁).of g₂ r₂ w₂) (by rw [g₂, g₁, hrcx]) (by rw [w₂, w₁]; exact hb) hd hda)
    fun s₃ ⟨m₃, a₃, b₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (pieceS_ok hrow (j := 1) (buf := buf) (by decide) h3.1
    (((hc.of g₁ r₁ w₁).of g₂ r₂ w₂).of g₃ r₃ w₃) (by rw [g₃, g₂, g₁, hrcx])
    (by rw [w₃, w₂, w₁]; exact hb) hd hda) fun s₄ ⟨m₄, a₄, b₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  obtain e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1.1 h1.2
  obtain e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2.1 h2.2).trans (l₁ _ l h2.1 h2.2)
  obtain e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l =>
    ((l₃ _ l h3.1 h3.2).trans (l₂ _ l h3.1 h3.2)).trans (l₁ _ l h3.1 h3.2)
  obtain bd := bR_dR3 hd
  obtain fb : ∀ j, ∀ k < 64, s₂.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
      s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) := fun j k hk => by
    obtain d : ∀ r ∈ [dR3 b], (bR buf j).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact bd _
    exact (f₂.bytes d (show 64 ≤ 2 ^ 64 by decide) hk).trans (f₁.bytes d (show 64 ≤ 2 ^ 64 by decide) hk)
  obtain c₂ : ∀ k, (64 * (2 + 0) + 16 * row ≤ k ∧ k < 64 * (2 + 0) + 16 * row + 16) ↔
      (k / 64 = 2 ∧ k % 64 / 16 = row) := fun k => by omega_using [hrow]
  obtain c₃ : ∀ k, (64 * (2 + 1) + 16 * row ≤ k ∧ k < 64 * (2 + 1) + 16 * row + 16) ↔
      (k / 64 = 3 ∧ k % 64 / 16 = row) := fun k => by omega_using [hrow]
  refine ⟨fun k hk => ?_, fun k hk hn => ?_, fun j hj k hk => ?_, ?_, fun r l n12 n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk]
    by_cases hr : k % 64 / 16 = row
    · rcases (by omega_using [hk] : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
        k / 64 = 4 ∨ k / 64 = 5) with h | h | h | h | h | h
      · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_right (by rw [c₂]; omega_arith), m₂ k hk,
          ite_eq_right (by omega_arith), m₁ k hk, ite_eq_left (by omega_arith), ite_eq_left hr]; simp [h]
      · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_right (by rw [c₂]; omega_arith), m₂ k hk,
          ite_eq_left (by omega_arith), a₁ k hk (by omega_arith), ite_eq_left hr, e1]; simp [h]
      · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_left (by rw [c₂]; omega_arith),
          a₂ k hk (by omega_arith), a₁ k hk (by omega_arith), ite_eq_left hr, e2]; simp [h]
      · rw [ite_eq_left (by rw [c₃]; omega_arith), a₃ k hk (by rw [c₂]; omega_arith), a₂ k hk (by omega_arith),
          a₁ k hk (by omega_arith), ite_eq_left hr, e3]; simp [h]
      · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_right (by rw [c₂]; omega_arith), m₂ k hk,
          ite_eq_right (by omega_arith), m₁ k hk, ite_eq_left (by omega_arith), ite_eq_left hr]; simp [h]
      · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_right (by rw [c₂]; omega_arith), m₂ k hk,
          ite_eq_left (by omega_arith), a₁ k hk (by omega_arith), ite_eq_left hr, e1]; simp [h]
    · rw [ite_eq_right (by rw [c₃]; omega_arith), m₃ k hk, ite_eq_right (by rw [c₂]; omega_arith), m₂ k hk,
        ite_eq_right (by omega_arith), m₁ k hk, ite_eq_right (by omega_arith), ite_eq_right hr]
  · rw [a₄ k hk (by rw [c₃]; omega_arith), a₃ k hk (by rw [c₂]; omega_arith), a₂ k hk (by omega_arith),
      a₁ k hk (by omega_arith)]
  · rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
    · have d : ∀ r ∈ [dR3 b, bR buf 1], (bR buf 0).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact bd _
        · exact bR_01
      rw [f₄.bytes d (show 64 ≤ 2 ^ 64 by decide) hk, b₃ k hk, fb _ k hk, e2]; rfl
    · have d : ∀ r ∈ [dR3 b, bR buf 0], (bR buf 1).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact bd _
        · exact bR_01.symm
      rw [b₄ k hk, f₃.bytes d (show 64 ≤ 2 ^ 64 by decide) hk, fb _ k hk, e3]; rfl
  · exact (((f₁.mono (by simp)).trans (f₂.mono (by simp))).trans (f₃.mono (by simp))).trans (f₄.mono (by simp))
  · rw [l₄ r l n12 n13, l₃ r l n12 n13, l₂ r l n12 n13, l₁ r l n12 n13]

/-- `xorRow8`'s effect: row `row` of the blocks `B 0, …, B 5` XORed with the
384 bytes of the source at `a` into the destination's at `b` (the source's
other rows intact), and of `B 6`, `B 7` stored to `buf` (`bR`). -/
def Eff8 (a b buf : Addr) (row : Nat) (B : Nat → CState) (m m' : Mem) : Prop :=
  (∀ k < 384, m' (b + BitVec.ofNat 64 k) =
    if k % 64 / 16 = row then m (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else m (b + BitVec.ofNat 64 k)) ∧
  (∀ k < 384, k % 64 / 16 ≠ row → m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) ∧
  ∀ j < 2, ∀ k < 64, m' (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
    if k / 16 = row then (serialize (B (6 + j))).getD k 0
    else m (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)

theorem xorRow8_out {a b buf : Addr} {g : Reg → BitVec 64} {rd w : List Region} (hrsi : g .rsi = a)
    (hds : XorBuf.DstAt true g a b) (hr : DWin3 (rd ++ w) a) (hwd : DWin3 w b)
    (al : b = a ∨ (dR3 a).Disjoint (dR3 b))
    (hrcx : g .rcx = buf) (hb : bufR buf ∈ w) (hd : (dR3 b).Disjoint (bufR buf)) (hda : (dR3 a).Disjoint (bufR buf))
    {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) :
    OutOk xorRow8 (Eff8 a b buf) [dR3 b, bR buf 0, bR buf 1] g rd w row x0 x1 x2 x3 := by
  intro B s hB hg hrd hws
  refine WP.mono (xorRow8_ok hrow (buf := buf) ⟨h0.1, h0.2.1⟩ ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩
    ⟨h3.1, h3.2.1⟩ ⟨by rw [hg]; exact hrsi, hds.congr hg, by rw [hrd, hws]; exact hr, by rw [hws]; exact hwd, al⟩
    (by rw [hg]; exact hrcx) (by rw [hws]; exact hb) hd hda) fun s₂ ⟨d₂, a₂, b₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_
  -- Row `row` of block `4 l + q`, from lane `l` of the `q`th register.
  obtain blk : ∀ l q, l < 2 → q < 4 → ∀ k, k % 64 / 16 = row →
      byte (s.lane ([x0, x1, x2, x3].getD q .xmm0) l) (k % 16) =
        (serialize (B (4 * l + q))).getD (k % 64) 0 := by
    intro l q hl hq k hr
    rw [serialize_row _ hrow hr]
    obtain ⟨b0, b1, b2, b3⟩ := hB l hl hrow
    rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
    · rw [List.getD_cons_zero, b0]
    · rw [List.getD_cons_succ, List.getD_cons_zero, b1]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b2]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b3]
  refine ⟨⟨fun k hk => ?_, a₂, fun j hj k hk => ?_⟩, f₂, fun r l _ _ _ _ n12 n13 _ _ => l₂ r l n12 n13,
    g₂, r₂, w₂⟩
  · rw [d₂ k hk]
    by_cases hr : k % 64 / 16 = row
    · rw [ite_eq_left hr, ite_eq_left hr, blk _ _ (by omega_arith) (by omega_arith) k hr,
        show 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 by omega_arith]
    · rw [ite_eq_right hr, ite_eq_right hr]
  · rw [b₂ j hj k hk]
    by_cases hr : k / 16 = row
    · have e := blk 1 (2 + j) (by decide) (by omega_arith) k (by rw [Nat.mod_eq_of_lt hk]; exact hr)
      rw [Nat.mod_eq_of_lt hk, show 4 * 1 + (2 + j) = 6 + j by omega_arith] at e
      rw [ite_eq_left hr, ite_eq_left hr, ← e]
      rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
    · rw [ite_eq_right hr, ite_eq_right hr]

/-! ## Moving blocks 6 and 7 -/

/-- Copy `buf[src, src + 32)` to `buf[dst, dst + 32)`, through `ymm12`. -/
def cp (src dst : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm12 (at_ .rcx src), .vmovdquStore .l256 (at_ .rcx dst) .xmm12]

theorem halves (v : BitVec 256) : v.extractLsb' 128 128 ++ v.extractLsb' 0 128 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega_arith, show 128 + (i - 128) = i by omega_arith]

theorem move67_eq : move67 = cp 128 0 ++ (cp 160 32 ++ (cp 224 64 ++ cp 256 96)) := rfl

theorem cp_ok {src dst : Nat} (hs : src + 32 ≤ 320) (hd : dst + 32 ≤ 320) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block (cp src dst)) s fun s' =>
      (∀ k < 32, s'.mem (buf + BitVec.ofNat 64 (dst + k)) = s.mem (buf + BitVec.ofNat 64 (src + k))) ∧
      Frame [⟨buf + BitVec.ofNat 64 dst, 32⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain i1 := in_buf (rs := s.rd) hb (d := src) (n := 32) hs
  obtain o1 := out_buf hb (d := dst) (n := 32) hd
  apply WP.of_runBlock
  simp only [cp, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1,
    State.store256_eq, o1, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr,
    State.setV_mem, State.setV_rd, State.setV_wr, State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, State.ymm_eq, State.lane_setV256, ite_true, Nat.reduceEqDiff, ite_false, halves]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    trivial, trivial, trivial⟩
  rw [← add_ofNat, writeW_byte _ _ _ (by lit_omega) (by lit_omega), byte_readW _ _ (by lit_omega), add_ofNat]

theorem nc {buf : Addr} {x d : Nat} (hx : x < 320) (hd : d + 32 ≤ 320) (h : x < d ∨ d + 32 ≤ x) :
    ¬ (⟨buf + BitVec.ofNat 64 d, 32⟩ : Region).Contains (buf + BitVec.ofNat 64 x) 1 := by
  simp only [Region.Contains]
  rw [Offset.sub_toNat' buf (by lit_omega) (by lit_omega)]
  split <;> omega_arith

/-- `move67`: blocks 6 and 7 (`bR`) to `buf[0, 128)`. -/
theorem move67_ok {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hb : bufR buf ∈ s.wr) :
    WP isa (.block move67) s fun s' =>
      (∀ j < 2, ∀ k < 64, s'.mem (buf + BitVec.ofNat 64 (64 * j + k)) =
        s.mem (buf + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k)) ∧
      Frame [slotsR buf] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [move67_eq]
  refine WP.block_append (WP.mono (cp_ok (src := 128) (dst := 0) (by decide) (by decide) hrcx hb)
    fun s₁ ⟨c₁, f₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (cp_ok (src := 160) (dst := 32) (buf := buf) (by decide) (by decide)
    (by rw [g₁]; exact hrcx) (by rw [w₁]; exact hb)) fun s₂ ⟨c₂, f₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (cp_ok (src := 224) (dst := 64) (buf := buf) (by decide) (by decide)
    (by rw [g₂, g₁]; exact hrcx) (by rw [w₂, w₁]; exact hb)) fun s₃ ⟨c₃, f₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (cp_ok (src := 256) (dst := 96) (buf := buf) (by decide) (by decide)
    (by rw [g₃, g₂, g₁]; exact hrcx) (by rw [w₃, w₂, w₁]; exact hb)) fun s₄ ⟨c₄, f₄, g₄, r₄, w₄⟩ => ?_
  -- A byte outside the copies' destinations, or before one, is unchanged by it.
  obtain u : ∀ {m m' : Mem} {d : Nat}, Frame [⟨buf + BitVec.ofNat 64 d, 32⟩] m m' → d + 32 ≤ 320 →
      ∀ x < 320, (x < d ∨ d + 32 ≤ x) → m' (buf + BitVec.ofNat 64 x) = m (buf + BitVec.ofNat 64 x) :=
    fun f hd x hx h => f _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact nc hx hd h
  obtain hs₂ : ∀ x, 128 ≤ x → x < 320 → s₂.mem (buf + BitVec.ofNat 64 x) = s.mem (buf + BitVec.ofNat 64 x) :=
    fun x h₁ h₂ => by rw [u f₂ (by decide) x h₂ (by omega_arith), u f₁ (by decide) x h₂ (by omega_arith)]
  obtain hs₃ : ∀ x, 128 ≤ x → x < 320 → s₃.mem (buf + BitVec.ofNat 64 x) = s.mem (buf + BitVec.ofNat 64 x) :=
    fun x h₁ h₂ => by rw [u f₃ (by decide) x h₂ (by omega_arith), hs₂ x h₁ h₂]
  refine ⟨fun j hj k hk => ?_, ?_, by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [add_ofNat]
    rcases (by omega_arith : (64 * j + k) / 32 = 0 ∨ (64 * j + k) / 32 = 1 ∨ (64 * j + k) / 32 = 2 ∨
      (64 * j + k) / 32 = 3) with h | h | h | h
    · obtain rfl : j = 0 := by omega_arith
      obtain e := c₁ k (by omega_arith)
      rw [Nat.zero_add] at e
      rw [Nat.mul_zero, Nat.zero_add, u f₄ (by decide) k (by omega_arith) (by omega_arith),
        u f₃ (by decide) k (by omega_arith) (by omega_arith), u f₂ (by decide) k (by omega_arith) (by omega_arith), e]
      rfl
    · obtain rfl : j = 0 := by omega_arith
      obtain e := c₂ (k - 32) (by omega_arith)
      rw [show 32 + (k - 32) = k by omega_arith, show 160 + (k - 32) = 128 + k by omega_arith] at e
      rw [Nat.mul_zero, Nat.zero_add, u f₄ (by decide) k (by omega_arith) (by omega_arith),
        u f₃ (by decide) k (by omega_arith) (by omega_arith), e, u f₁ (by decide) (128 + k) (by omega_arith) (by omega_arith)]
      rfl
    · obtain rfl : j = 1 := by omega_arith
      obtain e := c₃ k (by omega_arith)
      rw [show 64 + k = 64 * 1 + k by omega_arith] at e
      rw [u f₄ (by decide) (64 * 1 + k) (by omega_arith) (by omega_arith), e, hs₂ _ (by omega_arith) (by omega_arith)]
      rfl
    · obtain rfl : j = 1 := by omega_arith
      obtain e := c₄ (k - 32) (by omega_arith)
      rw [show 96 + (k - 32) = 64 * 1 + k by omega_arith, show 256 + (k - 32) = 224 + k by omega_arith] at e
      rw [e, hs₃ _ (by omega_arith) (by omega_arith)]
      rfl
  · have sub : ∀ d, d + 32 ≤ 128 → ∀ r ∈ [(⟨buf + BitVec.ofNat 64 d, 32⟩ : Region)],
        ∃ r' ∈ [slotsR buf], Region.Sub r r' := fun d hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨slotsR buf, by simp, Offset.sub_base buf hd⟩
    exact (((f₁.sub (sub 0 (by decide))).trans (f₂.sub (sub 32 (by decide)))).trans
      (f₃.sub (sub 64 (by decide)))).trans (f₄.sub (sub 96 (by decide)))

/-! ## The whole pass -/

theorem adv8_ok {s₀ : State} {p : Nat} (hge : 384 ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block ([.mov .r9 (.reg .rcx), .alu .add .rsi (.imm 384), .alu .sub .rdx (.imm 384)] : List Instr))
      s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 384) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 384)) ∧ s'.gpr .r9 = s.gpr .rcx ∧
      (∀ r, r ≠ .r9 → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain hL := eL_lt s₀
  obtain se : BitVec.signExtend 64 (384 : BitVec 32) = 384 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨?_, ?_, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial, trivial⟩
  · rw [hrsi]; exact Offset.add_add _ _ _
  · rw [hrdx, show (384 : BitVec 64) = BitVec.ofNat 64 384 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      show eL s₀ - p - 384 = eL s₀ - (p + 384) by omega_arith]

theorem last8_eq (vl : Bool) : last8 vl = .seq (.block setup) (.seq (roundsFor vl) (.seq
    (.block (finishWith xorRow8 ++ (move67 ++
      ([.mov .r9 (.reg .rcx), .alu .add .rsi (.imm 384), .alu .sub .rdx (.imm 384)] : List Instr))))
    (.seq (Impl.ChaCha20.X86_64.Avx2Tail.fromBuf vl) (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))) := by
  simp only [last8, List.append_assoc]

/-- The last 385 to 511 bytes, after `t` chunks. -/
theorem last8_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {t : Nat} (hge : 385 ≤ eL s₀ - 512 * t)
    (hlt : eL s₀ - 512 * t < 512) {s : State} (h : LInv s₀ t s) :
    WP isa (last8 vl) s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  obtain hL := eL_lt s₀
  obtain hw : 512 * t + 384 ≤ eL s₀ := by omega_arith
  obtain hst : stR (est s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_st
  obtain hb : bufR (ebp s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_b
  obtain hq : eqR s₀ ∈ s.wr := by rw [h.wr]; exact hp.w_q
  obtain hd : edR s₀ ∈ s.rd ++ s.wr := by rw [h.rd, h.wr]; exact hp.rd
  obtain sw : Region.Sub (dR3 (edp s₀ + BitVec.ofNat 64 (512 * t))) (edR s₀) := Offset.sub_base _ hw
  obtain sq : Region.Sub (dR3 (edq s₀ + BitVec.ofNat 64 (512 * t))) (eqR s₀) := Offset.sub_base _ hw
  obtain dsd := hp.st_q.sub_right sq
  obtain dbd := hp.q_b.symm.sub_right sq
  obtain dba := hp.d_b.symm.sub_right sw
  obtain dss : (stR (est s₀)).Disjoint (slotsR (ebp s₀)) := hp.st_b.sub_right (slotsR_sub _)
  obtain hsl : ∀ r ∈ [slotsR (ebp s₀)], (hiR (ebp s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _
  obtain al : edq s₀ + BitVec.ofNat 64 (512 * t) = edp s₀ + BitVec.ofNat 64 (512 * t) ∨
      (dR3 (edp s₀ + BitVec.ofNat 64 (512 * t))).Disjoint (dR3 (edq s₀ + BitVec.ofNat 64 (512 * t))) := by
    rcases hp.alias with he | hdis
    · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
    · exact .inr ((hdis.sub_left sw).sub_right sq)
  rw [last8_eq vl]
  refine WP.seq (WP.mono (setup_ok h.rdi h.rcx hst hb h.consts)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  obtain c₁ : Consts s₁.mem (ebp s₀) := by rw [m₁]; exact h.consts.w2 (by decide) y₁ y₂
  obtain F₁ : Frame [slotsR (ebp s₀)] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (roundsFor_ok vl hh h15 (by rw [g₁]; exact h.rcx) (by rw [wr₁]; exact hb) c₁.m8
    ⟨c₁.lo16, c₁.hi16⟩)
    fun s₂ hr => ?_)
  obtain F₂ := F₁.trans hr.frame
  obtain g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  obtain rd₂ : s₂.rd = s.rd := hr.rd.trans rd₁
  obtain wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  obtain hS₂ : stateAt s₂.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₂ (by simpa using dss)
  obtain hS : stateAt s.mem (est s₀) = ctr (Avx2.S0 s₀) (512 * t / 64) := by
    rw [h.cnt, show 512 * t / 64 = 8 * t by omega_arith]
  -- The regions the output writes.
  obtain hR : ∀ r ∈ [dR3 (edq s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1],
      (stR (est s₀)).Disjoint r ∧ (slotsR (ebp s₀)).Disjoint r ∧ (incR (ebp s₀)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dsd, dbd.sub_left (slotsR_sub _), dbd.sub_left (Offset.sub_base _ (by lit_omega))⟩
    · exact ⟨hp.st_b.sub_right (Offset.sub_base _ (by decide)),
        (Offset.disjoint_base _ (by decide) (by decide)).symm, Offset.disjoint _ (by decide) (by decide) (by decide)⟩
    · exact ⟨hp.st_b.sub_right (Offset.sub_base _ (by decide)),
        (Offset.disjoint_base _ (by decide) (by decide)).symm, Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  obtain hr₂ : DWin3 (s₂.rd ++ s₂.wr) (edp s₀ + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    refine ⟨edR s₀, by rw [rd₂, wr₂]; exact hd, ?_⟩
    rw [Offset.add_add]; exact Offset.contains_base _ (by lit_omega) (by lit_omega)
  obtain hw₂ : DWin3 s₂.wr (edq s₀ + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    refine ⟨eqR s₀, by rw [wr₂]; exact hq, ?_⟩
    rw [Offset.add_add]; exact Offset.contains_base _ (by lit_omega) (by lit_omega)
  obtain hds : XorBuf.DstAt true s₂.gpr (edp s₀ + BitVec.ofNat 64 (512 * t)) (edq s₀ + BitVec.ofNat 64 (512 * t)) :=
    XorBuf.DstAt.add (to := true) (g := s₂.gpr) (a := edp s₀) (b := edq s₀)
      ⟨fun _ => by rw [g₂]; exact h.r11, fun e => nomatch e⟩ _
  obtain o : ∀ {row : Nat} {x0 x1 x2 x3 : XReg}, row < 4 → (x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15) →
      (x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15) →
      (x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15) →
      (x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) →
      OutOk xorRow8 (Eff8 (edp s₀ + BitVec.ofNat 64 (512 * t)) (edq s₀ + BitVec.ofNat 64 (512 * t)) (ebp s₀))
        [dR3 (edq s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1] s₂.gpr s₂.rd s₂.wr
        row x0 x1 x2 x3 :=
    fun hrow => xorRow8_out (by rw [g₂]; exact h.rsi) hds hr₂ hw₂ al (by rw [g₂]; exact h.rcx)
      (by rw [wr₂]; exact hb) dbd.symm dba.symm hrow
  refine WP.seq (WP.block_append (WP.mono (finishWith_ok (out := xorRow8) hr.holds (st := est s₀)
    (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx) (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb)
    (incs_frame c₁.inc hr.frame hsl) hp.st_b hR
    (o (by decide) (by decide) (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide))
    (o (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun s₃ ⟨n₀, n₁, n₂, n₃, f₀, e₀, e₁, e₃, e₂, F₃, g₃, rd₃, wr₃⟩ => ?_))
  rw [hS₂] at e₀ e₁ e₂ e₃
  -- The keystream of block `j` of the eight.
  obtain ks : ∀ k, 512 * t ≤ k → k < eL s₀ → (KS s₀).getD k 0 =
      (serialize (plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (stateAt s.mem (est s₀)) j))
        (stateAt s.mem (est s₀)) ((k - 512 * t) / 64))).getD ((k - 512 * t) % 64) 0 := by
    intro k h₁ h₂
    rw [ks_at ⟨8 * t, by omega_arith⟩ h₁ h₂, hS]
  -- The output: the first six blocks XORed with the source into the destination, the last two in `buf`.
  obtain D₃ : ∀ k < 384, s₃.mem (edq s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
      D0 s₀ (512 * t + k) ^^^ (KS s₀).getD (512 * t + k) 0 := by
    intro k hk
    obtain z : n₀ (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
        s₂.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) :=
      f₀.bytes (R := dR3 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dba.sub_left (slotsR_sub _)).symm)
        (show 384 ≤ 2 ^ 64 by decide) hk
    obtain y : s₂.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) =
        s.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) :=
      F₂.bytes (R := dR3 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dba.sub_left (slotsR_sub _)).symm)
        (show 384 ≤ 2 ^ 64 by decide) hk
    obtain src : s.mem (edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 k) = D0 s₀ (512 * t + k) := by
      rw [add_ofNat]; exact h.src hp (by omega_arith) (by omega_arith)
    rw [e₂.1 k hk, ks _ (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]
    rcases (by omega_arith : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
      with hr | hr | hr | hr
    · rw [ite_eq_right (by omega_arith), e₃.1 k hk, ite_eq_right (by omega_arith), e₁.1 k hk,
        ite_eq_right (by omega_arith), e₀.1 k hk, ite_eq_left hr, z, y, src]
    · rw [ite_eq_right (by omega_arith), e₃.1 k hk, ite_eq_right (by omega_arith), e₁.1 k hk,
        ite_eq_left hr, e₀.2.1 k hk (by omega_arith), z, y, src]
    · rw [ite_eq_left hr, e₃.2.1 k hk (by omega_arith), e₁.2.1 k hk (by omega_arith), e₀.2.1 k hk (by omega_arith),
        z, y, src]
    · rw [ite_eq_right (by omega_arith), e₃.1 k hk, ite_eq_left hr, e₁.2.1 k hk (by omega_arith),
        e₀.2.1 k hk (by omega_arith), z, y, src]
  obtain K₃ : ∀ j < 2, ∀ k < 64, 512 * t + 384 + (64 * j + k) < eL s₀ →
      s₃.mem (ebp s₀ + BitVec.ofNat 64 (b67Off j) + BitVec.ofNat 64 k) =
        (KS s₀).getD (512 * t + 384 + (64 * j + k)) 0 := by
    intro j hj k hk hL
    rw [e₂.2.2 j hj k hk, e₃.2.2 j hj k hk, e₁.2.2 j hj k hk, e₀.2.2 j hj k hk, ks _ (by omega_arith) (by omega_arith),
      show (512 * t + 384 + (64 * j + k) - 512 * t) / 64 = 6 + j by omega_arith,
      show (512 * t + 384 + (64 * j + k) - 512 * t) % 64 = k by omega_arith]
    rcases (by omega_arith : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3)
      with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]
  obtain g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.block_append (WP.mono (move67_ok (buf := ebp s₀) (by rw [g₃']; exact h.rcx)
    (by rw [wr₃, wr₂]; exact hb)) fun s₄ ⟨mv, F₄, g₄, rd₄, wr₄⟩ => ?_)
  obtain g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  refine WP.mono (adv8_ok (s₀ := s₀) (p := 512 * t) (by omega_arith) (by rw [g₄']; exact h.rsi)
    (by rw [g₄']; exact h.rdx)) fun s₅ ⟨a₁, a₂, a₃, a₄, m₅, rd₅, wr₅⟩ => ?_
  obtain nb : ∀ (a : Addr) (R : Region), R.Disjoint (bufR (ebp s₀)) → R.Contains a 1 → ∀ (r : Region),
      Region.Sub r (bufR (ebp s₀)) → ¬ r.Contains a 1 := fun a R hR hc r hs hc' => hR _ hc (hs _ hc')
  obtain F₃' : Frame [slotsR (ebp s₀), dR3 (edq s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1]
      s.mem s₃.mem := (F₂.mono (by simp)).trans F₃
  obtain FA : Frame [slotsR (ebp s₀), dR3 (edq s₀ + BitVec.ofNat 64 (512 * t)), bR (ebp s₀) 0, bR (ebp s₀) 1]
      s.mem s₅.mem := by rw [m₅]; exact F₃'.trans (F₄.mono (by simp))
  obtain outS : ∀ k < eL s₀, (k < 512 * t ∨ 512 * t + 384 ≤ k) →
      ¬ (dR3 (edq s₀ + BitVec.ofNat 64 (512 * t))).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk ho
    rcases hp.alias with he | hdis
    · have := Avx2Tail.not_winQ (s₀ := s₀) (p := 512 * t) (n := 384) hw hk ho
      simp only [edq, edp] at he this ⊢; rwa [he] at this
    · exact fun hc => hdis _ (in_dR hk) (sq _ hc)
  refine WP.seq (WP.mono (Avx2Tail.fromBufY_ok vl hp (p := 512 * t + 384) (n := eL s₀ - (512 * t + 384))
    (by omega_arith) (by omega_arith) a₁ (by rw [a₄ _ (by decide) (by decide) (by decide), g₄']; exact h.r11)
    (by rw [a₃, g₄']; exact h.rcx) a₂ (by rw [rd₅, rd₄, rd₃, hr.rd, rd₁, h.rd])
    (by rw [wr₅, wr₄, wr₃, wr₂, h.wr]) (fun r hr => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk => ?_) ?_) fun s₆ d => Avx2Tail.fin_ok (d.fin hp))
  · obtain ⟨_, b, c⟩ := calleeSaved_ne hr
    rw [a₄ r (r9_not_calleeSaved hr).1 b c, g₄']; exact h.keep r hr
  · rw [m₅, F₄ _ (by
      simp only [List.mem_singleton, forall_eq]
      exact nb _ _ hp.q_b (in_eqR (by omega_arith)) _ (slotsR_sub _))]
    by_cases hkp : k < 512 * t
    · rw [F₃' _ (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact nb _ _ hp.q_b (in_eqR (by omega_arith)) _ (slotsR_sub _)
        · exact out_winQ' hw (by omega_arith) (.inl hkp)
        · exact nb _ _ hp.q_b (in_eqR (by omega_arith)) _ (Offset.sub_base _ (by decide))
        · exact nb _ _ hp.q_b (in_eqR (by omega_arith)) _ (Offset.sub_base _ (by decide))),
        h.data k (by omega_arith), ite_eq_left hkp]
    · rw [show edq s₀ + BitVec.ofNat 64 k = edq s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) by
          rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)], D₃ _ (by omega_arith),
        Nat.add_sub_cancel' (by omega_arith)]
  · rw [add_ofNat, FA _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact nb _ _ hp.d_b (in_dR (by omega_arith)) _ (slotsR_sub _)
      · exact outS _ (by omega_arith) (.inr (by omega_arith))
      · exact nb _ _ hp.d_b (in_dR (by omega_arith)) _ (Offset.sub_base _ (by decide))
      · exact nb _ _ hp.d_b (in_dR (by omega_arith)) _ (Offset.sub_base _ (by decide))),
      h.src hp (by omega_arith) (by omega_arith)]
  · have e := Nat.div_add_mod k 64
    rw [m₅, ← e, mv (k / 64) (by omega_arith) (k % 64) (by omega_arith), K₃ _ (by omega_arith) _ (by omega_arith) (by omega_arith)]
  · refine h.frame.trans (FA.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (ebp s₀), by simp, slotsR_sub _⟩
    · exact ⟨eqR s₀, by simp, sq⟩
    · exact ⟨bufR (ebp s₀), by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨bufR (ebp s₀), by simp, Offset.sub_base _ (by decide)⟩

end VG.Proof.ChaCha20.X86_64.Avx2

end

end

/-!
# `vg_chacha20_xor_avx2` verified

The loop over 512-byte chunks (`Avx2/Xor.lean`), then the last bytes
(`Avx2/Last8.lean`, `Avx2Tail/Tail.lean`), from the source to the
destination (`xorTo 16`, `TPre`); constant time and the calling
convention.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2

theorem tinv_of {s₀ : State} {t : Nat} {s : State} (h : LInv s₀ t s) :
    Avx512Tail.TInv (Avx2Tail.XA s₀) s₀ (512 * t) s where
  rdi := h.rdi
  rcx := h.rcx
  rsi := h.rsi
  r11 := h.r11
  rdx := h.rdx
  le := h.le
  dvd := ⟨8 * t, by omega_using []⟩
  keep := h.keep
  rd := h.rd
  wr := h.wr
  cnt := by rw [h.cnt, show 512 * t / 64 = 8 * t by omega_using []]
  data := h.data
  x := ⟨h.consts, h.incs⟩
  frame := h.frame

set_option simprocs false in
theorem cmp385_ok {s₀ : State} {t : Nat} {s : State} (h : LInv s₀ t s) :
    WP isa (.block [.alu .cmp .rdx (.imm 385)]) s fun s' =>
      LInv s₀ t s' ∧ s'.cf = some (decide (eL s₀ - 512 * t < 385)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (385 : BitVec 32) = 385 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨⟨h.rdi, h.rcx, h.rsi, h.r11, h.rdx, h.le, h.keep, h.rd, h.wr, h.cnt, h.data, h.consts, h.incs,
    h.frame⟩, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega_using [hL])]
  rfl

theorem xor_eq (vl : Bool) : Impl.ChaCha20.X86_64.Avx2.xorWith vl =
    .seq (.block (Impl.ChaCha20.X86_64.Avx2Tail.consts ++ consts ++ Impl.ChaCha20.X86_64.XorBuf.delta ++
      ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop (body vl) .ae))
    (.seq (.block [.alu .cmp .rdx (.imm 385)]) (.ite .b (Impl.ChaCha20.X86_64.Avx2Tail.tail vl) (last8 vl)))) :=
  rfl

theorem correct (vl : Bool) {s₀ : State} (hp : TPre s₀) :
    WP isa (Impl.ChaCha20.X86_64.Avx2.xorWith vl) s₀ fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  rw [xor_eq vl]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ < 512)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨0, by omega_using [h], h₁⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv : Nat → State → Prop := fun n s =>
        ∃ t, n = eL s₀ - 512 * t ∧ 512 ≤ eL s₀ - 512 * t ∧ LInv s₀ t s
      have hstep : ∀ n s, Inv n s → WP isa (body vl) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s') ∨
          (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
        rintro n s ⟨t, rfl, ht, hI⟩
        refine WP.mono (body_ok vl hp ht hI) fun s' ⟨h', hc'⟩ => ?_
        by_cases hl : eL s₀ - 512 * (t + 1) < 512
        · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
        · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 512 * (t + 1), by omega_using [ht], t + 1, rfl, by omega_using [hl], h'⟩
      exact WP.loop (M := isa) Inv hstep (eL s₀ - 512 * 0) s₁ ⟨0, rfl, by omega_using [h], h₁⟩
  · refine WP.seq (WP.mono (cmp385_ok h₂) fun s₃ ⟨h₃, c₃⟩ => ?_)
    refine WP.ite (decide (eL s₀ - 512 * t < 385)) (by simp [eval, c₃]) (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact Avx2Tail.tail_ok vl hp hs (tinv_of h₃)
    · simp only [decide_eq_false_iff_not] at hs
      exact last8_ok vl hp (by omega_using [hs]) ht h₃

theorem xorWith_to (vl : Bool)
    (hc : (Impl.ChaCha20.X86_64.Avx2.xorWith vl).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20.X86_64.Avx2.xorWith vl) s t s' ∧ abiPreserved s s' ∧
      (xorTo 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct vl (TPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec hc he h, hpost⟩

/-- `vg_chacha20_xor_avx2` from the source to the destination, returning
with `rsi` pointing at `buf`, as `vg_chacha20_xor` does. -/
theorem xor_to (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx2.xor s t s' ∧ abiPreserved s s' ∧ (xorTo 16).post s s' :=
  xorWith_to false (by lit_decide) s hs

theorem xor_ctTo : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Avx2.xor :=
  VG.Taint.constantTime (A := taint) Xor.τ₀ (fun _ _ h₁ h₂ hp => Xor.agree₀ h₁ h₂ hp) (by taint_decide)


end VG.Proof.ChaCha20.X86_64.Avx2
