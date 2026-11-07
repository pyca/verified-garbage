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
  have hL := eL_lt s₀
  obtain ⟨hm, hi⟩ := cst_of h hr9
  refine WP.seq (WP.mono (setup_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inr rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last_ok (h.ctx0 hp hr9 g₂ (sm₂.wr.trans wr₁)) hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃' := wregs0 hr9 g₂ f₃
  rw [m₂] at f₃'
  refine fromBufT_ok vl hp hle h hr9 (g₃.trans g₂) (rd₃.trans (sm₂.rd.trans rd₁))
    (wr₃.trans (sm₂.wr.trans wr₁)) f₃' fun k hk => ?_
  rw [show ebp s₀ + BitVec.ofNat 64 k = s₂.gpr .r9 + BitVec.ofNat 64 k by rw [g₂, hr9], b₃ k (by omega_arith),
    h.cntAt g₂ m₂, h.cntAt rfl rfl, ks_at h.dvd (by omega_arith) (by omega_arith), Nat.add_sub_cancel_left]

theorem last1T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hle : eL s₀ - p ≤ 128)
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last1 vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  obtain ⟨hm, hi⟩ := cst_of h hr9
  refine WP.seq (WP.mono (setup1_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS_ok vl (.inl rfl) hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.mono (last1_ok (h.ctx0 hp hr9 g₂ (sm₂.wr.trans wr₁)) hi₂ hz₂) fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃' := wregs0 hr9 g₂ f₃
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
  have hrd : edR s₀ ∈ s₁.rd ++ frT s₀ := by rw [← hwr, rd₁, wr₁, h.rd, h.wr]; exact hp.rd
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
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (small vl) s (FinT s₀) := by
  refine WP.seq (WP.mono (cmpN_ok h hr9 (N := 65) (by decide) (by decide)) fun s₁ ⟨h₁, r₁, c₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - p < 65)) (by simp [eval, c₁]) (fun _ => ?_) (fun _ => ?_)
  · exact scalarT_ok hp h₁
  · exact WP.mono (last1T_ok vl hp hle h₁ r₁) fun _ d => d.fin hp

theorem last3_eq (vl : Bool) : last3 vl = .seq (.block setup3) (.seq (roundsS vl 3 10) (.seq (.block
    ((addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0) ++
      ([.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] : List Instr))) (fromBuf vl))) := rfl

theorem last3T_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {p : Nat} (hge : 257 ≤ eL s₀ - p) (hle : eL s₀ - p ≤ 384)
    {s : State} (h : TInv (XA s₀) s₀ p s) (hr9 : s.gpr .r9 = ebp s₀) :
    WP isa (last3 vl) s (DoneT s₀) := by
  have hL := eL_lt s₀
  have hw : p + 4 * 64 ≤ eL s₀ := by omega_arith
  obtain ⟨hm, hi⟩ := cst_of h hr9
  rw [last3_eq vl]
  refine WP.seq (WP.mono (setup3_ok (h.ctx0 hp hr9 rfl rfl) hm hi) fun s₁ ⟨hz₁, ym₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsS3_ok vl hz₁ ym₁ 10) fun s₂ ⟨hz₂, _, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hi₂ : Incs s₂.mem (s₂.gpr .r9) := by rw [m₂, g₂]; exact hi
  refine WP.seq (WP.block_append (WP.mono (last3_ok (h.ctxT hp hr9 hw (by decide) g₂ rd₂ wr₂) hi₂ hz₂)
    fun s₃ ⟨d₃, b₃, f₃, g₃, rd₃, wr₃⟩ => ?_))
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (advN_ok (s₀ := s₀) (p := p) (N := 256) (by decide) (by omega_arith) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx)) fun s₄ ⟨e₁, e₂, e₃, m₄, rd₄, wr₄⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [e₃ r a b, g₃']
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
