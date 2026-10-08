import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call

/-!
# AES-GCM on whole blocks out of place, x86-64: the blocks left

Untrusted: everything here is checked by Lean. From `Mid s q q`, the
`n - q` blocks left, if any, are copied from the plaintext to the output
(`copyBlocks_wp`) and encrypted and hashed there by a call of
`vg_aes_gcm_encrypt_blocks` (`blkE_call`), with `scratch` pushed for it
(`tail_ok`). Counter mode and GHASH of the two parts make those of all the
blocks (`ctr32_append`, `ghashFrom_append`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Impl.AesGcm.X86_64.Blocks (argCtx argRounds argCtr argY argN)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32 aesWith)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.blocksToPost s s'

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

/-- The output is not all of memory: the key context is apart from it. -/
theorem n16_lt : n s * 16 < 2 ^ 64 := by
  have hw := hp.w_d
  refine Nat.lt_of_not_le fun hge => hp.k_d (K s) ?_ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := M.ge; omega
  · simp only [Region.Contains]
    have := (K s - Dst s).isLt
    omega

omit hp in
theorem dq_sub {q : Nat} (hq : q ≤ n s) : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) :=
  Offset.sub_base _ (by omega)

omit hp in
theorem sq_sub {q : Nat} (hq : q ≤ n s) : Region.Sub ⟨sq s q, (n s - q) * 16⟩ (srcR s) :=
  Offset.sub_base _ (by omega)

/-- With nothing left, `Mid` is the end. -/
theorem done_of {q : Nat} {st : State} (h : Mid s q q st) (h0 : n s - q = 0) : Done s st := by
  have hq : q = n s := by have := h.q_le; omega
  subst hq
  exact ⟨⟨h.saved, keep_r hp h.frame⟩, h.data, h.ctr, h.y⟩

/-- The head of `tail`: `rcx` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {st : State} (h : Mid s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rcx (.mem (at_ .r11 argN)), .alu .test .rcx (.reg .rcx)])
      st fun st' => Mid s q q st' ∧ st'.zf = some (decide (n s - q = 0)) ∧
        st'.gpr .r11 = S s ∧ st'.gpr .rcx = BitVec.ofNat 64 (n s - q) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hz := and_self_beq (show n s - q < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₂, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz],
    by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], by rfl⟩
  exact h.slots hp (by simp [gpr_setReg, gpr_arithFlags]) (fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags])
    h.kept (Frame.refl _ _) rfl rfl

/-- The pointers of the copy. -/
theorem ptrs_ok {q : Nat} {st : State} (h : Mid s q q st) (h11 : st.gpr .r11 = S s) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 argSrc)), .mov .rdi (.mem (at_ .r11 argDst))]) st
      fun st' => st'.gpr .rsi = sq s q ∧ st'.gpr .rdi = dq s q ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argSrc, argDst]; xrun [h11, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, by rfl, by rfl,
    by rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What the copy leaves: the plaintext left in the output, nothing else
written. -/
theorem copy_ok {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (hsi : st.gpr .rsi = sq s q) (hdi : st.gpr .rdi = dq s q) (hcx : st.gpr .rcx = BitVec.ofNat 64 (n s - q)) :
    WP isa copyBlocks st fun st' =>
      blocksAt st'.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) ∧
      Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hq := h.q_le
  have h16 := n16_lt hp
  have hwr := hp.w_r
  have hwd := hp.w_d
  have ss : Region.Sub ⟨sq s q, 16 * (n s - q)⟩ (srcR s) := Offset.sub_base _ (by omega)
  have ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega)
  have pre : CopyPre st (sq s q) (dq s q) (n s - q) :=
    ⟨hsi, hdi, hcx, by omega, by omega,
      Blocks.covers_off' (covers_of_mem (r := srcR s) (by rw [h.rd, h.wr, hp.rd]; simp)) (by omega) (by omega),
      Blocks.covers_off' (covers_of_mem (r := dR s) (by rw [h.wr, hp.wr]; simp)) (by omega) (by omega),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono (copyBlocks_wp st pre) fun st' ⟨hm, hg, hrd, hwr'⟩ => ⟨?_, ?_, hg, hrd, hwr'⟩
  · have e := bytesAt_writeBytes_self st.mem (dq s q) (Spec.Aes.bytesAt st.mem (sq s q) (16 * (n s - q)))
      (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at e
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, hm, e,
      bytesAt_frame h.frame (fun r hr => (src_wR hp r hr).sub_left ss) (by omega)]
  · rw [hm]; exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `Mid` through the copy, which writes only the output past the first `q`
blocks. -/
theorem Mid.copy {q : Nat} {st st' : State} (h : Mid s q q st)
    (hf : Frame [⟨dq s q, 16 * (n s - q)⟩] st.mem st'.mem) (hsp : st'.gpr .rsp = st.gpr .rsp)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    Mid s q q st' := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have ds : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega)
  have one : ∀ {r : Region}, r.Disjoint ⟨dq s q, 16 * (n s - q)⟩ →
      ∀ r' ∈ [(⟨dq s q, 16 * (n s - q)⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨hq, by rw [hsp, h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd, hwr.trans h.wr,
    h.kept.frame hf (one ((kR'_disj hp (dR s) (by simp)).sub_right ds)), h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩), ?_, ?_, ?_⟩
  · rw [← h.data]
    exact blocksAt_frame hf (one (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (n := 16 * (n s - q))
      (Nat.le_refl _) (by omega))) (by omega)
  · rw [← h.ctr]; exact blockAt_frame hf (one (hp.c_d.sub_right ds))
  · rw [← h.y]; exact blockAt_frame hf (one (hp.y_d.sub_right ds))

/-- The arguments of `vg_aes_gcm_encrypt_blocks` on the output left. -/
theorem args_ok {q : Nat} {st : State} (h : Mid s q q st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 24)), .mov .rdi (.mem (at_ .r11 argCtx)),
        .mov .rsi (.mem (at_ .r11 argRounds)), .mov .rdx (.mem (at_ .r11 argCtr)),
        .mov .rcx (.mem (at_ .r11 argY)), .mov .r8 (.mem (at_ .r11 argDst)), .mov .r9 (.mem (at_ .r11 argN)),
        .mov .rax (.reg .r11)]) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = C s ∧ st'.gpr .rcx = Y s ∧
      st'.gpr .r8 = dq s q ∧ st'.gpr .r9 = BitVec.ofNat 64 (n s - q) ∧ st'.gpr .rax = S s ∧
      st'.gpr .rsp = SP s ∧ (∀ r ∈ calleeSaved, st'.gpr r = s.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have a₂ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 24) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 2) (by decide)
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 24) 64 = S s := by
    rw [h.rsp, show (24 : Nat) = 8 * (2 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₇ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 48) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [argCtx, argRounds, argCtr, argY, argDst, argN]
    xrun [a₂, hS, r₁, r₂, r₃, r₄, r₆, r₇, kc0, h.kept.rounds, h.kept.ctr, h.kept.y, h.kept.dst, h.kept.n], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, h.rsp],
    fun r hr => ?_, by rfl, by rfl, by rfl⟩
  rw [← h.saved r hr]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

omit hp in
/-- The stack below the stack pointer after the push, as the call sees it. -/
theorem pushed_tR {st : State} (hsp : st.gpr .rsp = SP s) :
    (⟨(pushed [.rax] st).gpr .rsp - 16, 24⟩ : Region) = tR s := by
  rw [pushed_rsp, hsp]
  show (⟨SP s - BitVec.ofNat 64 8 - 16, 24⟩ : Region) = ⟨SP s - BitVec.ofNat 64 24, 24⟩
  rw [← Offset.sub_add_eq]; rfl

/-- What the call needs, after the push of `scratch`. -/
theorem blkCall_of {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    BlkCall M (pushed [.rax] st) (K s) (C s) (Y s) (dq s q) (S s) (R s) (n s - q) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  have hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax] (by decide) hn8
  have psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have harg : (pushed [.rax] st).mem.readW ((pushed [.rax] st).gpr .rsp) 64 = S s := by
    have := hpj 0 (by decide); rw [← h_ax]; rw [pushed_rsp]; exact this
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega)
  have tt := pushed_tR (s := s) hsp
  have hdq : (dq s q).toNat = (Dst s).toNat + 16 * q := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * q) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hR : BitVec.ofNat 64 (R s) = s.gpr .rsi := by simp [R]
  have hok : M.ok st.mem (K s) := M.frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]) hp.w_k hp.ok
  refine ⟨by rw [pushed_gpr _ _ (by decide)]; exact h_di, by rw [pushed_gpr _ _ (by decide), h_si, hR],
    by rw [pushed_gpr _ _ (by decide)]; exact h_dx, by rw [pushed_gpr _ _ (by decide)]; exact h_cx,
    by rw [pushed_gpr _ _ (by decide)]; exact h_8, by rw [pushed_gpr _ _ (by decide)]; exact h_9, harg, hp.rounds,
    hp.w_k, hp.w_c, hp.w_y, by rw [hdq]; omega, hp.w_s, ?_,
    hp.k_c, hp.k_y, hp.k_d.sub_right ds, hp.k_s, hp.c_y, hp.c_d.sub_right ds, hp.c_s, hp.y_d.sub_right ds, hp.y_s,
    hp.d_s.sub_left ds, by rw [tt]; exact hp.b_k, by rw [tt]; exact hp.b_c, by rw [tt]; exact hp.b_y,
    by rw [tt]; exact hp.b_d.sub_right ds, by rw [tt]; exact hp.b_s, ?_, ?_, ?_⟩
  · rw [psp, show SP s - BitVec.ofNat 64 8 - 8 = SP s - BitVec.ofNat 64 16 by rw [← Offset.sub_add_eq]; rfl,
      toNat_sub_ofNat (by omega)]
    omega
  · simp only [pushed_rd, pushed_wr, h.rd, h.wr, hp.rd, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by rw [pushed_rsp, hsp]; simp))
      (covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega) (by omega)
  · simp only [pushed_wr, h.wr, hp.wr, hsp]
    refine covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp))
      (covers_cons ?_ (covers_cons (covers_of_mem (by simp)) covers_nil)))
    exact Blocks.covers_off' (covers_of_mem (r := dR s) (by simp)) (by omega) (by omega)
  · exact M.frame hpf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.b_k.sub_left (below_sub (by decide) (by decide))).symm) hp.w_k hok

/-- What the call leaves, after the frame's pop. -/
theorem call_ok (B : BlkFn M) {q : Nat} {st : State} (h : Mid s q q st) (hlt : q < n s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = C s) (h_cx : st.gpr .rcx = Y s)
    (h_8 : st.gpr .r8 = dq s q) (h_9 : st.gpr .r9 = BitVec.ofNat 64 (n s - q)) (h_ax : st.gpr .rax = S s) :
    WP isa (.frame (.push [.rax]) (.call B.enc.name B.enc.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s] st.mem st'.mem ∧
      blocksAt st'.mem (dq s q) (n s - q) = ctr32 (aesWith (R s) (Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1))))
        (blockAt st.mem (C s)) (blocksAt st.mem (dq s q) (n s - q)) ∧
      blockAt st'.mem (C s) = Nat.repeat inc32 (n s - q) (blockAt st.mem (C s)) ∧
      blockAt st'.mem (Y s) = ghashFrom (blockAt st.mem (K s + 240)) (blockAt st.mem (Y s))
        (blocksAt st'.mem (dq s q) (n s - q)) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have h16 := n16_lt hp
  have hsp := h.rsp
  have wt := hp.w_t
  have hn8 : 8 * [Reg.rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax] (by decide) hn8
  have hpf' : Frame [below (SP s) 8] st.mem (pushed [.rax] st).mem := by rw [hsp] at hpf; exact hpf
  have b8 : Region.Sub (below (SP s) 8) (tR s) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (tR s).Disjoint r → ∀ r' ∈ [below (SP s) 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega)
  have eK : Spec.Aes.bytesAt (pushed [.rax] st).mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt st.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hpf' (one (hp.b_k.sub_right (Region.sub_prefix (Nat.le_trans hRb M.ge)))) (by have := hp.w_k; have := M.ge; omega)
  have eC : blockAt (pushed [.rax] st).mem (C s) = blockAt st.mem (C s) := blockAt_frame hpf' (one hp.b_c)
  have eY : blockAt (pushed [.rax] st).mem (Y s) = blockAt st.mem (Y s) := blockAt_frame hpf' (one hp.b_y)
  have eD : blocksAt (pushed [.rax] st).mem (dq s q) (n s - q) = blocksAt st.mem (dq s q) (n s - q) :=
    blocksAt_frame hpf' (one (by rw [Nat.mul_comm]; exact hp.b_d.sub_right ds)) (by omega)
  have eH : blockAt (pushed [.rax] st).mem (K s + 240) = blockAt st.mem (K s + 240) :=
    blockAt_frame hpf' (one (hp.b_k.sub_right (Offset.sub_base (d := 240) _ (by have := M.ge; omega))))
  refine WP.frame (by simp) (by decide) (by decide) hn8
    (WP.mono (blkE_call B (blkCall_of hp h hlt h_di h_si h_dx h_cx h_8 h_9 h_ax)) fun s₃ ⟨bp, o₁, o₂, o₃⟩ => ?_)
  have psp : (pushed [.rax] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have r₃ := bp.saved _ (by decide : Reg.rsp ∈ calleeSaved)
  refine ⟨r₃, bp.wr, fun r hr => ?_, by rw [popped_rd, bp.rd, pushed_rd], by rw [popped_wr, bp.wr, pushed_wr]; rfl,
    ?_, ?_, ?_, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, psp, hsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), bp.saved r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    refine (hpf'.sub fun r hr => ⟨tR s, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact b8⟩).trans
      (bp.frame.sub fun r hr => ?_)
    simp only [BlkCall.wr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨tR s, by simp, ?_⟩
      have e : SP s - BitVec.ofNat 64 8 - BitVec.ofNat 64 16 = SP s - BitVec.ofNat 64 24 := by
        rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
      show Region.Sub ⟨(pushed [.rax] st).gpr .rsp - BitVec.ofNat 64 16, 16⟩ _
      rw [psp, e]; exact Region.sub_prefix (by decide)
  · rw [popped_mem]; rw [eK, eC, eD] at o₁; exact o₁
  · rw [popped_mem]; rw [eC] at o₂; exact o₂
  · rw [popped_mem]; rw [eH, eY] at o₃; exact o₃

/-- The blocks left, from `Mid s q q`: copied and encrypted in place. -/
theorem tail_ok (B : BlkFn M) {q : Nat} {st : State} (h : Mid s q q st) : WP isa (tail B.enc) st (Done s) := by
  have hq := h.q_le
  have hwd := hp.w_d
  have hwr := hp.w_r
  have h16 := n16_lt hp
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M₁, hz, h11, hcx, hm₁⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (done_of hp M₁ e)
  have hlt : q < n s := by simp at e; omega
  refine WP.seq (WP.mono (ptrs_ok hp M₁ h11) fun st₂ ⟨hsi, hdi, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have M₂ : Mid s q q st₂ := M₁.copy hp (by rw [m₂]; exact Frame.refl _ _) (g₂ _ (by decide) (by decide))
    (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  refine WP.seq (WP.mono (copy_ok hp M₂ hlt hsi hdi (by rw [g₂ _ (by decide) (by decide), hcx]))
    fun st₃ ⟨hb₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have M₃ : Mid s q q st₃ := M₂.copy hp f₃ (g₃ _ (by decide) (by decide))
    (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  refine WP.seq (WP.mono (args_ok hp M₃) fun st₄ ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, sp₄, cs₄, m₄, rd₄, wr₄⟩ => ?_)
  have M₄ : Mid s q q st₄ := M₃.slots hp (by rw [sp₄, M₃.rsp]) (fun r hr => by rw [cs₄ r hr, M₃.saved r hr])
    (by rw [m₄]; exact M₃.kept) (by rw [m₄]; exact Frame.refl _ _) rd₄ wr₄
  refine WP.mono (call_ok hp B M₄ hlt a₁ a₂ a₃ a₄ a₅ a₆ a₇) fun st₅ ⟨cs₅, rd₅, wr₅, f₅, o₁, o₂, o₃⟩ => ?_
  -- The values the call read.
  have hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    keep_sch hp M₄.frame
  have hH : blockAt st₄.mem (K s + 240) = hk s := keep_h hp M₄.frame
  have hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (sq s q) (n s - q) := by rw [m₄]; exact hb₃
  rw [hK, M₄.ctr, hD₄] at o₁
  rw [M₄.ctr] at o₂
  rw [hH, M₄.y] at o₃
  -- What the call wrote is apart from the first `q` blocks and the return address.
  have ds : Region.Sub ⟨dq s q, (n s - q) * 16⟩ (dR s) := Offset.sub_base _ (by omega)
  have keep : ∀ {r : Region}, r.Disjoint (cR s) → r.Disjoint (yR s) → r.Disjoint ⟨dq s q, (n s - q) * 16⟩ →
      r.Disjoint (sR s) → r.Disjoint (tR s) → ∀ r' ∈ [cR s, yR s, ⟨dq s q, (n s - q) * 16⟩, sR s, tR s],
        r.Disjoint r' := by
    intro r a b c d e r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  have pq : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega)
  have hfirst : blocksAt st₅.mem (Dst s) q = ct s q := by
    rw [← M₄.data]
    exact blocksAt_frame f₅ (keep (hp.c_d.symm.sub_left pq) (hp.y_d.symm.sub_left pq)
      (Offset.base_disjoint (Dst s) (k := 16 * q) (e := 16 * q) (Nat.le_refl _) (by omega))
      (hp.d_s.sub_left pq) (hp.b_d.symm.sub_left pq)) (by omega)
  have hall : ct s (n s) = ct s q ++ ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (sq s q) (n s - q)) := by
    rw [ct, ← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Proof.Gcm.ctr32_append, Blocks.length_blocksAt,
      Nat.add_sub_cancel' hq]
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) (keep hp.t_c hp.t_y (hp.t_d.sub_right ds) hp.t_s
      (Offset.base_disjoint_below (SP s) (by omega))) (by decide), keep_r hp M₄.frame]
  · show blocksAt st₅.mem (Dst s) (n s) = ct s (n s)
    rw [← Nat.add_sub_cancel' hq, Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]
    rw [hfirst]; exact (congrArg (ct s q ++ ·) o₁).trans hall.symm
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [o₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (ct s (n s))
    rw [o₃, o₁, ← Proof.Gcm.ghashFrom_append, hall]
    rfl

end

end VG.Proof.AesGcm.X86_64.BlocksTo
