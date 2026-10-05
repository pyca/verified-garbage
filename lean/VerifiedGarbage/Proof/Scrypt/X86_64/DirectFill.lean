import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMixDirect

/-! Direct V-table filling, keeping the intermediate X in V[i]. -/
namespace VG.Proof.Scrypt.X86_64.RoMix.DirectFill
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.X86_64.RoMix
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_movm wp_add wp_addi wp_subi wp_cmpi)
open VG.Proof.Sha256.Stream (writeBytes)

/-- X after iteration i lives in V[i], except the final X which lives in b. -/
def loc (s₀ : State) (i : Nat) : Addr := if i = NN s₀ then bP s₀ else vAt s₀ i

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ NN s₀
  regs : KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (loc s₀ i) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

theorem loc_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) :
    InRegions s₀.wr (loc s₀ i) (128 * rr s₀) := by
  unfold loc; split
  · exact b_in hp
  · exact vAt_in hp (by omega)

theorem loc_nw {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) :
    (loc s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  unfold loc; split
  · have := hp.b_nw; omega
  · exact vAt_nw hp (by omega)

theorem loc_sc {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) :
    Region.Disjoint ⟨loc s₀ i, 128 * rr s₀⟩ (scR s₀) := by
  unfold loc; split
  · exact hp.b_s.sub_left b_sub'
  · exact vAt_s hp (by omega)

theorem loc_stk {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) :
    Region.Disjoint ⟨loc s₀ i, 128 * rr s₀⟩ (stkR s₀) := by
  unfold loc; split
  · exact hp.stk_b.symm.sub_left b_sub'
  · exact vAt_stk hp (by omega)

theorem v_loc_disj {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i ≤ NN s₀) (hk : k < i) :
    Region.Disjoint ⟨vAt s₀ k, 128 * rr s₀⟩ ⟨loc s₀ i, 128 * rr s₀⟩ := by
  unfold loc; split
  · exact (vAt_b hp (by omega)).sub_right b_sub'
  · exact vAt_disj hp (by omega) (by omega) (by omega)

theorem loc_frame {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) {m m' : Mem}
    (hf : Frame [⟨loc s₀ i, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] m m' := by
  refine hf.sub fun R hR => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · unfold loc; split
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨vR s₀, by simp, vAt_sub hp (by omega)⟩
  · exact ⟨scR s₀, by simp, w_sub⟩
  · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem loc_kept {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ NN s₀) {m m' : Mem}
    (hf : Frame [⟨loc s₀ i, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') (h : Kept s₀ m) :
    Kept s₀ m' := by
  refine h.frame hf fun R hR => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · unfold loc; split
    · exact (keep_b hp).sub_right b_sub'
    · exact (keep_v hp).sub_right (vAt_sub hp (by omega))
  · exact keep_w
  · exact keep_stk hp

theorem complete {s₀ s : State} (h : Inv s₀ (NN s₀) s) : Inv2 s₀ (NN s₀) s :=
  ⟨h.le, h.regs.rd, h.regs.wr, h.regs.rsp, h.regs.rbx, h.regs.rbp, h.regs.r12,
    h.regs.r13, h.regs.r14, h.regs.r15, h.frame, h.kept, by simpa only [loc, ite_true] using h.x, h.done⟩


theorem init_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ 0 s) :
    WP isa fillInit s (Inv s₀ 0) := by
  have hi := NN_pos hp
  have lt := r_lt hp
  have vlt := v_lt hp
  have pos := hp.pos
  have n1 := NN_pos hp
  have hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold fillInit
  refine WP.seq (wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → e.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ue.other _ h3, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : e.rd = s₀.rd := by rw [ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : e.wr = s₀.wr := by rw [ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have hme : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have ecx : e.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀) := by
    rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega
  have e8 : 16 * (8 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ 0) (n := 8 * rr s₀) (by omega)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.gpr, h.rbx])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp])
    ecx (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_
  rw [hme, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h4, ke r h2 h3 h4]
  have kr := h.kr.keep (by rw [rdt, erd, h.rd]) (by rw [wrt, ewr, h.wr]) kt
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := Memory.bytesAt_length _ _ _
  have f : Frame [⟨vAt s₀ 0, 128 * rr s₀⟩] s.mem t.mem := by
    rw [mt]
    exact Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨by omega, kr, h.frame.trans (f.sub ?_), h.kept.frame f ?_, ?_, fun k hk => by omega⟩
  · intro R hR
    simp only [List.mem_singleton] at hR; subst hR
    exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  · intro R hR
    simp only [List.mem_singleton] at hR; subst hR
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · have self := Memory.bytesAt_writeBytes_self s.mem (vAt s₀ 0)
      (bytesAt s.mem (bP s₀) (128 * rr s₀)) (by rw [hl]; exact lt)
    rw [hl] at self
    rw [loc, ite_eq_right (by omega), mt, self, h.x]

structure Ready (s₀ : State) (i : Nat) (s : State) : Prop where
  regs : KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s
  rdi : s.gpr .rdi = vAt s₀ i
  rsi : s.gpr .rsi = BitVec.ofNat 64 (rr s₀)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = loc s₀ (i + 1)
  r8 : s.gpr .r8 = sc s₀

theorem n_lt {s₀ : State} (hp : Pre s₀) : NN s₀ < 2 ^ 64 := by
  have h := v_lt hp
  have pos := hp.pos
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem args_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State}
    (h : KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s) :
    WP isa (.seq (.block fillArgs) fillSelect) s fun t => Ready s₀ i t ∧ t.mem = s.mem := by
  unfold fillArgs
  refine WP.seq (wp_mov fun a ua _ _ => wp_mov fun b ub _ _ =>
    wp_shr (by decide) (by decide) fun c uc _ => wp_mov fun d ud _ _ =>
    wp_mov fun e ue _ _ => wp_add fun f uf => wp_mov fun g ug _ _ =>
    wp_cmpi fun t gt mt rdt wrt _ zt => WP.block_nil ?_)
  have kg : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → t.gpr r = s.gpr r :=
    fun r hdi hsi hcx hdx h8 => by
      rw [gt, ug.other _ h8, uf.other _ hdx, ue.other _ hdx, ud.other _ hcx,
        uc.other _ hsi, ub.other _ hsi, ua.other _ hdi]
  have kr : KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) t :=
    h.upd (by rw [rdt, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd])
      (by rw [wrt, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr])
      (fun r _ hdi hsi hcx hdx h8 => kg r hdi hsi hcx hdx h8)
  have mm : t.mem = s.mem := by rw [mt, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  have di : t.gpr .rdi = vAt s₀ i := by
    simp (disch := decide) only [gt, ug.other, uf.other, ue.other, ud.other, uc.other, ub.other,
      ua.gpr, h.rbp]
  have si : c.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [uc.gpr, ub.gpr, ua.other _ (by decide), h.r14, shr_ofNat _ (r_lt hp)]
    exact congrArg (BitVec.ofNat _) (by omega)
  have tsi : t.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    simp (disch := decide) only [gt, ug.other, uf.other, ue.other, ud.other, si]
  have cx : t.gpr .rcx = BitVec.ofNat 64 (rr s₀) := by
    simp (disch := decide) only [gt, ug.other, uf.other, ue.other, ud.gpr, si]
  have dx : t.gpr .rdx = vAt s₀ (i + 1) := by
    simp (disch := decide) only [gt, ug.other, uf.gpr, ue.gpr, ue.other, ud.other,
      uc.other, ub.other, ua.other, h.rbp, h.r14]
    exact vAt_succ s₀ i
  have r8 : t.gpr .r8 = sc s₀ := by
    simp (disch := decide) only [gt, ug.gpr, uf.other, ue.other, ud.other, uc.other, ub.other,
      ua.other, h.r13]
  have zz : t.zf = some (decide (i + 1 = NN s₀)) := by
    rw [zt, ← congrFun gt .r15, kr.r15, dec_zf hi (n_lt hp)]
  unfold fillSelect
  refine WP.ite (decide (i + 1 = NN s₀)) (by simp only [eval, zz]) ?_ ?_
  · intro hb
    have hl := of_decide_eq_true hb
    refine wp_mov fun u uu _ _ => WP.block_nil ⟨?_, uu.mem.trans mm⟩
    refine ⟨kr.upd uu.rd uu.wr (fun r _ _ _ _ hd _ => uu.other r hd), ?_, ?_, ?_, ?_, ?_⟩
    · rw [uu.other _ (by decide), di]
    · rw [uu.other _ (by decide), tsi]
    · rw [uu.other _ (by decide), cx]
    · rw [uu.gpr, kr.rbx, loc, ite_eq_left hl]
    · rw [uu.other _ (by decide), r8]
  · intro hb
    have hl := of_decide_eq_false hb
    exact WP.block_nil ⟨⟨kr, di, tsi, cx, by rw [loc, ite_eq_right hl]; exact dx, r8⟩, mm⟩


theorem step_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv s₀ i s) :
    WP isa (fillStep c) s fun s' => Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  unfold fillStep
  refine WP.seq (WP.mono (args_ok hp hi h.regs) fun t ⟨a, mt⟩ => ?_)
  refine WP.seq (hS t (vAt s₀ i) (loc s₀ (i + 1)) (sc s₀) (rr s₀)
    a.rdi a.rsi a.rdx a.rcx a.r8 hp.pos (r_lt hp)
    ((loc_sc hp (by omega)).sub_right w_sub) (v_loc_disj hp (by omega) (by omega))
    ((vAt_s hp hi).sub_right w_sub)
    (by rw [a.regs.rsp]; exact (vAt_stk hp hi).symm)
    (by rw [a.regs.rsp]; exact (loc_stk hp (by omega)).symm)
    (by rw [a.regs.rsp]; exact hp.stk_s.sub_right w_sub)
    (vAt_nw hp hi) (loc_nw hp (by omega)) (by have := hp.s_nw; omega)
    (by rw [a.regs.rd, a.regs.wr]; exact Memory.InRegions.right (vAt_in hp hi))
    (by rw [a.regs.wr]; exact loc_in hp (by omega))
    (by rw [a.regs.wr]; exact w_in hp) _ fun u rd wr cs f x => ?_)
  rw [a.regs.rsp, mt] at f
  rw [mt] at x
  have xi : bytesAt s.mem (vAt s₀ i) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    simpa only [loc, ite_eq_right (show i ≠ NN s₀ by omega)] using h.x
  have xn : bytesAt u.mem (loc s₀ (i + 1)) (128 * rr s₀) =
      Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) := by rw [x, xi]; rfl
  have dn : ∀ k < i + 1, bytesAt u.mem (vAt s₀ k) (128 * rr s₀) =
      Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
    intro k hk
    have eq : bytesAt u.mem (vAt s₀ k) (128 * rr s₀) = bytesAt s.mem (vAt s₀ k) (128 * rr s₀) := by
      refine frame_bytesAt' f (fun R hR => ?_) (by have := r_lt hp; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl
      · exact v_loc_disj hp (by omega) hk
      · exact (vAt_s hp (by omega)).sub_right w_sub
      · exact vAt_stk hp (by omega)
    rw [eq]
    by_cases e : k = i
    · subst k; exact xi
    · exact h.done k (by omega)
  have ku := a.regs.keep rd wr cs
  refine wp_add fun v uv => wp_subi fun w uw zw => WP.block_nil ?_
  have kw : ∀ r, r ≠ .rbp → r ≠ .r15 → w.gpr r = u.gpr r := fun r hb hq => by
    rw [uw.other _ hq, uv.other _ hb]
  have e15 : v.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by rw [uv.other _ (by decide), ku.r15]
  refine ⟨⟨by omega, ⟨by rw [uw.rd, uv.rd, ku.rd], by rw [uw.wr, uv.wr, ku.wr],
    by rw [kw _ (by decide) (by decide), ku.rsp], by rw [kw _ (by decide) (by decide), ku.rbx],
    ?_, by rw [kw _ (by decide) (by decide), ku.r12],
    by rw [kw _ (by decide) (by decide), ku.r13], by rw [kw _ (by decide) (by decide), ku.r14],
    by rw [uw.gpr, e15, dec_count hi]⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [uw.other _ (by decide), uv.gpr, ku.rbp, ku.r14, vAt_succ]
  · rw [uw.mem, uv.mem]; exact h.frame.trans (loc_frame hp (by omega) f)
  · rw [uw.mem, uv.mem]; exact loc_kept hp (by omega) f h.kept
  · rw [uw.mem, uv.mem]; exact xn
  · rw [uw.mem, uv.mem]; exact dn
  · rw [zw, e15, dec_zf hi (n_lt hp)]

theorem fill_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (fillWith c) s (Inv2 s₀ (NN s₀)) := by
  refine WP.seq (WP.mono (init_ok hp h) fun t ht => ?_)
  exact WP.mono (count_loop (NN_pos hp) (Inv s₀) (fun _ hi _ h => step_ok hS hp hi h) ht)
    fun _ h => complete h


theorem call_pre {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State}
    (ha : Ready s₀ i s) :
    Proof.Scrypt.blockMixX86_64.pre (s.callEntry.withRegions [⟨vAt s₀ i, 128 * rr s₀⟩]
      [⟨loc s₀ (i + 1), 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨vAt s₀ i, 128 * rr s₀⟩] ++ [⟨loc s₀ (i + 1), 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨loc s₀ (i + 1), 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  exact bm_pre ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((loc_sc hp (by omega)).sub_right w_sub) (v_loc_disj hp (by omega) (by omega)) ((vAt_s hp hi).sub_right w_sub)
    (by rw [ha.regs.rsp]; exact (vAt_stk hp hi).symm) (by rw [ha.regs.rsp]; exact (loc_stk hp (by omega)).symm)
    (by rw [ha.regs.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) (vAt_nw hp hi) (loc_nw hp (by omega))
    (by have := hp.s_nw; omega) (by rw [ha.regs.rd, ha.regs.wr]; exact Memory.InRegions.right (vAt_in hp hi)) (by rw [ha.regs.wr]; exact loc_in hp (by omega))
    (by rw [ha.regs.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State}
    (ha : Ready s₀ i s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMixFused) s (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i))) := by
  have lt := r_lt hp
  exact blockMixSpec s (vAt s₀ i) (loc s₀ (i + 1)) (sc s₀) (rr s₀) ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((loc_sc hp (by omega)).sub_right w_sub) (v_loc_disj hp (by omega) (by omega)) ((vAt_s hp hi).sub_right w_sub)
    (by rw [ha.regs.rsp]; exact (vAt_stk hp hi).symm) (by rw [ha.regs.rsp]; exact (loc_stk hp (by omega)).symm)
    (by rw [ha.regs.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) (vAt_nw hp hi) (loc_nw hp (by omega))
    (by have := hp.s_nw; omega) (by rw [ha.regs.rd, ha.regs.wr]; exact Memory.InRegions.right (vAt_in hp hi)) (by rw [ha.regs.wr]; exact loc_in hp (by omega))
    (by rw [ha.regs.wr]; exact w_in hp) _ fun _ rd wr cs _ _ => ha.regs.keep rd wr cs

theorem loc_eq {s₀ s₀' : State} (hq : PubEq s₀ s₀') (i : Nat) : loc s₀ i = loc s₀' i := by
  unfold loc
  rw [hq.NN, hq.vAt i, show bP s₀ = bP s₀' from hq.rdi]

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
    {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Ready s₀ i s ∧ Ready s₀' i s')
      (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMixFused)
      fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev := (hq.vAt i).symm
  have ed := (loc_eq hq (i + 1)).symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have er := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' => Ready s₀ i s ∧ Ready s₀' i s')
    BlockMix.Fused.blockMix_correct BlockMix.Fused.blockMix_ct [⟨vAt s₀ i, 128 * rr s₀⟩]
    [⟨loc s₀ (i + 1), 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨ha, ha'⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hi ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hi' ha'
      simp only [ev, ed, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [ha.regs.rsp, ha'.regs.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8,
        ha'.rdi, ha'.rsi, ha'.rdx, ha'.rcx, ha'.r8, ev, ed, es, er, ha.regs.rsp, ha'.regs.rsp, hq.rsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun _ _ h => ⟨call_wp hp hi h.1, call_wp hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv s₀ i s ∧ Inv s₀' i s') (fillStep Impl.Scrypt.X86_64.blockMixFused)
      fun s s' => (Inv s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  have a : RelCT isa (fun s s' => Inv s₀ i s ∧ Inv s₀' i s')
      (.seq (.block fillArgs) fillSelect) (fun s s' => Ready s₀ i s ∧ Ready s₀' i s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.regs h.2.regs ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨WP.mono (args_ok hp hi h.1.regs) (fun _ h => h.1),
        WP.mono (args_ok hp' hi' h.2.regs) (fun _ h => h.1)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have e : RelCT isa (fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s')
      (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := a.seq ((call_rel hp hp' hq hi).seq e)
  exact (body.wp fun _ _ h => ⟨step_ok blockMixSpec hp hi h.1, step_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop (fillStep Impl.Scrypt.X86_64.blockMixFused) .ne)
      fun s s' => Inv s₀ (NN s₀) s ∧ Inv s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := fillStep Impl.Scrypt.X86_64.blockMixFused) (c := .ne)
    (Q := fun s s' => Inv s₀ (NN s₀) s ∧ Inv s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv s₀ i s ∧ Inv s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem fill_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s') (fillWith Impl.Scrypt.X86_64.blockMixFused)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have a : RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s') fillInit
      (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr (hq.vAt 0) (by rw [hq.NN]) (by simp))
      (by taint_decide)).wp fun _ _ h => ⟨init_ok hp h.1, init_ok hp' h.2⟩).mono
        (fun _ _ h => h) fun _ _ h => h.2
  exact (a.seq (loop_rel hp hp' hq)).mono (fun _ _ h => h) fun _ _ h => ⟨complete h.1, complete h.2⟩

end

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixDirectWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.roMixX86_64.post s₀ s' := by
  unfold roMixDirectWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine start_ok hp h₁ fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (fill_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₄) fun s₅ h₅ => ?_)
  refine WP.mono (restore_ok hp h₅) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₅.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_b
    · exact hp.ret_v
    · exact hp.ret_s
    · exact ret_stk s₀
  · show bytesAt s'.mem (bP s₀) (128 * rr s₀) = Spec.Scrypt.roMix (rr s₀) (NN s₀) (B s₀)
    rw [hm', ← h₅.x, Nat.sub_self]
    rfl

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hp hp' hq hL

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86_64.roMixDirect fun _ _ => True := by
  show RelCT isa _ (roMixDirectWith Impl.Scrypt.X86_64.blockMixFused) _
  unfold roMixDirectWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rdx, .rcx])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rax, h'.rax, hq.rr]
        · rw [h.rdx, h'.rdx]
        · rw [h.rcx, h'.rcx, RoMix.vl, RoMix.vl, hq.rcx]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdx, .r12, .r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rdx, h'.rdx, hq.NN]
        · rw [h.r12, h'.r12, vP, vP, hq.rdx]
        · rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((fill_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end
theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.roMixDirect s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct blockMixSpec (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixX86_64.pre Proof.Scrypt.roMixX86_64.pub
    Impl.Scrypt.X86_64.roMixDirect := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.roMixDirect (Spec.Scrypt.roMixContract X86_64.abi 16) :=
  Verified.of_correct roMix_correct roMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.RoMix.satState]
          [Proof.Scrypt.X86_64.RoMix.satState] using Proof.Scrypt.X86_64.RoMix.satState }

end VG.Proof.Scrypt.X86_64.RoMix.DirectFill
