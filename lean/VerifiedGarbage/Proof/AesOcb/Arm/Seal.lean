import VerifiedGarbage.Proof.AesOcb.Arm.Front

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. `seal` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W`
(`tag`); then the copy of the tag to `tag`, whose address is on the stack
(`tagOut_ok`), and `restore` (`seal_wp`), as on AArch64
(`Proof.AesOcb.AArch64.seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame length_bytesAt)
open VG.Proof.AesGcm.Arm (below SavedAt restore_ok copyLoop_ok covers_left covers_prefix covers_of_mem)

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem (State.addr p.T) (bytesAt s.mem (State.addr p.W) p.tl) ∧
      Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  have a₁₆ := E.perm.argR' L (k := 16) (by decide)
  have a₂₀ := E.perm.argR' L (k := 20) (by decide)
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₆, a₂₀, A.a16, A.a20], ?_⟩)
  refine WP.mono (copyLoop_ok _ (S := p.W) (D := p.T) (n := p.tl)
    ⟨by simp [gpr_setReg, E.r11], by simp [gpr_setReg, E.sp, A.a16], by simp [gpr_setReg, E.sp, A.a20], L.tl1,
      by omega, by omega, L.tw, by simp only [rd_setReg, wr_setReg]; exact covers_left (covers_prefix E.perm.w (by omega)),
      by simp only [wr_setReg]; exact hTw, (L.t_w.sub_right (Region.sub_prefix (by omega))).symm⟩)
    fun t ⟨m, O⟩ => ⟨by rw [m]; rfl, E.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl)
      (by rw [O.wr]; rfl), by rw [O.rd]; rfl, by rw [O.wr]; rfl⟩
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    (rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg])

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (q : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m q t = (Spec.Ocb.toBytes (blockAtMem m q)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {p : Prm} (L : Lay p) {d : Nat} (hd : d + 16 ≤ 128 ∨ (164 ≤ d ∧ d + 16 ≤ 2560)) {m m' : Mem}
    (h : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] m m') :
    Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L hd
  · exact w_mut L (.inr ⟨by decide, by decide⟩)
  · exact below_mut L

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s₀.wr) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (ciphOf p s₀.mem) (lstarOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
        (aadOf p s₀.mem) (bytesAt s₀.mem (State.addr p.D) p.n) =
        (bytesAt s'.mem (State.addr p.D) p.n, bytesAt s'.mem (State.addr p.T) p.tl) := by
  unfold «seal» front
  refine WP.seq (WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (pre_wp' L P A hsp h0 h1 h2 h3 hW))
    fun s₃ P₃ => ?_))))
  refine WP.seq (WP.mono (bodySeal_ok L P₃.env P₃.args P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar]))
    fun s₄ B => ?_)
  have F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut L B.frame
  refine WP.mono (tag_ok L B.env (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut L (.inl (by decide)) T₅.frame
  refine WP.seq (WP.mono (tagOut_ok L T₅.env ((P₃.args.mut L F₄).mut L F₅)
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw)) fun s₆ ⟨m₆, E₆, rd₆, wr₆⟩ => ?_)
  have hx : (bytesAt s₅.mem (State.addr p.W) p.tl).length = p.tl := length_bytesAt _ _ _
  have f₆ : Frame [⟨State.addr p.T, p.tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)
  have sv₆ : SavedAt s₆.mem p.W s₀ :=
    ((P₃.saved.frame F₄ (saved_mut L)).frame F₅ (saved_mut L)).frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (by decide)).symm
  refine WP.mono (restore_ok E₆.r11 L.ww (covers_left E₆.perm.w) sv₆ (by rw [E₆.sp, hsp]))
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  have c₄ : ciphOf p s₄.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_mut L F₄, P₃.sched]
  have c₃ : ciphOf p s₃.mem = ciphOf p s₀.mem := by simp only [ciphOf, P₃.sched]
  have hout := B.out
  rw [c₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have d₆ : bytesAt s'.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [hm, Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.n_lt; omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by have := L.n_lt; omega)
  have tv := T₅.val
  rw [show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at tv
  have t₆ : bytesAt s'.mem (State.addr p.T) p.tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem (State.addr p.W))).take p.tl := by
    rw [hm, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hx]) (by have := L.tl16; omega), hx,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ L.tl16]
  rw [Proof.Ocb.encryptWith_eq, d₆, hout, t₆, tv, hck, hofs, ld₄, sum₄, c₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  seal_wp' (lay_of h.2.2.1) (sealPerm h) (args_of s) rfl rfl (ofNat_toNat32' _).symm rfl (ofNat_toNat32' _).symm rfl
    (covers_of_mem (by rw [h.2.1]; simp [prmOf]))

end VG.Proof.AesOcb.Arm
