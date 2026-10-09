import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeLoop
import VerifiedGarbage.Proof.Ed448.X86.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed448.X86.BaseMain

/-!
# Ed448 verification's equation on x86 (32-bit): the whole function

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16])` returns `verifyEquation` of
its inputs (`verifyEquation_main`), given the reference computations'
agreement with the specification (`RecoverOk`, `VerifyEqOk`): the entry (the
registers saved, the bits of `S` and `k`, the check of `S`, the slots), `R`
and `A` decoded by one loop, `A` negated, `Q = [S]B + [k](-A)` by the loop,
`R` copied back, and the comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
arguments and the inputs are read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk vladder negPoint double verifyEquation_none pt evalOps)
open VG.Impl.X448.X86 (slot X2 BITS ACC TMP at_ ops)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The precondition and the arguments -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
  wr : s.wr = [scR (arg s 3)]
  pk_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  sig_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 3))
  ch_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  args_sc : (⟨argAddr s 0, 16⟩ : Region).Disjoint (scR (arg s 3))
  ret_sc : (retR s).Disjoint (scR (arg s 3))
  f0 : (arg s 0).toNat + 57 ≤ 2 ^ 32
  f1 : (arg s 1).toNat + 114 ≤ 2 ^ 32
  f2 : (arg s 2).toNat + 57 ≤ 2 ^ 32
  f3 : (arg s 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_pk : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sig : (stkR s).Disjoint ⟨(arg s 1).setWidth 64, 114⟩
  stk_ch : (stkR s).Disjoint ⟨(arg s 2).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 3))

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem VerifyPre.stk_args {s : State} (h : VerifyPre s) : (stkR s).Disjoint ⟨argAddr s 0, 16⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem VerifyPre.stk_ret {s : State} (h : VerifyPre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem VerifyPre.args {s : State} (h : VerifyPre s) : Args s 4 3 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.f3,
    h.args_sc, h.ret_sc⟩

/-- An argument's address, readable, and its value, in a later state. -/
theorem Args.argRead {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_same hm.frame hi⟩

/-- `argRead`, with the memory changed only in regions apart from the arguments. -/
theorem Args.argReadF {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r) {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_frame hf hd hi⟩

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

theorem bits_kept {base : Addr} {m m' : Mem} (h : WsOut2 base 16 2864 ACC 512 m m') :
    ∀ t < 456, m' (off base (BITS + t)) = m (off base (BITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)

theorem bits_keptD {base : Addr} {m m' : Mem} (h : DFrame base m m') :
    ∀ t < 456, m' (off base (BITS + t)) = m (off base (BITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)

/-- The checks of the decodings, in the order the result uses. -/
theorem decShape {S R A : Prop} : (S ∧ ((0 ≤ 1 → R) ∧ (0 = 0 → A))) ↔ ((S ∧ A) ∧ R) :=
  ⟨fun ⟨hs, hr, ha⟩ => ⟨⟨hs, ha rfl⟩, hr (by decide)⟩, fun ⟨⟨hs, ha⟩, hr⟩ => ⟨hs, fun _ => hr, fun _ => ha⟩⟩

/-! ## The entry -/

theorem ventry_ok {s₀ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base) :
    WP isa (.block ventry) s₀ fun t =>
      Scr t base ∧ Saved base s₀.gpr t.mem ∧ Outside base 0 8192 s₀.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ t ∧
      BadUpd (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L)
        0 (word t.mem base BAD) ∧
      (∀ j < 456, t.mem (off base (BITS + j)) = BitVec.ofNat 8
        (pair2 (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57))
          (decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)) j)) ∧
      BoundedEnv t.mem base ∧ (∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val)) := by
  have hA := h.args
  have isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  have ich : Input s₀ base (arg s₀ 2) 57 := Input.of_region h.f2 (by rw [h.rd]; simp) (hbase ▸ h.ch_sc)
  unfold ventry
  simp only [List.append_assoc]
  -- The registers saved.
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_
  rw [hbase] at hs₁ sv₁ o₁
  have o1w : Outside base 0 8192 s₀.mem s₁.mem := o₁.mono (by omega) (by omega)
  -- The bits.
  obtain ⟨e8, r8, v8⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 1) (by decide)
  obtain ⟨e12, r12, v12⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 2) (by decide)
  have rr1 : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.1, k₁.2.2]
  rw [WP.block_append_iff]
  refine WP.mono (vbits_ok hs₁ e8 r8 e12 r12 v8 v12 h.f1 h.f2
    (fun i hi => by rw [rr1, Offset.add_add]; exact isig.read _ (by omega))
    (fun i hi => by rw [rr1]; exact ich.read i hi)
    (fun i hi => by rw [Offset.add_add]; exact isig.far _ (by omega)) ich.far)
    fun s₂ ⟨esi₂, k₂, o₂, b₂⟩ => ?_
  have bs : bytesAt s₁.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o1w _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega)
  rw [bs, ich.bytes o1w] at b₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  -- `BAD = 0`.
  refine wp_mov rfl fun s₃ v₃ => store_ok (hs₂.of_upd v₃ (by decide)) (by decide) fun s₄ v₄ => ?_
  have hs₄ := (hs₂.of_upd v₃ (by decide)).of_keeps (v₄.rest []) (by decide)
  have bad₄ : word s₄.mem base BAD = 0 := by
    rw [v₄.mem, v₃.gpr]; exact Mem.readW_writeW_self32 _ _ _
  have o₄ : Outside base BAD 4 s₂.mem s₄.mem := by
    rw [v₄.mem, v₃.mem]; exact writeW_outside _ _ _ (by decide)
  -- The check of `S`.
  have esi₄ : s₄.gpr .esi = arg s₀ 1 := by rw [v₄.gpr, v₃.other _ (by decide), esi₂]
  have rr4 : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, k₂.2.1, k₂.2.2, rr1]
  have o04 : Outside base 0 8192 s₀.mem s₄.mem :=
    (o1w.trans (o₂.mono (by omega) (by simp only [BITS]; omega))).trans (o₄.mono (by omega) (by decide))
  change WP isa (.block (sCheck ++ initSlots)) s₄ _
  rw [WP.block_append_iff]
  refine WP.mono (sCheck_ok hs₄ (q := (arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) (by rw [esi₄])
    (by rw [esi₄]; exact h.f1) (fun j hj => by rw [rr4, Offset.add_add]; exact isig.read _ (by omega))
    (fun j hj => by rw [Offset.add_add]; exact isig.far _ (by omega))) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have bS : bytesAt s₄.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o04 _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega)
  rw [bS, bad₄] at c₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  -- The slots.
  refine WP.mono (initSlots_ok hs₅) fun t ⟨lt, ot, kt⟩ => ?_
  have e : ∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val) := initSlots_E lt
  refine ⟨hs₅.of_keeps kt (by decide), ?_, ?_, ?_, ?_, fun j hj => ?_, initSlots_bounded lt, e⟩
  · exact (((sv₁.outside o₂ (by decide)).outside o₄ (by decide)).outside2 o₅ (by decide)
      (by decide)).outside ot (by decide)
  · exact (o04.trans (o₅.whole (by decide) (by decide))).trans (ot.mono (by omega) (by omega))
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((v₃.rest (by decide)).trans
      ((v₄.rest _).trans ((k₅.mono (by decide)).trans (kt.mono (by decide))))))
  · refine c₅.of_eq ?_
    exact ot.word (Or.inl (by decide)) (by decide)
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)),
      o₅ _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, TMP]; omega)
        (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, BAD]; omega),
      o₄ _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, BAD]; omega)]
    exact b₂ j hj

/-- The arguments, in any state after the entry block whose writes since are in the working
space and the stack below the return address. -/
theorem ventry_args {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (o₁ : Outside base 0 8192 s₀.mem s₁.mem) {rs : List Reg} (k₁ : Keeps rs s₀ s₁) (hesp : .esp ∉ rs) :
    ∀ i < 2, ArgAt s₁ base (4 + 4 * i) (arg s₀ i) := fun i hi t h1 h2 h3 h4 => by
  have sp₁ := k₁.1 .esp hesp
  have st : callStk s₁ = stkR s₀ := by
    simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  change Frame [⟨base, 8192⟩, callStk s₁] _ _ at h4
  rw [st] at h4
  obtain ⟨ae, ar, av⟩ := h.args.argReadF (h1.trans sp₁) (h2.trans k₁.2.1) (h3.trans k₁.2.2)
    (((Outside.frame o₁).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans h4)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [← hbase]; exact h.args_sc
      · exact h.stk_args.symm) (i := i) (by omega)
  exact ⟨_, ae, ar, av⟩

/-- The calls' context after the entry block. -/
theorem ventry_ctx {s₀ s₁ : State} (h : VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hsp : s₁.gpr .esp = s₀.gpr .esp) : CallCtx s₁ base :=
  ⟨by rw [hsp]; exact h.sp_room, by
    simp only [callStk, hsp]; rw [← stkR_below h.sp_room, ← hbase]; exact h.stk_sc.symm⟩

/-- What the decoding loop needs of the state `s` after the entry, with the arguments of
`s₀`. -/
structure LoopPre (s₀ s : State) : Prop where
  scr : Scr s ((arg s₀ 3).setWidth 64)
  ctx : CallCtx s ((arg s₀ 3).setWidth 64)
  wr : s.wr = [⟨(arg s₀ 3).setWidth 64, 8192⟩]
  bounded : BoundedEnv s.mem ((arg s₀ 3).setWidth 64)
  sig : ArgAt s ((arg s₀ 3).setWidth 64) 8 (arg s₀ 1)
  pk : ArgAt s ((arg s₀ 3).setWidth 64) 4 (arg s₀ 0)
  isig : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 1) 57
  ipk : Input s ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57
  dsig : (⟨(arg s₀ 1).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  dpk : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region).Disjoint (callStk s)
  e10 : E s.mem ((arg s₀ 3).setWidth 64) 10 = 1
  e11 : E s.mem ((arg s₀ 3).setWidth 64) 11 = Spec.Ed448.d

theorem ventry_loopPre {s₀ : State} (h : VerifyPre s₀) : WP isa (.block ventry) s₀ (LoopPre s₀) := by
  have hA := h.args
  have ipk : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 0) 57 :=
    Input.of_region h.f0 (by rw [h.rd]; simp) h.pk_sc
  have isig : Input s₀ ((arg s₀ 3).setWidth 64) (arg s₀ 1) 114 :=
    Input.of_region h.f1 (by rw [h.rd]; simp) h.sig_sc
  refine WP.mono (ventry_ok h rfl) fun s₁ ⟨hs₁, _, o₁, k₁, _, _, b₁, e₁⟩ => ?_
  obtain ⟨_, eq, ed⟩ := initE _ e₁
  have hArg := ventry_args h rfl o₁ k₁ (by decide)
  have st : callStk s₁ = stkR s₀ := by
    simp only [callStk, k₁.1 .esp (by decide)]; rw [stkR_below h.sp_room]
  exact ⟨hs₁, ventry_ctx h rfl (k₁.1 .esp (by decide)), k₁.2.2.trans h.wr, b₁, hArg 1 (by decide),
    hArg 0 (by decide), (isig.take57 (by decide)).of_keeps k₁, ipk.of_keeps k₁,
    by rw [st]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm,
    by rw [st]; exact h.stk_pk.symm, congrArg Spec.Ed448.Point.Z eq, ed⟩

/-! ## The whole function -/

theorem sub6_E (e : Env) : evalOps [.sub 6 0 6] e 6 = e 0 - e 6 ∧ ∀ i : Index, i ≠ 6 → evalOps [.sub 6 0 6] e i = e i :=
  ⟨rfl, fun _ hi => Function.update_of_ne hi _ _⟩

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s₀ : State} (h : VerifyPre s₀) :
    WP isa verifyEquation s₀ fun t => abiPreserved s₀ t ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0 := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  have ipk : Input s₀ base (arg s₀ 0) 57 := Input.of_region h.f0 (by rw [h.rd]; simp) (hbase ▸ h.pk_sc)
  have isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok h hbase) fun s₁ ⟨hs₁, sv₁, o₁, k₁, c₁, bits₁, b₁, e₁⟩ => ?_)
  rw [hS] at c₁ bits₁
  rw [hK] at bits₁
  obtain ⟨er, eq, ed⟩ := initE _ e₁
  have h10 : E s₁.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z eq
  have sp₁ : s₁.gpr .esp = s₀.gpr .esp := k₁.1 .esp (by decide)
  have hc₁ : CallCtx s₁ base := ventry_ctx h hbase sp₁
  have hw₁ : s₁.wr = [⟨base, 8192⟩] := by rw [k₁.2.2, h.wr, ← hbase]
  have st₁ : callStk s₁ = stkR s₀ := by simp only [callStk, sp₁]; rw [stkR_below h.sp_room]
  -- The rest writes the working space and the stack below the return address.
  have retk : ∀ t : State, Frame (s₁.wr ++ [below (s₁.gpr .esp) (stackUse (.seq vdecode vafter))]) s₁.mem t.mem →
      t.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    intro t ft
    have frame : Frame (s₁.wr ++ [below (s₁.gpr .esp) 20]) s₀.mem t.mem :=
      ((Outside.frame o₁).mono fun r hr => by
        rw [List.mem_singleton.mp hr, hw₁]; exact List.mem_cons_self).trans
        (Frame.below_mono ft (by lit_decide) hc₁.sp)
    have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine frame.readW ret ?_ (by decide)
    rw [hw₁, show below (s₁.gpr .esp) 20 = stkR s₀ from st₁]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hbase ▸ h.ret_sc
    · exact h.stk_ret.symm
  refine WP.mono (WP.withFrame (NoSp.of_all (by lit_decide))
    (Nat.le_trans (by lit_decide : stackUse (.seq vdecode vafter) ≤ 20) hc₁.sp)
    (Q := fun t => (∀ r ∈ calleeSaved, t.gpr r = s₀.gpr r) ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0) ?_) fun t ⟨⟨regs, res⟩, ft⟩ => ⟨⟨regs, retk t ft⟩, res⟩
  -- `R` and `A`.
  have hArg := ventry_args h hbase o₁ k₁ (by decide)
  have isig57 : Input s₀ base (arg s₀ 1) 57 := isig.take57 (by decide)
  refine WP.seq (WP.mono (vdecode_ok hR hs₁ hc₁ hw₁ b₁ (hArg 1 (by decide)) (hArg 0 (by decide))
    (isig57.of_keeps k₁) (ipk.of_keeps k₁)
    (by rw [st₁]; exact (h.stk_sig.sub_right (Region.sub_prefix (by decide))).symm)
    (by rw [st₁]; exact h.stk_pk.symm) h10 ed) fun s₂ D₂ => ?_)
  have dR : decAt s₁.mem (arg s₀ 1) = Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) := by
    rw [bytesAt_take57]; exact congrArg Spec.Ed448.decodePoint (isig57.bytes o₁)
  have dA : decAt s₁.mem (arg s₀ 0) = Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) :=
    congrArg Spec.Ed448.decodePoint (ipk.bytes o₁)
  have c₂ := D₂.bad
  have v₂ := D₂.aIn rfl
  have vR₂ := D₂.rOut rfl
  have e₂ := D₂.other
  rw [dR, dA] at c₂
  rw [dA] at v₂
  rw [dR] at vR₂
  have hs₂ := D₂.scr hs₁
  have hc₂ : CallCtx s₂ base := hc₁.keep (D₂.keeps.1 _ (by decide))
  have b₂ := D₂.bounded
  unfold vafter
  -- `-A`.
  refine field_seq [.sub 6 0 6] (by decide) hs₂ hc₂ b₂ fun s₃ k₃ b₃ e₃ => ?_
  have hs₃ := k₃.scr hs₂
  have hc₃ := k₃.ctx hc₂
  obtain ⟨n₃, k₃e⟩ := sub6_E (E s₂.mem base)
  rw [← e₃] at n₃ k₃e
  -- `Q`'s `Y` set to 1.
  rw [show ops [Impl.X448.X86.Op.copy X2 (slot 10)] = ops (([.copy 1 10] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₃ hc₃ b₃ [.copy 1 10]) fun s₄ ⟨k₄, b₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  have hc₄ := k₄.ctx hc₃
  have e₄1 : E s₄.mem base 1 = E s₃.mem base 10 := by
    rw [e₄]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₄k : ∀ i : Index, i ≠ 1 → E s₄.mem base i = E s₃.mem base i := fun i hi => by
    rw [e₄]; exact Function.update_of_ne hi _ _
  -- What is kept from the entry to the loop.
  have k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem base i = E s₁.mem base i := fun i hi => by
    rw [e₄k i (fun h => by subst h; omega), k₃e i (fun h => by subst h; omega),
      e₂ i (fun h => by subst h; omega) (fun h => by subst h; omega) (by omega)]
  have bits₄ : ∀ t < 456, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (pair2 S K t) := fun t ht => by
    rw [bits_kept (WsOut2.widen k₄.mem) t ht, bits_kept (WsOut2.widen k₃.mem) t ht,
      bits_keptD D₂.frame t ht]
    exact bits₁ t ht
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (s₀ := s₄) (A := pt (E s₄.mem base) 6 7 10) bits₄
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s₅ I₅ => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs₄.of_keeps k' (by decide), hc₄.keep (h2 _ (by decide)), h3 ▸ b₄, k', h1,
      h3 ▸ WsOut2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self]
      show (⟨E s₄.mem base 0, E s₄.mem base 1, E s₄.mem base 2⟩ : Spec.Ed448.Point) = Spec.Ed448.identity
      rw [k41 0 (Or.inl rfl), k41 2 (Or.inr (Or.inl rfl)), e₄1, k₃e 10 (by decide),
        e₂ 10 (by decide) (by decide) (by decide), h10]
      rw [show E s₁.mem base 0 = Spec.Ed448.identity.X from congrArg Spec.Ed448.Point.X er,
        show E s₁.mem base 2 = Spec.Ed448.identity.Z from congrArg Spec.Ed448.Point.Z er]
      rfl
    · rw [h3, pt_congr' (k41 8 (by decide)) (k41 9 (by decide)) (k41 10 (by decide))]; exact eq
    · rw [h3]
    · rw [h3, k41 11 (by decide)]; exact ed
  -- `Q`'s `Y` moved to slot 6.
  have hs₅ := I₅.scr
  rw [show ops [Impl.X448.X86.Op.copy (slot 6) X2] = ops (([.copy 6 1] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₅ I₅.ctx I₅.bounded [.copy 6 1]) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have hs₆ := k₆.scr hs₅
  have e₆6 : E s₆.mem base 6 = E s₅.mem base 1 := by
    rw [e₆]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₆k : ∀ i : Index, i ≠ 6 → E s₆.mem base i = E s₅.mem base i := fun i hi => by
    rw [e₆]; exact Function.update_of_ne hi _ _
  have k06 : Keeps (.esi :: workRegs) s₁ s₆ :=
    ((D₂.keeps.trans (k₃.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (k₄.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (I₅.regs.trans (k₆.regs.mono (fun _ h => List.mem_cons_of_mem _ h)))
  -- `R` copied back.
  have h106 : E s₆.mem base 10 = 1 := by rw [e₆k 10 (by decide)]; exact congrArg Spec.Ed448.Point.Z I₅.q
  have FR : ∀ o, o = RX ∨ o = RY →
      F s₆.mem base o = F s₂.mem base o ∧ (Bounded s₂.mem base o → Bounded s₆.mem base o) := fun o ho => by
    obtain ⟨f3, g3⟩ := F_high k₃.mem (by decide) ho
    obtain ⟨f4, g4⟩ := F_high k₄.mem (by decide) ho
    obtain ⟨f5, g5⟩ := F_high I₅.mem (by decide) ho
    obtain ⟨f6, g6⟩ := F_high k₆.mem (by decide) ho
    exact ⟨f6.trans (f5.trans (f4.trans f3)), fun h => g6 (g5 (g4 (g3 h)))⟩
  obtain ⟨bRX, bRY⟩ := D₂.rBnd rfl
  refine WP.seq (WP.mono (vR_ok hs₆ b₆ ((FR RX (Or.inl rfl)).2 bRX) ((FR RY (Or.inr rfl)).2 bRY))
    fun s₇ ⟨k₇, b₇, x₇, y₇, e₇⟩ => ?_)
  have hs₇ := k₇.scr hs₆
  -- `BAD`.
  have bad₄ : word s₄.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₄, Keep.bad k₃]
  have bad₆ : word s₆.mem base BAD = word s₄.mem base BAD := by
    rw [Keep.bad k₆]; exact I₅.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)
  have bad₇ : word s₇.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₇, bad₆, bad₄]
  have z₇ := ((c₁.trans (c₂.of_eq bad₇)).congr decShape).zero
  -- The comparison.
  have sv₇ : Saved base s₀.gpr s₇.mem :=
    (((((sv₁.wsout2 D₂.frame (by decide) (by decide)).wsout2 k₃.mem (by decide) (by decide)).wsout2
      k₄.mem (by decide) (by decide)).wsout2 I₅.mem (by decide) (by decide)).wsout2 k₆.mem (by decide)
      (by decide)).wsout2 k₇.mem (by decide) (by decide)
  have hc₇ : CallCtx s₇ base := k₇.ctx (k₆.ctx I₅.ctx)
  refine WP.mono (vfinish_ok hs₇ hc₇ b₇ sv₇ z₇.2) fun t ⟨rt, st, spt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact st (.ebx, 0) (by decide)
    · exact st (.esi, 4) (by decide)
    · exact st (.edi, 8) (by decide)
    · exact st (.ebp, 12) (by decide)
    · rw [spt, k₇.regs.1 _ (by decide), k06.1 _ (by decide), k₁.1 _ (by decide)]
  · rw [rt]
    refine if_congr ?_ rfl rfl
    rw [z₇.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.1.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        exact ⟨fun h => absurd h.1.2 (by simp), fun h => absurd h (by decide)⟩
      | some r =>
        obtain ⟨ax, ay, az⟩ := v₂ a ha
        obtain ⟨rx, ry, rz⟩ := vR₂ r hr
        have e20 : E s₂.mem base 0 = 0 := by
          rw [e₂ 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X er
        have e210 : E s₂.mem base 10 = 1 := by
          rw [e₂ 10 (by decide) (by decide) (by decide)]; exact h10
        have hA' : pt (E s₄.mem base) 6 7 10 = negPoint a := by
          show (⟨E s₄.mem base 6, E s₄.mem base 7, E s₄.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [e₄k 6 (by decide), e₄k 7 (by decide), e₄k 10 (by decide), n₃, k₃e 7 (by decide),
            k₃e 10 (by decide), e20, ax, ay, e210, az]
        have hQ : pt (E s₇.mem base) 0 6 2 = vladder S K (negPoint a) 456 := by
          rw [pt_congr' (e₇ 0 (by decide) (by decide)) (e₇ 6 (by decide) (by decide)) (e₇ 2 (by decide) (by decide))]
          show (⟨E s₆.mem base 0, E s₆.mem base 6, E s₆.mem base 2⟩ : Spec.Ed448.Point) = _
          rw [e₆k 0 (by decide), e₆6, e₆k 2 (by decide), ← hA']
          exact I₅.rep
        have hRR : pt (E s₇.mem base) 8 9 10 = r := by
          show (⟨E s₇.mem base 8, E s₇.mem base 9, E s₇.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [x₇, y₇, (FR RX (Or.inl rfl)).1, (FR RY (Or.inr rfl)).1, rx, ry, e₇ 10 (by decide) (by decide), h106,
            ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK]
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.X86
