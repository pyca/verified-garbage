import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed448.X86.BaseMain

/-!
# Ed448 verification's equation on x86 (32-bit): the whole function

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16])` returns `verifyEquation` of
its inputs (`verifyEquation_main`), given the reference computations'
agreement with the specification (`RecoverOk`, `VerifyEqOk`): the entry (the
registers saved, the bits of `S` and `k`, the check of `S`, the slots), `A`
decoded and negated, `Q = [S]B + [k](-A)` by the loop, `R` decoded, and the
comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
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

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

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

theorem bits_kept {base : Addr} {m m' : Mem} (h : Outside2 base 16 2864 ACC 512 m m') :
    ∀ t < 456, m' (off base (BITS + t)) = m (off base (BITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)

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
  -- `A`.
  obtain ⟨a0e, a0r, a0v⟩ := hA.argRead (k₁.1 .esp (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o₁) (i := 0) (by decide)
  refine WP.seq (WP.mono (decode_ok hR hs₁ b₁ a0e a0r a0v h.f0
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact ipk.read j hj) ipk.far 6 7 (Or.inl ⟨rfl, rfl⟩) h10 ed)
    fun s₂ ⟨k₂, b₂, c₂, v₂, e₂⟩ => ?_)
  rw [ipk.bytes o₁] at c₂ v₂
  have hs₂ := k₂.scr hs₁
  -- `-A`.
  refine field_seq [.sub 6 0 6] (by decide) hs₂ b₂ fun s₃ k₃ b₃ e₃ => ?_
  have hs₃ := k₃.scr hs₂
  obtain ⟨n₃, k₃e⟩ := sub6_E (E s₂.mem base)
  rw [← e₃] at n₃ k₃e
  -- `Q`'s `Y` set to 1.
  rw [show ops [Impl.X448.X86.Op.copy X2 (slot 10)] = ops (([.copy 1 10] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs₃ b₃ [.copy 1 10]) fun s₄ ⟨k₄, b₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  have e₄1 : E s₄.mem base 1 = E s₃.mem base 10 := by
    rw [e₄]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₄k : ∀ i : Index, i ≠ 1 → E s₄.mem base i = E s₃.mem base i := fun i hi => by
    rw [e₄]; exact Function.update_of_ne hi _ _
  -- What is kept from the entry to the loop.
  have k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem base i = E s₁.mem base i := fun i hi => by
    rw [e₄k i (fun h => by subst h; omega), k₃e i (fun h => by subst h; omega),
      e₂ i (fun h => by subst h; omega) (fun h => by subst h; omega) (by omega)]
  have O₄ : Outside base 0 8192 s₀.mem s₄.mem :=
    ((o₁.trans (k₂.mem.whole (by decide) (by decide))).trans (k₃.mem.whole (by decide) (by decide))).trans
      (k₄.mem.whole (by decide) (by decide))
  have bits₄ : ∀ t < 456, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (pair2 S K t) := fun t ht => by
    rw [bits_kept (Outside2.widen k₄.mem) t ht, bits_kept (Outside2.widen k₃.mem) t ht,
      bits_kept k₂.mem t ht]
    exact bits₁ t ht
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (s₀ := s₄) (A := pt (E s₄.mem base) 6 7 10) bits₄
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s₅ I₅ => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs₄.of_keeps k' (by decide), h3 ▸ b₄, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
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
  refine WP.seq (WP.mono (ops_ok hs₅ I₅.bounded [.copy 6 1]) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have hs₆ := k₆.scr hs₅
  have e₆6 : E s₆.mem base 6 = E s₅.mem base 1 := by
    rw [e₆]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₆k : ∀ i : Index, i ≠ 6 → E s₆.mem base i = E s₅.mem base i := fun i hi => by
    rw [e₆]; exact Function.update_of_ne hi _ _
  have O₆ : Outside base 0 8192 s₀.mem s₆.mem :=
    (O₄.trans (I₅.mem.whole (by decide) (by decide))).trans (k₆.mem.whole (by decide) (by decide))
  have k06 : Keeps (.esi :: workRegs) s₁ s₆ :=
    ((k₂.regs.trans (k₃.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (k₄.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (I₅.regs.trans (k₆.regs.mono (fun _ h => List.mem_cons_of_mem _ h)))
  -- `R`.
  obtain ⟨a1e, a1r, a1v⟩ := hA.argRead (s := s₆) (by rw [k06.1 _ (by decide), k₁.1 _ (by decide)])
    (by rw [k06.2.1, k₁.2.1]) (by rw [k06.2.2, k₁.2.2]) (hbase ▸ O₆) (i := 1) (by decide)
  have h106 : E s₆.mem base 10 = 1 := by rw [e₆k 10 (by decide)]; exact congrArg Spec.Ed448.Point.Z I₅.q
  have d₆ : E s₆.mem base 11 = Spec.Ed448.d := by rw [e₆k 11 (by decide)]; exact I₅.d
  refine WP.seq (WP.mono (decode_ok hR hs₆ b₆ a1e a1r a1v (by have := h.f1; omega)
    (fun j hj => by rw [k06.2.1, k06.2.2, k₁.2.1, k₁.2.2]; exact isig.read j (by omega))
    (fun j hj => isig.far j (by omega)) 8 9 (Or.inr ⟨rfl, rfl⟩) h106 d₆)
    fun s₇ ⟨k₇, b₇, c₇, v₇, e₇⟩ => ?_)
  have bR : bytesAt s₆.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => O₆ _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    exact isig.far i (by omega)
  rw [bR, ← bytesAt_take57] at c₇ v₇
  have hs₇ := k₇.scr hs₆
  -- `BAD`.
  have bad₄ : word s₄.mem base BAD = word s₂.mem base BAD := by rw [Keep.bad k₄, Keep.bad k₃]
  have bad₆ : word s₆.mem base BAD = word s₄.mem base BAD := by
    rw [Keep.bad k₆]; exact I₅.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)
  have c₇' : BadUpd ((Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57)).isSome)
      (word s₂.mem base BAD) (word s₇.mem base BAD) := by
    rw [← bad₄, ← bad₆]; exact c₇
  have z₇ := ((c₁.trans c₂).trans c₇').zero
  -- The comparison.
  have sv₇ : Saved base s₀.gpr s₇.mem :=
    (((((sv₁.outside2 k₂.mem (by decide) (by decide)).outside2 k₃.mem (by decide) (by decide)).outside2
      k₄.mem (by decide) (by decide)).outside2 I₅.mem (by decide) (by decide)).outside2 k₆.mem (by decide)
      (by decide)).outside2 k₇.mem (by decide) (by decide)
  refine WP.mono (vfinish_ok hs₇ b₇ sv₇ z₇.2) fun t ⟨rt, st, spt, ot⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact st (.ebx, 0) (by decide)
    · exact st (.esi, 4) (by decide)
    · exact st (.edi, 8) (by decide)
    · exact st (.ebp, 12) (by decide)
    · rw [spt, k₇.regs.1 _ (by decide), k06.1 _ (by decide), k₁.1 _ (by decide)]
  · have O₇ : Outside base 0 8192 s₀.mem t.mem :=
      (O₆.trans (k₇.mem.whole (by decide) (by decide))).trans ot
    have frame : Frame [⟨base, 8192⟩] s₀.mem t.mem := Outside.frame O₇
    have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    exact frame.readW ret
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr; exact hbase ▸ h.ret_sc) (by decide)
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
        obtain ⟨rx, ry, rz⟩ := v₇ r hr
        have e20 : E s₂.mem base 0 = 0 := by
          rw [e₂ 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X er
        have e210 : E s₂.mem base 10 = 1 := by
          rw [e₂ 10 (by decide) (by decide) (by decide)]; exact h10
        have hA' : pt (E s₄.mem base) 6 7 10 = negPoint a := by
          show (⟨E s₄.mem base 6, E s₄.mem base 7, E s₄.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [e₄k 6 (by decide), e₄k 7 (by decide), e₄k 10 (by decide), n₃, k₃e 7 (by decide),
            k₃e 10 (by decide), e20, ax, ay, e210, az]
        have hQ : pt (E s₇.mem base) 0 6 2 = vladder S K (negPoint a) 456 := by
          rw [pt_congr' (e₇ 0 (by decide) (by decide) (Or.inl rfl)) (e₇ 6 (by decide) (by decide)
            (Or.inr (Or.inr ⟨by decide, by decide⟩))) (e₇ 2 (by decide) (by decide) (Or.inr (Or.inl rfl)))]
          show (⟨E s₆.mem base 0, E s₆.mem base 6, E s₆.mem base 2⟩ : Spec.Ed448.Point) = _
          rw [e₆k 0 (by decide), e₆6, e₆k 2 (by decide), ← hA']
          exact I₅.rep
        have hRR : pt (E s₇.mem base) 8 9 10 = r := by
          show (⟨E s₇.mem base 8, E s₇.mem base 9, E s₇.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [rx, ry, e₇ 10 (by decide) (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK]
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.X86
