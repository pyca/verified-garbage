import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
import VerifiedGarbage.Proof.AesOcb.X86_64.CmpMask

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the copy of the received tag from `tag` to `W`
(`recv`), its comparison with the computed tag (`cmp`), the mask of the
data (`mask`), the result and `restore` (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame)

/-- `recv`: the `tl` bytes of the tag at `T` copied to `W`. -/
theorem recv_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 3584⟩) :
    WP isa recv s fun t => t.mem = writeBytes s.mem W (bytesAt s.mem T tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := recvArgs_ok E htg htl
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (copyLoop_ok s₁ (S := T) (Dd := W) (n := tl) (by omega) (by omega) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact hT) (by rw [wr₁]; exact covers_prefix E.perm.w (by omega))
    (hTW.sub_right (Region.sub_prefix (by omega)))) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» (callees v)) s fun s' => gprPreserved s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  unfold «open» front
  refine WP.seq (pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_)
  have hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.lstar]; exact P₃.tbl)) fun s₄ B => ?_)
  have F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok v L B.env Ar.rounds ((kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  -- The received tag, to `W`.
  have tg₅ : s₅.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T := by
    rw [kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg]
  have hTs : Buf W SP s₅ T tl := Ar.tag.of_eq (T₅.rd.trans (B.rd.trans P₃.rd)) (T₅.wr.trans (B.wr.trans P₃.wr))
  refine WP.seq (WP.mono (recv_ok T₅.env Ar.t1 Ar.t16 tg₅ S₅.tl hTs.rd Ar.tag.w) fun s₅' ⟨mr, gr, rdr, wrr⟩ => ?_)
  have E₅' : Env K W SP s₅' := T₅.env.keep gr rdr wrr
  have Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have Fr' : Frame (mutR W SP D n) s₅.mem s₅'.mem := Fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := Ar.t16; omega)⟩
  have S₅' := Slots.of_mut L Ar.data.w Fr' S₅
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₅' Ar.t1 Ar.t16 S₅'.tl) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env K W SP s₆ := E₅'.keep (fun r hr => g₆ r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₆ wr₆
  have F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₆ : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 3584 →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₆, readW_writeW_off _ (by simp only [tagO]; omega) (by omega) (by decide)]
  have hD₅ : DBuf K W SP s₅' D n := hD₃.of_eq (rdr.trans (T₅.rd.trans B.rd)) (wrr.trans (T₅.wr.trans B.wr))
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ (c := c) (by rw [k₆ (by decide) (by decide)]; exact S₅'.data)
    (by rw [k₆ (by decide) (by decide)]; exact S₅'.len) (hD₅.of_eq rd₆ wr₆)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  have F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have F₃₇ : Frame (mutR W SP D n) s₃.mem s₇.mem :=
    (((F₄.trans F₅).trans Fr').trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩)).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The result, and `restore`.
  have ok₇ : s₇.mem.readW (W + BitVec.ofNat 64 0) 64 = if c then 1#64 else 0#64 := by
    rw [F₇.readW (r := ⟨W + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), m₆]
    exact (Mem.readW_writeW_self64 _ _ _).trans (by simp only [c, decide_eq_true_eq])
  have r₀ : InRegions (s₇.rd ++ s₇.wr) (W + BitVec.ofNat 64 0) 8 := E₇.perm.wR (by decide)
  obtain ⟨s₈, run₈, rax₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .rax .r15 tagO] s₇ = some s₈ ∧
      s₈.gpr .rax = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧
      s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.r15, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : Env K W SP s₈ := E₇.keep (fun r hr => g₈ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₈ wr₈
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ := restore_ok E₈ (by rw [m₈]; exact saved_mut L Ar.data.w F₃₇ P₃.saved)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈, Option.bind_some, run₉], ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, savO) (by decide)
    · exact hg₉ (.rbp, savO + 8) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, savO + 16) (by decide)
    · exact hg₉ (.r13, savO + 24) (by decide)
    · exact hg₉ (.r14, savO + 32) (by decide)
    · exact hg₉ (.r15, savO + 40) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      P₃.frame.trans (F₃₇.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, m₈, hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
    have i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := by
      unfold Spec.Ocb.ctxInv
      rw [bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
        · exact (k_mut L Ar.data.k r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
    have hout := B.out
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hout
    have hofs := B.ofs
    rw [P₃.lstar] at hofs
    have hck := B.ck
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hck
    have hTn := Ar.tag.lt
    have recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
      rw [mr, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) (by omega), length_bytesAt,
        List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil,
        buf_mut Ar.tag Ar.td (F₄.trans F₅)]
      exact bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Ar.tag.w.sub_right (Region.sub_prefix (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.stk.symm
          · exact Ar.td
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))) (by omega)
    have t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
      bytesAt_frame Fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega)
          (by have := Ar.t16; unfold t2O; omega)).symm) (by omega)
    have tagv := T₅.val
    rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
    have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
      have hn := Ar.data.lt
      have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
        rw [bytesAt_frame F₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
            (by omega),
          bytesAt_frame Fr (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))) (by omega),
          bytesAt_frame T₅.frame (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.stk.symm) (by omega)]
      rw [hm₉, m₈, m₇, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
        List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
    rw [hax₉, rax₈, d₉, hout]
    rw [Proof.Ocb.decryptWith_eq]
    simp only [length_bytesAt, List.length_drop]
    have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
        (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
      show decide (_ = _) = true ↔ _
      rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
    by_cases hr : 0 < n % 16
    · have h' : n - 16 * (n / 16) > 0 := by omega
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
      have hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
    · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
      have hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openPreX s) :
    WP isa («open» (callees v)) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  open_wp' v (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64
