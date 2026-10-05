import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Impl.EcKey.X86

/-!
# Elliptic curve public keys on x86 (32-bit): the result

`finish` reads `out` from its argument, writes `04 ‖ x ‖ y` big-endian to
it, or zeros, by the flag's mask, returns the flag's low bit and restores
the callee-saved registers (`pkFinish_ok`): the leading byte by `store8`,
the two coordinates from `out + 1` as the signature's `finish` writes
`r ‖ s`, then the signature's tail (`tail_ok`).
-/

namespace VG.Proof.EcKey.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (YM Y)

variable {c : Cfg}

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov byte [m], r`. -/
theorem wp_store8S {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

theorem mask4 (b : Bool) :
    (((4 : BitVec 32) &&& mask32 (b = true)).setWidth 8 : BitVec 8) = if b then 4 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : Impl.EcKey.X86.Cfg.finish c =
    .mov .ecx (.mem (sc (c.sl FLAG))) :: .mov .ebx (.mem (Cfg.argOp 0)) :: .mov .eax (.imm 4) ::
    .alu .and .eax (.reg .ecx) :: .store8 (at_ .ebx 0) .al ::
    (storeBytes c.C.len c.n .ebx 1 (c.sl X) ++ (storeBytes c.C.len c.n .ebx (1 + c.C.len) (c.sl Y) ++
    (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore))) := by
  simp only [Impl.EcKey.X86.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : readSrc s (.mem (Cfg.argOp 0)) = some o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.X86.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (o32.setWidth 64) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s X) ++ toBytes c.C.len (sv c base s Y))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧
      Outside (o32.setWidth 64) 0 (1 + 2 * c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  generalize hout64 : o32.setWidth 64 = out at hw hd ⊢
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have h16 : ∀ rd ∈ Cfg.saved, ∀ w ∈ [(size, 2 ^ 64)], rd.2 + 4 ≤ w.1 ∨ w.1 + w.2 ≤ rd.2 :=
    fun rd hrd w hw => by
      have := saved_lt rd hrd
      simp only [List.mem_singleton] at hw; subst hw; exact .inl (by omega)
  rw [finish_eq]
  -- The flag, `out`, and the leading byte.
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movS (show readSrc s₁ (.mem (Cfg.argOp 0)) = some o32 by
    have hea : s₁.ea (Cfg.argOp 0) = s.ea (Cfg.argOp 0) := by
      show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
      rw [u₁.other _ (by decide)]
    rw [← hout]; show s₁.load32 _ = s.load32 _
    rw [State.load32, State.load32, hea, u₁.rd, u₁.wr, u₁.mem]) fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have k₄ : Keeps [.eax, .ebx, .ecx] s s₄ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hc₄ : s₄.gpr .ecx = mask32 (b = true) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ← flagW, hf]
  have hb₄ : s₄.gpr .ebx = o32 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have ha₄ : (s₄.gpr Reg8.al.reg).setWidth 8 = (if b then 4 else 0 : BitVec 8) := by
    show (s₄.gpr .eax).setWidth 8 = _
    rw [u₄.gpr, u₃.gpr, u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.gpr, ← flagW, hf]
    simp only [ite_true]
    exact mask4 b
  refine wp_store8S (a := off out 0)
    (by show (s₄.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = _; rw [hb₄, BitVec.add_zero, hout64]; exact (BitVec.add_zero out).symm)
    ⟨_, by rw [k₄.2.2]; exact hw, Offset.contains_base out (by omega) (by omega)⟩ fun s₅ m₅ => ?_
  have hs₅ := hs₄.of_keeps (m₅.keeps []) (by decide)
  have O₅ : Outside out 0 1 s₄.mem s₅.mem := by rw [m₅.mem]; exact writeW8_outside _ _ _ (by omega)
  have L₅ : s₅.mem (out + BitVec.ofNat 64 0) = if b then 4 else 0 := by rw [m₅.mem, writeW8_self, ha₄]
  have U₅ := O₅.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega)))
  have hb₅ : s₅.gpr .ebx = o32 := by rw [m₅.gpr, hb₄]
  have hc₅ : s₅.gpr .ecx = mask32 (b = true) := by rw [m₅.gpr, hc₄]
  have x₅ : wordsVal s₅.mem base (c.sl X) c.n = sv c base s X := by
    rw [U₅.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₄]
  -- `x`, from `out + 1`.
  refine WP.block_append (WP.mono (storeBytes_ok hs₅ (dst := .ebx) (d := 1) (a := c.sl X) (by decide) (by decide) b
    hc₅ hX (by omega) hlhi (by rw [hb₅]; omega) (fun e m he => ⟨_, by rw [m₅.wr, k₄.2.2]; exact hw, by
      rw [hb₅, hout64, Offset.add_add]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hb₅, hout64]; exact hdsc hX (by omega))) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_)
  rw [hb₅, hout64, x₅] at e₆
  rw [hb₅, hout64] at O₆
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have U₆ := O₆.unch_far (hscd (d := 1) (by omega))
  have hb₆ : s₆.gpr .ebx = o32 := by rw [k₆.1 _ (by decide), hb₅]
  have hc₆ : s₆.gpr .ecx = mask32 (b = true) := by rw [k₆.1 _ (by decide), hc₅]
  have y₆ : wordsVal s₆.mem base (c.sl Y) c.n = sv c base s Y := by
    rw [U₆.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₅.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₄]
  -- `y`, from `out + 1 + len`.
  refine WP.block_append (WP.mono (storeBytes_ok hs₆ (dst := .ebx) (d := 1 + c.C.len) (a := c.sl Y) (by decide)
    (by decide) b hc₆ hY (by omega) hlhi (by rw [hb₆]; omega) (fun e m he => ⟨_, by rw [k₆.2.2, m₅.wr, k₄.2.2]; exact hw, by
      rw [hb₆, hout64, Offset.add_add]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hb₆, hout64]; exact hdsc hY (by omega))) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_)
  rw [hb₆, hout64, y₆] at e₇
  rw [hb₆, hout64] at O₇
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have U₇ := O₇.unch_far (hscd (d := 1 + c.C.len) (by omega))
  have hsv₇ : ∀ rd ∈ Cfg.saved, s₇.mem.readW (off base rd.2) 32 = g rd.1 := fun rd hrd => by
    have := saved_lt rd hrd
    rw [Unch.readW32 U₇ (h16 rd hrd) (by omega), Unch.readW32 U₆ (h16 rd hrd) (by omega),
      Unch.readW32 U₅ (h16 rd hrd) (by omega), hm₄, hsv rd hrd]
  -- The return value and the callee-saved registers.
  refine WP.mono (tail_ok hs₇ hsv₇ b (by rw [k₇.1 _ (by decide), hc₆]))
    fun s' ⟨hm', eax', saved', others'⟩ => ⟨?_, eax', saved', fun r hr => ?_, ?_⟩
  · have lead : Spec.Ecdsa.bytesAt s₇.mem out 1 = [if b then 4 else 0] := by
      rw [bytesAt_keep O₇ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
        bytesAt_keep O₆ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
      exact congrArg (· :: []) L₅
    have xs : Spec.Ecdsa.bytesAt s₇.mem (out + BitVec.ofNat 64 1) c.C.len =
        if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0 := by
      rw [bytesAt_keep O₇ (Offset.disjoint out (.inl (Nat.le_refl _)) (by omega) (by omega)) (by omega)
        (by omega), e₆]
    rw [hm', show 1 + 2 * c.C.len = 1 + (c.C.len + c.C.len) by omega, bytesAt_add, bytesAt_add, lead, xs,
      Offset.add_add, e₇]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · simp only [ite_true]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7'⟩ := hr
    rw [others' _ (by simp [h1, h2, h4, h5, h6, h7']), k₇.1 _ (by simp [h1, h4]), k₆.1 _ (by simp [h1, h4]),
      m₅.gpr, k₄.1 _ (by simp [h1, h2, h3])]
  · rw [hm', ← hm₄]
    exact ((O₅.mono (Nat.zero_le _) (by omega)).trans ((O₆.shift (by omega)).mono (Nat.zero_le _) (by omega))).trans
      ((O₇.shift (by omega)).mono (Nat.zero_le _) (by omega))

end VG.Proof.EcKey.X86
