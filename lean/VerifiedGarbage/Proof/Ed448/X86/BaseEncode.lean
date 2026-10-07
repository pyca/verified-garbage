import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.Proof.X448.X86.Inv
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# Ed448 base-point multiplication on x86 (32-bit): the encoding

`baseEncode`: `Z` inverted into slot 21, `y = Y/Z` into slot 4 and
`x = X/Z` into slot 1; `x` fully reduced and its low bit written as the top
bit of the output's 57th byte; `y` copied into slot 1, fully reduced and
written to the output's first 56 bytes (RFC 8032 §5.2.2); then the
callee-saved registers restored (`baseEncode_ok`). The 57 bytes are
`encodePoint` of the point in slots 0–2 (`Proof.Ed448.encodePoint_code`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (signBit baseEncode)
open VG.Impl.X448.X86 (slot X2 ACC ld at_)
open VG.Spec.Ed448 (bytesAt)

theorem invEnv_x0 (e : Env) : invEnv e 0 = e 0 := rfl

/-- The value of slot 1 mod 2 is its limb 0's. -/
theorem fe_mod2 (m : Mem) (base : Addr) : fe m base X2 % 2 = limbs m base X2 0 % 2 := by
  have h : ∀ n, valN (limbs m base X2) (n + 1) % 2 = limbs m base X2 0 % 2 := by
    intro n
    induction n with
    | zero => simp [valN]
    | succ n ih =>
      have e : (2 ^ 16) ^ (n + 1) * limbs m base X2 (n + 1) =
          2 * ((2 ^ 16) ^ n * 2 ^ 15 * limbs m base X2 (n + 1)) := by
        rw [Nat.pow_succ]; grind
      rw [valN_succ, Nat.add_mod, ih, radix, e, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact h 27

/-- The low bit of a word, rotated into bit 7 of its low byte. -/
theorem sign_byte (w : BitVec 32) :
    ((w &&& (1 : BitVec 32)).rotateRight 25).setWidth 8 = BitVec.ofNat 8 (128 * (w.toNat % 2)) := by
  have e : w &&& (1 : BitVec 32) = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.toNat % 2)
        (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  have h : ∀ b < 2, ((BitVec.ofNat 32 b).rotateRight 25).setWidth 8 = BitVec.ofNat 8 (128 * b) := by
    decide
  rw [e]; exact h _ (Nat.mod_lt _ (by decide))

def encodeFields : List FieldOp := [.mul 4 1 21, .mul 1 0 21]

theorem encodeFields_impl :
    [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)] = encodeFields.map FieldOp.impl := by
  decide +kernel

/-- The registers the encoding may change. -/
def encRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem baseEncode_ok {s₀ s : State} {n sc : Nat} (hA : Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hm : Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s₀.mem s.mem)
    (hawr : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20], (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r)
    (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (hout : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region) ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 57 ≤ 2 ^ 32)
    (hd : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 32} (sv : Saved base g s.mem) :
    WP isa baseEncode s fun t =>
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint ⟨E s.mem base 0, E s.mem base 1, E s.mem base 2⟩ ∧
      (∀ p ∈ savedSlots, t.gpr p.1 = g p.1) ∧ Keeps encRegs s t ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s.mem t.mem := by
  have hfar : ∀ j < 8192, 57 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j) := fun j hj => far_out hd hj
  have hfar56 : ∀ j < 8192, 56 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j) :=
    fun j hj => Nat.le_trans (by decide) (hfar j hj)
  have hw57 : ∀ j < 57, InRegions s₀.wr (off ((arg s₀ 0).setWidth 64) j) 1 := fun j hj =>
    ⟨_, hout, Offset.contains_base _ (by omega) (by omega)⟩
  have ws : (⟨base, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] :=
    List.mem_append_left _ (hwr ▸ hs.wr)
  -- What code writing the working space and the call stack keeps.
  have wf : ∀ {u : State}, u.gpr .esp = s₀.gpr .esp → u.wr = s₀.wr →
      ∀ {m : Mem}, Frame (u.wr ++ [below (u.gpr .esp) 20]) u.mem m →
        Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) u.mem m := by
    intro u hu hw m hf; rw [hu, hw] at hf; exact hf
  have ws1 : ∀ {m m' : Mem}, Outside base 0 8192 m m' → Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) m m' :=
    fun h => (Outside.frame h).mono fun r hr => by rw [List.mem_singleton.mp hr]; exact ws
  unfold baseEncode
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by decide +kernel))
    (by rw [show stackUse Impl.X448.X86.invert = 20 by decide +kernel]; exact hc.sp)
    (invert_ok hs hc hb)) fun s₁ ⟨⟨k₁, b₁, e₁⟩, f₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hc₁ := k₁.ctx hc
  have sp₁ : s₁.gpr .esp = s₀.gpr .esp := (k₁.regs.1 _ (by decide)).trans hsp
  rw [encodeFields_impl]
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by decide +kernel))
    (Nat.le_trans (by decide +kernel :
      stackUse (Impl.X448.X86.ops (encodeFields.map FieldOp.impl)) ≤ 20) hc₁.sp)
    (ops_ok hs₁ hc₁ b₁ encodeFields)) fun s₂ ⟨⟨k₂, b₂, e₂⟩, f₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have ex : E s₂.mem base 1 = E s.mem base 0 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, encodeFields, FieldOp.apply, opMul, Function.update_self]
    rw [Function.update_of_ne (show (21 : Index) ≠ 4 by decide),
      Function.update_of_ne (show (0 : Index) ≠ 4 by decide), invEnv_x0, invEnv_eval]
  have ey : E s₂.mem base 4 = E s.mem base 1 * Proof.X448.invert (E s.mem base 2) := by
    rw [e₂, e₁]
    simp only [applyOps, encodeFields, FieldOp.apply, opMul]
    rw [Function.update_of_ne (show (4 : Index) ≠ 1 by decide), Function.update_self, invEnv_x2,
      invEnv_eval]
  simp only [List.append_assoc]
  -- `x` fully reduced.
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs₂ (b₂ 1)) fun s₃ ⟨bx₃, vx₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have f03 : Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s.mem s₃.mem :=
    ((wf hsp hwr (by rwa [show stackUse Impl.X448.X86.invert = 20 by decide +kernel] at f₁)).trans
      (wf sp₁ (k₁.regs.2.2.trans hwr) (Frame.below_mono f₂ (by decide +kernel) hc₁.sp))).trans
      (ws1 (m₃.whole (by decide)))
  have kk : Keeps (.esi :: workRegs) s s₃ :=
    k₁.regs.trans ((k₂.regs.mono (by decide)).trans (k₃.mono (by decide)))
  -- Its bit, to the output's byte 56.
  rw [Impl.Ed448.X86.signBit, List.cons_append]
  refine hA.loadF (kk.1 _ (by decide) |>.trans hsp) (kk.2.1.trans hr) (kk.2.2.trans hwr)
    (hm.trans f03) hawr h0 fun s₄ u₄ => ?_
  refine load_ok (hs₃.of_upd u₄ (by decide)) (by decide) fun s₅ u₅ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun s₆ u₆ _ => ?_
  refine wp_shift (by decide) fun s₇ u₇ => ?_
  have esi₇ : s₇.gpr .esi = arg s₀ 0 := by
    rw [u₇.other .esi (by decide), u₆.other .esi (by decide), u₅.other .esi (by decide), u₄.gpr]
  refine wp_store8 (a := (arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56)
    (by change addr (s₇.gpr .esi) 56 = _; rw [esi₇]; exact addr_eq (by omega))
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, kk.2.2, hwr]; exact hw57 56 (by decide)) fun s₈ u₈ => ?_
  have hx : (E s₂.mem base 1).val = fe s₂.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
  have byte₈ : s₈.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) =
      BitVec.ofNat 8 (128 * ((E s.mem base 0 * Proof.X448.invert (E s.mem base 2)).val % 2)) := by
    rw [u₈.mem, writeW8_apply, ite_eq_left rfl, Reg8.reg]
    have : s₇.gpr .eax = (s₅.gpr .eax &&& (1 : BitVec 32)).rotateRight 25 := by
      rw [u₇.gpr]; change (s₆.gpr .eax).rotateRight 25 = _; rw [u₆.gpr]; rfl
    rw [this, sign_byte, u₅.gpr, u₄.mem, ← ex, hx, ← vx₃, fe_mod2]; rfl
  have m₈ : s₈.mem = s₃.mem.writeW ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56)
      ((s₇.gpr Reg8.al.reg).setWidth 8) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have o₈ : Outside ((arg s₀ 0).setWidth 64) 0 57 s₃.mem s₈.mem := by
    rw [m₈]; intro q hq
    exact writeW8_outside _ _ _ (d := 56) (by decide) (by omega)
  have w₈ : ∀ d, d + 4 ≤ 8192 → word s₈.mem base d = word s₃.mem base d := fun d hd4 =>
    out_word o₈ hd4 hfar
  have hs₈ : Scr s₈ base := (((hs₃.of_upd u₄ (by decide)).of_upd u₅ (by decide)).of_upd u₆ (by decide)).of_upd
    u₇ (by decide) |>.of_keeps (u₈.rest []) (by decide)
  have E₈ : E s₈.mem base = E s₃.mem base := by
    funext i
    simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr fun j hj =>
      congrArg BitVec.toNat (w₈ _ (by have := i.isLt; simp only [slot]; omega)))
  have E₃ : E s₃.mem base = E s₂.mem base := by
    rw [E_update (o := 1) (m₃.ws (by decide))]
    funext i
    by_cases hi : i = 1
    · subst hi; rw [Function.update_self]
      change Proof.X448.toFe (fe s₃.mem base X2) = Proof.X448.toFe (fe s₂.mem base X2)
      rw [vx₃]; exact Proof.X448.toFe_mod _
    · rw [Function.update_of_ne hi]
  have b₃ : BoundedEnv s₃.mem base := bounded_update (o := 1) (m₃.ws (by decide)) b₂ bx₃
  have b₈ : BoundedEnv s₈.mem base := fun i j hj => by
    change (word s₈.mem base (slot i.val + 4 * j)).toNat < _
    rw [w₈ _ (by have := i.isLt; simp only [slot]; omega)]; exact b₃ i j hj
  -- `y` into slot 1, fully reduced.
  change WP isa (.block (Impl.X448.X86.copy X2 (slot 4) ++ _)) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.and (copyE hs₈ b₈ 1 4) (copy_ok hs₈ (o := X2) (a := slot 4) (by decide) (by decide)
    (by decide))) fun s₉ ⟨⟨k₉, b₉, e₉⟩, _, m₉, _⟩ => ?_
  have hs₉ := k₉.scr hs₈
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs₉ (b₉ 1)) fun s₁₀ ⟨by₁₀, vy₁₀, m₁₀, k₁₀⟩ => ?_
  have hs₁₀ := hs₉.of_keeps k₁₀ (by decide)
  have y₁₀ : fe s₁₀.mem base X2 = (E s.mem base 1 * Proof.X448.invert (E s.mem base 2)).val := by
    have hy : (E s₉.mem base 1).val = fe s₉.mem base X2 % Spec.X448.P := Proof.X448.toFe_val _
    have h9 : E s₉.mem base 1 = E s₈.mem base 4 := by
      rw [e₉]; exact Function.update_self _ _ _
    rw [vy₁₀, ← hy, h9, E₈, E₃, ey]
  -- The output.
  have esi₁₀ : s₁₀.gpr .esi = arg s₀ 0 := by
    rw [k₁₀.1 _ (by decide), k₉.regs.1 _ (by decide), u₈.gpr, esi₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by
    rw [k₁₀.2.2, k₉.regs.2.2, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, kk.2.2, hwr]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (p := (arg s₀ 0).setWidth 64) hs₁₀ by₁₀ (by rw [esi₁₀])
    (by rw [esi₁₀]; omega) (fun j hj => by rw [wr₁₀]; exact hw57 j (by omega)) hfar56)
    fun s₁₁ ⟨v₁₁, o₁₁, k₁₁⟩ => ?_
  -- The saved registers.
  have sv₃ : Saved base g s₃.mem :=
    ((sv.wsout2 k₁.mem (by decide) (by decide)).wsout2 k₂.mem (by decide) (by decide)).field m₃
      (by decide)
  have sv₈ : Saved base g s₈.mem := sv₃.of_readW fun q hq => by
    have := savedSlots_bound q hq; exact w₈ _ (by omega)
  have sv₁₀ : Saved base g s₁₀.mem :=
    (sv₈.wsout2 k₉.mem (by decide) (by decide)).field m₁₀ (by decide)
  have sv₁₁ : Saved base g s₁₁.mem := sv₁₀.of_readW fun q hq => by
    have := savedSlots_bound q hq
    exact out_word o₁₁ (by omega) fun j hj => Nat.le_trans (by decide) (hfar j hj)
  have hs₁₁ : Scr s₁₁ base := hs₁₀.of_keeps k₁₁ (by decide)
  refine WP.mono (restore_ok hs₁₁ sv₁₁) fun t ⟨rt, mt, kt⟩ => ?_
  have f810 : Outside base 0 8192 s₈.mem s₁₀.mem :=
    Outside.trans (fun p hp => m₉ p (Or.inr (by simp only [X2, slot]; omega))) (m₁₀.whole (by decide))
  refine ⟨?_, rt, ?_, ?_⟩
  · have b56 : s₁₁.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) =
        s₈.mem ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 56) := by
      rw [o₁₁ _ (Or.inr (by rw [ofs_off' _ (by decide)]))]
      exact f810 _ (Or.inr (VG.Proof.Ed448.X86.far hd (i := 56) (by decide) (by decide)))
    rw [mt, Limbs16.bytesAt_57, v₁₁, y₁₀, b56, byte₈, Proof.Ed448.encodePoint_code]
  · refine (k₁.regs.mono ?_).trans ((k₂.regs.mono ?_).trans ((k₃.mono ?_).trans
      ((u₄.rest ?_).trans ((u₅.rest ?_).trans ((u₆.rest ?_).trans ((u₇.rest ?_).trans
      ((u₈.rest _).trans ((k₉.regs.mono ?_).trans ((k₁₀.mono ?_).trans ((k₁₁.mono ?_).trans
      (kt.mono ?_)))))))))))
    all_goals first | decide | (intro r hr; revert r; decide)
  · rw [mt]
    have os : ∀ r ∈ [(⟨(arg s₀ 0).setWidth 64, 57⟩ : Region)], r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
      intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ hout
    refine f03.trans (((Outside.frame o₈).mono os).trans
      ((ws1 f810).trans (((Outside.frame o₁₁).sub fun r hr => ?_))))
    refine ⟨_, List.mem_append_left _ hout, ?_⟩
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)

end VG.Proof.Ed448.X86
