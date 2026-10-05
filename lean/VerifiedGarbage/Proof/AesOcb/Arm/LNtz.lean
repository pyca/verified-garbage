import VerifiedGarbage.Proof.AesOcb.Arm.Words

/-!
# AES-OCB on ARMv7: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `r6`), shifted right
once more each time (in `lr`), is even: `ntz(i)` times (`lNtz_ok`), as on
AArch64 (`Proof.AesOcb.AArch64.lNtz_ok`). The invariant: after `j`
doublings, `W + lO` holds `L_j`, `lr` is `i / 2^j`, which is positive, and
`ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.Arm (eval_eq' z_cmp0 z_subFlags)

theorem and1 {v : Nat} (hv : v < 2 ^ 32) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat32 hv, show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat32 (by omega)]

theorem shr1 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by
  rw [ofNat_lsr32 hv]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : Others ntzRegs s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `r12 ← lr ∧ 1` and `Z` set if it is zero, with `v` in `lr`. -/
theorem low1_wp (s : State) {v : Nat} (hv : v < 2 ^ 32) (hlr : s.gpr .lr = BitVec.ofNat 32 v) :
    WP isa (.block low1) s fun s' => s'.z = decide (v % 2 = 0) ∧ Ran [.r12] s.mem s s' := by
  refine WP.of_runBlock ⟨_, by orun [low1], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, hlr, and1 hv, BitVec.sub_zero]
  exact z_cmp0 (by omega)

theorem lNtz_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 32) (h6 : s.gpr .r6 = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost (State.addr p.W) l i s) := by
  have fw := L.ww
  unfold lNtz
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (copy16_wp (W := State.addr p.W) (by rw [E.r11])
    (by decide) (by decide) (by rw [E.r11]; omega) (by decide) (by decide) (E.perm.wCR (by decide))
    (E.perm.wC (by decide))) fun s₁ R₁ => ?_)))
  have g₁ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3] → s₁.gpr r = s.gpr r := R₁.gpr
  refine WP.block_cons_iff.mpr ⟨s₁.setReg .lr (s₁.gpr .r6), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ hi' (by simp [gpr_setReg, g₁ .r6 (by decide), h6])) fun s₂ ⟨z₂, R₂⟩ => ?_
  -- The state before the loop.
  have post_of : ∀ t : State, Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      Others ntzRegs s₂ t → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      LNtzPost (State.addr p.W) l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        R₂.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2), g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by
    rw [R₂.mem, mem_setReg, R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have v₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l 0 := by
    rw [R₂.mem, mem_setReg, R₁.mem, blockAtMem_copy, hl0]
  have sp₂ : s₂.sp = s.sp := by rw [R₂.sp, sp_setReg, R₁.sp]
  have rd₂ : s₂.rd = s.rd := by rw [R₂.rd, rd_setReg, R₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [R₂.wr, wr_setReg, R₁.wr]
  have lr₂ : s₂.gpr .lr = BitVec.ofNat 32 i := by
    rw [R₂.gpr _ (by decide), gpr_setReg_self, g₁ _ (by decide), h6]
  have r11₂ : s₂.gpr .r11 = p.W := by
    rw [R₂.gpr _ (by decide), gpr_setReg_of_ne (h := by decide), g₁ _ (by decide), E.r11]
  refine WP.ite (decide (i % 2 = 0)) (eval_eq' z₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂ rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      Others ntzRegs s₂ t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using lr₂, fr₂, v₂,
      fun _ _ => rfl, sp₂, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, lrt, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have r11t : t.gpr .r11 = p.W := by rw [g _ (by decide), r11₂]
  have Pt : Perm p t := E.perm.of_eq rd wr
  refine WP.block_append (WP.block_append (WP.mono (dbl_wp (b := .r11) (W := State.addr p.W)
    (P := State.addr p.W) (by decide) (by rw [r11t]) (by rw [r11t]) (by decide) (by decide)
    (by rw [r11t]; simp only [lO]; omega) (by rw [r11t]; simp only [lO]; omega) (Pt.wCR (by decide)) (Pt.wC (by decide))) fun t₁ D₁ => ?_))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have lr₁ : t₁.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), lrt]
  refine WP.block_cons_iff.mpr ⟨t₁.setReg .lr (t₁.gpr .lr >>> 1), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ (v := i / 2 ^ (j + 1)) (by omega) (by simp [gpr_setReg, lr₁, shr1 hv, e]))
    fun t₃ ⟨z₃, R₃⟩ => ?_
  have fr' : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [R₃.mem, mem_setReg, D₁.mem]
    exact fun x hx => (dblMem_frame _ _ _ x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [R₃.mem, mem_setReg, D₁.mem, blockAtMem_dbl, v]; rfl
  have g' : Others ntzRegs s₂ t₃ := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2),
      D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [R₃.sp, sp_setReg, D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [R₃.rd, rd_setReg, D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [R₃.wr, wr_setReg, D₁.wr, wr]
  have lr₃ : t₃.gpr .lr = BitVec.ofNat 32 (i / 2 ^ (j + 1)) := by
    rw [R₃.gpr _ (by decide), gpr_setReg_self, lr₁, shr1 hv, e]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', lr₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), post_of t₃ fr' ?_ g' sp' rd' wr'⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.Arm
