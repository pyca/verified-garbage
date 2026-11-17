module

public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Impl.AesOcb.Arm
public import VerifiedGarbage.Proof.AesOcb.Arm.Env
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesOcb.Arm.Words
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `AesOcb.Arm.LNtz`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `r6`), shifted right
once more each time (in `lr`), is even: `ntz(i)` times (`lNtz_ok`), as on
AArch64 (`Proof.AesOcb.AArch64.lNtz_ok`). The invariant: after `j`
doublings, `W + lO` holds `L_j`, `lr` is `i / 2^j`, which is positive, and
`ntz(i) = j + ntz(i / 2^j)`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.Arm (eval_eq' z_cmp0 z_subFlags)

theorem and1 {v : Nat} (hv : v < 2 ^ 32) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat32 hv, show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat32 (by omega_using [])]

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
  exact z_cmp0 (by omega_using [])

theorem lNtz_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 32) (h6 : s.gpr .r6 = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost (State.addr p.W) l i s) := by
  have fw := L.ww
  unfold lNtz
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (copy16_wp (W := State.addr p.W) (by rw [E.r11])
    (by decide) (by decide) (by rw [E.r11]; omega_using [fw]) (by decide) (by decide) (E.perm.wCR (by decide))
    (E.perm.wC (by decide))) fun s₁ R₁ => ?_)))
  have g₁ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3] → s₁.gpr r = s.gpr r := R₁.gpr
  refine WP.block_cons_iff.mpr ⟨s₁.setReg .lr (s₁.gpr .r6), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ hi' (by simp [gpr_setReg, g₁ .r6 (by decide), h6])) fun s₂ ⟨z₂, R₂⟩ => ?_
  -- The state before the loop.
  obtain post_of : ∀ t : State, Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      Others ntzRegs s₂ t → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      LNtzPost (State.addr p.W) l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        R₂.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2), g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1])], sp, rd, wr⟩
  obtain fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by
    rw [R₂.mem, mem_setReg, R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain v₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l 0 := by
    rw [R₂.mem, mem_setReg, R₁.mem, blockAtMem_copy, hl0]
  obtain sp₂ : s₂.sp = s.sp := by rw [R₂.sp, sp_setReg, R₁.sp]
  obtain rd₂ : s₂.rd = s.rd := by rw [R₂.rd, rd_setReg, R₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [R₂.wr, wr_setReg, R₁.wr]
  obtain lr₂ : s₂.gpr .lr = BitVec.ofNat 32 i := by
    rw [R₂.gpr _ (by decide), gpr_setReg_self, g₁ _ (by decide), h6]
  obtain r11₂ : s₂.gpr .r11 = p.W := by
    rw [R₂.gpr _ (by decide), gpr_setReg_of_ne (h := by decide), g₁ _ (by decide), E.r11]
  refine WP.ite (decide (i % 2 = 0)) (eval_eq' z₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂ rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega_using [hb])]
  obtain he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      Others ntzRegs s₂ t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using lr₂, fr₂, v₂,
      fun _ _ => rfl, sp₂, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, lrt, fr, v, g, sp, rd, wr⟩
  obtain hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  obtain r11t : t.gpr .r11 = p.W := by rw [g _ (by decide), r11₂]
  obtain Pt : Perm p t := E.perm.of_eq rd wr
  refine WP.block_append (WP.block_append (WP.mono (dbl_wp (b := .r11) (W := State.addr p.W)
    (P := State.addr p.W) (by decide) (by rw [r11t]) (by rw [r11t]) (by decide) (by decide)
    (by rw [r11t]; simp only [lO]; omega_using [fw]) (by rw [r11t]; simp only [lO]; omega_using [fw]) (Pt.wCR (by decide)) (Pt.wC (by decide))) fun t₁ D₁ => ?_))
  obtain e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain lr₁ : t₁.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), lrt]
  refine WP.block_cons_iff.mpr ⟨t₁.setReg .lr (t₁.gpr .lr >>> 1), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ (v := i / 2 ^ (j + 1)) (by omega_using [hv, e]) (by simp [gpr_setReg, lr₁, shr1 hv, e]))
    fun t₃ ⟨z₃, R₃⟩ => ?_
  obtain fr' : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [R₃.mem, mem_setReg, D₁.mem]
    exact fun x hx => (dblMem_frame _ _ _ x hx).trans (fr x hx)
  obtain v' : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [R₃.mem, mem_setReg, D₁.mem, blockAtMem_dbl, v]; rfl
  obtain g' : Others ntzRegs s₂ t₃ := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2),
      D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  obtain sp' : t₃.sp = s.sp := by rw [R₃.sp, sp_setReg, D₁.sp, sp]
  obtain rd' : t₃.rd = s.rd := by rw [R₃.rd, rd_setReg, D₁.rd, rd]
  obtain wr' : t₃.wr = s.wr := by rw [R₃.wr, wr_setReg, D₁.wr, wr]
  obtain lr₃ : t₃.gpr .lr = BitVec.ofNat 32 (i / 2 ^ (j + 1)) := by
    rw [R₃.gpr _ (by decide), gpr_setReg_self, lr₁, shr1 hv, e]
  obtain hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega_using []
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega_using [hpos], j + 1, rfl,
      by rw [e]; omega_using [hpos, hev], hodd, hntz', lr₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), post_of t₃ fr' ?_ g' sp' rd' wr'⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega_using [hodd])]

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xorB_wp`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashFill_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (z_subFlags dec32 z_dec)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r8, .r12, .lr]

theorem w_A {p : Prm} (L : Lay p) {k : Nat} (h : 16 + k ≤ p.al) :
    State.addr (p.A + BitVec.ofNat 32 k) = State.addr p.A + BitVec.ofNat 64 k :=
  addr_add (by have := L.aw; omega_using [h, this])

/-- What one `hashFill` leaves. -/
structure FillPost (p : Prm) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (State.addr p.A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  r4 : t'.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i + 1))
  r6 : t'.gpr .r6 = BitVec.ofNat 32 (j + i + 2)
  r8 : t'.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (c - (i + 1))
  z : t'.z = decide (i + 1 = c)
  gpr : Others fillRegs t t'
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {j i c : Nat} (hi : i < c)
    (hc : c ≤ 16) (hj : 16 * (j + i + 1) ≤ p.al)
    (h6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)) (h4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)))
    (h8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (c - i))
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)) :
    WP isa hashFill t (FillPost p l j i c t) := by
  have fw := L.ww
  have fa := L.aw
  have al32 := L.al_lt
  obtain hb : bufO + 16 * i + 16 ≤ 512 := by simp only [bufO]; omega_using [hi, hc]
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) L E (by omega_using []) (by omega_using [hj, fa]) h6 hl0) fun t₁ P₁ => ?_)
  obtain E₁ : Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  have g₁ : Others ntzRegs t t₁ := P₁.gpr
  -- the offset
  refine WP.block_append (WP.block_append (WP.mono (xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11)
    (pd := ohO) (qd := lO) (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega_using [fw])
    (by rw [E₁.r11]; simp only [lO]; omega_using [fw]) (by rw [E₁.r11]; simp only [ohO]; omega_using [fw])
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_))
  rw [E₁.r11] at R₂
  obtain E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  obtain oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), P₁.val,
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    obtain h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', g₁ r hr]
  obtain fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  -- the block of the associated data
  obtain eA : State.addr (p.A + BitVec.ofNat 32 (16 * (j + i))) = State.addr p.A + BitVec.ofNat 64 (16 * (j + i)) :=
    w_A L (by omega_using [hj])
  obtain eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * i)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i) :=
    L.wA (by omega_using [hb])
  obtain r4₂ : t₂.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [g₂ _ (by decide), h4]
  obtain r8₂ : t₂.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₂ _ (by decide), h8]
  obtain hj' : 16 * (j + i) + 16 ≤ p.al := by omega_using [hj]
  obtain dA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega_using [hj])
  refine WP.mono (xorB_wp (s := t₂) (pb := .r4) (qb := .r11) (cb := .r8) (pd := 0) (qd := ohO) (cd := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r4₂, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (j + i)) (by omega_using [hj, fa]),
      Nat.mod_eq_of_lt (by omega_using [hj, fa])]; omega_using [hj, fa])
    (by rw [E₂.r11]; simp only [ohO]; omega_using [fw]) (by rw [r8₂, L.wN (by omega_using [hb])]; omega_using [fw, hb])
    (by rw [r4₂, eA, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E₂.perm.aad hj' (by omega_using [fa]))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [r8₂, eB, BitVec.add_zero]; exact E₂.perm.wC (by omega_using [hb]))) fun t₃ R₃ => ?_
  rw [r4₂, r8₂, E₂.r11, eA, eB, BitVec.add_zero, BitVec.add_zero] at R₃
  obtain fB : Frame [⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t₂.mem t₃.mem := by
    rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain dAW : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := (L.a_w' (by omega_using [hb])).sub_left dA
  obtain g₃ : ∀ r, r ∉ fillRegs → t₃.gpr r = t.gpr r := fun r hr => by
    simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2])]
  obtain r4₃ : t₃.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [R₃.gpr _ (by decide), r4₂]
  obtain r8₃ : t₃.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [R₃.gpr _ (by decide), r8₂]
  obtain r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (j + i + 1) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h6]
  obtain r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (c - i) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [r4₃, r8₃, r6₃, r5₃], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact (fr₂.mono (by simp)).trans (fB.mono (by simp))
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [blockAtMem_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by simp only [ohO, bufO]; omega_using [])) (by decide) (by omega_using [hb])), oh₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₃.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.of_disjoint dAW.symm)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by simp only [ohO, bufO]; omega_using [])) (by omega_using [hb]) (by decide))),
      blockAtMem_frame fr₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (L.a_w' (by decide)).sub_left dA), oh₂]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega_using []]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 256 + 16 * i + 16 = bufO + 16 * (i + 1) by simp only [bufO]; omega_using []]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega_using [hc])]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega_using [hc]), z_dec hi (by omega_using [hc])]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, ite_false,
      Proof.AesGcm.Arm.gpr_subFlags]
    exact g₃ r (by simp [fillRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])
  · simp only [sp_setReg, Proof.AesGcm.Arm.sp_subFlags]; rw [R₃.sp, R₂.sp, P₁.sp]
  · simp only [rd_setReg, Proof.AesGcm.Arm.rd_subFlags]; rw [R₃.rd, R₂.rd, P₁.rd]
  · simp only [wr_setReg, Proof.AesGcm.Arm.wr_subFlags]; rw [R₃.wr, R₂.wr, P₁.wr]

end VG.Proof.AesOcb.Arm
