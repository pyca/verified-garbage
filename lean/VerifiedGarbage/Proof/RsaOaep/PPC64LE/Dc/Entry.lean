module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Frame

/-!
# RSAES-OAEP decryption on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave our caller's
registers and return address in their slots, `r14`–`r19` holding `scratch`,
`k`, `out`, `msg_len`, the label and its length, and `r6`–`r10` and `r12` the
entry's `n`, `n_len`, `e`, `e_len`, `p` and the frame's base (`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_ld wp_mov wp_nil)

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 15) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-- After the saves and the prologue. -/
structure Entered (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  mem : Frame [kR s] s.mem t.mem
  r12 : t.gpr .r12 = fb s
  r14 : t.gpr .r14 = Sd s
  r15 : t.gpr .r15 = s.gpr .r7
  r16 : t.gpr .r16 = s.gpr .r3
  r17 : t.gpr .r17 = s.gpr .r5
  r18 : t.gpr .r18 = stackArg s 9
  r19 : t.gpr .r19 = stackArg s 10
  args : ∀ r ∈ [Reg.r6, .r7, .r8, .r9, .r10, .r20, .r21, .r22, .r23], t.gpr r = s.gpr r

section
variable {s : State} (P : PreD s)
include P

omit P in
theorem toD {m m' : Mem} (h : Frame [kR s] m m') : Frame [kD s] m m' :=
  h.sub fun r hr => ⟨kD s, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact kR_sub⟩

/-- A load of our stack argument `j` through `r`, which holds `fb s + o`. -/
theorem wp_argD {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 15)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kD s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by
    rw [hb, stackArgAddr_fb, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]) ?_
    (fun t' o' e => k t' o' ?_) hb0 ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

theorem entry_ok : WP isa (.block (save ++ Dec.prologue)) (allocated frameBytes s) (Entered s) := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (allocated_sp _ _) (by rw [allocated_wr, frameR_eq]) hm0 (fun r _ => by rw [allocated_gpr])
    (allocated_lr _ _) fun v kv h12 hm hsv hls => ?_
  have hrd : v.rd = s.rd := kv.rd.trans (allocated_rd _ _)
  have h12' : v.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [h12, BitVec.sub_zero]
  simp only [Dec.prologue]
  refine wp_argD P (j := 13) (o := 0) (by decide) h12' hrd (toD hm) fun v₁ o₁ e₁ => ?_
  refine wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ => ?_
  have k₄ : Only [.r14, .r15, .r16, .r17] v v₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have g4 : v₄.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [k₄.get .r12]; exact h12'
  have m4 : Frame [kR s] s.mem v₄.mem := by rw [k₄.mem]; exact hm
  refine wp_argD P (j := 9) (o := 0) (by decide) g4 (k₄.rd.trans hrd) (toD m4) fun v₅ o₅ e₅ => ?_
  have g5 : v₅.gpr .r12 = fb s - BitVec.ofNat 64 0 := by rw [o₅.get .r12]; exact g4
  have m5 : Frame [kR s] s.mem v₅.mem := by rw [o₅.mem]; exact m4
  refine wp_argD P (j := 10) (o := 0) (by decide) g5 (o₅.rd.trans (k₄.rd.trans hrd)) (toD m5) fun w ow ew => wp_nil ?_
  have kw : Only [.r14, .r15, .r16, .r17, .r18, .r19] v w := (k₄.trans (o₅.trans ow)).mono
  have gs : ∀ r ∉ [Reg.r12, .r0], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r hr, allocated_gpr]
  refine ⟨⟨by rw [kw.sp, kv.sp, allocated_sp], by rw [kw.wr, kv.wr, allocated_wr, frameR_eq],
    fun r hr => by rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)],
    by rw [kw.mem]; exact hsv, by rw [kw.mem]; exact hls⟩, kw.rd.trans hrd, by rw [kw.mem]; exact hm,
    by rw [kw.get .r12]; exact h12, ?_, ?_, ?_, ?_, ?_, ew, fun r hr => ?_⟩
  · rw [ow.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, o₂.get .r14]; exact e₁
  · rw [ow.get .r15, o₅.get .r15, o₄.get .r15, o₃.get .r15, e₂, o₁.get .r7, gs .r7 (by decide)]
  · rw [ow.get .r16, o₅.get .r16, o₄.get .r16, e₃, o₂.get .r3, o₁.get .r3, gs .r3 (by decide)]
  · rw [ow.get .r17, o₅.get .r17, e₄, o₃.get .r5, o₂.get .r5, o₁.get .r5, gs .r5 (by decide)]
  · rw [ow.get .r18]; exact e₅
  · rw [kw.gpr r (by revert r; decide), gs r (by revert r; decide)]

end

end VG.Proof.RsaOaep.PPC64LE.Dec
