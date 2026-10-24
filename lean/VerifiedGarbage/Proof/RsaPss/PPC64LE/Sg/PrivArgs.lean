module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS signing on PPC64LE: the private operation's arguments

Untrusted: everything here is checked by Lean. In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s twelve
stack arguments to its Parameter Save Area (`psa`: `p`, `p_len`, our stack
arguments 0 to 7, the rest of `scratch` and its length in words) and sets its
registers: `out`, `n`, `e` and `EM` (`AtPriv`), as RSAES-OAEP decryption does.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr stackArgAddr_fb saved_offs
  allocated_sp allocated_rd allocated_wr allocated_gpr allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_std wp_mov wp_li wp_add wp_addi wp_subi wp_addSp wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The base of the private operation's frame. -/
abbrev pb (s : State) : Addr := fb s - BitVec.ofNat 64 privBytes

/-- Its stack argument `i`, as `privArgs` writes it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r9
  | 1 => s.gpr .r10
  | 10 => Ss s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 12).toNat - 1024)
  | i + 2 => stackArg s i

theorem pb_eq (s : State) : pb s = s.sp - BitVec.ofNat 64 (frameBytes + privBytes) := by
  rw [pb, fb, BitVec.sub_sub, BitVec.ofNat_add]

theorem pb_base (s : State) :
    pb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  rw [pb, fb, ← Offset.sub_add_eq, ← BitVec.ofNat_add, ← Offset.sub_sub_eq,
    Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The region of `pb s + d` within the stack the function uses. -/
theorem pb_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes) :
    Region.Sub ⟨pb s + BitVec.ofNat 64 d, n⟩ (kS s) := by
  rw [pb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes; omega)

/-- In the private operation's frame, at the call, with `em` at `scratch`. -/
structure AtPriv (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = pb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr
  mem : Frame [kS s, SC Ss s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r7
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = off (Ss s) oEm
  r10 : t.gpr .r10 = s.gpr .r6
  psa : ∀ i < 12, t.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i

/-- The state of the copies of our stack arguments: `n` of them done. -/
structure Cp (s t₀ : State) (n : Nat) (t : State) : Prop where
  k : Keep [.r0] t₀ t
  mem : Frame [⟨pb s + BitVec.ofNat 64 112, 64⟩] t₀.mem t.mem
  got : ∀ j < n, t.mem.readW (pb s + BitVec.ofNat 64 (112 + 8 * j)) 64 = stackArg s j

theorem privArgs_eq : privArgs = ([.addSp .r12 0, .store .d .r17 .r12 96, .store .d .r18 .r12 104] : List Instr) ++
    ((List.range 8).flatMap fun j => [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (112 + 8 * j)]) ++
    ([.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP 12),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184, Impl.AesGcm.PPC64LE.mov .r3 .r16,
      Impl.AesGcm.PPC64LE.mov .r4 .r15, Impl.AesGcm.PPC64LE.mov .r5 .r20, Impl.AesGcm.PPC64LE.mov .r6 .r15,
      Impl.AesGcm.PPC64LE.mov .r7 .r21, Impl.AesGcm.PPC64LE.mov .r8 .r22, .addi .r9 .r14 oEm,
      Impl.AesGcm.PPC64LE.mov .r10 .r15] : List Instr) := rfl

theorem pb_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes) :
    (kS s).Contains (pb s + BitVec.ofNat 64 d) n := by
  rw [pb_base, Offset.add_add]
  exact Offset.contains_base _ (by unfold stackBytes; omega)
    (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes frameBytes privBytes at *; omega)

theorem sub_ofNat {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega)]; omega

/-- The private operation's frame. -/
abbrev PB (s : State) : Region := ⟨pb s, privBytes⟩

theorem pb_in (s : State) {d : Nat} (h : d + 8 ≤ privBytes) : (PB s).Contains (pb s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by unfold privBytes at h; omega)

theorem psa_in {s : State} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ privBytes) :
    InRegions (⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr) (pb s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold privBytes at h₂; omega) (by decide)⟩

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

omit P in
theorem PB_sub : Region.Sub (PB s) (kS s) := by
  have := pb_sub s (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this

/-- A load of our stack argument `j` through `b`, which holds `fb s - o`. -/
theorem wp_argS {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 13)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kS s, SC Ss s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by
    rw [hb, stackArgAddr_fb, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]) ?_
    (fun t' o' e => k t' o' ?_) hb0 ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

/-- The copies of our stack arguments 0 to `n - 1`. -/
theorem copies_ok {t₀ : State} (h12 : t₀.gpr .r12 = pb s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr) (hm : Frame [kS s, SC Ss s] s.mem t₀.mem) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j =>
      [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (112 + 8 * j)])) t₀ (Cp s t₀ n)
  | 0, _ => wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok h12 hrd hwr hm n (by omega)) fun t ⟨k, fm, got⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hmt : Frame [kS s, SC Ss s] s.mem t.mem := hm.trans (fm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kS s, List.mem_cons_self .., pb_sub s (by unfold frameBytes privBytes; omega)⟩)
    have hb : t.gpr .r12 = fb s - BitVec.ofNat 64 privBytes := by rw [k.get .r12, h12]
    refine wp_argS P (j := n) (o := privBytes) (by omega) hb (k.rd.trans hrd) hmt (fun t₁ o₁ e₁ => ?_)
      ⟨by unfold arg frameBytes privBytes; omega, by unfold arg frameBytes privBytes; omega⟩
    have hw : InRegions t₁.wr (pb s + BitVec.ofNat 64 (112 + 8 * n)) 8 := by
      rw [o₁.wr, k.wr, hwr]; exact psa_in (by omega) (by unfold privBytes; omega)
    refine wp_std (a := pb s + BitVec.ofNat 64 (112 + 8 * n)) (by rw [o₁.get .r12, hb]) hw (fun t₂ m₂ => wp_nil ?_)
      (by decide) ⟨by omega, by omega⟩
    have k₂ : Keep [.r0] t₀ t₂ := (k.trans (o₁.keep.trans m₂.keep)).mono
    refine ⟨k₂, ?_, fun j hj => ?_⟩
    · rw [m₂.mem, o₁.mem]
      exact fm.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [m₂.mem, o₁.mem]
      by_cases hj' : j < n
      · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), got j hj']
      · rw [show j = n by omega, Mem.readW_writeW_self64, e₁]

theorem privArgs_ok {t : State} (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) :
    WP isa (.block privArgs) (allocated privBytes t) (AtPriv s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have usp : (allocated privBytes t).sp = pb s := by rw [allocated_sp, hsp]
  have uwr : (allocated privBytes t).wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr := by
    rw [allocated_wr, h.sv.wr, frameR, hsp]; rfl
  have urd : (allocated privBytes t).rd = s.rd := by rw [allocated_rd, h.rd]
  have um : Frame [PB s] t.mem (allocated privBytes t).mem := by
    rw [allocated_mem]
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [hsp, show fb s - BitVec.ofNat 64 privBytes = pb s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
    exact pb_in s (by decide)
  have ug : (allocated privBytes t).gpr = t.gpr := rfl
  have hmS : ∀ {x : State}, Frame [PB s] t.mem x.mem → Frame [kS s, SC Ss s] s.mem x.mem := fun hx =>
    (h.mem.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨kS s, List.mem_cons_self .., kR_sub⟩
      · exact ⟨SC Ss s, by simp, fun _ h => h⟩).trans
      (hx.sub fun r hr => ⟨kS s, List.mem_cons_self .., by rw [List.mem_singleton.mp hr]; exact PB_sub⟩)
  rw [privArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [usp, BitVec.add_zero] at e₁
  refine wp_std (a := pb s + BitVec.ofNat 64 96) (by rw [e₁]) (by rw [o₁.wr, uwr]; exact psa_in (by decide) (by decide))
    fun u₂ m₂ => ?_
  refine wp_std (a := pb s + BitVec.ofNat 64 104) (by rw [m₂.gpr, e₁])
    (by rw [m₂.wr, o₁.wr, uwr]; exact psa_in (by decide) (by decide)) fun u₃ m₃ => wp_nil ?_
  have k₃ : Keep [.r12] (allocated privBytes t) u₃ := (o₁.keep.trans (m₂.keep.trans m₃.keep)).mono
  have f₃ : Frame [PB s] t.mem u₃.mem := by
    rw [m₃.mem, m₂.mem, o₁.mem]
    exact (um.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))).writeW (List.mem_singleton_self _) _
      (pb_in s (by decide))
  have r₃₉₆ : u₃.mem.readW (pb s + BitVec.ofNat 64 96) 64 = s.gpr .r9 := by
    rw [m₃.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₂.mem,
      Mem.readW_writeW_self64, o₁.get .r17, ug, Base.r17 h]
  have r₃₁₀₄ : u₃.mem.readW (pb s + BitVec.ofNat 64 104) 64 = s.gpr .r10 := by
    rw [m₃.mem, Mem.readW_writeW_self64, m₂.gpr, o₁.get .r18, ug, Base.r18 h]
  have g₃ : u₃.gpr .r12 = pb s := by rw [m₃.gpr, m₂.gpr, e₁]
  refine WP.mono (copies_ok P (t₀ := u₃) g₃ (by rw [k₃.rd, urd]) (by rw [k₃.wr, uwr]) (hmS f₃) 8 (Nat.le_refl 8))
    fun u₄ ⟨k₄, f₄, got⟩ => ?_
  have g₄ : u₄.gpr .r12 = pb s := by rw [k₄.get .r12, g₃]
  have w₄ : u₄.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr := by rw [k₄.wr, k₃.wr, uwr]
  have f₄' : Frame [PB s] t.mem u₄.mem := f₃.trans (f₄.sub fun r hr => ⟨PB s, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_add fun u₆ o₆ e₆ => ?_
  have g₆ : u₆.gpr .r12 = pb s := by rw [o₆.get .r12, o₅.get .r12, g₄]
  refine wp_std (a := pb s + BitVec.ofNat 64 176) (by rw [g₆]) (by rw [o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (by decide))
    fun u₇ m₇ => ?_
  have f₇ : Frame [PB s] t.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]; exact f₄'.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  have rd₇ : u₇.rd = s.rd := by rw [m₇.rd, o₆.rd, o₅.rd, k₄.rd, k₃.rd, urd]
  refine wp_argS P (j := 12) (o := privBytes) (by decide) (by rw [m₇.gpr, g₆]) rd₇ (hmS f₇) fun u₈ o₈ e₈ => ?_
  refine wp_subi fun u₉ o₉ e₉ => ?_
  refine wp_std (a := pb s + BitVec.ofNat 64 184) (by rw [o₉.get .r12, o₈.get .r12, m₇.gpr, g₆])
    (by rw [o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (by decide)) fun u₁₀ m₁₀ => ?_
  have f₁₀ : Frame [PB s] t.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]; exact f₇.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_mov fun u₁₆ o₁₆ e₁₆ => wp_addi fun u₁₇ o₁₇ e₁₇ =>
    wp_mov fun w ow ew => wp_nil ?_
  have K : Keep [.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (allocated privBytes t) w :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      (m₁₀.keep.trans (o₁₁.keep.trans (o₁₂.keep.trans (o₁₃.keep.trans (o₁₄.keep.trans (o₁₅.keep.trans
      (o₁₆.keep.trans (o₁₇.keep.trans ow.keep))))))))))))))).mono
  have kt : ∀ r ∉ [Reg.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], w.gpr r = t.gpr r :=
    fun r hr => by rw [K.gpr r hr]; rfl
  have K₁₀ : Keep [.r12, .r0, .r11] (allocated privBytes t) u₁₀ :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      m₁₀.keep))))))).mono
  have k10 : ∀ r ∉ [Reg.r12, .r0, .r11], u₁₀.gpr r = t.gpr r := fun r hr => by rw [K₁₀.gpr r hr]; rfl
  have hl : 1024 ≤ (stackArg s 12).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have v184 : u₉.gpr .r11 = psa s 11 := by rw [e₉, e₈]; exact sub_ofNat hl
  have v176 : u₆.gpr .r0 = psa s 10 := by
    rw [e₆, o₅.get .r14, e₅, k₄.get .r14, k₃.get .r14, ug, h.r14]; rfl
  have wm : w.mem = (u₇.mem.writeW (pb s + BitVec.ofNat 64 184) (psa s 11)) := by
    rw [ow.mem, o₁₇.mem, o₁₆.mem, o₁₅.mem, o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem, m₁₀.mem, o₉.mem, o₈.mem, v184]
  have m7 : u₇.mem = (u₄.mem.writeW (pb s + BitVec.ofNat 64 176) (psa s 10)) := by
    rw [m₇.mem, o₆.mem, o₅.mem, v176]
  have fw : Frame [PB s] t.mem w.mem := by
    rw [ow.mem, o₁₇.mem, o₁₆.mem, o₁₅.mem, o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem]; exact f₁₀
  have sl : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [PB s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r :=
    fun hd r hr => by
      rw [List.mem_singleton.mp hr]
      have h := Offset.disjoint_below_above (fb s) (m := privBytes) (a := 0) (l := frameBytes) (by decide)
      rw [BitVec.add_zero] at h
      exact (h.sub_right (Offset.sub_base _ hd)).symm
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes → b + 8 ≤ privBytes →
      Mem.Sep (pb s + BitVec.ofNat 64 a) (64 / 8) (pb s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    Offset.sep _ h (by unfold privBytes at ha; omega) (by unfold privBytes at hb; omega)
  have hpsa : ∀ i < 12, w.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i := by
    intro i hi
    rw [wm]
    by_cases h11 : i = 11
    · subst h11; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega) (by unfold privBytes; omega) (by decide)) (by decide), m7]
    by_cases h10 : i = 10
    · subst h10; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega) (by unfold privBytes; omega) (by decide)) (by decide)]
    have fr4 : ∀ {d : Nat}, d + 8 ≤ 112 → u₄.mem.readW (pb s + BitVec.ofNat 64 d) 64 =
        u₃.mem.readW (pb s + BitVec.ofNat 64 d) 64 := fun hd =>
      f₄.readW (r := ⟨pb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl hd) (by omega) (by decide)) (by decide)
    by_cases h0 : i = 0
    · subst h0; rw [fr4 (by decide)]; exact r₃₉₆
    by_cases h1 : i = 1
    · subst h1; rw [fr4 (by decide)]; exact r₃₁₀₄
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
      rw [show 96 + 8 * (j + 2) = 112 + 8 * j by omega, got j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hemw : Spec.Rsa.bytesAt w.mem (off (Ss s) oEm) (kk s) = em := by
    rw [← hem]
    have hk2 : kk s ≤ 1024 := P.k2
    have hR : Region.Sub ⟨off (Ss s) oEm, kk s⟩ (scR s) := fun a ha =>
      sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by unfold oEm oRsa; omega) a ha)
    have hd : (PB s).Disjoint ⟨off (Ss s) oEm, kk s⟩ := (P.ks.sub_left PB_sub).sub_right hR
    exact VG.Proof.RsaOaep.PPC64LE.bytes_entry (A := PB s) (B := PB s)
      (fw.mono fun r hr => by simp at hr ⊢; exact hr) hd hd
      (by have := (fits P).wS; unfold oEm oRsa at *; omega)
  refine ⟨by rw [K.sp, usp], by rw [K.rd, urd], by rw [K.wr, uwr], hmS fw, hemw,
    h.sv.sv.frame fw fun p hp r hr => sl (by have := saved_offs p hp; unfold oLr frameBytes at *; omega) r hr,
    by rw [fw.readW (Region.contains_self _ _) (sl (by decide)) (by decide)]; exact h.sv.ls,
    fun r hr => by rw [kt r (by revert r; decide)]; exact h.sv.hi r hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpsa⟩
  · rw [ow.get .r3, o₁₇.get .r3, o₁₆.get .r3, o₁₅.get .r3, o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, e₁₁,
      k10 .r16 (by decide), Base.r16 h]
  · rw [ow.get .r4, o₁₇.get .r4, o₁₆.get .r4, o₁₅.get .r4, o₁₄.get .r4, o₁₃.get .r4, e₁₂, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r5, o₁₇.get .r5, o₁₆.get .r5, o₁₅.get .r5, o₁₄.get .r5, e₁₃, o₁₂.get .r20, o₁₁.get .r20,
      k10 .r20 (by decide), Base.r20 h]
  · rw [ow.get .r6, o₁₇.get .r6, o₁₆.get .r6, o₁₅.get .r6, e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r7, o₁₇.get .r7, o₁₆.get .r7, e₁₅, o₁₄.get .r21, o₁₃.get .r21, o₁₂.get .r21, o₁₁.get .r21,
      k10 .r21 (by decide), Base.r21 h]
  · rw [ow.get .r8, o₁₇.get .r8, e₁₆, o₁₅.get .r22, o₁₄.get .r22, o₁₃.get .r22, o₁₂.get .r22, o₁₁.get .r22,
      k10 .r22 (by decide), Base.r22 h]
  · rw [ow.get .r9, e₁₇, o₁₆.get .r14, o₁₅.get .r14, o₁₄.get .r14, o₁₃.get .r14, o₁₂.get .r14, o₁₁.get .r14,
      k10 .r14 (by decide), h.r14]
  · rw [ew, o₁₇.get .r15, o₁₆.get .r15, o₁₅.get .r15, o₁₄.get .r15, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]

end

end VG.Proof.RsaPss.PPC64LE.Sg
