module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Pre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

/-!
# RSAES-OAEP decryption on RISC-V: the private operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/PrivArgs.lean`, `Dc/PrivPre.lean`,
`Dc/PrivCall.lean`), with the call as in RSASSA-PKCS1-v1_5 signing
(`Proof/RsaPkcs1Sig/RISCV64/Sign/Call.lean`). In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s
twelve stack arguments at its stack pointer (`psa`: `p`, our stack
arguments 0 to 8, the rest of `scratch` and its length in words) and sets
its registers (`AtPriv`); the call is narrowed to `n`, `e`, the ciphertext,
the private key and its stack arguments (`callRd`), and `EM`'s place and the
rest of `scratch` (`callWr`), where its precondition holds (`preP_at`);
`privF_ok`: it leaves `EM` (or zeros) at `scratch` and the outcome's code
(`rcOf`) in `s4`, and the state `Base` needs for the decoding
(`AfterPriv`), with memory from after the call as the entry's.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes oRsa saved)
open VG.Impl.RsaOaep.RISCV64.Dec (privBytes privArgs copyArg privCall)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr Saves stackArgAddr_eq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_li wp_add wp_addi wp_subi wp_sll wp_srl
  wp_addSp wp_nil)

/-! ## Addresses in the stack the function uses -/

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 stackBytes

/-- The base of the private operation's frame. -/
abbrev pb (s : State) : Addr := fb s - BitVec.ofNat 64 privBytes

/-- The private operation's frame. -/
abbrev PB (s : State) : Region := ⟨pb s, privBytes⟩

/-- Its stack argument `i`, as `privArgs` writes it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .a7
  | 10 => Sd s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)
  | i + 1 => stackArg s i

section
variable {s : State} (P : PreD s)
include P

theorem kb_add {d : Nat} (hd : d ≤ stackBytes) : kb s + BitVec.ofNat 64 d = s.sp - BitVec.ofNat 64 (stackBytes - d) := by
  have := P.sp1
  apply BitVec.eq_of_toNat_eq
  simp only [kb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq] at *
  omega

theorem fb_kb : fb s = kb s + BitVec.ofNat 64 3344 := by rw [kb_add P (by decide)]; rfl

theorem pb_kb : pb s = kb s + BitVec.ofNat 64 3248 := by
  rw [kb_add P (by decide)]
  have := P.sp1
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq, frameBytes, privBytes] at *
  omega

theorem kb_toNat : (kb s).toNat = s.sp.toNat - stackBytes := by
  have := P.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq] at *
  omega

omit P in
/-- A range at `kb s + d` in the stack the function uses. -/
theorem kb_sub {d n : Nat} (h : d + n ≤ stackBytes) : Region.Sub ⟨kb s + BitVec.ofNat 64 d, n⟩ (kD s) :=
  Offset.sub_base _ h

omit P in theorem kb_contains {d n : Nat} (h : d + n ≤ stackBytes) : (kD s).Contains (kb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by rw [stackBytes_eq] at h; omega)

theorem pb_al : (pb s).toNat % 16 = 0 := by
  have := P.sp1; have := P.spal
  simp only [pb, fb, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq, frameBytes, privBytes] at *
  omega

theorem pb_off_al {d : Nat} (hd : d % 8 = 0) : (pb s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := P.sp1; have := P.spal; have := s.sp.isLt
  simp only [pb, fb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq, frameBytes,
    privBytes] at *
  omega

/-- A range of the private operation's frame, in the stack the function uses. -/
theorem pb_sub {d n : Nat} (h : d + n ≤ privBytes) : Region.Sub ⟨pb s + BitVec.ofNat 64 d, n⟩ (kD s) := by
  rw [pb_kb P, Offset.add_add]; exact kb_sub (by unfold privBytes at h; rw [stackBytes_eq]; omega)

theorem PB_sub : Region.Sub (PB s) (kD s) := by
  have := pb_sub P (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this

theorem fr_subD : Region.Sub (fr s) (kD s) := by
  show Region.Sub ⟨fb s, frameBytes⟩ _
  rw [fb_kb P]; exact kb_sub (by decide)

omit P in theorem kR_subD : Region.Sub (kR s) (kD s) := kR_sub

end

/-! ## The arguments -/

/-- In the private operation's frame, at the call. -/
structure AtPriv (s t : State) : Prop where
  sp : t.sp = pb s
  rd : t.rd = s.rd
  wr : t.wr = PB s :: fr s :: s.wr
  mem : Frame [kD s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  s0 : t.gpr .s0 = Sd s
  s1 : t.gpr .s1 = s.gpr .a4
  s2 : t.gpr .s2 = s.gpr .a0
  s3 : t.gpr .s3 = s.gpr .a2
  a0 : t.gpr .a0 = Sd s
  a1 : t.gpr .a1 = s.gpr .a4
  a2 : t.gpr .a2 = s.gpr .a3
  a3 : t.gpr .a3 = s.gpr .a4
  a4 : t.gpr .a4 = s.gpr .a5
  a5 : t.gpr .a5 = s.gpr .a6
  a6 : t.gpr .a6 = stackArg s 11
  a7 : t.gpr .a7 = s.gpr .a4
  psa : ∀ i < 12, t.mem.readW (pb s + BitVec.ofNat 64 (8 * i)) 64 = psa s i

/-- After the first `n` copies of our stack arguments, from `w`. -/
structure Cp (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [PB s] w.mem t.mem
  z : t.mem.readW (pb s + BitVec.ofNat 64 0) 64 = w.mem.readW (pb s + BitVec.ofNat 64 0) 64
  got : ∀ j < n, t.mem.readW (pb s + BitVec.ofNat 64 (8 * (j + 1))) 64 = stackArg s j

section
variable {s : State} (P : PreD s)
include P

/-- A load of our stack argument `j` through `t6`, with memory changed only
in the stack the function uses. -/
theorem wp_argD {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 15)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kD s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

omit P in theorem pb_in {d : Nat} (h : d + 8 ≤ privBytes) {rs : List Region} :
    InRegions (PB s :: rs) (pb s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold privBytes at h; omega)⟩

theorem copy_step {w : State} (hw0 : w.gpr .t0 = pb s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB s :: fr s :: s.wr) (hm : Frame [kD s] s.mem w.mem) {n : Nat} (hn : n < 9) {t : State}
    (hc : Cp s w n t) : WP isa (.block (copyArg n)) t (Cp s w (n + 1)) := by
  have hmt : Frame [kD s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  unfold copyArg
  refine wp_argD P (j := n) (by omega) (by rw [hc.keep.get .t6, hw6]) (hc.keep.rd.trans hrd) hmt
    (fun t₁ o₁ e₁ => ?_) (by omega)
  refine wp_sd (a := pb s + BitVec.ofNat 64 (8 * (n + 1))) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (pb_off_al P (by omega))
    (by rw [o₁.wr, hc.keep.wr, hwr]; exact pb_in (by unfold privBytes; omega)) (fun t₂ m₂ => wp_nil ?_)
    (by omega)
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, ?_, fun j hj => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (pb s) (d := 8 * (n + 1)) (n := 8)
      (k := privBytes) (by unfold privBytes; omega) (by omega))
  · rw [m₂.mem, o₁.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hc.z
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.got j hj
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {w : State} (hw0 : w.gpr .t0 = pb s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB s :: fr s :: s.wr) (hm : Frame [kD s] s.mem w.mem) :
    WP isa (.block ((List.range 9).flatMap copyArg)) w (Cp s w 9) :=
  wp_range_flatMap (M := isa) (Cp s w) (fun _ _ hn hc => copy_step P hw0 hw6 hrd hwr hm hn hc) 9
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩


/-- Our stack arguments' base, from the private operation's frame. -/
theorem pb_top : pb s + BitVec.ofNat 64 (privBytes + frameBytes) = s.sp := by
  have := P.sp1
  apply BitVec.eq_of_toNat_eq
  simp only [pb, fb, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq, frameBytes,
    privBytes] at *
  omega

/-- The private operation's part of `scratch`, in words. -/
theorem sl_sub : stackArg s 14 - BitVec.ofNat 64 1024 = BitVec.ofNat 64 ((stackArg s 14).toNat - 1024) := by
  have := scLen P; unfold oRsa at this
  have := (stackArg s 14).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Our frame's slots, apart from the private operation's frame. -/
theorem slots_PB : Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes -
    Proof.RsaOaep.RISCV64.oSv⟩ (PB s) := by
  show Region.Disjoint _ ⟨pb s, privBytes⟩
  rw [fb_kb P, Offset.add_add, pb_kb P]
  exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem privArgs_ok {t : State} (E : Entered s t) :
    WP isa (.block privArgs) (allocd privBytes t) (AtPriv s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have usp : (allocd privBytes t).sp = pb s := by show t.sp - _ = _; rw [hsp]
  have uwr : (allocd privBytes t).wr = PB s :: fr s :: s.wr := by
    show (⟨t.sp - _, _⟩ : Region) :: t.wr = _; rw [hsp, E.sv.wr]
  have urd : (allocd privBytes t).rd = s.rd := E.rd
  have hmD : Frame [kD s] s.mem t.mem := E.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, kR_subD⟩
  have inD : ∀ {d : Nat}, d + 8 ≤ privBytes → (kD s).Contains (pb s + BitVec.ofNat 64 d) 8 := fun {d} hd => by
    rw [pb_kb P, Offset.add_add]; exact kb_contains (by unfold privBytes at hd; rw [stackBytes_eq]; omega)
  have inPB : ∀ {d : Nat}, d + 8 ≤ privBytes → (PB s).Contains (pb s + BitVec.ofNat 64 d) 8 := fun {d} hd =>
    Offset.contains_base _ hd (by unfold privBytes at hd; omega)
  unfold privArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (imm := 0) (fun w₁ o₁ e₁ => wp_addSp (imm := privBytes + frameBytes) (fun w₂ o₂ e₂ => ?_)
    (by decide)) (by decide)
  rw [usp] at e₁
  have O₂ : Only [.t0, .t6] (allocd privBytes t) w₂ := o₁.trans o₂
  have g0 : w₂.gpr .t0 = pb s := by rw [o₂.get .t0, e₁, BitVec.add_zero]
  have g6 : w₂.gpr .t6 = s.sp := by rw [e₂, o₁.sp, usp, pb_top P]
  refine wp_sd (a := pb s + BitVec.ofNat 64 0) (by rw [g0]) (pb_off_al P (by decide))
    (by rw [O₂.wr, uwr]; exact pb_in (by decide)) (fun w₃ m₃ => ?_) (by decide)
  have hw0 : w₃.gpr .t0 = pb s := by rw [m₃.gpr]; exact g0
  have hw6 : w₃.gpr .t6 = s.sp := by rw [m₃.gpr]; exact g6
  have hrd : w₃.rd = s.rd := m₃.rd.trans (O₂.rd.trans urd)
  have hwr : w₃.wr = PB s :: fr s :: s.wr := m₃.wr.trans (O₂.wr.trans uwr)
  have hm₃ : Frame [kD s] s.mem w₃.mem := by
    rw [m₃.mem, O₂.mem]; exact hmD.writeW (List.mem_singleton_self _) _ (inD (by decide))
  have pb₃ : Frame [PB s] t.mem w₃.mem := by
    rw [m₃.mem, O₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (inPB (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok P hw0 hw6 hrd hwr hm₃) fun v hc => ?_
  have v0 : v.gpr .t0 = pb s := by rw [hc.keep.get .t0, hw0]
  have v6 : v.gpr .t6 = s.sp := by rw [hc.keep.get .t6, hw6]
  have vrd : v.rd = s.rd := hc.keep.rd.trans hrd
  have vwr : v.wr = PB s :: fr s :: s.wr := hc.keep.wr.trans hwr
  have hmv : Frame [kD s] s.mem v.mem := hm₃.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
  have gv : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .a3, .a5, .a6, .a7], v.gpr r = t.gpr r := fun r hr => by
    rw [hc.keep.gpr r (by revert r; decide), m₃.gpr, O₂.gpr r (by revert r; decide)]; rfl
  refine wp_li (imm := 1024) (by decide) fun x₁ o₁ e₁ => wp_sll (sh := 3) (fun x₂ o₂ e₂ =>
    wp_add fun x₃ o₃ e₃ => ?_) (by decide)
  have O₃ : Only [.t1] v x₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_sd (a := pb s + BitVec.ofNat 64 80) (by rw [O₃.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [O₃.wr, vwr]; exact pb_in (by decide)) (fun x₄ m₄ => ?_) (by decide)
  have hm₄ : Frame [kD s] s.mem x₄.mem := by
    rw [m₄.mem, O₃.mem]; exact hmv.writeW (List.mem_singleton_self _) _ (inD (by decide))
  refine wp_argD P (j := 14) (by decide) (by rw [m₄.gpr, O₃.get .t6, v6]) (m₄.rd.trans (O₃.rd.trans vrd)) hm₄
    (fun x₅ o₅ e₅ => wp_subi (imm := 1024) (fun x₆ o₆ e₆ => ?_) (by decide))
  have K₆ : Kept [.t1] v x₆ := (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans o₆.keep))).mono
  refine wp_sd (a := pb s + BitVec.ofNat 64 88) (by rw [K₆.get .t0, v0]) (pb_off_al P (by decide))
    (by rw [K₆.wr, vwr]; exact pb_in (by decide)) (fun x₇ m₇ => ?_) (by decide)
  have K₇ : Kept [.t1] v x₇ := (K₆.trans m₇.keep).mono
  have hm₇ : Frame [kD s] s.mem x₇.mem := by
    rw [m₇.mem, (o₅.trans o₆).mem]; exact hm₄.writeW (List.mem_singleton_self _) _ (inD (by decide))
  refine wp_mov fun x₈ o₈ e₈ => wp_mov fun x₉ o₉ e₉ => wp_mov fun x₁₀ o₁₀ e₁₀ => wp_mov fun x₁₁ o₁₁ e₁₁ => ?_
  have O₁₁ : Only [.a2, .a3, .a4, .a5] x₇ x₁₁ := (o₈.trans (o₉.trans (o₁₀.trans o₁₁))).mono
  refine wp_argD P (j := 11) (by decide) (by rw [O₁₁.get .t6, K₇.get .t6, v6])
    (O₁₁.rd.trans (K₇.rd.trans vrd)) (by rw [O₁₁.mem]; exact hm₇) fun x₁₂ o₁₂ e₁₂ => ?_
  refine wp_mov fun x₁₃ o₁₃ e₁₃ => wp_addi (imm := Impl.RsaOaep.RISCV64.oEm) (fun x₁₄ o₁₄ e₁₄ =>
    wp_mov fun x₁₅ o₁₅ e₁₅ => wp_nil ?_) (by decide)
  have T : Only [.a2, .a3, .a4, .a5, .a6, .a7, .a0, .a1] x₇ x₁₅ :=
    (O₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))).mono
  have K : Kept [.t1, .a2, .a3, .a4, .a5, .a6, .a7, .a0, .a1] v x₁₅ := (K₇.trans T.keep).mono
  have ks : ∀ r ∈ [Reg.s0, .s1, .s2, .s3], x₁₅.gpr r = t.gpr r := fun r hr => by
    rw [K.gpr r (by revert r; decide), gv r (by revert r; decide)]
  have hpb : Frame [PB s] t.mem x₁₅.mem := by
    rw [T.mem, m₇.mem, (o₅.trans o₆).mem, m₄.mem, O₃.mem]
    exact ((pb₃.trans hc.mem).writeW (List.mem_singleton_self _) _ (inPB (by decide))).writeW
      (List.mem_singleton_self _) _ (inPB (by decide))
  have hfm : x₁₅.mem = (v.mem.writeW (pb s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb s + BitVec.ofNat 64 88) (x₆.gpr .t1) := by
    rw [T.mem, m₇.mem, (o₅.trans o₆).mem, m₄.mem, O₃.mem]
  have t80 : x₃.gpr .t1 = psa s 10 := by
    rw [e₃, o₂.get .s0, o₁.get .s0, e₂, e₁, gv .s0 (by decide), E.s0]
    show _ = Sd s + BitVec.ofNat 64 8192
    congr 1
  have t88 : x₆.gpr .t1 = psa s 11 := by rw [e₆, e₅]; exact sl_sub P
  have r2 : ∀ d, d + 8 ≤ 80 → ((v.mem.writeW (pb s + BitVec.ofNat 64 80) (x₃.gpr .t1)).writeW
      (pb s + BitVec.ofNat 64 88) (x₆.gpr .t1)).readW (pb s + BitVec.ofNat 64 d) 64 =
      v.mem.readW (pb s + BitVec.ofNat 64 d) 64 := fun d hd => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  have z0 : v.mem.readW (pb s + BitVec.ofNat 64 0) 64 = psa s 0 := by
    rw [hc.z, m₃.mem, Mem.readW_writeW_self64, O₂.get .a7]; exact E.args .a7 (by decide)
  have hg := hc.got
  refine {
    sp := K.sp.trans (hc.keep.sp.trans (m₃.sp.trans (O₂.sp.trans usp)))
    rd := K.rd.trans vrd
    wr := K.wr.trans vwr
    mem := hmD.trans (hpb.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, PB_sub P⟩)
    sv := E.sv.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
        (fun p hp => by
          have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega)
        hpb
      fun r hr => by rw [List.mem_singleton.mp hr]; exact slots_PB P
    s0 := (ks .s0 (by decide)).trans E.s0
    s1 := (ks .s1 (by decide)).trans E.s1
    s2 := (ks .s2 (by decide)).trans E.s2
    s3 := (ks .s3 (by decide)).trans E.s3
    a0 := by
      rw [o₁₅.get .a0, e₁₄, o₁₃.get .s0, o₁₂.get .s0, O₁₁.get .s0, K₇.get .s0, gv .s0 (by decide), E.s0]
      exact BitVec.add_zero _
    a1 := by
      rw [e₁₅, o₁₄.get .s1, o₁₃.get .s1, o₁₂.get .s1, O₁₁.get .s1, K₇.get .s1, gv .s1 (by decide), E.s1]
    a2 := by
      rw [(o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))))).get .a2, e₈,
        K₇.get .a3, gv .a3 (by decide)]
      exact E.args .a3 (by decide)
    a3 := by
      rw [(o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))).get .a3, e₉, o₈.get .s1, K₇.get .s1,
        gv .s1 (by decide), E.s1]
    a4 := by
      rw [(o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))).get .a4, e₁₀, o₉.get .a5, o₈.get .a5,
        K₇.get .a5, gv .a5 (by decide)]
      exact E.args .a5 (by decide)
    a5 := by
      rw [(o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))).get .a5, e₁₁, o₁₀.get .a6, o₉.get .a6, o₈.get .a6,
        K₇.get .a6, gv .a6 (by decide)]
      exact E.args .a6 (by decide)
    a6 := by rw [(o₁₃.trans (o₁₄.trans o₁₅)).get .a6, e₁₂]
    a7 := by
      rw [(o₁₄.trans o₁₅).get .a7, e₁₃, o₁₂.get .s1, O₁₁.get .s1, K₇.get .s1, gv .s1 (by decide), E.s1]
    psa := fun i hi => by
      rw [hfm]
      match i, hi with
      | 0, _ => exact (r2 _ (by decide)).trans z0
      | 1, _ => exact (r2 _ (by decide)).trans (hg 0 (by decide))
      | 2, _ => exact (r2 _ (by decide)).trans (hg 1 (by decide))
      | 3, _ => exact (r2 _ (by decide)).trans (hg 2 (by decide))
      | 4, _ => exact (r2 _ (by decide)).trans (hg 3 (by decide))
      | 5, _ => exact (r2 _ (by decide)).trans (hg 4 (by decide))
      | 6, _ => exact (r2 _ (by decide)).trans (hg 5 (by decide))
      | 7, _ => exact (r2 _ (by decide)).trans (hg 6 (by decide))
      | 8, _ => exact (r2 _ (by decide)).trans (hg 7 (by decide))
      | 9, _ => exact (r2 _ (by decide)).trans (hg 8 (by decide))
      | 10, _ =>
        show Mem.readW _ (pb s + BitVec.ofNat 64 80) 64 = _
        rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_self64]
        exact t80
      | 11, _ =>
        show Mem.readW _ (pb s + BitVec.ofNat 64 88) 64 = _
        rw [Mem.readW_writeW_self64]
        exact t88 }

end


/-! ## The call -/

/-- `EM`'s place, the ciphertext as the call reads it, and the private
operation's part of `scratch`. -/
abbrev emR (s : State) : Region := ⟨Sd s, kk s⟩
abbrev iD (s : State) : Region := ⟨stackArg s 11, kk s⟩
abbrev rsR (s : State) : Region := ⟨Sd s + BitVec.ofNat 64 oRsa, ((stackArg s 14).toNat - 1024) * 8⟩

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, iD s, pR s, qR s, dpR s, dqR s, qiR s, PB s]

abbrev callWr (s : State) : List Region := [emR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} (A : AtPriv s t) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, show (callE s t).sp = pb s from A.sp]
  exact A.psa i hi

/-- The private operation's frame, below its stack arguments. -/
abbrev pkR (s : State) : Region := ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩

section
variable {s : State} (P : PreD s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) := by
  have := P.hs; have := P.k2; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at *
  exact Region.sub_prefix (by unfold kk; omega)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := scLen P
  exact Offset.sub_base _ (by unfold oRsa at *; omega)

theorem i_sub : Region.Sub (iD s) (ctR s) := by
  have := P.oc
  exact Region.sub_prefix (by unfold kk; omega)

omit P in
theorem pk_sub : Region.Sub (pkR s) (kD s) := by
  have := Offset.sub_base (kb s) (d := 0) (n := Impl.Rsa.RISCV64.Priv.frameBytes) (k := stackBytes) (by decide)
  rwa [BitVec.add_zero] at this

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have := P.wsc; have := P.k2; have := scLen P
  exact Offset.base_disjoint _ (by unfold kk oRsa at *; omega) (by unfold oRsa at *; omega)

theorem pk_PB : (pkR s).Disjoint (PB s) := by
  show Region.Disjoint _ ⟨pb s, privBytes⟩
  rw [pb_kb P]
  exact Offset.base_disjoint _ (by decide) (by unfold privBytes; decide)

theorem preP_at {t : State} (A : AtPriv s t) : Rsa.RISCV64.Priv.PreP (callE s t) := by
  have hk := P.k2
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = pb s := A.sp
  have g0 : (callE s t).gpr .a0 = Sd s := (callE_gpr s t).trans A.a0
  have g1 : (callE s t).gpr .a1 = s.gpr .a4 := (callE_gpr s t).trans A.a1
  have g2 : (callE s t).gpr .a2 = s.gpr .a3 := (callE_gpr s t).trans A.a2
  have g3 : (callE s t).gpr .a3 = s.gpr .a4 := (callE_gpr s t).trans A.a3
  have g4 : (callE s t).gpr .a4 = s.gpr .a5 := (callE_gpr s t).trans A.a4
  have g5 : (callE s t).gpr .a5 = s.gpr .a6 := (callE_gpr s t).trans A.a5
  have g6 : (callE s t).gpr .a6 = stackArg s 11 := (callE_gpr s t).trans A.a6
  have g7 : (callE s t).gpr .a7 = s.gpr .a4 := (callE_gpr s t).trans A.a7
  have s0 : stackArg (callE s t) 0 = s.gpr .a7 := sa 0 (by decide)
  have s1 : stackArg (callE s t) 1 = stackArg s 0 := sa 1 (by decide)
  have s2 : stackArg (callE s t) 2 = stackArg s 1 := sa 2 (by decide)
  have s3 : stackArg (callE s t) 3 = stackArg s 2 := sa 3 (by decide)
  have s4 : stackArg (callE s t) 4 = stackArg s 3 := sa 4 (by decide)
  have s5 : stackArg (callE s t) 5 = stackArg s 4 := sa 5 (by decide)
  have s6 : stackArg (callE s t) 6 = stackArg s 5 := sa 6 (by decide)
  have s7 : stackArg (callE s t) 7 = stackArg s 6 := sa 7 (by decide)
  have s8 : stackArg (callE s t) 8 = stackArg s 7 := sa 8 (by decide)
  have s9 : stackArg (callE s t) 9 = stackArg s 8 := sa 9 (by decide)
  have s10 : stackArg (callE s t) 10 = Sd s + BitVec.ofNat 64 oRsa := sa 10 (by decide)
  have s11 : stackArg (callE s t) 11 = BitVec.ofNat 64 ((stackArg s 14).toNat - 1024) := sa 11 (by decide)
  have hl : 1024 ≤ (stackArg s 14).toNat := by have := scLen P; unfold oRsa at this; omega
  have l11 : (stackArg (callE s t) 11).toNat = (stackArg s 14).toNat - 1024 := by
    rw [s11, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega)
  have hO : Rsa.RISCV64.Priv.oR (callE s t) = emR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1]
  have hN : Rsa.RISCV64.Priv.nR (callE s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE s t) = iD s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7]
  have hP : Rsa.RISCV64.Priv.pR (callE s t) = pR s := by simp only [Rsa.RISCV64.Priv.pR, s0, s1]
  have hQ : Rsa.RISCV64.Priv.qR (callE s t) = qR s := by simp only [Rsa.RISCV64.Priv.qR, s2, s3]
  have hDP : Rsa.RISCV64.Priv.dpR (callE s t) = dpR s := by simp only [Rsa.RISCV64.Priv.dpR, s4, s5]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE s t) = dqR s := by simp only [Rsa.RISCV64.Priv.dqR, s6, s7]
  have hQI : Rsa.RISCV64.Priv.qiR (callE s t) = qiR s := by simp only [Rsa.RISCV64.Priv.qiR, s8, s9]
  have hS : Rsa.RISCV64.Priv.sR (callE s t) = rsR s := by simp only [Rsa.RISCV64.Priv.sR, s10, l11]
  have hA : Rsa.RISCV64.Priv.aR (callE s t) = PB s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]; rfl
  have hK : Rsa.RISCV64.Priv.kR (callE s t) = pkR s := by
    show Region.mk ((callE s t).sp - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
    rw [hsp, pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)
  have es := em_sub P
  have rs := rs_sub P
  have is := i_sub P
  have ks : Region.Sub (pkR s) (kD s) := pk_sub
  have pbs := PB_sub P
  have pt := kb_toNat P
  have spl := s.sp.isLt
  have st := P.sp1
  rw [stackBytes_eq] at pt st
  have pbt : (pb s).toNat = s.sp.toNat - 224 := by
    have := pb_kb P
    rw [this, Offset.toNat_add_ofNat, kb_toNat P, stackBytes_eq]; omega
  have e13 : (Sd s).toNat = (stackArg s 13).toNat := rfl
  have hsw := P.hs
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have sdt : (Sd s + BitVec.ofNat 64 oRsa).toNat = (Sd s).toNat + oRsa := by
    rw [Offset.toNat_add_ofNat]; have := P.wsc; unfold oRsa at *; omega
  exact {
    sp16 := by rw [hsp]; exact pb_al P
    sp1 := by rw [hsp, pbt]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega
    sp2 := by rw [hsp, pbt]; omega
    hrd := by rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]; rfl
    hwr := by rw [hO, hS]; rfl
    on := by rw [hO, hN]; exact (P.ns.sub_right es).symm
    oe := by rw [hO, hE]; exact (P.es.sub_right es).symm
    oi := by rw [hO, hI]; exact (P.cts.sub_left is |>.sub_right es).symm
    op := by rw [hO, hP]; exact (P.ps.sub_right es).symm
    oq := by rw [hO, hQ]; exact (P.qs.sub_right es).symm
    odp := by rw [hO, hDP]; exact (P.dps.sub_right es).symm
    odq := by rw [hO, hDQ]; exact (P.dqs.sub_right es).symm
    oqi := by rw [hO, hQI]; exact (P.qis.sub_right es).symm
    os := by rw [hO, hS]; exact em_rs P
    oa := by rw [hO, hA]; exact (P.ks.sub_left pbs |>.sub_right es).symm
    ns := by rw [hN, hS]; exact P.ns.sub_right rs
    es := by rw [hE, hS]; exact P.es.sub_right rs
    is := by rw [hI, hS]; exact P.cts.sub_left is |>.sub_right rs
    ps := by rw [hP, hS]; exact P.ps.sub_right rs
    qs := by rw [hQ, hS]; exact P.qs.sub_right rs
    dps := by rw [hDP, hS]; exact P.dps.sub_right rs
    dqs := by rw [hDQ, hS]; exact P.dqs.sub_right rs
    qis := by rw [hQI, hS]; exact P.qis.sub_right rs
    sa := by rw [hS, hA]; exact (P.ks.sub_left pbs |>.sub_right rs).symm
    ko := by rw [hK, hO]; exact P.ks.sub_left ks |>.sub_right es
    kn := by rw [hK, hN]; exact P.kn.sub_left ks
    ke := by rw [hK, hE]; exact P.ke.sub_left ks
    ki := by rw [hK, hI]; exact P.kct.sub_left ks |>.sub_right is
    kp := by rw [hK, hP]; exact P.kp.sub_left ks
    kq := by rw [hK, hQ]; exact P.kq.sub_left ks
    kdp := by rw [hK, hDP]; exact P.kdp.sub_left ks
    kdq := by rw [hK, hDQ]; exact P.kdq.sub_left ks
    kqi := by rw [hK, hQI]; exact P.kqi.sub_left ks
    ks := by rw [hK, hS]; exact P.ks.sub_left ks |>.sub_right rs
    ka := by rw [hK, hA]; exact pk_PB P
    wo := by rw [g0, g1]; have := P.wsc; omega
    wn := by rw [g2, g3]; exact P.wn
    we := by rw [g4, g5]; exact P.we
    wi := by rw [g6, g7]; have := P.wct; have := P.oc; omega
    wp := by rw [s0, s1]; exact P.wp
    wq := by rw [s2, s3]; exact P.wq
    wdp := by rw [s4, s5]; exact P.wdp
    wdq := by rw [s6, s7]; exact P.wdq
    wqi := by rw [s8, s9]; exact P.wqi
    ws := by rw [s10, l11, sdt]; have := P.wsc; unfold oRsa; omega
    k1 := by rw [g3]; exact P.k1
    k2 := by rw [g3]; exact P.k2
    h1 := by rw [g1, g3]
    h7 := by rw [g7, g3]
    e1 := by rw [g5]; exact P.e1
    e2 := by rw [g5, g3]; exact P.e2
    p1 := by rw [s1]; exact P.p1
    p2 := by rw [s1, g3]; exact P.p2
    q1 := by rw [s3]; exact P.q1
    q2 := by rw [s3, g3]; exact P.q2
    h5 := by rw [s5, s1]; exact P.h4
    h9 := by rw [s9, s1]; exact P.h8
    h7' := by rw [s7, s3]; exact P.h6
    hs := by rw [g3, l11]; unfold Spec.Rsa.scratchWords; omega
    al := by rw [s10, sdt]; have := P.als; unfold oRsa; omega }

end


/-! ## The outcome -/

/-- RSADP checked against `e`, of the entry's buffers. -/
def privO (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 11) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 0).toNat)

/-- The result's code: 1, 0 or 2. -/
def rcOf : Spec.Rsa.Outcome → Nat
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- What it writes to `EM`'s place. -/
def emOf (k : Nat) : Spec.Rsa.Outcome → List Byte
  | .ok y => y
  | _ => List.replicate k 0

/-- The entry state with memory `m`, as `Base` takes it for the decoding. -/
abbrev withMem (s : State) (m : Mem) : State := { s with mem := m }

/-- After the private operation. -/
structure AfterPriv (s v : State) : Prop where
  base : Base (SD s) (VD s (rcOf (privO s))) (withMem s v.mem) v
  mem : Frame [kD s, scR s] s.mem v.mem
  em : Spec.Rsa.bytesAt v.mem (Sd s) (kk s) = emOf (kk s) (privO s)

theorem rcOf_le (o : Spec.Rsa.Outcome) : rcOf o ≤ 2 := by cases o <;> simp [rcOf]

/-- The outcome, from `writtenOutcome`. -/
theorem of_written {m : Mem} {p : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m p k r o) : r = BitVec.ofNat 32 (rcOf o) ∧ Spec.Rsa.bytesAt m p k = emOf k o := by
  cases o with
  | ok y => exact ⟨h.1, h.2⟩
  | invalid => exact ⟨h.1, h.2⟩
  | fault => exact ⟨h.1, h.2⟩

/-- `slli`, `srli` by 32: the low word, zero-extended. -/
theorem zext32 {x : BitVec 64} {r : Nat} (hr : x.setWidth 32 = BitVec.ofNat 32 r) (h : r ≤ 2) :
    (x <<< 32) >>> 32 = BitVec.ofNat 64 r := by
  have e := congrArg BitVec.toNat hr
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at e
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

section
variable {s : State} (P : PreD s)
include P

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 14).toNat * 8) {rs : List Region} :
    Covers [⟨Sd s + BitVec.ofNat 64 d, n⟩] (rs ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} (A : AtPriv s t) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hsw := P.hs
  have := P.k2
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsw
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · have := cov_sc P (d := 0) (n := kk s) (rs := [PB s, fr s]) (by unfold kk; omega)
      rwa [BitVec.add_zero] at this
    · exact cov_sc P (d := oRsa) (rs := [PB s, fr s]) (by unfold oRsa; omega)
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  have hct : iD s = ctR s := by simp only [iD, ctR, kk, P.oc]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hct]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} (A : AtPriv s t) {R : Region} (hd : (kD s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => A.mem.bytes (R := R) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) hl (List.mem_range.mp hi)

theorem below_pb : below (pb s) Impl.Rsa.RISCV64.Priv.frameBytes = pkR s := by
  show Region.mk (pb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes) _ = _
  rw [pb_kb P]; exact congrArg (Region.mk · _) (BitVec.add_sub_cancel _ _)

/-- Our frame's slots and what the call writes. -/
theorem slots_dis : ∀ r ∈ callWr s ++ [pkR s],
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv, frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ r := by
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 Proof.RsaOaep.RISCV64.oSv,
      frameBytes - Proof.RsaOaep.RISCV64.oSv⟩ (kD s) := by
    rw [fb_kb P, Offset.add_add]; exact kb_sub (by decide)
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (P.ks.sub_left hk).sub_right (em_sub P)
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · rw [fb_kb P, Offset.add_add]
    exact Offset.disjoint_base _ (by decide) (by decide)

/-- The private operation's frame, with the stack pointer after it. -/
theorem privF_ok {t : State} (E : Entered s t) :
    WP isa (.frame (.alloc privBytes) (.seq (.block privArgs) privCall) (.free privBytes)) t
      fun w => w.sp = fb s ∧
        WP isa (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32]) w (AfterPriv s) := by
  have hsp : t.sp = fb s := E.sv.sp
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, stackBytes_eq, frameBytes] at *
    unfold privBytes; omega) ?_
  refine WP.seq (WP.mono (privArgs_ok P E) fun u A => ?_)
  obtain ⟨hc, hw⟩ := call_covers P A
  unfold privCall
  refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    (Rsa.RISCV64.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf hpres hpost => ?_)
    (by rw [priv_sdepth]; decide)
  rw [priv_sdepth, A.sp, below_pb P] at hf
  have fsp : (freed privBytes v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 privBytes = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  refine ⟨fsp, wp_sll (fun w₁ o₁ e₁ => wp_srl (fun w ow ew => wp_nil ?_))⟩
  -- The outcome.
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have s0 : stackArg (callE s u) 0 = s.gpr .a7 := sa 0 (by decide)
  have s1 : stackArg (callE s u) 1 = stackArg s 0 := sa 1 (by decide)
  have s2 : stackArg (callE s u) 2 = stackArg s 1 := sa 2 (by decide)
  have s3 : stackArg (callE s u) 3 = stackArg s 2 := sa 3 (by decide)
  have s4 : stackArg (callE s u) 4 = stackArg s 3 := sa 4 (by decide)
  have s6 : stackArg (callE s u) 6 = stackArg s 5 := sa 6 (by decide)
  have s8 : stackArg (callE s u) 8 = stackArg s 7 := sa 8 (by decide)
  simp only [Rsa.RISCV64.Priv.fnContract, Rsa.RISCV64.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr s u (r := .a0), callE_gpr s u (r := .a2), callE_gpr s u (r := .a3),
    callE_gpr s u (r := .a4), callE_gpr s u (r := .a5), callE_gpr s u (r := .a6), A.a0, A.a2, A.a3, A.a4, A.a5,
    A.a6, s0, s1, s2, s3, s4, s6, s8] at hpost
  have hb := fun {p : Addr} {len : Nat} (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
    bytes_at A (R := ⟨p, len⟩) hd hl
  rw [hb P.kn (by have := P.wn; omega), hb P.ke (by have := P.we; omega),
    hb (by have := P.kct; simp only [ctR, P.oc] at this; exact this) (by omega),
    hb P.kp (by have := P.wp; omega), hb P.kq (by have := P.wq; omega),
    hb (by have := P.kdp; simp only [dpR, P.h4] at this; exact this) (by have := P.wdp; omega),
    hb (by have := P.kdq; simp only [dqR, P.h6] at this; exact this) (by have := P.wdq; omega),
    hb (by have := P.kqi; simp only [qiR, P.h8] at this; exact this) (by have := P.wqi; omega)] at hpost
  change Spec.Rsa.writtenOutcome _ _ _ _ (privO s) at hpost
  obtain ⟨hr, hem⟩ := of_written hpost
  -- The state after the frame's release.
  have O : Only [.s4] (freed privBytes v) w := (o₁.trans ow).mono
  have fwr : (freed privBytes v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have wm : w.mem = v.mem := O.mem
  have pv : ∀ r ∈ preserved, r ≠ .s4 → w.gpr r = u.gpr r := fun r hr' h4 =>
    (O.gpr r (by simpa using h4)).trans (hpres r hr')
  have r4 : w.gpr .s4 = BitVec.ofNat 64 (rcOf (privO s)) := by
    rw [ew, e₁]; exact zext32 hr (rcOf_le _)
  have fm : Frame [kD s, scR s] s.mem w.mem := by
    rw [wm]
    refine (A.mem.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans (hf.sub fun r hr => ?_)
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s, by simp, em_sub P⟩
    · exact ⟨scR s, by simp, rs_sub P⟩
    · exact ⟨kD s, by simp, pk_sub⟩
  have svs : Spill.Saved (fb s) s.gpr Impl.RsaOaep.RISCV64.saved w.mem := by
    rw [wm]
    exact A.sv.frame_in (lo := Proof.RsaOaep.RISCV64.oSv) (n := frameBytes - Proof.RsaOaep.RISCV64.oSv)
      (fun p hp => by
        have := Proof.RsaOaep.RISCV64.saved_offs p hp; unfold frameBytes Proof.RsaOaep.RISCV64.oSv at *; omega)
      hf (slots_dis P)
  refine ⟨⟨⟨by rw [O.sp]; exact fsp, by rw [O.wr]; exact fwr, svs⟩, by rw [O.rd]; exact hrd.trans A.rd,
    by rw [pv .s0 (by decide) (by decide)]; exact A.s0, ?_, Frame.refl _ _⟩, fm, by rw [wm, hem]⟩
  intro r hr
  simp only [Proof.RsaOaep.RISCV64.fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [pv _ (by decide) (by decide)]; exact A.s1
  · rw [pv _ (by decide) (by decide)]; exact A.s2
  · rw [pv _ (by decide) (by decide)]; exact A.s3
  · exact r4

theorem priv_ok {t : State} (E : Entered s t) : WP isa Impl.RsaOaep.RISCV64.Dec.priv t (AfterPriv s) :=
  WP.seq (WP.mono (privF_ok P E) fun _ h => h.2)

end

end VG.Proof.RsaOaep.RISCV64.Dec
