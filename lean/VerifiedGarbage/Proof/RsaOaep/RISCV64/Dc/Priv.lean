module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Pre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith

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
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_ld wp_sd wp_mov wp_li wp_add wp_addi wp_subi wp_sll wp_addSp
  wp_nil)

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

/-- A range at `kb s + d` in the stack the function uses. -/
omit P in theorem kb_sub {d n : Nat} (h : d + n ≤ stackBytes) : Region.Sub ⟨kb s + BitVec.ofNat 64 d, n⟩ (kD s) :=
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
  rw [pb_kb P, Offset.add_add]; exact kb_sub P (by unfold privBytes at h; rw [stackBytes_eq]; omega)

theorem PB_sub : Region.Sub (PB s) (kD s) := by
  have := pb_sub P (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this

theorem fr_subD : Region.Sub (fr s) (kD s) := by
  show Region.Sub ⟨fb s, frameBytes⟩ _
  rw [fb_kb P]; exact kb_sub P (by decide)

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
    (pb_off_al P (by omega) (by unfold privBytes; omega))
    (by rw [o₁.wr, hc.keep.wr, hwr]; exact pb_in P (by unfold privBytes; omega)) (fun t₂ m₂ => wp_nil ?_)
    (by omega)
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, fun j hj => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (pb s) (d := 8 * (n + 1)) (n := 8)
      (k := privBytes) (by unfold privBytes; omega) (by omega))
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.got j hj
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {w : State} (hw0 : w.gpr .t0 = pb s) (hw6 : w.gpr .t6 = s.sp) (hrd : w.rd = s.rd)
    (hwr : w.wr = PB s :: fr s :: s.wr) (hm : Frame [kD s] s.mem w.mem) :
    WP isa (.block ((List.range 9).flatMap copyArg)) w (Cp s w 9) :=
  wp_range_flatMap (M := isa) (Cp s w) (fun _ _ hn hc => copy_step P hw0 hw6 hrd hwr hm hn hc) 9
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

end

end VG.Proof.RsaOaep.RISCV64.Dec
