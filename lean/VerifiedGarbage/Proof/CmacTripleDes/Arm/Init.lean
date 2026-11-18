module

public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Block
import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `CmacTripleDes.Arm.Finalize`, which the modules that import this one used -/

section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize`, the last block

Untrusted: everything here is checked by Lean. The steps that form the last
block `Mₙ` (§6.2 step 4) in `r4:r5` as little-endian words (`BPost`):
`Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a byte at a time
onto the zeroed bytes `[124, 132)` of the scratch buffer, `0x80` after it,
XORed with `K2`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldrSp wp_ldr
  wp_str wp_rev wp_ldrb wp_strb saveMem saveList_ok cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev FW : BitVec 32 := s₀.gpr .r0
abbrev FSt : BitVec 32 := s₀.gpr .r1
abbrev FP : BitVec 32 := s₀.gpr .r2
abbrev FL : Nat := (s₀.gpr .r3).toNat
abbrev FS : BitVec 32 := stackArg s₀ 0

abbrev keyR : Region := ⟨State.addr (FW s₀), 400⟩
abbrev fstR : Region := ⟨State.addr (FSt s₀), 8⟩
abbrev lastR : Region := ⟨State.addr (FP s₀), FL s₀⟩
abbrev fscrR : Region := ⟨State.addr (FS s₀), 640⟩
abbrev fargsR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, lastR s₀, fargsR s₀]
  wr : s₀.wr = [fstR s₀, fscrR s₀]
  key_st : (keyR s₀).Disjoint (fstR s₀)
  key_scr : (keyR s₀).Disjoint (fscrR s₀)
  last_st : (lastR s₀).Disjoint (fstR s₀)
  last_scr : (lastR s₀).Disjoint (fscrR s₀)
  st_scr : (fstR s₀).Disjoint (fscrR s₀)
  st_args : (fstR s₀).Disjoint (fargsR s₀)
  scr_args : (fscrR s₀).Disjoint (fargsR s₀)
  key_fit : (FW s₀).toNat + 400 ≤ 2 ^ 32
  st_fit : (FSt s₀).toNat + 8 ≤ 2 ^ 32
  last_fit : (FP s₀).toNat + FL s₀ ≤ 2 ^ 32
  scr_fit : (FS s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32
  len : FL s₀ ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- The bytes where a partial last block is formed. -/
abbrev mnR (s₀ : State) : Region := ⟨State.addr (FS s₀) + BitVec.ofNat 64 124, 8⟩

/-- What the first block leaves. -/
structure P1 (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = FS s₀
  r9 : s.gpr .r9 = FW s₀
  r1 : s.gpr .r1 = FSt s₀
  r2 : s.gpr .r2 = FP s₀
  r3 : s.gpr .r3 = s₀.gpr .r3
  sp : s.sp = s₀.sp
  mem : s.mem = savedMem s₀ (FS s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the branch on the length leaves: `Mₙ` in `r4:r5`. -/
structure BPost (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = FS s₀
  r9 : s.gpr .r9 = FW s₀
  r1 : s.gpr .r1 = FSt s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [mnR s₀] (savedMem s₀ (FS s₀)) s.mem
  blk : le8 (s.gpr .r5 ++ s.gpr .r4) = mn s₀.mem (State.addr (FW s₀)) (State.addr (FP s₀)) (FL s₀)

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) (_hn : 0 < n) :
    InRegions s₀.wr (State.addr (FS s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ h (by omega_arith))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) (_hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (FW s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := keyR s₀) (by simp) (Offset.contains_base _ h (by omega_arith))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ FL s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (FP s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := lastR s₀) (by simp) (Offset.contains_base _ h (by have := hp.len; omega_arith))

theorem FPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (FS s₀ + BitVec.ofNat 32 d) = State.addr (FS s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega_arith)

theorem FPre.keyAddr {d : Nat} (h : d < 400) :
    State.addr (FW s₀ + BitVec.ofNat 32 d) = State.addr (FW s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega_arith)

theorem FPre.arg_in : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]; exact in_rw (r := fargsR s₀) (by simp) (Region.contains_self _ _)

/-- Saving the registers leaves the key unchanged. -/
theorem FPre.keyBytes {d : Nat} (h : d + 8 ≤ 400) :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) (State.addr (FW s₀) + BitVec.ofNat 64 d) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 d) 8 :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))) (by decide)

theorem FPre.lastBytes :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) (State.addr (FP s₀)) (FL s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))) (by have := hp.len; omega_arith)

end

/-! ## The prologue -/

theorem fpre1_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.ldrSp .r12 0] : List Instr) ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)))
      s₀ fun s => P1 s₀ s ∧ s.z = decide (FL s₀ = 8) := by
  have hsc := hp.scr_fit
  have hL := hp.len
  rw [show [Instr.ldrSp .r12 0] ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr) =
    .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = FS s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega_arith, by omega_arith, hp.inScr (by omega_arith) (by decide)⟩
  obtain hm₂ : s₂.mem = savedMem s₀ (FS s₀) := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  simp only [mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₅.gpr, u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide),
      show s₀.gpr .r3 = BitVec.ofNat 32 (FL s₀) by simp [FL], show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      MdStream.Arm.sub_beq (by omega_arith) (by decide)]

/-! ## A complete last block -/

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ = 8) {s : State} (h : P1 s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  simp only [full]
  refine wp_ldr (by decide) (by rw [h.r2, add0]) (by rw [hrw]; simpa using hp.inLast (d := 0) (n := 4) (by omega_arith) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (FP s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.other _ (by decide), h.r2]; exact addr_add (by omega_arith))
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.inLast (d := 4) (n := 4) (by omega_arith) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9,
      hp.keyAddr (by decide)])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => wp_eor (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.2, u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  obtain mem : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [g _ (by decide), h.r10], by rw [g _ (by decide), h.r9], by rw [g _ (by decide), h.r1],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [mem, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [u₆.gpr, u₆.other .r4 (by decide), u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr,
    u₄.other .r4 (by decide), u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide),
    u₃.other .r5 (by decide), u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (FW s₀) + BitVec.ofNat 64 388 = State.addr (FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 384 4).symm, ← readW64_split, h.mem, le8_xor, le8_readW, le8_readW,
    hp.keyBytes (by decide)]
  have lb := hp.lastBytes
  rw [hL] at lb
  rw [lb]
  simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
  exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem eval_ne' (s : State) : isa.eval .ne s = some !s.z := rfl

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 8)
    (h7 : s.gpr .r7 = p) (h6 : s.gpr .r6 = c) (h8 : s.gpr .r8 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 8 ≤ 2 ^ 32)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (State.addr c + BitVec.ofNat 64 i) 1)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 8⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r4 .r7 0, .strb .r4 .r6 0, .dp .add .r7 .r7 (.imm 1),
      .dp .add .r6 .r6 (.imm 1), .subs .r8 .r8 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r7 = p + BitVec.ofNat 32 i ∧
      t.gpr .r6 = c + BitVec.ofNat 32 i ∧ t.gpr .r8 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; exact (BitVec.add_zero p).symm, by rw [h6]; exact (BitVec.add_zero c).symm,
      by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega_arith)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x7, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x6, BitVec.add_zero, aC]) (by rw [u₁.wr, wr]; exact hw i (by omega_arith))
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  obtain hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  obtain hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  obtain x8' : t₅.gpr .r8 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  obtain ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    rw [eval_ne', z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
  obtain gg : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t₅.gpr r = s.gpr r := fun r h₄ h₆ h₇ h₈ => by
    rw [u₅.other _ h₈, u₄.other _ h₆, u₃.other _ h₇, v₂.gpr, u₁.other _ h₄, g r h₄ h₆ h₇ h₈]
  obtain x6' : t₅.gpr .r6 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain x7' : t₅.gpr .r7 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  obtain rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  obtain wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x7', x6', x8', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ < 8) {s : State} (h : P1 s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  let C : Addr := State.addr (FS s₀) + BitVec.ofNat 64 124
  obtain hC : State.addr (FS s₀ + BitVec.ofNat 32 124) = C := hp.scrAddr (by decide)
  obtain hC4 : State.addr (FS s₀ + BitVec.ofNat 32 128) = C + BitVec.ofNat 64 4 := by
    rw [hp.scrAddr (by decide)]; exact (Offset.add_add _ 124 4).symm
  obtain cIn : ∀ i < 8, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [Offset.add_add]; exact hp.inScr (by omega_arith) (by decide)
  -- Zero the bytes.
  refine WP.seq ?_
  simp only [zero, mov]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (by decide) (by rw [u₁.other _ (by decide), h.r10, hC])
    (by rw [u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₂ w₂ => ?_
  refine wp_str (by decide) (by rw [w₂.gpr, u₁.other _ (by decide), h.r10, hC4])
    (by rw [w₂.wr, u₁.wr, h.wr]; rw [Offset.add_add]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _)
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  let m₁ := ((savedMem s₀ (FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
  obtain mem₇ : s₇.mem = m₁ := by
    rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, w₃.mem, w₂.mem, w₂.gpr, u₁.gpr, u₁.mem, h.mem]
  obtain g₇ : ∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other _ hr.2.2.2, u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, w₃.gpr, w₂.gpr, u₁.other _ hr.1]
  obtain r6₇ : s₇.gpr .r6 = FS s₀ + BitVec.ofNat 32 124 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r10]; rfl
  obtain r7₇ : s₇.gpr .r7 = FP s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r2]
  obtain r8₇ : s₇.gpr .r8 = BitVec.ofNat 32 (FL s₀) := by
    rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r3]; simp [FL]
  obtain z7 : s₇.z = decide (FL s₀ = 0) := by
    rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr,
      u₁.other _ (by decide), h.r3, show s₀.gpr .r3 = BitVec.ofNat 32 (FL s₀) by simp [FL]]
    exact cmp0 (by omega_arith)
  obtain rd₇ : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, w₃.rd, w₂.rd, u₁.rd, h.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, w₃.wr, w₂.wr, u₁.wr, h.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, w₂.sp, u₁.sp, h.sp]
  obtain dPC : (lastR s₀).Disjoint ⟨C, 8⟩ := hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  obtain lastM₁ : Spec.Aes.bytesAt m₁ (State.addr (FP s₀)) (FL s₀) = Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) := by
    rw [← hp.lastBytes]
    refine bytesAt_frame (rs := [⟨C, 8⟩]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega_arith)
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    simpa using Offset.contains_base C (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (t : State) =>
      t.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)) ∧
      t.gpr .r6 = FS s₀ + BitVec.ofNat 32 124 + BitVec.ofNat 32 (FL s₀) ∧
      (∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → t.gpr r = s.gpr r) ∧
      t.sp = s₀.sp ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr) ?_ fun t ht => ?_)
  · by_cases hL0 : FL s₀ = 0
    · refine WP.ite true (by show some s₇.z = _; rw [z7, hL0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₇, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [r6₇, hL0]; exact (BitVec.add_zero _).symm, g₇, sp₇, rd₇, wr₇⟩
    · refine WP.ite false (by show some s₇.z = _; rw [z7]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp (p := FP s₀) (c := FS s₀ + BitVec.ofNat 32 124) (by omega_arith) (by omega_arith) r7₇ r6₇ r8₇
        (by omega_arith) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith)
        (fun i hi => by rw [rd₇, wr₇]; exact hp.inLast (by omega_arith) (by decide))
        (fun i hi => by rw [wr₇, hC]; exact cIn i hi) (by rw [hC]; exact dPC)) ?_
      rintro t ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, mem₇, hC, lastM₁], r6₂, fun r hr => by
        rw [g₂ r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
          (fun h => hr (by simp [h])), g₇ r hr], by rw [sp₂, sp₇], by rw [rd₂, rd₇], by rw [wr₂, wr₇]⟩
  obtain ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩ := ht
  obtain hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)).length = FL s₀ := Proof.Cmac.bytesAt_length _ _ _
  obtain cL : State.addr (t.gpr .r6 + BitVec.ofNat 32 0) = C + BitVec.ofNat 64 (FL s₀) := by
    rw [r6₂, add0, Straight.add_ofNat_ofNat, addr_add (by omega_arith)]
    show _ = State.addr (FS s₀) + BitVec.ofNat 64 124 + BitVec.ofNat 64 (FL s₀)
    rw [Offset.add_add]
  obtain trw : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂]
  simp only [padK2]
  refine wp_mov (op2_imm (by decide)) fun t₁ v₁ => ?_
  refine wp_strb (by decide) (by rw [v₁.other _ (by decide), cL]) (by rw [v₁.wr, wr₂]; exact cIn _ hL)
    fun t₂ v₂ => ?_
  refine wp_ldr (by decide) (by rw [v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10, hC])
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact wr_in (hp.inScr (by decide) (by decide))) fun t₃ v₃ => ?_
  refine wp_ldr (by decide) (by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10,
      hC4])
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw, Offset.add_add]
        exact wr_in (hp.inScr (by decide) (by decide))) fun t₄ v₄ => ?_
  refine wp_ldr (by decide) (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide),
      g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact hp.inKey (by decide) (by decide))
    fun t₅ v₅ => ?_
  refine wp_ldr (by decide) (by rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr,
      v₁.other _ (by decide), g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]
        exact hp.inKey (by decide) (by decide)) fun t₆ v₆ => ?_
  refine wp_eor (op2_reg _ _) fun t₇ v₇ => wp_eor (op2_reg _ _) fun t₈ v₈ => WP.block_nil ?_
  let m₃ := (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀))).writeW
    (C + BitVec.ofNat 64 (FL s₀)) (0x80 : Byte)
  obtain mem₂ : t₂.mem = m₃ := by rw [v₂.mem, v₁.mem, m₂, v₁.gpr, b80]
  obtain g₈ : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8] → t₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₈.other _ hr.2.1, v₇.other _ hr.1, v₆.other _ hr.2.2.2.1, v₅.other _ hr.2.2.1, v₄.other _ hr.2.1,
      v₃.other _ hr.1, v₂.gpr, v₁.other _ hr.1, g₂ r (by simp [hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  -- The frame.
  obtain cR : ∀ d n, d + n ≤ 8 → (mnR s₀).Contains (C + BitVec.ofNat 64 d) n := fun d n h =>
    Offset.contains_base _ h (by omega_arith)
  obtain fr : Frame [mnR s₀] (savedMem s₀ (FS s₀)) m₃ := by
    refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (cR 4 4 (by decide))).trans (writeBytes_frame _ _ _ ?_)).writeW (List.mem_singleton_self _) _
      (cR _ 1 (by omega_arith))
    · simpa using cR 0 4 (by decide)
    · rw [hlen]; simpa using cR 0 (FL s₀) (by omega_arith)
  -- The block.
  obtain kD : (⟨State.addr (FW s₀) + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint (mnR s₀) :=
    (hp.key_scr.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
  obtain k2 : Spec.Aes.bytesAt m₃ (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 := by
    rw [bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
      hp.keyBytes (by decide)]
  obtain pad : Spec.Aes.bytesAt m₃ C 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) ++ [0x80] ++ Spec.Cmac.zeros (8 - FL s₀ - 1) := by
    obtain hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
      rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi]; decide
    have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)) (by rw [hlen]; exact hL) hz
    rw [hlen] at this
    exact this
  refine ⟨by rw [g₈ _ (by decide), h.r10], by rw [g₈ _ (by decide), h.r9], by rw [g₈ _ (by decide), h.r1],
    by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp₂],
    by rw [v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₂],
    by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₂],
    by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, mem₂]; exact fr, ?_⟩
  rw [v₈.gpr, v₈.other .r4 (by decide), v₇.gpr, v₇.other .r5 (by decide), v₇.other .r7 (by decide), v₆.gpr,
    v₆.other .r4 (by decide), v₆.other .r5 (by decide), v₆.other .r6 (by decide), v₅.gpr, v₅.other .r4 (by decide),
    v₅.other .r5 (by decide), v₄.gpr, v₄.other .r4 (by decide), v₃.gpr, v₅.mem, v₄.mem, v₃.mem, mem₂,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (FW s₀) + BitVec.ofNat 64 396 = State.addr (FW s₀) + BitVec.ofNat 64 392 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 392 4).symm, ← readW64_split, le8_xor, le8_readW, le8_readW, pad, k2]
  simp only [mn, Spec.Cmac.lastBlock, hlen, show FL s₀ ≠ 8 by omega_arith, ite_false]
  exact Proof.Cmac.xor_comm _ _

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (BPost s₀) := by
  refine WP.seq (WP.mono (fpre1_wp hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  by_cases hL : FL s₀ = 8
  · exact WP.ite true (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_arith) h₁)

end VG.Proof.CmacTripleDes.Arm

end

end

/-! ### `CmacTripleDes.Arm.Keys`, which only this module used -/

section

/-!
# DES's key schedule on 32-bit ARM

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key in `r0:r1` (its high and low words)
to the round keys' words it stores: the kernel checks it over the lane
domain (`roundKeys_check`), and `getLsbD_expandDesKey` says the bits are the
specification's.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.Arm
  VG.Proof.CmacTripleDes

/-- The round keys' words, at `r2`. -/
def kCfg : Cfg := { base := .r2, slots := 32, ext := .r2, exts := 0 }

/-- Bit `q` of word `w` (0 low, 1 high) of round key `j`: bit `rkSrc j (32 w + q)`
of the key. -/
def rkG (k q : Nat) : List Nat :=
  if q < (if k % 2 = 0 then 32 else 16) then [xAtom (rkSrc (k / 2) (32 * (k % 2) + q))] else []

theorem rkG_lo {j q : Nat} (hq : q < 32) : rkG (2 * j) q = [xAtom (rkSrc j q)] := by
  simp [rkG, hq, show 2 * j / 2 = j by omega_using []]

theorem rkG_hi {j q : Nat} (hq : q < 16) : rkG (2 * j + 1) q = [xAtom (rkSrc j (32 + q))] := by
  simp [rkG, hq, show (2 * j + 1) % 2 = 1 by omega_using [], show (2 * j + 1) / 2 = j by omega_using []]

theorem rkG_hi0 {j q : Nat} (hq : 16 ≤ q) : rkG (2 * j + 1) q = [] := by
  simp [rkG, show (2 * j + 1) % 2 = 1 by omega_using [], show ¬ q < 16 by omega_using [hq]]

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 32).all fun k => e.slot k == some (outWord (rkG k))

theorem roundKeys_check :
    check (lanes 32 6) kCfg (linExt 2) roundKeys (linEnv [(.r0, 0), (.r1, 1)]) kPost = true := by
  rw [roundKeys_eq]; lit_decide

theorem rkG_lt : ∀ k < 32, ∀ q < 32, ∀ a ∈ rkG k q, a < 2 ^ 6 := by lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.r6, .r7, .r8]

/-- Every register `roundKeys` writes is one of `kWrites`: checked once
for every instruction, rather than once for every other register. -/
theorem roundKeys_writes : roundKeys.all (fun i => (dsts i).all kWrites.contains) = true := by
  rw [roundKeys_eq]; lit_decide

theorem roundKeys_kept {r : Reg} (hr : r ∉ kWrites) : roundKeys.all (fun i => !clobbers i r) = true :=
  List.all_eq_true.mpr fun i hi => by
    rw [clobbers_eq_false_of_contains (List.all_eq_true.mp roundKeys_writes i hi) hr]; rfl

/-- The round keys of the DES key in `r0:r1`, in `[r2 + 8 j]` and `[r2 + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .r2) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (s.gpr .r0 ++ s.gpr .r1)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ roundKeys_check
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r0 else s.gpr .r1
  obtain hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) kCfg (linExt 2) (linEnv [(.r0, 0), (.r1, 1)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun j a hj h => absurd hj (by simp [kCfg])),
      fun _ _ h => by cases h⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · split at h
      · rename_i _ hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel W (i := 1) (by decide)
      · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  obtain hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .r2) k) 32).getLsbD q = xorBits W (rkG k q) := by
    intro k hk q hq
    obtain h := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at h
    have := outWord_rel (rkG_lt k hk) (p.rel.slot k _ (by simp only [kCfg]; omega_using [hk]) h)
    rw [p.base] at this
    exact this q hq
  have hx : W 0 ++ W 1 = s.gpr .r0 ++ s.gpr .r1 := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_append, getLsbD_expandDesKey _ hj hq]
    obtain hs := rkSrc_lt j hj q hq
    by_cases h32 : q < 32
    · rw [ite_eq_left h32, hw (2 * j) (by omega_using [hj]) q h32, rkG_lo h32, xorBits_cons, xorBits_nil,
        Bool.xor_false, bit_xAtom W hs, hx]
    · rw [ite_eq_right h32, BitVec.getLsbD_setWidth, decide_eq_true (by omega_using [hq] : q - 32 < 16), Bool.true_and,
        hw (2 * j + 1) (by omega_using [hj]) (q - 32) (by omega_using [hq]), rkG_hi (by omega_using [hq]), show 32 + (q - 32) = q by omega_using [h32],
        xorBits_cons, xorBits_nil, Bool.xor_false, bit_xAtom W hs, hx]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_ushiftRight]
    by_cases hq' : 16 + q < 32
    · rw [hw (2 * j + 1) (by omega_using [hj]) (16 + q) hq', rkG_hi0 (by omega_using [])]
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hq'])]
      simp
  · have h := roundKeys_kept hr
    simp [h]

end VG.Proof.CmacTripleDes.Arm

end

end


/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[88, 112)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldr wp_str wp_rev saveMem saveList_ok sub_beq)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := s₀.gpr .r0
abbrev Kl : Nat := (s₀.gpr .r1).toNat
abbrev O : BitVec 32 := s₀.gpr .r2
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev ikeyR : Region := ⟨State.addr (K s₀), Kl s₀⟩
abbrev outR : Region := ⟨State.addr (O s₀), 400⟩
abbrev iscrR : Region := ⟨State.addr (Sc s₀), 640⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (State.addr (K s₀)) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨State.addr (Sc s₀), 52⟩, ⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩, outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikeyR s₀]
  wr : s₀.wr = [outR s₀, iscrR s₀]
  key_out : (ikeyR s₀).Disjoint (outR s₀)
  key_scr : (ikeyR s₀).Disjoint (iscrR s₀)
  out_scr : (outR s₀).Disjoint (iscrR s₀)
  key_fit : (K s₀).toNat + Kl s₀ ≤ 2 ^ 32
  out_fit : (O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 640 ≤ 2 ^ 32
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨a, b, c, d, e, f, g, h, i⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = Sc s₀
  r4 : s.gpr .r4 = Sc s₀ + BitVec.ofNat 32 (88 + 8 * i)
  r2 : s.gpr .r2 = O s₀ + BitVec.ofNat 32 (128 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (3 - i)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 (88 + 8 * j)) 32 ++
    s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 (92 + 8 * j)) 32 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (State.addr (O s₀) + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 24⟩, ⟨State.addr (O s₀), 384⟩]
    (savedMem s₀ (Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega_arith

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (_hn : 0 < n) :
    InRegions s₀.wr (State.addr (Sc s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega_arith))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (_hn : 0 < n) :
    InRegions s₀.wr (State.addr (O s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega_arith))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (K s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega_arith))

theorem IPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (Sc s₀ + BitVec.ofNat 32 d) = State.addr (Sc s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega_arith)

theorem IPre.keyAddr {d : Nat} (h : d < Kl s₀) :
    State.addr (K s₀ + BitVec.ofNat 32 d) = State.addr (K s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega_arith)

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ Kl s₀) :
    m.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (K s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 32) ++
      rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) j + 4)) 32) = kw s₀ j := by
  rw [rev_eq, rev_eq, byteRev32_append, kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ Kl s₀) (hd' : d < 4096) (ho : o + 4 ≤ 640)
    (h0 : s.gpr .r0 = K s₀) (h10 : s.gpr .r10 = Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (Sc s₀) + BitVec.ofNat 64 o)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.ldr .r4 .r0 d :: .rev .r4 .r4 :: .str .r4 .r10 o :: rest)) s Q
  refine wp_ldr hd' (by rw [h0, hp.keyAddr (by omega_arith)]) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_rev fun s₂ u₂ => ?_
  refine wp_str (by omega_arith) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h10, hp.scrAddr (by omega_arith)])
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) (by rw [w₃.sp, u₂.sp, u₁.sp]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[88, 112)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 88 ≤ d) (h₂ : d + 4 ≤ 112) :
    (⟨S + BitVec.ofNat 64 88, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 88 + BitVec.ofNat 64 (d - 88) from
    (Offset.add_add_eq _ (by omega_arith)).symm]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  obtain kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega_arith
  rw [show initPre = .seq (.block (saved.map (fun p => Instr.str p.1 .r3 p.2) ++
      (mov .r10 .r3 :: (keyWord 0 88 ++ (keyWord 4 92 ++ (keyWord 8 96 ++ (keyWord 12 100 ++
        ([.cmp .r1 (.imm 16)] : List Instr))))))))
      (.seq (.ite .eq (.block [.ldr .r4 .r0 0, .ldr .r5 .r0 4]) (.block [.ldr .r4 .r0 16, .ldr .r5 .r0 20]))
        (.block [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r10 104, .str .r5 .r10 108,
          .dp .add .r4 .r10 (.imm 88), .mov .r5 (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine saveList_ok saved s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb := saved_bound p hp'
    exact ⟨by omega_arith, by omega_arith, hp.inScr (by omega_arith) (by decide)⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  obtain m₂ : s₂.mem = savedMem s₀ (Sc s₀) := by rw [u₂.mem, m₁]; rfl
  obtain g₂ : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [u₂.other _ hr, g₁]
  obtain r10₂ : s₂.gpr .r10 = Sc s₀ := by rw [u₂.gpr, g₁]
  obtain rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, wr₁]
  obtain sp₂ : s₂.sp = s₀.sp := by rw [u₂.sp, sp₁]
  obtain sv : Frame [iscrR s₀] s₀.mem (savedMem s₀ (Sc s₀)) := (savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  obtain scrC : ∀ d, d + 4 ≤ 640 → (iscrR s₀).Contains (State.addr (Sc s₀) + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega_arith)
  -- The four words of the first two DES keys.
  refine keyWord_wp hp (by omega_arith) (by decide) (by decide) (g₂ _ (by decide)) r10₂ rd₂ wr₂ (by rw [m₂]; exact sv)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  obtain F₃ : Frame [iscrR s₀] s₀.mem s₃.mem := by
    rw [m₃, m₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 88 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₃ _ (by decide), r10₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂]) F₃ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  obtain F₄ : Frame [iscrR s₀] s₀.mem s₄.mem := by
    rw [m₄]; exact F₃.writeW (List.mem_singleton_self _) _ (scrC 92 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by decide)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]) (by rw [g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₄, rd₃, rd₂]) (by rw [wr₄, wr₃, wr₂]) F₄ fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  obtain F₅ : Frame [iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact F₄.writeW (List.mem_singleton_self _) _ (scrC 96 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by decide)
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₅, rd₄, rd₃, rd₂]) (by rw [wr₅, wr₄, wr₃, wr₂]) F₅ fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => ?_
  obtain F₆ : Frame [iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  obtain g₆' : ∀ r, r ≠ .r4 → r ≠ .r10 → s₆.gpr r = s₀.gpr r := fun r h4 h10 => by
    rw [g₆ _ h4, g₅ _ h4, g₄ _ h4, g₃ _ h4, g₂ _ h10]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂]
  obtain sp₆' : s₆.sp = s₀.sp := by rw [sp₆, sp₅, sp₄, sp₃, sp₂]
  refine wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  obtain r1 : s₀.gpr .r1 = BitVec.ofNat 32 (Kl s₀) := by simp [Kl]
  obtain ev : isa.eval .eq s₇ = some (decide (Kl s₀ = 16)) := by
    show some s₇.z = _
    rw [z₇, g₆' _ (by decide) (by decide), r1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      sub_beq (s₀.gpr .r1).isLt (by decide)]
  -- The third DES key.
  obtain third : ∀ d, d + 8 ≤ Kl s₀ → d + 4 < 4096 →
      WP isa (.block [.ldr .r4 .r0 d, .ldr .r5 .r0 (d + 4)]) s₇ fun s₈ =>
        s₈.gpr .r4 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 d) 32 ∧
        s₈.gpr .r5 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
        s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp := by
    intro d hd hl
    obtain r0₇ : s₇.gpr .r0 = K s₀ := by rw [f₇.gpr, g₆' _ (by decide) (by decide)]
    refine wp_ldr (by omega_arith) (by rw [r0₇, hp.keyAddr (by omega_arith)])
      (by rw [f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega_arith) (by decide)) fun s₈ u₈ => ?_
    refine wp_ldr (by omega_arith) (by rw [u₈.other _ (by decide), r0₇, hp.keyAddr (by omega_arith)])
      (by rw [u₈.rd, u₈.wr, f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega_arith) (by decide))
      fun s₉ u₉ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.gpr, f₇.mem, hp.keyRead F₆ (by omega_arith)]
    · rw [u₉.gpr, u₈.mem, f₇.mem, hp.keyRead F₆ (by omega_arith)]
    · rw [u₉.other _ h5, u₈.other _ h4]
    · rw [u₉.mem, u₈.mem, f₇.mem]
    · rw [u₉.rd, u₈.rd, f₇.rd, rd₆']
    · rw [u₉.wr, u₈.wr, f₇.wr, wr₆']
    · rw [u₉.sp, u₈.sp, f₇.sp, sp₆']
  refine WP.seq (WP.mono (Q := fun (s₈ : State) =>
      s₈.gpr .r4 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32 ∧
      s₈.gpr .r5 = s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
      s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp) ?_ fun s₈ h₈ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega_arith) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      obtain h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega_arith
      have := third 16 (by omega_arith) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₄, ax₅, g₈, m₈, rd₈, wr₈, sp₈⟩ := h₈
  obtain r10₈ : s₈.gpr .r10 = Sc s₀ := by
    rw [g₈ _ (by decide) (by decide), f₇.gpr, g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      g₃ _ (by decide), r10₂]
  refine wp_rev fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  obtain r10₁₀ : s₁₀.gpr .r10 = Sc s₀ := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), r10₈]
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 104) (by decide) (by rw [r10₁₀, hp.scrAddr (by decide)])
    (by rw [u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 108) (by decide)
    (by rw [w₁₁.gpr, r10₁₀, hp.scrAddr (by decide)])
    (by rw [w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₂ w₁₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_imm (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  obtain mem₁₄ : s₁₄.mem = ((((((savedMem s₀ (Sc s₀)).writeW (State.addr (Sc s₀) + BitVec.ofNat 64 88)
      (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 0) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 92) (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 4) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 96) (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 8) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 100)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 12) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 104)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32))).writeW
      (State.addr (Sc s₀) + BitVec.ofNat 64 108)
        (rev (s₀.mem.readW (State.addr (K s₀) + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32)) := by
    rw [u₁₄.mem, u₁₃.mem, w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .r4 (by decide), u₉.gpr,
      u₁₀.mem, u₉.mem, u₉.other .r5 (by decide), ax₄, ax₅, m₈, m₆, m₅, m₄, m₃, m₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega_arith), ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, r10₁₀]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w₁₂.gpr, w₁₁.gpr, r10₁₀]; rfl
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈ _ (by decide) (by decide), f₇.gpr, g₆' _ (by decide) (by decide), add0]
  · rw [u₁₄.gpr]; rfl
  · rw [u₁₄.sp, u₁₃.sp, w₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, sp₈]
  · rw [u₁₄.rd, u₁₃.rd, w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, rd₈]
  · rw [u₁₄.wr, u₁₃.wr, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  · rw [mem₁₄, ← kw_eq (s₀ := s₀) j]
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
  · rw [mem₁₄]
    obtain c : ∀ d, 88 ≤ d → d + 4 ≤ 112 → (⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 24⟩ : Region).Contains
        (State.addr (Sc s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 88 (by decide) (by decide))).writeW (by simp) _
      (c 92 (by decide) (by decide))).writeW (by simp) _ (c 96 (by decide) (by decide))).writeW (by simp) _
      (c 100 (by decide) (by decide))).writeW (by simp) _ (c 104 (by decide) (by decide))).writeW (by simp) _
      (c 108 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => KInv s₀ (i + 1) s' ∧ s'.z = decide (3 - (i + 1) = 0) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  obtain rdwr : s.rd ++ s.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) (State.addr (Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  rw [keysBody, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 (88 + 8 * i)) (by decide)
    (by rw [h.r4, add0, hp.scrAddr (by omega_arith)]) (scrIn _ (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 (92 + 8 * i)) (by decide)
    (by rw [u₁.other _ (by decide), h.r4, Straight.add_ofNat_ofNat, hp.scrAddr (by omega_arith),
      show 88 + 8 * i + 4 = 92 + 8 * i by omega_arith])
    (by rw [u₁.rd, u₁.wr]; exact scrIn _ (by omega_arith)) fun s₂ u₂ => ?_
  obtain ax₂ : s₂.gpr .r0 ++ s₂.gpr .r1 = kw s₀ i := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, h.keys i hi]
  obtain g₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s.gpr r := fun r h0 h1 => by rw [u₂.other _ h1, u₁.other _ h0]
  obtain r2₂ : s₂.gpr .r2 = O s₀ + BitVec.ofNat 32 (128 * i) := by rw [g₂ _ (by decide) (by decide), h.r2]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  obtain oA : State.addr (O s₀ + BitVec.ofNat 32 (128 * i)) = State.addr (O s₀) + BitVec.ofNat 64 (128 * i) :=
    addr_add (by omega_arith)
  obtain r2n : (O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain wA : ∀ k < 32, wordAddr (s₂.gpr .r2) k = State.addr (O s₀) + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by
      rw [r2₂, wordAddr_eq _ (by rw [r2n]; omega_arith), oA, Offset.add_add]
  obtain hok : Ok kCfg s₂ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [kCfg]), ?_, fun k _ j hj => absurd hj (by simp [kCfg])⟩
    · rw [show kCfg.base = .r2 from rfl, wA k hk, wr₂]
      exact hp.inOut (by simp only [kCfg] at hk; omega_arith) (by decide)
    · show (s₂.gpr .r2).toNat + 4 * 32 ≤ 2 ^ 32
      rw [r2₂, r2n]; omega_arith
  obtain ⟨s₃, run₃, rk₃, hi₃, rd₃, wr₃, sp₃, g₃, f₃⟩ := roundKeys_ok hok
  show WP isa (.block (roundKeys ++ ([.dp .add .r2 .r2 (.imm 128), .dp .add .r4 .r4 (.imm 8),
    .subs .r5 .r5 (.imm 1)] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  obtain gk : ∀ r, r ∉ kWrites → r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s.gpr r := fun r hk h0 h1 => by
    rw [g₃ r hk, g₂ r h0 h1]
  obtain slotR : slotRegion kCfg s₂ = ⟨State.addr (O s₀) + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .r2 from rfl, r2₂, oA]; rfl
  rw [slotR, u₂.mem, u₁.mem] at f₃
  obtain m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  obtain r5₃ : s₃.gpr .r5 = BitVec.ofNat 32 (3 - i) := by rw [gk _ (by decide) (by decide) (by decide), h.r5]
  obtain dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := ofNat_sub_one (by omega_arith) (by omega_arith)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      gk _ (by decide) (by decide) (by decide), h.r10]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), gk _ (by decide) (by decide) (by decide), h.r4,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Straight.add_ofNat_ofNat,
      show 88 + 8 * i + 8 = 88 + 8 * (i + 1) by omega_arith]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, gk _ (by decide) (by decide) (by decide), h.r2,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Straight.add_ofNat_ofNat,
      show 128 * i + 128 = 128 * (i + 1) by omega_arith]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, dec]
  · rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [m₆, ← h.keys j hj]
    obtain keep : ∀ d, 88 ≤ d → d + 4 ≤ 112 → s₃.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 =
        s.mem.readW (State.addr (Sc s₀) + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ => by
      rw [f₃.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega_arith))).symm.sub_left (Offset.sub_base _ (by omega_arith)))
        (by decide)]
    rw [keep _ (by omega_arith) (by omega_arith), keep _ (by omega_arith) (by omega_arith)]
  · rw [m₆]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₃.readW (r := ⟨State.addr (O s₀) + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega_arith⟩
      obtain hj : j < 16 := by omega_arith
      obtain hk := keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega_arith,
        ← wA (2 * j + 1) (by omega_arith), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega_arith, ← wA (2 * j) (by omega_arith),
        append_of_hi _ _ (hi₃ j hj), rk₃ j hj, ax₂, kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₆]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (O s₀), 384⟩, by simp, Offset.sub_base _ (by omega_arith)⟩)
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_arith) (by decide)]
    simp only [decide_eq_decide]; omega_arith

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp; omega_arith, 3 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `r0:r1` and stores it, as bytes, at `[r2 + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop} (hd : d + 4 < 4096)
    (ha : State.addr (s.gpr .r2 + BitVec.ofNat 32 d) = a)
    (ha4 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (d + 4)) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .r0 ++ s'.gpr .r1 = dbl64 (s.gpr .r0 ++ s.gpr .r1) →
      s'.mem = (s.mem.writeW a (rev (s'.gpr .r0))).writeW (a + BitVec.ofNat 64 4) (rev (s'.gpr .r1)) →
      (∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .r3 (.shifted .r0 .lsr 31) :: .mov .r4 (.imm 0) :: .dp .sub .r3 .r4 (.reg .r3) ::
    .dp .and .r3 .r3 (.imm 0x1b) :: .mov .r4 (.shifted .r1 .lsr 31) :: .mov .r0 (.shifted .r0 .lsl 1) ::
    .dp .orr .r0 .r0 (.reg .r4) :: .mov .r1 (.shifted .r1 .lsl 1) :: .dp .eor .r1 .r1 (.reg .r3) ::
    .rev .r3 .r0 :: .str .r3 .r2 d :: .rev .r3 .r1 :: .str .r3 .r2 (d + 4) :: rest)) s Q
  refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_sub (op2_reg _ _) fun s₃ u₃ => wp_and (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_mov (op2_lsl (by decide)) fun s₆ u₆ =>
    wp_orr (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ =>
    wp_eor (op2_reg _ _) fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  obtain g₁₀ : ∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other _ hr.2.2.1, u₉.other _ hr.2.1, u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.1,
      u₅.other _ hr.2.2.2, u₄.other _ hr.2.2.1, u₃.other _ hr.2.2.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.2.1]
  obtain m₁₀ : s₁₀.mem = s.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain r2₁₀ : s₁₀.gpr .r2 = s.gpr .r2 := g₁₀ _ (by decide)
  refine wp_str (by omega_arith) (by rw [r2₁₀, ha]) (by rw [wr₁₀]; exact w0) fun s₁₁ w₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  refine wp_str (by omega_arith) (by rw [u₁₂.other _ (by decide), w₁₁.gpr, r2₁₀, ha4])
    (by rw [u₁₂.wr, w₁₁.wr, wr₁₀]; exact w4) fun s₁₃ w₁₃ => ?_
  obtain r0f : s₁₃.gpr .r0 = s₉.gpr .r0 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  obtain r1f : s₁₃.gpr .r1 = s₉.gpr .r1 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  refine k s₁₃ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · have a3 : s₈.gpr .r3 = ((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    obtain a0 : s₉.gpr .r0 = s.gpr .r0 <<< 1 ||| s.gpr .r1 >>> 31 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.gpr,
        u₅.other _ (by decide), u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        u₁.other _ (by decide)]
    obtain a1 : s₉.gpr .r1 = s.gpr .r1 <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₉.gpr, a3, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₃.mem, u₁₂.mem, w₁₁.mem, m₁₀, u₁₂.gpr, w₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), r0f, r1f]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [w₁₃.gpr, u₁₂.other _ hr.2.2.1, w₁₁.gpr, g₁₀ _ (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [w₁₃.rd, u₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₃.wr, u₁₂.wr, w₁₁.wr, wr₁₀]
  · rw [w₁₃.sp, u₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  obtain hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  obtain rdwr₂ : s₂.rd ++ s₂.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by rw [h₂.rd, h₂.wr, hp.rd, hp.wr]; rfl
  -- The key schedule is in place.
  obtain hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (State.addr (O s₀)) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega_arith)]
  refine WP.seq ?_
  refine wp_str (a := State.addr (Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [h₂.r10, hp.scrAddr (by decide)])
    (by rw [h₂.wr]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain g₆ : ∀ r, r ∉ [Reg.r0, .r1, .r9] → s₆.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2, w₃.gpr]
  obtain r9₆ : s₆.gpr .r9 = O s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, h₂.r2,
      show (384 : BitVec 32) = BitVec.ofNat 32 (128 * 3) from rfl, BitVec.add_sub_cancel]
  obtain r10₆ : s₆.gpr .r10 = Sc s₀ := by rw [g₆ _ (by decide), h₂.r10]
  obtain ax₆ : s₆.gpr .r0 ++ s₆.gpr .r1 = (0 : BitVec 64) := by rw [u₆.other _ (by decide), u₅.gpr, u₆.gpr]; rfl
  obtain m₆ : s₆.mem = s₂.mem.writeW (State.addr (Sc s₀) + BitVec.ofNat 64 112) (O s₀ + BitVec.ofNat 32 384) := by
    rw [u₆.mem, u₅.mem, u₄.mem, w₃.mem, h₂.r2]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, w₃.rd, h₂.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, w₃.wr, h₂.wr]
  obtain c112 : (iscrR s₀).Contains (State.addr (Sc s₀) + BitVec.ofNat 64 112) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega_arith)
  obtain F₆ : Frame [iscrR s₀] s₂.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c112
  obtain outScr : ∀ r ∈ [iscrR s₀], (⟨State.addr (O s₀), 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
  obtain hsch₆ : sch s₆ = Spec.TripleDes.expandKey (keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₆.mem (State.addr (s₆.gpr .r9)) = _
    rw [r9₆, scheduleAt_frame F₆ outScr, hsch₂]
  obtain bp : BlockPre s₆ :=
    { sched := ⟨400, by rw [r9₆, rd₆, wr₆, hp.rd, hp.wr]; simp, by decide, by rw [r9₆]; exact of⟩
      scr := ⟨640, by rw [r10₆, wr₆, hp.wr]; simp, by decide, by rw [r10₆]; exact sf⟩
      disj := by
        rw [r9₆, r10₆]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₇ ⟨same₇, r9₇, ax₇⟩ => ?_)
  rw [ax₆, hsch₆] at ax₇
  obtain r10₇ : s₇.gpr .r10 = Sc s₀ := by rw [same₇.r10, r10₆]
  obtain xR₆ : xR s₆ = ⟨State.addr (Sc s₀), 52⟩ := by rw [xR, r10₆]
  obtain f₇ : Frame [⟨State.addr (Sc s₀), 52⟩] s₆.mem s₇.mem := by rw [← xR₆]; exact same₇.frame
  obtain wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  show WP isa (.block (.ldr .r2 .r10 112 :: (dbl 0 ++ (dbl 8 ++ restore)))) s₇ _
  refine wp_ldr (a := State.addr (Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [r10₇, hp.scrAddr (by decide)])
    (by rw [rd₇, wr₇, hp.rd, hp.wr]
        exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega_arith))) fun s₈ u₈ => ?_
  obtain r2₈ : s₈.gpr .r2 = O s₀ + BitVec.ofNat 32 384 := by
    rw [u₈.gpr, f₇.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega_arith)) (by decide), m₆, Mem.readW_writeW_self32]
  obtain oA : ∀ d, d < 16 → State.addr (O s₀ + BitVec.ofNat 32 384 + BitVec.ofNat 32 d) =
      State.addr (O s₀) + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [Straight.add_ofNat_ofNat, addr_add (by omega_arith)]
  obtain wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, wr₇]; exact hp.inOut (by omega_arith) (by decide)
  obtain a4 : ∀ d, State.addr (O s₀) + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      State.addr (O s₀) + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine dbl_wp (a := State.addr (O s₀) + BitVec.ofNat 64 (384 + 0)) (by decide) (by rw [r2₈, oA 0 (by decide)])
    (by rw [r2₈, oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ sp₉ => ?_
  refine dbl_wp (a := State.addr (O s₀) + BitVec.ofNat 64 (384 + 8)) (by decide)
    (by rw [g₉ _ (by decide), r2₈, oA 8 (by decide)]) (by rw [g₉ _ (by decide), r2₈, oA 12 (by decide), a4])
    (by rw [wr₉]; exact wO 8 (by decide)) (by rw [wr₉, a4]; exact wO 12 (by decide))
    fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ => ?_
  obtain r10₁₀ : s₁₀.gpr .r10 = Sc s₀ := by rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), r10₇]
  obtain rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [ikeyR s₀, outR s₀, iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, same₇.rd, same₇.wr, u₆.rd, u₅.rd, u₄.rd, w₃.rd, u₆.wr, u₅.wr, u₄.wr,
      w₃.wr, rdwr₂]
  -- What changed since the registers were saved.
  obtain oC : ∀ d, d + 4 ≤ 16 → (outR s₀).Contains (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain F₁₀ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₁₀.mem := by
    obtain F₂ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩
    obtain F₆' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₆.mem := by
      rw [m₆]
      refine F₂.writeW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 88, 28⟩) (by simp) _ ?_
      rw [show State.addr (Sc s₀) + BitVec.ofNat 64 112 = State.addr (Sc s₀) + BitVec.ofNat 64 88 +
        BitVec.ofNat 64 (112 - 88) from (Offset.add_add_eq _ (by omega_arith)).symm]
      exact Offset.contains_base _ (by decide) (by decide)
    obtain F₇ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₇.mem :=
      F₆'.trans (f₇.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, a4, a4]
    exact (((F₇.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (restore_ok r10₁₀ (by omega_arith) fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨restored (S := Sc s₀) (fun d h₁' h₂' => ?_) hl ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨State.addr (Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm
  · rw [sp', sp₁₀, sp₉, u₈.sp, same₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, h₂.sp]
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem (State.addr (O s₀)) = Spec.TripleDes.expandKey (keyB s₀)
    rw [m', ← hsch₂]
    refine scheduleAt_frame (rs := [iscrR s₀, ⟨State.addr (O s₀) + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨State.addr (O s₀) + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          (State.addr (O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
      rw [m₁₀, m₉, u₈.mem, a4, a4]
      exact ((((F₆.mono (by simp)).trans (f₇.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide)) |>.writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem (State.addr (O s₀) + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    rw [subkeys_tdes, m', bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem]
    simp (disch := decide) only [Offset.add_add, readW_writeW_far, Mem.readW_writeW_self32]
    rw [rev_eq, rev_eq, rev_eq, rev_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .r0 (by decide), u₈.other .r1 (by decide), ax₇]

end VG.Proof.CmacTripleDes.Arm
