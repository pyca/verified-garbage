module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Keys
public import VerifiedGarbage.Proof.GcmSiv.MulX
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV in registers on x86-64: POLYVAL

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the key
`mulXG H` on its blocks as little-endian numbers
(`Proof.GcmSiv.Polyval.polyvalFrom_eq`): `hkey` leaves GHASH's registers for
that key (`hkey_ok`), and each block loaded as it is and multiplied
(`mulY_ok`, `body4_ok`) is a step of `Spec.Gcm.ghashFrom`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc punpck_movq mulXG_words)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only zero_ok acc_ok reduce_ok constImm_ok hInvImm_ok pows_ok step1
  step4 pxor72_ok)
open VG.Proof.Gcm.Poly (φ x)
open VG.Proof.GcmSiv.Polyval (mulXG)

/-- GHASH's key for the authentication key at `W + 16`. -/
abbrev hOf (m : Mem) (W : Addr) : Spec.Gcm.Block :=
  mulXG (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16))

/-- GHASH's registers for the key `H`: the reduction constant in `xmm1` and
`H'` in `xmm3`. -/
structure GReg (H : Spec.Gcm.Block) (t : State) : Prop where
  c : t.xmm .xmm1 = Impl.Gcm.X86_64.Pclmul.poly
  h : x * φ (t.xmm .xmm3) = φ H

theorem GReg.keep {H : Spec.Gcm.Block} {rs : List XReg} {t t' : State} (g : GReg H t) (o : Only rs t t')
    (h1 : .xmm1 ∉ rs) (h3 : .xmm3 ∉ rs) : GReg H t' :=
  ⟨by rw [o.xmm _ h1, g.c], by rw [o.xmm _ h3]; exact g.h⟩

/-- The registers `mulY` writes. -/
abbrev mulRegs : List XReg :=
  [.xmm8, .xmm9, .xmm10, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

/-- `mulY`: a step of GHASH, on the block in `xmm7`. -/
theorem mulY_ok {H : Spec.Gcm.Block} {t : State} (g : GReg H t) :
    WP isa (.block mulY) t fun t' =>
      t'.xmm .xmm2 = Spec.Gcm.mul (t.xmm .xmm2 ^^^ t.xmm .xmm7) H ∧ Only mulRegs t t' := by
  simp only [mulY, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok t) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨p₃, o₃⟩ => ?_
  have c₃ : s₃.xmm .xmm1 = Impl.Gcm.X86_64.Pclmul.poly := by
    rw [o₃.xmm _ (by decide), o₂.xmm _ (by decide), o₁.xmm _ (by decide), g.c]
  refine WP.mono (reduce_ok .xmm2 s₃ (by decide) (by decide) (by decide) (by decide) c₃) fun s₄ ⟨e₄, o₄⟩ =>
    ⟨?_, o₁.trans (o₂.trans (o₃.trans o₄))⟩
  rw [e₄, p₃, o₂.prod (by decide) (by decide) (by decide), p₁, e₂, o₂.xmm .xmm3 (by decide),
    o₁.xmm .xmm2 (by decide), o₁.xmm .xmm7 (by decide), o₁.xmm .xmm3 (by decide)]
  exact step1 H _ _ _ g.h

/-- `hkey`: GHASH's registers for the key of the authentication key, and
`Y = 0`. -/
theorem hkey_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    WP isa (.block hkey) t fun t' =>
      GReg (hOf t.mem W) t' ∧ t'.xmm .xmm2 = 0 ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 16 + 8 ≤ 488 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 488 by decide)
  simp only [hkey, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x7, m₁, rd₁, wr₁, g₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 akO)), .mov .rdx (.mem (at_ .r15 (akO + 8))), .mov .rcx (.reg .rax),
        .alu .and .rcx (imm 1), .mov32 .r8 (imm 0), .alu .sub .r8 (.reg .rcx), .shift .shr .rax 1,
        .mov .rcx (.reg .rdx), .alu .and .rcx (imm 1), .shift .ror .rcx 1, .alu .or .rax (.reg .rcx),
        .shift .shr .rdx 1, .movImm64 .rcx 0xE100000000000000, .alu .and .rcx (.reg .r8),
        .alu .xor .rdx (.reg .rcx), .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .rdx),
        .xop (.bin .punpcklqdq .xmm7 .xmm11)] t = some t₁ ∧
      t₁.xmm .xmm7 = hOf t.mem W ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r := by
    refine ⟨_, by xrun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
        ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
        punpck_movq, add_ofNat_assoc, Nat.reduceAdd, ne_eq, not_false_eq_true]
      rw [hOf, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc, ← mulXG_words]
      rfl
    · rfl
    · rfl
    · rfl
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 Impl.Gcm.X86_64.Pclmul.poly t₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInvImm_ok s₂) fun s₃ ⟨h₃, o₃⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show s₃.xmm .xmm1 = _
    rw [o₃.xmm _ (by decide), c₂]
  · show x * φ (s₃.xmm .xmm3) = _
    rw [h₃, o₂.xmm _ (by decide), x7]
  · show XBinOp.eval .pxor (s₃.xmm .xmm2) (s₃.xmm .xmm2) = 0
    exact BitVec.xor_self
  · show s₃.mem = _
    rw [o₃.mem, o₂.mem, m₁]
  · show s₃.rd = _
    rw [o₃.rd, o₂.rd, rd₁]
  · show s₃.wr = _
    rw [o₃.wr, o₂.wr, wr₁]
  · intro r hr
    have hne : r ≠ .rax := by rintro rfl; exact absurd hr (by decide)
    show s₃.gpr r = _
    rw [o₃.gpr r hne, o₂.gpr r hne, g₁ r hr]

/-! ## Whole blocks -/

open VG.Spec.Gcm (ghashFrom)
open VG.Proof.AesGcmSiv.X86_64 (readW128_app eval_ne eval_e eval_b)
open VG.Proof.AesGcm.X86_64 (in_off ofNat_add_ofNat)

/-- The field element of block `j` at `P`. -/
abbrev xel (m : Mem) (P : Addr) (j : Nat) : Spec.Gcm.Block :=
  Spec.GcmSiv.ofBytes (bytesAt m (P + BitVec.ofNat 64 (16 * j)) 16)

theorem ghashFrom_snoc (H Y : Spec.Gcm.Block) (xs : List Spec.Gcm.Block) (v : Spec.Gcm.Block) :
    ghashFrom H Y (xs ++ [v]) = Spec.Gcm.mul (ghashFrom H Y xs ^^^ v) H := by
  simp only [ghashFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A block read as a register: its field element. -/
theorem readW_xel (m : Mem) (P : Addr) (j : Nat) : m.readW (P + BitVec.ofNat 64 (16 * j)) 128 = xel m P j := by
  rw [xel, GcmSiv.ofBytes_bytesAt, readW128_app]

/-- The block at `r12 + 16 k` into `xmm7`. -/
theorem ld_run (k : Nat) (t : State) (hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ t₁ : State, runBlock isa (ld k) t = some t₁ ∧
      t₁.xmm .xmm7 = t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (16 * k)) 128 ∧ Only [.xmm7] t t₁ := by
  refine ⟨t.setXmm .xmm7 (t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (16 * k)) 128), by xrun [ld, hin], ?_,
    fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [xmm_setXmm_self]
  · simp only [List.mem_singleton] at hr
    simp only [xmm_setXmm_of_ne _ _ hr]

/-- `j` of the `nb` blocks at `P` absorbed, from `σ`. -/
structure AInv (K W SP : Addr) (H : Spec.Gcm.Block) (σ : State) (P : Addr) (nb j : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  mem : t.mem = σ.mem
  g : GReg H t
  r12 : t.gpr .r12 = P + BitVec.ofNat 64 (16 * j)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (nb - j)
  rbp : t.gpr .rbp = σ.gpr .rbp
  y : t.xmm .xmm2 = ghashFrom H (σ.xmm .xmm2) ((List.range j).map (xel σ.mem P))

/-- One block absorbed. -/
theorem body1_ok {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb j : Nat}
    (hP : Buf K W SP σ P (16 * nb)) (hj : j < nb) {t : State} (I : AInv K W SP H σ P nb j t) :
    WP isa (.block body1) t fun t' => AInv K W SP H σ P nb (j + 1) t' ∧ t'.zf = some (decide (nb - j = 1)) := by
  have hlt := hP.lt
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (16 * 0)) 16 := by
    rw [I.r12, I.rd, I.wr, Nat.mul_zero, BitVec.add_zero]
    exact in_off hP.rd (by omega_arith) hlt
  obtain ⟨t₁, run₁, x7, o₁⟩ := ld_run 0 t hin
  simp only [body1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (mulY_ok (I.g.keep o₁ (by decide) (by decide))) fun t₂ ⟨y₂, o₂⟩ => ?_
  have h12 : t₂.gpr .r12 = P + BitVec.ofNat 64 (16 * j) := by
    rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide), I.r12]
  have hbx : t₂.gpr .rbx = BitVec.ofNat 64 (nb - j) := by
    rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide), I.rbx]
  obtain ⟨t₃, run₃, r12₃, rbx₃, zf₃, g₃, x₃, m₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] t₂ = some t₃ ∧
      t₃.gpr .r12 = P + BitVec.ofNat 64 (16 * (j + 1)) ∧ t₃.gpr .rbx = BitVec.ofNat 64 (nb - (j + 1)) ∧
      t₃.zf = some (decide (nb - j = 1)) ∧ (∀ r, r ≠ .r12 → r ≠ .rbx → t₃.gpr r = t₂.gpr r) ∧
      t₃.xmm = t₂.xmm ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12, add_ofNat_assoc]
      rw [show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        Proof.AesGcm.X86_64.sub_beq (show nb - j < 2 ^ 64 by omega_arith) (show 1 < 2 ^ 64 by decide)]
    · intro r h₁ h₂
      simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.of_runBlock ⟨t₃, run₃, ⟨?_, ?_, ?_, ?_, ?_, r12₃, rbx₃, ?_, ?_⟩, zf₃⟩
  · exact I.env.keep (fun r hr => by
      have hne : r ≠ .r12 ∧ r ≠ .rbx ∧ r ≠ .rax := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [g₃ r hne.1 hne.2.1, o₂.gpr r hne.2.2, o₁.gpr r hne.2.2]) (by rw [rd₃, o₂.rd, o₁.rd])
      (by rw [wr₃, o₂.wr, o₁.wr])
  · rw [rd₃, o₂.rd, o₁.rd, I.rd]
  · rw [wr₃, o₂.wr, o₁.wr, I.wr]
  · rw [m₃, o₂.mem, o₁.mem, I.mem]
  · exact ⟨by rw [x₃, o₂.xmm _ (by decide), o₁.xmm _ (by decide), I.g.c],
      by rw [x₃, o₂.xmm _ (by decide), o₁.xmm _ (by decide)]; exact I.g.h⟩
  · rw [g₃ _ (by decide) (by decide), o₂.gpr _ (by decide), o₁.gpr _ (by decide), I.rbp]
  · rw [x₃, y₂, x7, o₁.xmm _ (by decide), I.y, I.r12, Nat.mul_zero, BitVec.add_zero, I.mem, readW_xel,
      List.range_succ, List.map_append, List.map_cons, List.map_nil, ghashFrom_snoc]

/-! ## Four blocks -/

/-- `H'²`–`H'⁴` in `xmm4`–`xmm6`. -/
structure PW (H : Spec.Gcm.Block) (t : State) : Prop where
  p2 : x * φ (t.xmm .xmm4) = φ H ^ 2
  p3 : x * φ (t.xmm .xmm5) = φ H ^ 3
  p4 : x * φ (t.xmm .xmm6) = φ H ^ 4

/-- The block at `r12 + 16 k` added to the product with the power in `b`. -/
theorem ldAcc_ok (k : Nat) (b : XReg) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 (16 * k)) 16)
    (hb7 : b ≠ .xmm7) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (ld k ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 b)) s fun s' =>
      prod s' = (prod s).acc (s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 (16 * k)) 128) (s.xmm b) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  obtain ⟨s₁, run₁, x7, o₁⟩ := ld_run k s hin
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine WP.mono (acc_ok .xmm7 b s₁ (by decide) (by decide) (by decide) (by decide) hb8 hb9 hb10 hb11)
    fun s' ⟨p', o'⟩ => ⟨?_, o₁.trans o'⟩
  rw [p', o₁.prod (by decide) (by decide) (by decide), x7, o₁.xmm b (by simp [hb7])]

/-- The first block of a group: `Y` added to it. -/
theorem ldAccY_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 (16 * 0)) 16) :
    WP isa (.block (ld 0 ++ (([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++
      Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm6))) s fun s' =>
      prod s' = (prod s).acc (s.xmm .xmm2 ^^^ s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 (16 * 0)) 128)
        (s.xmm .xmm6) ∧
      Only [.xmm7, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  obtain ⟨s₁, run₁, x7, o₁⟩ := ld_run 0 s hin
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  refine WP.mono (acc_ok .xmm7 .xmm6 s₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s' ⟨p', o'⟩ => ⟨?_, o₁.trans (o₂.trans o')⟩
  rw [p', o₂.prod (by decide) (by decide) (by decide), o₁.prod (by decide) (by decide) (by decide), e₂, x7,
    o₁.xmm .xmm2 (by decide), o₂.xmm .xmm6 (by decide), o₁.xmm .xmm6 (by decide)]

theorem PW.keep {H : Spec.Gcm.Block} {rs : List XReg} {t t' : State} (p : PW H t) (o : Only rs t t')
    (h4 : .xmm4 ∉ rs) (h5 : .xmm5 ∉ rs) (h6 : .xmm6 ∉ rs) : PW H t' :=
  ⟨by rw [o.xmm _ h4]; exact p.p2, by rw [o.xmm _ h5]; exact p.p3, by rw [o.xmm _ h6]; exact p.p4⟩

theorem ghashFrom_snoc4 (H Y : Spec.Gcm.Block) (f : Nat → Spec.Gcm.Block) (j : Nat) :
    ghashFrom H Y ((List.range (j + 4)).map f) =
      Spec.Gcm.mul (Spec.Gcm.mul (Spec.Gcm.mul (Spec.Gcm.mul (ghashFrom H Y ((List.range j).map f) ^^^ f j) H ^^^
        f (j + 1)) H ^^^ f (j + 2)) H ^^^ f (j + 3)) H := by
  simp only [show j + 4 = j + 1 + 1 + 1 + 1 from rfl, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    ghashFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Four blocks absorbed. -/
theorem body4_ok {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb j : Nat}
    (hP : Buf K W SP σ P (16 * nb)) (hj : j + 4 ≤ nb) {t : State} (I : AInv K W SP H σ P nb j t) (pw : PW H t) :
    WP isa (.block body4) t fun t' => AInv K W SP H σ P nb (j + 4) t' ∧ PW H t' ∧
      t'.cf = some (decide (nb - (j + 4) < 4)) := by
  have hlt := hP.lt
  have inb : ∀ k < 4, InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk => by
    rw [I.r12, I.rd, I.wr, add_ofNat_assoc]
    exact in_off hP.rd (by omega_arith) hlt
  rw [show body4 = Impl.Gcm.X86_64.Pclmul.zero ++ ((ld 0 ++ (([.xop (.bin .pxor .xmm7 .xmm2)] : List Instr) ++
      Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm6)) ++ ((ld 1 ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm5) ++
      ((ld 2 ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm4) ++ ((ld 3 ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm3) ++
      (Impl.Gcm.X86_64.Pclmul.reduce .xmm2 ++ ([.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4),
        .alu .cmp .rbx (imm 4)] : List Instr)))))) from by simp only [body4, List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok t) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldAccY_ok s₁ (by rw [o₁.gpr _ (by decide), o₁.rd, o₁.wr]; exact inb 0 (by decide)))
    fun s₂ ⟨p₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldAcc_ok 1 .xmm5 s₂ (by rw [O₂.gpr _ (by decide), O₂.rd, O₂.wr]; exact inb 1 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨p₃, o₃⟩ => ?_
  have O₃ := O₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (ldAcc_ok 2 .xmm4 s₃ (by rw [O₃.gpr _ (by decide), O₃.rd, O₃.wr]; exact inb 2 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨p₄, o₄⟩ => ?_
  have O₄ := O₃.trans o₄
  rw [WP.block_append_iff]
  refine WP.mono (ldAcc_ok 3 .xmm3 s₄ (by rw [O₄.gpr _ (by decide), O₄.rd, O₄.wr]; exact inb 3 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨p₅, o₅⟩ => ?_
  have O₅ := O₄.trans o₅
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₅ (by decide) (by decide) (by decide) (by decide)
    (by rw [O₅.xmm _ (by decide), I.g.c])) fun s₆ ⟨e₆, o₆⟩ => ?_
  have O₆ := O₅.trans o₆
  have h12 : s₆.gpr .r12 = P + BitVec.ofNat 64 (16 * j) := by rw [O₆.gpr _ (by decide), I.r12]
  have hbx : s₆.gpr .rbx = BitVec.ofNat 64 (nb - j) := by rw [O₆.gpr _ (by decide), I.rbx]
  obtain ⟨t₇, run₇, r12₇, rbx₇, cf₇, g₇, x₇, m₇, rd₇, wr₇⟩ : ∃ t₇ : State, runBlock isa
      [.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4), .alu .cmp .rbx (imm 4)] s₆ = some t₇ ∧
      t₇.gpr .r12 = P + BitVec.ofNat 64 (16 * (j + 4)) ∧ t₇.gpr .rbx = BitVec.ofNat 64 (nb - (j + 4)) ∧
      t₇.cf = some (decide (nb - (j + 4) < 4)) ∧ (∀ r, r ≠ .r12 → r ≠ .rbx → t₇.gpr r = s₆.gpr r) ∧
      t₇.xmm = s₆.xmm ∧ t₇.mem = s₆.mem ∧ t₇.rd = s₆.rd ∧ t₇.wr = s₆.wr := by
    refine ⟨_, by srun [h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12, add_ofNat_assoc]
      rw [show 16 * j + 64 = 16 * (j + 4) by omega_arith]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
      simp only [Proof.AesGcm.X86_64.toNat_ofNat_of_lt (show nb - (j + 4) < 2 ^ 64 by omega_arith)]
      rfl
    · intro r h₁ h₂
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.of_runBlock ⟨t₇, run₇, ⟨?_, ?_, ?_, ?_, ?_, r12₇, rbx₇, ?_, ?_⟩, ?_, cf₇⟩
  · exact I.env.keep (fun r hr => by
      have hne : r ≠ .r12 ∧ r ≠ .rbx ∧ r ≠ .rax := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [g₇ r hne.1 hne.2.1, O₆.gpr r hne.2.2]) (by rw [rd₇, O₆.rd]) (by rw [wr₇, O₆.wr])
  · rw [rd₇, O₆.rd, I.rd]
  · rw [wr₇, O₆.wr, I.wr]
  · rw [m₇, O₆.mem, I.mem]
  · exact ⟨by rw [x₇, O₆.xmm _ (by decide), I.g.c], by rw [x₇, O₆.xmm _ (by decide)]; exact I.g.h⟩
  · rw [g₇ _ (by decide) (by decide), O₆.gpr _ (by decide), I.rbp]
  · have rd : ∀ k, t.mem.readW (P + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * k)) 128 = xel σ.mem P (j + k) :=
      fun k => by rw [add_ofNat_assoc, ← Nat.mul_add, I.mem, readW_xel]
    rw [x₇, e₆, p₅, p₄, p₃, p₂, p₁, O₄.gpr _ (by decide), O₄.mem, O₄.xmm .xmm3 (by decide),
      O₃.gpr _ (by decide), O₃.mem, O₃.xmm .xmm4 (by decide), O₂.gpr _ (by decide), O₂.mem,
      O₂.xmm .xmm5 (by decide), o₁.gpr _ (by decide), o₁.mem, o₁.xmm .xmm6 (by decide), o₁.xmm .xmm2 (by decide),
      I.r12, rd 0, rd 1, rd 2, rd 3, I.y, ghashFrom_snoc4,
      step4 H _ _ _ _ _ _ _ _ _ I.g.h pw.p2 pw.p3 pw.p4]
    rfl
  · exact ⟨by rw [x₇, O₆.xmm _ (by decide)]; exact pw.p2, by rw [x₇, O₆.xmm _ (by decide)]; exact pw.p3,
      by rw [x₇, O₆.xmm _ (by decide)]; exact pw.p4⟩

end VG.Proof.AesGcmSivReg.X86_64
