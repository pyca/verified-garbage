module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Keys
public import VerifiedGarbage.Proof.GcmSiv.MulX
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Stream
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
open VG.Impl.AesGcmSiv.X86_64 (akO bO)
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


/-! ## The whole blocks -/

theorem AInv.flags {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb j : Nat} {t : State}
    (I : AInv K W SP H σ P nb j t) (x : BitVec 64) (c o : Bool) : AInv K W SP H σ P nb j (arithFlags t x c o) :=
  ⟨I.env.keep (fun _ _ => rfl) rfl rfl, I.rd, I.wr, I.mem, ⟨I.g.c, I.g.h⟩, I.r12, I.rbx, I.rbp, I.y⟩

theorem AInv.only {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb j : Nat} {rs : List XReg}
    {t t' : State} (I : AInv K W SP H σ P nb j t) (o : Only rs t t') (h1 : .xmm1 ∉ rs) (h2 : .xmm2 ∉ rs)
    (h3 : .xmm3 ∉ rs) : AInv K W SP H σ P nb j t' :=
  ⟨I.env.keep (fun r hr => o.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      o.rd o.wr, o.rd.trans I.rd, o.wr.trans I.wr, o.mem.trans I.mem, I.g.keep o h1 h3,
    (o.gpr _ (by decide)).trans I.r12, (o.gpr _ (by decide)).trans I.rbx, (o.gpr _ (by decide)).trans I.rbp,
    (o.xmm _ h2).trans I.y⟩

/-- `cmp rbx, 4` with `k` in `rbx`: CF says whether `k < 4`. -/
theorem cmpbx_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .rbx = BitVec.ofNat 64 k) :
    ∃ (x : BitVec 64) (o : Bool), runBlock isa [.alu .cmp .rbx (imm 4)] u =
      some (arithFlags u x (decide (k < 4)) o) := by
  have e4 : BitVec.signExtend 64 (BitVec.ofNat 32 4) = BitVec.ofNat 64 4 := by decide
  refine ⟨BitVec.ofNat 64 k - BitVec.ofNat 64 4,
    subOverflow (BitVec.ofNat 64 k) (BitVec.ofNat 64 4) (BitVec.ofNat 64 k - BitVec.ofNat 64 4), ?_⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, imm, h, Option.bind_some]
  rw [e4]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- `test r, r` with `k` in `r`: ZF says whether `k = 0`. -/
theorem test_run (r : Reg) (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr r = BitVec.ofNat 64 k) :
    runBlock isa [.alu .test r (.reg r)] u = some (arithFlags u (BitVec.ofNat 64 k) false false) ∧
      (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  refine ⟨?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some, h,
      BitVec.and_self]
  · by_cases hk0 : k = 0
    · subst hk0; rfl
    · have : BitVec.ofNat 64 k ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
        exact hk0 this
      rw [beq_eq_false_iff_ne.mpr this, decide_eq_false hk0]

/-- The loop of single blocks, from any block before the last. -/
theorem ones_ok {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb j₀ : Nat}
    (hP : Buf K W SP σ P (16 * nb)) (hj₀ : j₀ < nb) {t : State} (I₀ : AInv K W SP H σ P nb j₀ t) :
    WP isa (.loop (.block body1) .ne) t (AInv K W SP H σ P nb nb) := by
  refine WP.loop (M := isa) (body := .block body1) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = nb - j ∧ j < nb ∧ AInv K W SP H σ P nb j t) ?_ (nb - j₀) t
    ⟨j₀, rfl, hj₀, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  refine WP.mono (body1_ok hP hj I) fun t' ⟨I', hz⟩ => ?_
  have ev : isa.eval .ne t' = some !(decide (nb - j = 1)) := by
    show t'.zf.map (!·) = _; rw [hz]; rfl
  by_cases h1 : nb - j = 1
  · left
    refine ⟨by rw [ev, decide_eq_true h1]; rfl, ?_⟩
    rw [show nb = j + 1 by omega_arith]; rw [show nb = j + 1 by omega_arith] at I'; exact I'
  · right
    exact ⟨by rw [ev, decide_eq_false h1]; rfl, nb - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

/-- The whole blocks absorbed. -/
theorem absorbBlocks_ok (four : Bool) {K W SP : Addr} {H : Spec.Gcm.Block} {σ : State} {P : Addr} {nb : Nat}
    (hP : Buf K W SP σ P (16 * nb)) {t : State} (I : AInv K W SP H σ P nb 0 t)
    (hz : t.zf = some (decide (nb = 0))) :
    WP isa (absorbBlocks four) t (AInv K W SP H σ P nb nb) := by
  have hlt := hP.lt
  have ones : ∀ k, k ≤ nb → ∀ u, AInv K W SP H σ P nb k u →
      WP isa (.seq (.block [.alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop (.block body1) .ne))) u
        (AInv K W SP H σ P nb nb) := by
    intro k hk u Iu
    obtain ⟨run₂, hy⟩ := test_run .rbx u (k := nb - k) (by omega_arith) Iu.rbx
    refine WP.seq (WP.of_runBlock ⟨_, run₂, ?_⟩)
    have I₃ := Iu.flags (BitVec.ofNat 64 (nb - k)) false false
    refine WP.ite (decide (nb - k = 0)) (by rw [← hy]; rfl) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
    · have : k = nb := by simp at h0; omega_arith
      subst this; exact I₃
    · exact ones_ok hP (by simp at h0; omega_arith) I₃
  cases four
  · simp only [absorbBlocks, Bool.false_eq_true, ite_false]
    refine WP.ite (decide (nb = 0)) hz (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
    · have : nb = 0 := by simpa using h0
      subst this; exact I
    · exact ones_ok hP (by simp at h0; omega_arith) I
  · simp only [absorbBlocks, ite_true]
    refine WP.ite (decide (nb = 0)) hz (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
    · have : nb = 0 := by simpa using h0
      subst this; exact I
    obtain ⟨x, o, run₁⟩ := cmpbx_run t (k := nb) (by omega_arith) (by rw [I.rbx, Nat.sub_zero])
    refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
    have I₁ := I.flags x (decide (nb < 4)) o
    have mid : WP isa (.ite .b (.block []) (.seq (.block Impl.Gcm.X86_64.Pclmul.pows) (.loop (.block body4) .ae)))
        (arithFlags t x (decide (nb < 4)) o) fun v => ∃ k, k ≤ nb ∧ AInv K W SP H σ P nb k v := by
      refine WP.ite (decide (nb < 4)) rfl (fun _ => WP.block_nil ⟨0, Nat.zero_le _, I₁⟩) (fun h4 => ?_)
      have h4' : ¬ nb < 4 := by simpa using h4
      refine WP.seq (WP.mono (Proof.Gcm.X86_64.Pclmul.pows_ok _ I₁.g.c I₁.g.h) fun u₁ ⟨p2, p3, p4, o₁⟩ => ?_)
      have Iu := I₁.only o₁ (by decide) (by decide) (by decide)
      refine WP.loop (M := isa) (body := .block body4) (c := .ae)
        (fun (m : Nat) (v : State) => ∃ k, m = nb - k ∧ k + 4 ≤ nb ∧ AInv K W SP H σ P nb k v ∧ PW H v) ?_
        (nb - 0) u₁ ⟨0, rfl, by omega_arith, Iu, ⟨p2, p3, p4⟩⟩
      rintro m v ⟨k, rfl, hk, Iv, pv⟩
      refine WP.mono (body4_ok hP hk Iv pv) fun v' ⟨Iv', pv', hcf'⟩ => ?_
      have ev : isa.eval .ae v' = some !(decide (nb - (k + 4) < 4)) := by
        show v'.cf.map (!·) = _; rw [hcf']; rfl
      by_cases hlt4 : nb - (k + 4) < 4
      · left
        exact ⟨by rw [ev, decide_eq_true hlt4]; rfl, k + 4, hk, Iv'⟩
      · right
        exact ⟨by rw [ev, decide_eq_false hlt4]; rfl, nb - (k + 4), by omega_arith, k + 4, rfl, by omega_arith,
          Iv', pv'⟩
    exact WP.seq (WP.mono mid fun v ⟨k, hk, Iv⟩ => ones k hk v Iv)

/-! ## The last bytes, and a whole input -/

open VG.Proof.AesGcmSiv.X86_64 (writeW128_app pxor_self pad_bytes)

/-- What absorbing the elements `xs` leaves. -/
structure APost (K W SP : Addr) (H : Spec.Gcm.Block) (xs : List Spec.Gcm.Block) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t'.mem
  g : GReg H t'
  y : t'.xmm .xmm2 = ghashFrom H (t.xmm .xmm2) xs

/-- The last `r` bytes, padded, absorbed. -/
theorem tail_ok {K W SP : Addr} (L : Lay K W SP) {H : Spec.Gcm.Block} {t : State} (E : Env K W SP t)
    (g : GReg H t) {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hP : Buf K W SP t P r)
    (hsi : t.gpr .rsi = P) (hcx : t.gpr .rcx = BitVec.ofNat 64 r) :
    WP isa absorbTail t
      (APost K W SP H [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have h15 := E.r15
  have hw := L.ww
  obtain w₀ := E.perm.wW (show 128 + 16 ≤ 488 by decide)
  obtain ⟨t₁, run₁, hm₁, hdi₁, hg₁, hx₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa (ptr .rdi .r15 bO ++ ([.xop (.bin .pxor .xmm7 .xmm7), .movdquStore (at_ .rdi 0) .xmm7] : List Instr)) t =
        some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (W + BitVec.ofNat 64 128) ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 128 ∧
      (∀ r, r ≠ .rdi → t₁.gpr r = t.gpr r) ∧ (∀ r, r ≠ .xmm7 → t₁.xmm r = t.xmm r) ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by xrun [ptr, bO, h15, w₀, pxor_self], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [mem_setReg, mem_arithFlags, mem_setXmm, gpr_setXmm, gpr_setReg,
        gpr_arithFlags, ite_true, ite_false, reduceCtorEq, xmm_setXmm_self, pxor_self, writeW128_app,
        Proof.Cmac.zero2, h15, add_ofNat_assoc, ne_eq, not_false_eq_true]
      rfl
    · simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h15]
    · intro r h; simp only [gpr_arithFlags, gpr_setReg, gpr_setXmm, h, ite_false]
    · intro r h; simp only [xmm_setXmm_of_ne _ _ h, xmm_setReg, xmm_arithFlags]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain lp : Proof.AesGcm.X86_64.LoopPre t₁ P (W + BitVec.ofNat 64 128) r :=
    ⟨by rw [hg₁ _ (by decide), hsi], hdi₁, by rw [hg₁ _ (by decide), hcx], hr1, by omega_arith,
      by rw [hrd₁, hwr₁]; exact hP.rd, by rw [hwr₁]; exact E.perm.wC (by omega_arith),
      hP.w.sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.seq (WP.mono (Proof.AesGcm.X86_64.copyLoopX_ok t₁ lp) fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂, hx₂⟩ => ?_)
  obtain hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁, Proof.Cmac.zero2]
    exact Proof.AesGcm.X86_64.bytesAt_frame
      (((Frame.refl [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region)] _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide)))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  obtain hb₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    obtain hl := Proof.Cmac.bytesAt_length t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  obtain fr₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₂.mem := by
    obtain f₁ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₁.mem := by
      rw [hm₁, Proof.Cmac.zero2]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains W (Nat.le_refl _) (by decide) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (show 8 + 8 ≤ 16 by decide) (by decide))
    refine f₁.trans ?_
    rw [hm₂]
    obtain f₂ : Frame [⟨W + BitVec.ofNat 64 128, r⟩] t₁.mem
        (VG.WriteBytes.writeBytes t₁.mem (W + BitVec.ofNat 64 128) (bytesAt t₁.mem P r)) :=
      VG.WriteBytes.writeBytes_frame _ _ _ (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)
    exact f₂.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  obtain hdi₂ : t₂.gpr .rdi = W + BitVec.ofNat 64 128 := by rw [hg₂ _ (by decide) (by decide), hdi₁]
  obtain rin : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 128) 16 := by
    rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact E.perm.wR (by decide)
  obtain ⟨t₃, run₃, x7, o₃⟩ : ∃ t₃ : State, runBlock isa [.movdquLoad .xmm7 (at_ .rdi 0)] t₂ = some t₃ ∧
      t₃.xmm .xmm7 = t₂.mem.readW (W + BitVec.ofNat 64 128) 128 ∧ Only [.xmm7] t₂ t₃ := by
    refine ⟨t₂.setXmm .xmm7 (t₂.mem.readW (W + BitVec.ofNat 64 128) 128), by xrun [hdi₂, rin], ?_,
      fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
    · simp only [xmm_setXmm_self]
    · simp only [List.mem_singleton] at hr
      simp only [xmm_setXmm_of_ne _ _ hr]
  obtain g₃ : GReg H t₃ :=
    ⟨by rw [o₃.xmm _ (by decide), hx₂, hx₁ _ (by decide)]; exact g.c,
      by rw [o₃.xmm _ (by decide), hx₂, hx₁ _ (by decide)]; exact g.h⟩
  rw [show (([.movdquLoad .xmm7 (at_ .rdi 0)] : List Instr) ++ mulY) =
    ([.movdquLoad .xmm7 (at_ .rdi 0)] : List Instr) ++ mulY from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  refine WP.mono (mulY_ok g₃) fun t₄ ⟨y₄, o₄⟩ => ?_
  have hgp : ∀ q, q ≠ .rax → q ≠ .r10 → q ≠ .rdi → t₄.gpr q = t.gpr q := fun q h₁ h₂ h₃ => by
    rw [o₄.gpr q h₁, o₃.gpr q h₁, hg₂ q h₁ h₂, hg₁ q h₃]
  refine ⟨E.keep (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact hgp _ (by decide) (by decide) (by decide))
      (by rw [o₄.rd, o₃.rd, hrd₂, hrd₁]) (by rw [o₄.wr, o₃.wr, hwr₂, hwr₁]),
    by rw [o₄.rd, o₃.rd, hrd₂, hrd₁], by rw [o₄.wr, o₃.wr, hwr₂, hwr₁],
    by rw [o₄.mem, o₃.mem]; exact fr₂, g₃.keep o₄ (by decide) (by decide), ?_⟩
  rw [y₄, x7, o₃.xmm _ (by decide), hx₂, hx₁ _ (by decide), ← hb₂, GcmSiv.ofBytes_bytesAt, ← readW128_app]
  simp only [ghashFrom, List.foldl_cons, List.foldl_nil]

/-- The `n` bytes at `Q`, padded, absorbed. -/
theorem absorb_ok (four : Bool) {K W SP : Addr} (L : Lay K W SP) {H : Spec.Gcm.Block} {t : State}
    (E : Env K W SP t) (g : GReg H t) {Q : Addr} {n : Nat} (hQ : Buf K W SP t Q n) (h12 : t.gpr .r12 = Q)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 n) :
    WP isa (absorb four) t (APost K W SP H (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q n))) t) := by
  have hn := hQ.lt
  obtain ⟨t₁, run₁, hbx₁, hzf₁, hg₁, hx₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .test .rbx (.reg .rbx)] t = some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ t₁.zf = some (decide (n / 16 = 0)) ∧
      (∀ r, r ≠ .rbx → t₁.gpr r = t.gpr r) ∧ t₁.xmm = t.xmm ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
        Proof.AesGcm.X86_64.shr4 _ hn]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hn]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
    · intro r h₁; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain I₁ : AInv K W SP H t Q (n / 16) 0 t₁ :=
    ⟨E.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁, hrd₁, hwr₁, hm₁,
      ⟨by rw [hx₁]; exact g.c, by rw [hx₁]; exact g.h⟩,
      by rw [hg₁ _ (by decide), h12, Nat.mul_zero, BitVec.add_zero], by rw [hbx₁, Nat.sub_zero],
      hg₁ _ (by decide), by rw [hx₁]; rfl⟩
  refine WP.seq (WP.mono (absorbBlocks_ok four (hQ.take (k := 16 * (n / 16)) (by omega_arith)) I₁ hzf₁)
    fun t₂ I₂ => ?_)
  obtain hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 n := I₂.rbp.trans hbp
  obtain ⟨t₃, run₃, hsi₃, hcx₃, hzf₃, hg₃, hx₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa [.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp), .alu .and .rcx (imm 15),
        .alu .test .rcx (.reg .rcx)] t₂ = some t₃ ∧
      t₃.gpr .rsi = Q + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₃.gpr .rcx = BitVec.ofNat 64 (n % 16) ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, r ≠ .rsi → r ≠ .rcx → t₃.gpr r = t₂.gpr r) ∧
      t₃.xmm = t₂.xmm ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, I₂.r12]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp₂, imm, hand]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hbp₂, imm, hand]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
    · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain E₃ : Env K W SP t₃ := I₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  obtain g₃ : GReg H t₃ := ⟨by rw [hx₃]; exact I₂.g.c, by rw [hx₃]; exact I₂.g.h⟩
  obtain y₃ : t₃.xmm .xmm2 = ghashFrom H (t.xmm .xmm2) (Proof.AesGcmSiv.X86_64.elemsAt t.mem Q (n / 16)) := by
    rw [hx₃, I₂.y]
  rw [Proof.AesGcmSiv.X86_64.elems_pad16_bytesAt]
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil ⟨E₃, hrd₃.trans I₂.rd, hwr₃.trans I₂.wr, by rw [hm₃, I₂.mem]; exact Frame.refl _ _, g₃, y₃⟩
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    obtain hP : Buf K W SP t₃ (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hQ.slice (by omega_arith)).of_eq (hrd₃.trans I₂.rd) (hwr₃.trans I₂.wr)
    refine WP.mono (tail_ok L E₃ g₃ (by omega_arith) (by omega_arith) hP hsi₃ hcx₃) fun t₄ T => ?_
    refine ⟨T.env, T.rd.trans (hrd₃.trans I₂.rd), T.wr.trans (hwr₃.trans I₂.wr),
      by have := T.frame; rw [hm₃, I₂.mem] at this; exact this, T.g, ?_⟩
    rw [T.y, y₃, hm₃, I₂.mem, ← Proof.Gcm.ghashFrom_append]

/-! ## The lengths block, and POLYVAL -/

open VG.Impl.AesGcmSiv.X86_64 (aadO alenO dataO lenO)

/-- The lengths block absorbed. -/
theorem lens_ok {K W SP : Addr} {H : Spec.Gcm.Block} {t : State} (E : Env K W SP t) (g : GReg H t) {al n : Nat}
    (hal : t.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (hn : t.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) (hal' : al < 2 ^ 64) (hn' : n < 2 ^ 64) :
    WP isa (.block lens) t fun t' =>
      t'.xmm .xmm2 = Spec.Gcm.mul (t.xmm .xmm2 ^^^
        Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))) H ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r := by
  have h15 := E.r15
  obtain r₁ := E.perm.wR (show 240 + 8 ≤ 488 by decide)
  obtain r₂ := E.perm.wR (show 224 + 8 ≤ 488 by decide)
  obtain ⟨t₁, run₁, x7, x2, x1, x3, m₁, rd₁, wr₁, g₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax),
        .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
        .alu .add .rdx (.reg .rdx),
        .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .rdx), .xop (.bin .punpcklqdq .xmm7 .xmm11)] t = some t₁ ∧
      t₁.xmm .xmm7 = BitVec.ofNat 64 (8 * n) ++ BitVec.ofNat 64 (8 * al) ∧ t₁.xmm .xmm2 = t.xmm .xmm2 ∧
      t₁.xmm .xmm1 = t.xmm .xmm1 ∧ t₁.xmm .xmm3 = t.xmm .xmm3 ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r := by
    refine ⟨_, by xrun [alenO, lenO, h15, r₁, r₂, hal, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
        ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
        mem_setReg, mem_arithFlags, mem_setXmm, alenO, lenO, h15, hal, hn,
        punpck_movq, Proof.AesGcm.X86_64.times8_val, Proof.AesGcm.X86_64.toNat_ofNat_of_lt hal',
        Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn', ne_eq, not_false_eq_true]
    · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags, ne_eq,
        not_false_eq_true]
    · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags, ne_eq,
        not_false_eq_true]
    · simp (config := {decide := true}) only [xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags, ne_eq,
        not_false_eq_true]
    · rfl
    · rfl
    · rfl
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  simp only [lens]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  refine WP.mono (mulY_ok (H := H) ⟨x1.trans g.c, by rw [x3]; exact g.h⟩) fun t₂ ⟨y₂, o₂⟩ => ?_
  refine ⟨?_, o₂.mem.trans m₁, o₂.rd.trans rd₁, o₂.wr.trans wr₁, fun r hr => ?_⟩
  · rw [y₂, x7, x2, GcmSiv.le64_le8, GcmSiv.le64_le8, GcmSiv.ofBytes_le8]
  · rw [o₂.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide),
      g₁ r hr]

/-- What `polyval` leaves: POLYVAL of the padded additional data, the padded
data and the lengths block in `xmm2`, as GHASH with the key's `mulXG`. -/
structure PolyPost (K W SP : Addr) (A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t'.mem
  out : t'.xmm .xmm2 = ghashFrom (hOf t.mem W) 0
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem A al)) ++
      Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem D n)) ++
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * al) ++ Spec.GcmSiv.le64 (8 * n))])

theorem polyval_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n) :
    WP isa polyval t (PolyPost K W SP A D al n t) := by
  have hw := L.ww
  have slot : ∀ {m : Mem}, Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem m → ∀ d, 200 ≤ d → d + 8 ≤ 248 →
      m.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun hf d h₁ h₂ =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)) (by decide)
  have ld : ∀ (u : State) (o : Nat) (P : Addr) (k : Nat), Env K W SP u → 200 ≤ o → o + 16 ≤ 248 →
      u.mem.readW (W + BitVec.ofNat 64 o) 64 = P → u.mem.readW (W + BitVec.ofNat 64 (o + 8)) 64 = BitVec.ofNat 64 k →
      ∃ u' : State, runBlock isa [.mov .r12 (.mem (at_ .r15 o)), .mov .rbp (.mem (at_ .r15 (o + 8)))] u = some u' ∧
        u'.gpr .r12 = P ∧ u'.gpr .rbp = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → u'.gpr r = u.gpr r) ∧
        u'.xmm = u.xmm ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
    intro u o P k Eu h₁ h₂ hP hk
    have h15 := Eu.r15
    obtain r₁ := Eu.perm.wR (show o + 8 ≤ 488 by omega_arith)
    obtain r₂ := Eu.perm.wR (show o + 8 + 8 ≤ 488 by omega_arith)
    refine ⟨_, by srun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, hP]
    · simp only [gpr_setReg, mem_setReg, ite_true, ite_false, reduceCtorEq, h15, hk]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  simp only [polyval]
  rw [show (hkey ++ ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr)) =
    hkey ++ ([.mov .r12 (.mem (at_ .r15 216)), .mov .rbp (.mem (at_ .r15 (216 + 8)))] : List Instr) from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (hkey_ok E) fun t₁ ⟨g₁, y₁, m₁, rd₁, wr₁, sv₁⟩ => ?_
  have E₁ : Env K W SP t₁ := E.of_saved sv₁ rd₁ wr₁
  obtain ⟨t₂, run₂, r12₂, rbp₂, g₂, x₂, m₂, rd₂, wr₂⟩ := ld t₁ 216 A al E₁ (by decide) (by decide)
    (by rw [m₁]; exact S.aad) (by rw [m₁]; exact S.alen)
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
  have mem₂ : t₂.mem = t.mem := m₂.trans m₁
  refine WP.seq (WP.mono (absorb_ok false L E₂ ⟨by rw [x₂]; exact g₁.c, by rw [x₂]; exact g₁.h⟩
    (hA.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) r12₂ rbp₂) fun t₃ P₃ => ?_)
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₃.mem := mem₂ ▸ P₃.frame
  obtain ⟨t₄, run₄, r12₄, rbp₄, g₄, x₄, m₄, rd₄, wr₄⟩ := ld t₃ 232 D n P₃.env (by decide) (by decide)
    (by rw [slot fr₃ 232 (by decide) (by decide)]; exact S.data)
    (by rw [slot fr₃ 240 (by decide) (by decide)]; exact S.len)
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  have E₄ : Env K W SP t₄ := P₃.env.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₄ wr₄
  have rd₄' : t₄.rd = t.rd := by rw [rd₄, P₃.rd, rd₂, rd₁]
  have wr₄' : t₄.wr = t.wr := by rw [wr₄, P₃.wr, wr₂, wr₁]
  refine WP.seq (WP.mono (absorb_ok true L E₄ ⟨by rw [x₄]; exact P₃.g.c, by rw [x₄]; exact P₃.g.h⟩
    (hD.of_eq rd₄' wr₄') r12₄ rbp₄) fun t₅ P₅ => ?_)
  have fr₅ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t.mem t₅.mem := fr₃.trans (m₄ ▸ P₅.frame)
  refine WP.mono (lens_ok P₅.env P₅.g (al := al) (n := n)
    (by rw [slot fr₅ 224 (by decide) (by decide)]; exact S.alen)
    (by rw [slot fr₅ 240 (by decide) (by decide)]; exact S.len) hA.lt hD.lt) fun t₆ ⟨y₆, m₆, rd₆, wr₆, g₆⟩ => ?_
  have eD : bytesAt t₄.mem D n = bytesAt t.mem D n := by
    rw [m₄]
    exact Proof.AesGcm.X86_64.bytesAt_frame fr₃ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))) (Nat.le_of_lt hD.lt)
  refine ⟨P₅.env.keep g₆ rd₆ wr₆, by rw [rd₆, P₅.rd, rd₄'], by rw [wr₆, P₅.wr, wr₄'], m₆ ▸ fr₅, ?_⟩
  rw [y₆, P₅.y, x₄, P₃.y, x₂, y₁, eD, mem₂, ← ghashFrom_snoc, ← Proof.Gcm.ghashFrom_append, List.append_assoc]

end VG.Proof.AesGcmSivReg.X86_64
