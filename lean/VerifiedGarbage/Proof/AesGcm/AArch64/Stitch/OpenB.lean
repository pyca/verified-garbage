module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on AArch64, interleaved: `open`'s branch on the tag

Untrusted: everything here is checked by Lean. `openRunWithS` is `openRunAS`,
up to the branch on the tag, then `omBS` (`openRunWithS_split`). Before the
branch (`MidS`), the interleaved loop has decrypted the first `P` bytes of
the text and kept the first counter block at `W + cbO`; `omBS` decrypts the
rest if the tag is right, and encrypts the first `P` bytes again from the
kept counter block if not, which leaves them as they were (`omBS_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Impl.Gcm.AArch64.Pmull (Y)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

section
variable (c : Callees) (cl : Prog isa) (tb : List Instr)

/-- `openRunWithS` up to the branch on the tag. -/
def openRunAS : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.front
  (.seq (.block [.ldrq .v0 .x20 48, .strq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO])
  (.seq (Impl.AesGcm.AArch64.Stitch.stitched [] tb Impl.Gcm.AArch64.Stitch.dec)
  (.seq (.block (Impl.AesGcm.AArch64.Stitch.whole ++ [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] ++
      absSeg2 16))
  (.seq cl
  (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
      [mov .x13 .x24, mov .x12 .x23]))
  (.seq Impl.AesGcm.AArch64.Fast.padMul
  (.seq (.block (Impl.AesGcm.AArch64.Fast.lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
    (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))))

/-- If the tag is wrong: the first bytes encrypted again, from the kept
counter block. -/
def failB : Prog isa :=
  .seq (.block ([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48, .ldr .x .x23 .x19 dataO,
      .ldr .x .x26 .x19 lenO] ++ Impl.AesGcm.AArch64.Stitch.whole ++ [mov .x24 .x9, imm .x25 0])) (cryptAl c)

/-- If the tag is right: the rest decrypted. -/
def okB : Prog isa :=
  .seq (.block ([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0])) (cryptAl c)

/-- The branch on the tag. -/
def omBS : Prog isa := .seq (.ite (.zero .x .x27) (failB c) (okB c)) (.block [mov .x0 .x27])

/-- `openRunWithS` is `openRunAS` then `omBS`. -/
theorem openRunWithS_split :
    PEq (.seq (openRunAS c cl tb) (omBS c)) (Impl.AesGcm.AArch64.Stitch.openRunWithS c tb cl) := by
  unfold openRunAS omBS failB okB Impl.AesGcm.AArch64.Stitch.openRunWithS
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

end

/-- XORing with the keystream twice leaves the text. -/
theorem xorKs_xorKs (ciph : Block → Block) (icb : Block) (k : Nat) (d : List Byte) :
    xorKs ciph icb k (xorKs ciph icb k d) = d := by
  refine Proof.Gcm.list_ext (by rw [Proof.Gcm.length_xorKs, Proof.Gcm.length_xorKs]) fun i hi => ?_
  simp only [Proof.Gcm.length_xorKs] at hi
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by simpa only [Proof.Gcm.length_xorKs] using hi),
    Proof.Gcm.getD_xorKs _ _ _ _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A block copied. -/
theorem blockAt_copy (m : Mem) (a b : Addr) : blockAt (m.write a 16 (m.read b 16)) a = blockAt m b := by
  simp only [blockAt, Spec.Aes.bytesAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi', ite_true]
  exact Mem.extractLsb'_read m b hi'

/-- Before the branch on the tag, from `s` (after `open`'s entry): `MidO`,
but for the first `P` bytes of the text, decrypted, the counter block past
them, and the first counter block at `W + cbO`. -/
structure MidS (fr : List Region) (Ctx W SP D Np A : Addr) (R nl al n tl P : Nat) (s s₇ : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame fr s.mem s₇.mem
  x22 : s₇.gpr .x22 = BitVec.ofNat 64 R
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : DataW Ctx (W + BitVec.ofNat 64 16) W s₇ D n
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  hP : P = 128 * (n / 128)
  pre : bytesAt s₇.mem D P = xorKs (ciphOf s.mem Ctx R)
    (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))) 0 (bytesAt s.mem D P)
  rest : bytesAt s₇.mem (D + BitVec.ofNat 64 P) (n - P) = bytesAt s.mem (D + BitVec.ofNat 64 P) (n - P)
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (P / 16) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)))
  cbs : blockAt s₇.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))
  ciph : ciphOf s₇.mem Ctx R = ciphOf s.mem Ctx R

section
variable {Ctx W SP D Np A : Addr} {R nl al n tl P : Nat} (L : Lay Ctx (W + BitVec.ofNat 64 16) W)
include L

omit L in
theorem failArgs_ok {fr : List Region} {s s₇ : State} (mo : MidS fr Ctx W SP D Np A R nl al n tl P s s₇) :
    ∃ s₈, runBlock isa (([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48,
      .ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [mov .x24 .x9, imm .x25 0]) s₇ = some s₈ ∧
      s₈.mem = s₇.mem.write (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16
        (s₇.mem.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16) ∧
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 P ∧ s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧
      Others [.x9, .x23, .x24, .x25, .x26] s₇ s₈ ∧ s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
  have he := mo.env
  have hn := mo.data.ok.lt
  have q₀ := he.perm.wR (show 320 + 16 ≤ 2560 by decide)
  have q₁ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have w₀ := he.perm.stW (show 48 + 16 ≤ 80 by decide)
  have e₁ : s₇.mem.read (W + 232#64) 8 = D := by
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, mo.sD]
  have e₂ : s₇.mem.read (W + 240#64) 8 = BitVec.ofNat 64 n := by
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, mo.sN]
  have rs : ∀ {v : BitVec (8 * 16)} (d : Nat), 80 ≤ d → d + 8 ≤ 2560 →
      (s₇.mem.write (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16 v).read (W + BitVec.ofNat 64 d) 8 =
        s₇.mem.read (W + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    rw [add_ofNat_assoc]
    exact Mem.read_write_sep (Offset.sep W (.inr (by omega)) (by omega) (by decide)) (by decide)
  have e₉ : (BitVec.ofNat 64 n >>> 7) <<< 7 = BitVec.ofNat 64 P := by
    rw [Gcm.AArch64.Stitch.ushr7 hn, Stitch.shl7 (by have := Nat.mul_div_le n 128; omega), ← mo.hP]
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20, q₀, q₁,
    q₂, w₀, gpr_setV, wr_setV, rd_setV, mem_setV, sp_setV, v_setV_self], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp [mem_write, he.x20, Impl.AesGcm.AArch64.Stitch.cbO]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [rs 232 (by decide) (by decide), e₁]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [rs 240 (by decide) (by decide), e₂, e₉, BitVec.add_zero]
  · simp [gpr_write]

omit L in
theorem okArgs_ok {fr : List Region} {s s₇ : State} (mo : MidS fr Ctx W SP D Np A R nl al n tl P s s₇) :
    ∃ s₈, runBlock isa (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr)) s₇ = some s₈ ∧
      s₈.gpr .x23 = D + BitVec.ofNat 64 P ∧ s₈.gpr .x24 = BitVec.ofNat 64 (n - P) ∧
      s₈.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧ Regs [.x9, .x23, .x24, .x25, .x26] s₇ s₈ := by
  have he := mo.env
  have hn := mo.data.ok.lt
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  have q₁ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 240 + 8 ≤ 2560 by decide)
  have e₁ : s₇.mem.read (W + 232#64) 8 = D := by
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, mo.sD]
  have e₂ : s₇.mem.read (W + 240#64) 8 = BitVec.ofNat 64 n := by
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, mo.sN]
  have e₉ : (BitVec.ofNat 64 n >>> 7) <<< 7 = BitVec.ofNat 64 P := by
    rw [Gcm.AArch64.Stitch.ushr7 hn, Stitch.shl7 (by have := Nat.mul_div_le n 128; omega), ← mo.hP]
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, he.x19, q₁, q₂], ?_⟩
  refine ⟨?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp [gpr_write, e₁, e₂, e₉]
  · simp [gpr_write, e₂, e₉]
    rw [Offset.ofNat_sub_ofNat hPn]
  · simp [gpr_write]
    rw [mo.hP, show 128 * (n / 128) % 16 = 0 by omega]

/-- `omBS`: the rest decrypted if the tag is right, and the text as it was
if not. -/
theorem omBS_ok (v : GcmImpl) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidS fr Ctx W SP D Np A R nl al n tl P s s₇) :
    WP isa (omBS v.callees) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n) ∧ Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s'.mem := by
  have hn := mo.data.ok.lt
  have hwrap := mo.data.ok.wrap
  have hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  have hP16 : P % 16 = 0 := by rw [mo.hP]; omega
  have x27₇ := mo.x27
  have dPr : (⟨D, P⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 P, n - P⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have subP : Region.Sub ⟨D, P⟩ ⟨D, n⟩ := Region.sub_prefix hPn
  have subR : Region.Sub ⟨D + BitVec.ofNat 64 P, n - P⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  have hsplit : ∀ m : Mem, bytesAt m D n = bytesAt m D P ++ bytesAt m (D + BitVec.ofNat 64 P) (n - P) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' hPn]
  have crSub : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨D, n⟩ →
      ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W E k, ∃ r' ∈ crFrame (W + BitVec.ofNat 64 16) W D n, Region.Sub r r' :=
    fun {E k} hE r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., hE⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  dsimp only
  generalize hJ : inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)) = J at mo ⊢
  have pre₇ := mo.pre
  have cb₇ := mo.cb
  have cbs₇ := mo.cbs
  rw [hJ] at pre₇ cb₇ cbs₇
  generalize decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R) (blockAt s.mem (Ctx + BitVec.ofNat 64 240))
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  unfold omBS
  have hite : WP isa (.ite (.zero .x .x27) (failB v.callees) (okB v.callees)) s₇
      (fun (s₉ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ ∧ s₉.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame (W + BitVec.ofNat 64 16) W D n) s₇.mem s₉.mem ∧
      bytesAt s₉.mem D n = if B then gctr (ciphOf s.mem Ctx R) J (bytesAt s.mem D n) else bytesAt s.mem D n) := by
    refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
      (fun hf => ?_)
    · have hB : B = false := by revert ht; cases B <;> simp
      subst hB
      unfold failB
      obtain ⟨s₈, run₈, m₈, x23₈, x24₈, x25₈, og₈, sp₈, rd₈, wr₈⟩ := failArgs_ok mo
      refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
      have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := mo.env.keep (fun r hr => og₈ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
      have f₈ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩] s₇.mem s₈.mem := by
        rw [m₈]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
      have dS : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨D, n⟩ →
          ∀ r ∈ [(⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨E, k⟩ : Region).Disjoint r :=
        fun hE r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (mo.data.ok.st.sub_left hE).sub_right (Lay.stSub (by decide))
      have hCr : CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 D P s₈ :=
        ⟨he₈, fun _ _ => rfl, by rw [og₈ _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
          (mo.data.take hPn).of_eq rd₈ wr₈⟩
      have hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = J := by
        rw [m₈, blockAt_copy, cbs₇]
      have hc₈ : ciphOf s₈.mem Ctx R = ciphOf s.mem Ctx R := by
        rw [ciph_frame f₈ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact L.cs.sub_right (Lay.stSub (by decide))) hR, mo.ciph]
      refine WP.mono (cryptAl_ok L v (icb := J) hCr rfl) fun s₉ h₉ => ⟨h₉.env, ?_, ?_, ?_⟩
      · rw [h₉.kept .x27 (by decide), og₈ _ (by decide)]
      · refine (f₈.sub fun r hr => ?_).trans (h₉.frame.sub (crSub subP))
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · have e₁ : bytesAt s₉.mem D P = bytesAt s.mem D P := by
          rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, bytesAt_frame f₈ (dS subP) (by omega), pre₇,
            xorKs_xorKs]
        have e₂ : bytesAt s₉.mem (D + BitVec.ofNat 64 P) (n - P) = bytesAt s.mem (D + BitVec.ofNat 64 P) (n - P) := by
          rw [bytesAt_frame h₉.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact dPr.symm
              · exact (mo.data.ok.st.sub_left subR).sub_right (Lay.stSub (by decide))
              · exact (mo.data.ok.w.sub_left subR).sub_right (Lay.wSub (by decide))) (by omega),
            bytesAt_frame f₈ (dS subR) (by omega), mo.rest]
        rw [hsplit, e₁, e₂, ← hsplit]; rfl
    · have hB : B = true := by revert hf; cases B <;> simp
      subst hB
      unfold okB
      obtain ⟨s₈, run₈, x23₈, x24₈, x25₈, r₈⟩ := okArgs_ok mo
      refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
      have he₈ := mo.env.of_regs r₈
      have hCr : CrIn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (D + BitVec.ofNat 64 P) (n - P) s₈ :=
        ⟨he₈, fun _ _ => rfl, by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
          (mo.data.drop hPn).of_eq r₈.rd r₈.wr⟩
      have hctr : Ctr s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
          (ciphOf s₈.mem Ctx R) J P :=
        ⟨by rw [r₈.mem, cb₇]; congr 1; omega, fun h => absurd hP16 h⟩
      refine WP.mono (cryptAl_ok L v (icb := J) hCr hP16) fun s₉ h₉ => ⟨h₉.env, ?_, ?_, ?_⟩
      · rw [h₉.kept .x27 (by decide), r₈.others _ (by decide)]
      · rw [← r₈.mem]; exact h₉.frame.sub (crSub subR)
      · have e₁ : bytesAt s₉.mem D P = bytesAt s₇.mem D P := by
          rw [bytesAt_frame h₉.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact dPr
              · exact (mo.data.ok.st.sub_left subP).sub_right (Lay.stSub (by decide))
              · exact (mo.data.ok.w.sub_left subP).sub_right (Lay.wSub (by decide))) (by omega), r₈.mem]
        rw [hsplit, e₁, pre₇, h₉.out hctr, r₈.mem, mo.ciph, mo.rest,
          show (if true = true then gctr (ciphOf s.mem Ctx R) J (bytesAt s.mem D n) else bytesAt s.mem D n) =
            gctr (ciphOf s.mem Ctx R) J (bytesAt s.mem D n) from rfl, Proof.Gcm.gctr_eq, hsplit s.mem,
          Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add]
  refine WP.seq (WP.mono hite fun s₉ ⟨he₉, x27₉, f₉, d₉⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨⟨he₉.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, by simp [gpr_write, x27₉, x27₇], d₉⟩, f₉⟩

omit L in
/-- The first counter block kept at `W + cbO`. -/
theorem saveCb_ok {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    ∃ t, runBlock isa [.ldrq .v0 .x20 48, .strq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO] s = some t ∧
      t.mem = s.mem.write (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16
        (s.mem.read (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16) ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₀ := he.perm.stR (show 48 + 16 ≤ 80 by decide)
  have w₀ := he.perm.wW (show 320 + 16 ≤ 2560 by decide)
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20, q₀, w₀, gpr_setV, wr_setV, rd_setV,
    mem_setV, sp_setV, v_setV_self], ?_⟩
  exact ⟨by simp [Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20], rfl, rfl, rfl, rfl⟩

end

end VG.Proof.AesGcm.AArch64.Fast
