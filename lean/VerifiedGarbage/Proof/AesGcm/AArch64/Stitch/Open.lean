module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok

/-! ### `AesGcm.AArch64.Stitch.OpenB`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64, interleaved: `open`'s branch on the tag

Untrusted: everything here is checked by Lean. `openRunWithSG c to` is
`openRunAS`, up to the branch on the tag, then `omBS` (`openRunWithS_split`).
Before the branch (`MidSG`), the interleaved loop has decrypted the first `P`
bytes of the text to the output (over the text in place, to `dst` out of
place), and in place kept the first counter block at `W + cbO`; `omBS`
decrypts the rest if the tag is right, and if not encrypts the first `P`
bytes again from the kept counter block in place, which leaves them as they
were, or zeroes the output out of place (`omBS_ok`).
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
variable (c : Callees) (cl : Prog isa) (tb : List Instr) (to : Bool)

/-- `openRunWithSG` up to the branch on the tag. -/
def openRunAS : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.front
  (.seq (.block (Impl.AesGcm.AArch64.Stitch.decPre to))
  (.seq (Impl.AesGcm.AArch64.Stitch.stitched [] tb (Impl.Gcm.AArch64.Stitch.dec to))
  (.seq (.block (Impl.AesGcm.AArch64.Stitch.whole ++ [.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] ++
      absSeg2 16))
  (.seq cl
  (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
      [mov .x13 .x24, mov .x12 .x23]))
  (.seq Impl.AesGcm.AArch64.Fast.padMulT
  (.seq (.block (Impl.AesGcm.AArch64.Fast.lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
    (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))))

/-- The branch on the tag. -/
def omBS : Prog isa :=
  .seq (.ite (.zero .x .x27) (Impl.AesGcm.AArch64.Stitch.failS c to) (Impl.AesGcm.AArch64.Stitch.okS c to))
    (.block [mov .x0 .x27])

/-- `openRunWithSG` is `openRunAS` then `omBS`. -/
theorem openRunWithS_split :
    PEq (.seq (openRunAS c cl tb to) (omBS c to)) (Impl.AesGcm.AArch64.Stitch.openRunWithSG c to tb cl) := by
  unfold openRunAS omBS Impl.AesGcm.AArch64.Stitch.openRunWithSG
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
  obtain hi' := List.mem_range.mp hi
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega_using [hi']), hi', ite_true]
  exact Mem.extractLsb'_read m b hi'

/-- Before the branch on the tag, from `s` (after `open`'s entry): `MidOG`,
but for the first `P` bytes of the text at `D`, decrypted to the output at
`O`, and the counter block past them; in place (`O = D`), the first counter
block at `W + cbO`. The ciphertext is `C₁ ++ C₂`, of which `D` holds `C₂`
after its first `P` bytes. -/
structure MidSG (Wn : Nat) (to : Bool) (fr : List Region) (Ctx W SP D O Np A : Addr) (R nl al n tl P : Nat)
    (C₁ C₂ : List Byte) (s s₇ : State) : Prop where
  env : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₇
  frame : Frame fr s.mem s₇.mem
  x22 : s₇.gpr .x22 = BitVec.ofNat 64 R
  x27 : s₇.gpr .x27 = BitVec.ofNat 64 (if decide ((Spec.Gcm.fullTag (ciphOf s.mem Ctx R)
    (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl) (bytesAt s.mem A al)
    (C₁ ++ C₂)).take tl = bytesAt s.mem W tl) then 1 else 0)
  data : cond to (DataOk Wn (W + BitVec.ofNat 64 16) W s₇ D n) (DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₇ D n)
  sD : s₇.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n
  hP : P = 128 * (n / 128)
  len₁ : C₁.length = P
  pre : bytesAt s₇.mem O P = xorKs (ciphOf s.mem Ctx R)
    (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl))) 0 C₁
  rest : bytesAt s₇.mem (D + BitVec.ofNat 64 P) (n - P) = C₂
  cb : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (P / 16) (inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)))
  cbs : cond to True (blockAt s₇.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) =
    inc32 (Spec.Gcm.j0 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (bytesAt s.mem Np nl)))
  ciph : ciphOf s₇.mem Ctx R = ciphOf s.mem Ctx R
  out : cond to (OutIn Ctx W D O n s₇) (O = D)

theorem MidSG.dataOk {Wn : Nat} {to : Bool} {fr : List Region} {Ctx W SP D O Np A : Addr} {R nl al n tl P : Nat}
    {C₁ C₂ : List Byte} {s s₇ : State} (mo : MidSG Wn to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    DataOk Wn (W + BitVec.ofNat 64 16) W s₇ D n := dataOk_of mo.data

theorem MidSG.outW {Wn : Nat} {to : Bool} {fr : List Region} {Ctx W SP D O Np A : Addr} {R nl al n tl P : Nat}
    {C₁ C₂ : List Byte} {s s₇ : State} (mo : MidSG Wn to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₇ O n := outG_dataW mo.out mo.data

section
variable {Ctx W SP D O Np A : Addr} {R nl al n tl P : Nat} {C₁ C₂ : List Byte}
  (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W)
include L

omit L in
theorem failArgs_ok {Wn : Nat} {fr : List Region} {s s₇ : State}
    (mo : MidSG Wn false fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldrq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO, .strq .v0 .x20 48,
      .ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++ Impl.AesGcm.AArch64.Stitch.whole ++
      [mov .x24 .x9, imm .x25 0]) s₇ = some s₈ ∧
      s₈.mem = s₇.mem.write (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16
        (s₇.mem.read (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16) ∧
      s₈.gpr .x23 = D ∧ s₈.gpr .x24 = BitVec.ofNat 64 P ∧ s₈.gpr .x25 = BitVec.ofNat 64 (0 % 16) ∧
      s₈.gpr .x26 = BitVec.ofNat 64 n ∧
      Others [.x9, .x23, .x24, .x25, .x26] s₇ s₈ ∧ s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
  have he := mo.env
  have hn := mo.dataOk.lt
  obtain q₀ := he.perm.wR (show 320 + 16 ≤ 512 by decide)
  obtain q₁ := he.perm.wR (show 232 + 8 ≤ 512 by decide)
  obtain q₂ := he.perm.wR (show 240 + 8 ≤ 512 by decide)
  obtain w₀ := he.perm.stW (show 48 + 16 ≤ 80 by decide)
  obtain e₁ : s₇.mem.read (W + 232#64) 8 = D := by
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, mo.sD]
  obtain e₂ : s₇.mem.read (W + 240#64) 8 = BitVec.ofNat 64 n := by
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, mo.sN]
  obtain rs : ∀ {v : BitVec (8 * 16)} (d : Nat), 80 ≤ d → d + 8 ≤ Wn →
      (s₇.mem.write (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16 v).read (W + BitVec.ofNat 64 d) 8 =
        s₇.mem.read (W + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    rw [add_ofNat_assoc]
    exact Mem.read_write_sep (Offset.sep W (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
  obtain e₉ : (BitVec.ofNat 64 n >>> 7) <<< 7 = BitVec.ofNat 64 P := by
    rw [Gcm.AArch64.Stitch.ushr7 hn, Stitch.shl7 (by have := Nat.mul_div_le n 128; omega_using [hn]), ← mo.hP]
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20, q₀, q₁,
    q₂, w₀, gpr_setV, wr_setV, rd_setV, mem_setV, sp_setV, v_setV_self], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp [mem_write, he.x20, Impl.AesGcm.AArch64.Stitch.cbO]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [rs 232 (by decide) (by decide), e₁]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [rs 240 (by decide) (by decide), e₂, e₉, BitVec.add_zero]
  · simp [gpr_write]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [rs 240 (by decide) (by decide), e₂]

omit L in
/-- `okS`'s loads: the rest of the text, and out of place the output past the
first bytes in `x26`. -/
theorem okArgsG_ok {Wn : Nat} (to : Bool) {fr : List Region} {s s₇ : State}
    (mo : MidSG Wn to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    ∃ s₈, runBlock isa (([.ldr .x .x23 .x19 dataO, .ldr .x .x26 .x19 lenO] : List Instr) ++
      Impl.AesGcm.AArch64.Stitch.whole ++ ([.add .x .x23 .x23 .x9, .sub .x .x24 .x26 .x9, imm .x25 0] : List Instr) ++
      cond to ([.ldr .x .x26 .x19 dstO, .add .x .x26 .x26 .x9] : List Instr) []) s₇ = some s₈ ∧
      s₈.gpr .x23 = D + BitVec.ofNat 64 P ∧ s₈.gpr .x24 = BitVec.ofNat 64 (n - P) ∧
      s₈.gpr .x25 = BitVec.ofNat 64 (P % 16) ∧
      cond to (s₈.gpr .x26 = O + BitVec.ofNat 64 P) (s₈.gpr .x26 = BitVec.ofNat 64 n) ∧
      Regs [.x9, .x23, .x24, .x25, .x26] s₇ s₈ := by
  have he := mo.env
  have hn := mo.dataOk.lt
  obtain hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain q₁ := he.perm.wR (show 232 + 8 ≤ 512 by decide)
  obtain q₂ := he.perm.wR (show 240 + 8 ≤ 512 by decide)
  obtain q₃ := he.perm.wR (show 320 + 8 ≤ 512 by decide)
  obtain e₁ : s₇.mem.read (W + 232#64) 8 = D := by
    rw [show s₇.mem.read (W + 232#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, mo.sD]
  obtain e₂ : s₇.mem.read (W + 240#64) 8 = BitVec.ofNat 64 n := by
    rw [show s₇.mem.read (W + 240#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, mo.sN]
  obtain e₉ : (BitVec.ofNat 64 n >>> 7) <<< 7 = BitVec.ofNat 64 P := by
    rw [Gcm.AArch64.Stitch.ushr7 hn, Stitch.shl7 (by have := Nat.mul_div_le n 128; omega_using [hn]), ← mo.hP]
  cases to with
  | false =>
    refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, he.x19, q₁, q₂, Bool.cond_false, List.append_nil], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e₁, e₂, e₉]
    · simp [gpr_write, e₂, e₉]
      rw [Offset.ofNat_sub_ofNat hPn]
    · simp [gpr_write]
      rw [mo.hP, show 128 * (n / 128) % 16 = 0 by omega_using []]
    · show _ = _
      simp [gpr_write, e₂]
  | true =>
    have ou : OutIn Ctx W D O n s₇ := mo.out
    obtain e₃ : s₇.mem.read (W + 320#64) 8 = O := by
      rw [show s₇.mem.read (W + 320#64) 8 = s₇.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl, ou.sO]
    refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.whole, he.x19, q₁, q₂, q₃, dstO, Bool.cond_true], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_write, e₁, e₂, e₉]
    · simp [gpr_write, e₂, e₉]
      rw [Offset.ofNat_sub_ofNat hPn]
    · simp [gpr_write]
      rw [mo.hP, show 128 * (n / 128) % 16 = 0 by omega_using []]
    · show _ = _
      simp [gpr_write, e₂, e₃, e₉]

/-- `omBS to`: the rest decrypted if the tag is right; if not, in place the
text as it was, out of place the output zeroed. -/
theorem omBS_ok {Wn : Nat} (v : GcmImpl) (to : Bool) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidSG Wn to fr Ctx W SP D O Np A R nl al n tl P C₁ C₂ s s₇) :
    WP isa (omBS v.callees to) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (C₁ ++ C₂)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem O n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (C₁ ++ C₂)
        else cond to (List.replicate n 0) (C₁ ++ C₂)) ∧ Frame (crFrame Wn (W + BitVec.ofNat 64 16) W O n) s₇.mem s'.mem := by
  have hdk := mo.dataOk
  have hn := hdk.lt
  have hwrap := hdk.wrap
  have ow := mo.outW
  obtain hPn : P ≤ n := mo.hP ▸ Nat.mul_div_le n 128
  obtain hP16 : P % 16 = 0 := by rw [mo.hP]; omega_using []
  have x27₇ := mo.x27
  obtain dPr : ∀ E : Addr, (⟨E, P⟩ : Region).Disjoint ⟨E + BitVec.ofNat 64 P, n - P⟩ :=
    fun E => Offset.base_disjoint E (Nat.le_refl _) (by omega_using [hn, hPn])
  obtain subP : ∀ E : Addr, Region.Sub ⟨E, P⟩ ⟨E, n⟩ := fun _ => Region.sub_prefix hPn
  obtain subR : ∀ E : Addr, Region.Sub ⟨E + BitVec.ofNat 64 P, n - P⟩ ⟨E, n⟩ := fun E => Offset.sub_base E (by omega_using [hPn])
  obtain hsplit : ∀ (m : Mem) (E : Addr), bytesAt m E n = bytesAt m E P ++ bytesAt m (E + BitVec.ofNat 64 P) (n - P) :=
    fun m E => by rw [← bytesAt_add, Nat.add_sub_cancel' hPn]
  obtain crSub : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨O, n⟩ →
      ∀ r ∈ crFrame Wn (W + BitVec.ofNat 64 16) W E k, ∃ r' ∈ crFrame Wn (W + BitVec.ofNat 64 16) W O n, Region.Sub r r' :=
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
    (bytesAt s.mem Np nl) (bytesAt s.mem A al) (C₁ ++ C₂)).take tl = bytesAt s.mem W tl) = B at x27₇ ⊢
  unfold omBS
  obtain hite : WP isa (.ite (.zero .x .x27) (Impl.AesGcm.AArch64.Stitch.failS v.callees to)
      (Impl.AesGcm.AArch64.Stitch.okS v.callees to)) s₇
      (fun (s₉ : State) => Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₉ ∧ s₉.gpr .x27 = s₇.gpr .x27 ∧
      Frame (crFrame Wn (W + BitVec.ofNat 64 16) W O n) s₇.mem s₉.mem ∧
      bytesAt s₉.mem O n = if B then gctr (ciphOf s.mem Ctx R) J (C₁ ++ C₂)
        else cond to (List.replicate n 0) (C₁ ++ C₂)) := by
    refine WP.ite (decide ((if B then 1 else 0) = 0)) (eval_zero x27₇ (by cases B <;> decide)) (fun ht => ?_)
      (fun hf => ?_)
    · have hB : B = false := by revert ht; cases B <;> simp
      subst hB
      cases to with
      | true =>
        have ou : OutIn Ctx W D O n s₇ := mo.out
        refine WP.mono (wipeTo_ok mo.env ou.sO mo.sN ou.dw) fun s₉ ⟨z, f, g, sp, rd, wr⟩ =>
          ⟨mo.env.keep (fun r hr => g r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> decide) (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> decide) (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr,
            g _ (by decide) (by decide) (by decide),
            f.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩,
            by rw [z]; rfl⟩
      | false =>
        have eO : O = D := mo.out
        subst eO
        have hdw : DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₇ O n := mo.data
        simp only [Impl.AesGcm.AArch64.Stitch.failS, Bool.cond_false]
        obtain ⟨s₈, run₈, m₈, x23₈, x24₈, x25₈, x26₈, og₈, sp₈, rd₈, wr₈⟩ := failArgs_ok mo
        refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
        obtain he₈ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈ := mo.env.keep (fun r hr => og₈ r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
        obtain f₈ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩] s₇.mem s₈.mem := by
          rw [m₈]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
        obtain dS : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨O, n⟩ →
            ∀ r ∈ [(⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨E, k⟩ : Region).Disjoint r :=
          fun hE r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hdw.ok.st.sub_left hE).sub_right (Lay.stSub (by decide))
        obtain hCr : CrIn Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R 0 O P s₈ :=
          ⟨he₈, fun _ _ => rfl, by rw [og₈ _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
            (hdw.take hPn).of_eq rd₈ wr₈, rfl⟩
        obtain hcb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = J := by
          rw [m₈, blockAt_copy]; exact cbs₇
        obtain hc₈ : ciphOf s₈.mem Ctx R = ciphOf s.mem Ctx R := by
          rw [ciph_frame f₈ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact L.cs.sub_right (Lay.stSub (by decide))) hR, mo.ciph]
        refine WP.mono (cryptAlT_ok L v (icb := J) hCr rfl x26₈ hn fun _ h => absurd (by omega_using [hP16]) h)
          fun s₉ h₉ => ⟨h₉.env, ?_, ?_, ?_⟩
        · rw [h₉.kept .x27 (by decide), og₈ _ (by decide)]
        · refine (f₈.sub fun r hr => ?_).trans (h₉.frame.sub (crSub (subP O)))
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
        · have e₁ : bytesAt s₉.mem O P = C₁ := by
            rw [h₉.out (Proof.Gcm.ctr_zero _ _ _ _ hcb₈), hc₈, bytesAt_frame f₈ (dS (subP O)) (by omega_using [hn, hPn]), pre₇,
              xorKs_xorKs]
          obtain e₂ : bytesAt s₉.mem (O + BitVec.ofNat 64 P) (n - P) = C₂ := by
            rw [bytesAt_frame h₉.frame (fun r hr => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl
                · exact (dPr O).symm
                · exact (hdw.ok.st.sub_left (subR O)).sub_right (Lay.stSub (by decide))
                · exact (hdw.ok.w.sub_left (subR O)).sub_right (Lay.wSub (by decide))) (by omega_using [hn]),
              bytesAt_frame f₈ (dS (subR O)) (by omega_using [hn]), mo.rest]
          rw [hsplit, e₁, e₂]; rfl
    · have hB : B = true := by revert hf; cases B <;> simp
      subst hB
      unfold Impl.AesGcm.AArch64.Stitch.okS
      obtain ⟨s₈, run₈, x23₈, x24₈, x25₈, x26₈, r₈⟩ := okArgsG_ok to mo
      refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
      obtain he₈ := mo.env.of_regs r₈
      obtain hctr : Ctr s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
          (ciphOf s₈.mem Ctx R) J P :=
        ⟨by rw [r₈.mem, cb₇]; congr 1; omega_using [hP16], fun h => absurd hP16 h⟩
      obtain hfin : ∀ {s₉ : State}, Frame (crFrame Wn (W + BitVec.ofNat 64 16) W (O + BitVec.ofNat 64 P) (n - P)) s₈.mem s₉.mem →
          bytesAt s₉.mem (O + BitVec.ofNat 64 P) (n - P) =
            xorKs (ciphOf s₈.mem Ctx R) J P (bytesAt s₈.mem (D + BitVec.ofNat 64 P) (n - P)) →
          bytesAt s₉.mem O n = gctr (ciphOf s.mem Ctx R) J (C₁ ++ C₂) := fun {s₉} f₉ o₉ => by
        obtain e₁ : bytesAt s₉.mem O P = bytesAt s₇.mem O P := by
          rw [bytesAt_frame f₉ (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl
              · exact dPr O
              · exact (ow.ok.st.sub_left (subP O)).sub_right (Lay.stSub (by decide))
              · exact (ow.ok.w.sub_left (subP O)).sub_right (Lay.wSub (by decide))) (by omega_using [hn, hPn]), r₈.mem]
        rw [hsplit, e₁, pre₇, o₉, r₈.mem, mo.ciph, mo.rest, Proof.Gcm.gctr_eq, Proof.Gcm.xorKs_append, mo.len₁,
          Nat.zero_add]
      cases to with
      | false =>
        have eO : O = D := mo.out
        subst eO
        have hdw : DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₇ O n := mo.data
        have x26f : s₈.gpr .x26 = BitVec.ofNat 64 n := x26₈
        obtain hCr : CrIn Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (O + BitVec.ofNat 64 P) (n - P) s₈ :=
          ⟨he₈, fun _ _ => rfl, by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈, x25₈,
            (hdw.drop hPn).of_eq r₈.rd r₈.wr, rfl⟩
        simp only [Bool.cond_false]
        refine WP.mono (cryptAlT_ok L v (icb := J) hCr hP16 x26f hn
            (tail_big (by rw [r₈.wr]; exact hdw.wr) hn rfl (by omega_using [hPn])))
          fun s₉ h₉ => ⟨h₉.env, ?_, ?_, ?_⟩
        · rw [h₉.kept .x27 (by decide), r₈.others _ (by decide)]
        · rw [← r₈.mem]; exact h₉.frame.sub (crSub (subR O))
        · rw [hfin h₉.frame (h₉.out hctr)]; rfl
      | true =>
        have ou : OutIn Ctx W D O n s₇ := mo.out
        have x26t : s₈.gpr .x26 = O + BitVec.ofNat 64 P := x26₈
        obtain hCr : CrInG Wn true Ctx (W + BitVec.ofNat 64 16) W SP s₈.gpr R P (D + BitVec.ofNat 64 P)
            (O + BitVec.ofNat 64 P) (n - P) s₈ :=
          ⟨he₈, (fun _ _ => rfl : KeptTo s₈.gpr s₈), by rw [r₈.others _ (by decide), mo.x22], hR, x23₈, x24₈,
            x25₈, ((dataOk_of mo.data).drop hPn).of_eq r₈.rd r₈.wr,
            OutAt.mkTo ((ou.dw.drop hPn).of_eq r₈.rd r₈.wr)
              ((ou.dd.sub_left (subR D)).sub_right (subR O)) (by rw [x26t, BitVec.add_zero])⟩
        simp only [Bool.cond_true]
        refine WP.mono (cryptAlG_ok L v true (icb := J) hCr hP16) fun s₉ h₉ => ⟨h₉.env, ?_, ?_, ?_⟩
        · rw [keptG_x27 h₉.kept, r₈.others _ (by decide)]
        · rw [← r₈.mem]; exact h₉.frame.sub (crSub (subR O))
        · rw [hfin h₉.frame (h₉.out hctr)]; rfl
  refine WP.seq (WP.mono hite fun s₉ ⟨he₉, x27₉, f₉, d₉⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨⟨he₉.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, by simp [gpr_write, x27₉, x27₇], d₉⟩, f₉⟩

omit L in
/-- The first counter block kept at `W + cbO`. -/
theorem saveCb_ok {Wn : Nat} {s : State} (he : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s) :
    ∃ t, runBlock isa [.ldrq .v0 .x20 48, .strq .v0 .x19 Impl.AesGcm.AArch64.Stitch.cbO] s = some t ∧
      t.mem = s.mem.write (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) 16
        (s.mem.read (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) 16) ∧
      t.gpr = s.gpr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hWn := he.perm.hWn
  obtain q₀ := he.perm.stR (show 48 + 16 ≤ 80 by decide)
  obtain w₀ := he.perm.wW (show 320 + 16 ≤ 512 by decide)
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20, q₀, w₀, gpr_setV, wr_setV, rd_setV,
    mem_setV, sp_setV, v_setV_self], ?_⟩
  exact ⟨by simp [Impl.AesGcm.AArch64.Stitch.cbO, he.x19, he.x20], rfl, rfl, rfl, rfl⟩

omit L in
/-- Out of place, the destination (kept at `W + dstO`) loaded into `x15`. -/
theorem ldrDst_ok {Wn : Nat} {s : State} {O : Addr} (he : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sO : s.mem.readW (W + BitVec.ofNat 64 320) 64 = O) :
    ∃ t, runBlock isa [.ldr .x .x15 .x19 dstO] s = some t ∧ t.gpr .x15 = O ∧ Regs [.x15] s t := by
  obtain hWn := he.perm.hWn
  obtain q₃ := he.perm.wR (show 320 + 8 ≤ 512 by decide)
  obtain e₃ : s.mem.read (W + 320#64) 8 = O := by
    rw [show s.mem.read (W + 320#64) 8 = s.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl, sO]
  refine ⟨_, by arun [he.x19, q₃, dstO], ?_⟩
  exact ⟨by simp [gpr_write, e₃], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

end

end VG.Proof.AesGcm.AArch64.Fast

end

end

/-!
# AES-GCM on AArch64, interleaved: `open` up to the branch on the tag

Untrusted: everything here is checked by Lean. `openRunAS` does what
`openRunA` does (`Fast/Open.lean`), with the first `128 ⌊n / 128⌋` bytes of
the ciphertext (the text) decrypted to the output and hashed by the
interleaved loop (`stitchDM_ok`), for a `tb` that writes the table of keys
(`htb`) and a `ghPart` that is GHASH (`Gh8Ok`): in place over the text, the
first counter block kept at `W + cbO`; out of place to `dst`, the text only
read. It leaves `MidSG`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)
open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok)

/-! ## What the path writes, in place or out of place

In place, the path writes `fastFrame`, the first counter block at `W + cbO`
among it; out of place it writes `fastFrameP`, outside of where `open_to`
keeps `dst`. -/

/-- What the path writes in the working space. -/
abbrev sfr (to : Bool) (W : Addr) : List Region := cond to (fastFrameP Wn W) (fastFrame W)

/-- What `decPre` writes: in place the first counter block, out of place nothing. -/
abbrev cbF (to : Bool) (W : Addr) : List Region :=
  cond to [] [⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩]

theorem sfr_lo {to : Bool} {W : Addr} {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ sfr to W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  cases to
  · exact fast_lo h₁ h₂
  · exact fastP_lo h₁ h₂

theorem sfr_lo' {to : Bool} {W : Addr} {d k : Nat} (h₂ : 16 + d + k ≤ 128) :
    ∃ r' ∈ sfr to W, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r' := by
  cases to
  · exact fast_lo' h₂
  · exact fastP_lo' h₂

theorem sfr_hi {Wn : Nat} {to : Bool} {W : Addr} {d k : Nat}
    (h : (256 ≤ d ∧ d + k ≤ 320) ∨ (512 ≤ d ∧ d + k ≤ Wn)) :
    ∃ r' ∈ sfr to W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  cases to
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact fast_hi h₁ (by omega_using [h₂])
    · exact fast_hi (by omega_using [h₁]) h₂
  · exact fastP_hi h

theorem sfr_work {Wn : Nat} (to : Bool) (W : Addr) : ∀ r ∈ sfr to W, Region.Sub r (workR Wn W) := by
  cases to
  · exact fastFrame_work W
  · exact fastFrameP_work W

theorem slots_sfr (to : Bool) (W : Addr) : ∀ r ∈ sfr to W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  cases to
  · exact slots_fastFrame W
  · exact slots_fastFrameP W

theorem sfr_sub {to : Bool} {W : Addr} {ex : List Region} :
    ∀ r ∈ sfr to W ++ ex, ∃ r' ∈ fastFrame W ++ ex, Region.Sub r r' := by
  cases to
  · exact fun r hr => ⟨r, hr, fun _ h => h⟩
  · exact fastFrameP_sub

theorem cbF_sub {to : Bool} {W : Addr} : ∀ r ∈ cbF to W, ∃ r' ∈ sfr to W, Region.Sub r r' := by
  cases to
  · intro r hr
    simp only [cbF, Bool.cond_false, List.mem_singleton] at hr; subst hr
    exact fast_hi (by decide) (by decide)
  · intro r hr
    simp at hr

theorem cbF_disj {to : Bool} {W : Addr} {X : Region}
    (h : X.Disjoint ⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩) : ∀ r ∈ cbF to W, X.Disjoint r := by
  cases to
  · intro r hr
    simp only [cbF, Bool.cond_false, List.mem_singleton] at hr; subst hr; exact h
  · intro r hr
    simp at hr

theorem tag_sfr {to : Bool} {W : Addr} {k : Nat} (hk : k ≤ 16) :
    ∀ r ∈ sfr to W, (⟨W, k⟩ : Region).Disjoint r := by
  cases to
  · intro r hr
    simp only [sfr, Bool.cond_false, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.disjoint_base W (show k ≤ 16 by omega_using [hk]) (by decide)).symm
    · exact (Offset.disjoint_base W (show k ≤ 256 by omega_using [hk]) (by decide)).symm
  · intro r hr
    simp only [sfr, Bool.cond_true, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (Offset.disjoint_base W (show k ≤ 16 by omega_using [hk]) (by decide)).symm
    · exact (Offset.disjoint_base W (show k ≤ 256 by omega_using [hk]) (by decide)).symm
    · exact (Offset.disjoint_base W (show k ≤ 512 by omega_using [hk]) (by decide)).symm

/-- `decPre`: in place the first counter block kept at `W + cbO`, out of
place `dst` (kept at `W + dstO`) loaded into `x15`. -/
theorem decPre_ok {Wn : Nat} {to : Bool} {Ctx W SP O : Addr} {s₂ : State} {J0 : Block}
    (he₂ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    (cb₂ : blockAt s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J0)
    (sO₂ : cond to (s₂.mem.readW (W + BitVec.ofNat 64 320) 64 = O) True) :
    ∃ s₂c, runBlock isa (Impl.AesGcm.AArch64.Stitch.decPre to) s₂ = some s₂c ∧ Frame (cbF to W) s₂.mem s₂c.mem ∧
      (∀ r, r ≠ .x15 → s₂c.gpr r = s₂.gpr r) ∧ cond to (s₂c.gpr .x15 = O) True ∧ s₂c.sp = s₂.sp ∧
      s₂c.rd = s₂.rd ∧ s₂c.wr = s₂.wr ∧
      cond to True (blockAt s₂c.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) = inc32 J0) := by
  obtain hWn := he₂.perm.hWn
  cases to with
  | false =>
    obtain ⟨u, run, m, g, sp, rd, wr⟩ := saveCb_ok he₂
    exact ⟨u, run, by rw [m]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _),
      fun r _ => by rw [g], trivial, sp, rd, wr, by show blockAt _ _ = _; rw [m, blockAt_copy, cb₂]⟩
  | true =>
    obtain ⟨u, run, x15, r⟩ := ldrDst_ok he₂ sO₂
    exact ⟨u, run, by rw [r.mem]; exact Frame.refl _ _,
      fun q hq => r.others q (fun h => hq (by simpa using h)), x15, r.sp, r.rd, r.wr, trivial⟩

section
variable (cl : Prog isa) {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `openRunAX_ok` for `openRunAS`: the first bytes of the text at `D`
(`x6`) decrypted by the interleaved loop to the output at `O`, over the text
in place, to `dst` out of place (`to`). -/
theorem openRunASX_ok {Wn : Nat} (v : GcmImpl) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {to : Bool} {O : Addr}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop}
    (o : OpenInG Wn to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexO : ∀ r ∈ ex, (⟨O, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR Wn W] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = t.rd → s'.wr = t.wr → s'.sp = SP → Frame [workR Wn W, ⟨O, n⟩] t.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : ∀ u : State, Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t.rd → u.wr = t.wr →
      Frame [workR Wn W, ⟨O, n⟩] t.mem u.mem → KeyAt (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u fun t' => TblOk t'.mem W (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) ∧
        Frame [Stitch.tblR W] u.mem t'.mem ∧ (∀ r, r ≠ .x5 → t'.gpr r = u.gpr r) ∧
        t'.sp = u.sp ∧ t'.rd = u.rd ∧ t'.wr = u.wr) :
    WP isa (openRunAS v.callees cl tb to) t fun u =>
      MidSG Wn to (⟨O, n⟩ :: (fastFrame W ++ ex)) Ctx W SP D O Np A R 12 al n tl (Stitch.pre n)
        (bytesAt t.mem D (Stitch.pre n)) (bytesAt t.mem (D + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n)) t u ∧
        I u.mem := by
  have L := o.lay
  obtain hle := tagLenOk_le hok
  obtain hdk := dataOk_of o.dat
  have hnlt := hdk.lt
  have hRb := o.rounds
  have ddW := o.ddW
  have dcW := o.dcW
  have ow := o.outW
  have doW : (⟨O, n⟩ : Region).Disjoint (workR Wn W) := ow.ok.w
  obtain hJ : J0In Wn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t :=
    ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, rfl⟩
  generalize hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H at hJ htb
  unfold openRunAS
  refine WP.seq (WP.mono (front_ok L hMK hJ o.aad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  have he₂ := h₂.env
  have y₂ := h₂.y
  have cb₂ := h₂.cb
  have j0₂ := h₂.j0
  generalize hJ0 : Spec.Gcm.j0 H (bytesAt t.mem Np 12) = J0 at cb₂ j0₂
  generalize hx₁ : bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length) = x₁ at y₂
  obtain hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hwrap := hdk.wrap
  obtain wE : ∀ {r : Region}, Region.Sub r (workR Wn W) → ∃ r' ∈ [workR Wn W, (⟨O, n⟩ : Region)], Region.Sub r r' :=
    fun h => ⟨_, List.mem_cons_self .., h⟩
  obtain dO : ∀ {r : Region}, Region.Sub r ⟨O, n⟩ → ∃ r' ∈ [workR Wn W, (⟨O, n⟩ : Region)], Region.Sub r r' :=
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩
  -- What the path has written by `front`.
  obtain Fa : Frame (sfr to W) t.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact sfr_lo (by decide) (by decide)
    · exact sfr_lo (by decide) (by decide)
    · exact sfr_hi (.inr ⟨by decide, by decide⟩)
    · exact sfr_hi (.inl ⟨by decide, by decide⟩)
  -- In place the first counter block kept, out of place `dst` in `x15`.
  rw [WP.seq_iff]
  obtain ⟨s₂c, run₂c, fcb, g₂c, x15₂c, sp₂c, rd₂c, wr₂c, hcbs₂⟩ := decPre_ok (to := to) (O := O) he₂ cb₂ (by
    cases to with
    | false => trivial
    | true =>
      show _ = _
      rw [Fa.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _) (dst_fastFrameP W) (by decide)]
      exact (o.out : OutIn Ctx W D O n t).sO)
  refine WP.of_runBlock ⟨s₂c, run₂c, ?_⟩
  obtain he₂c : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₂c := he₂.keep (fun r hr => g₂c r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂c rd₂c wr₂c
  obtain F₂c : Frame [workR Wn W, ⟨O, n⟩] t.mem s₂c.mem :=
    (Fa.sub fun r hr => wE (sfr_work to W r hr)).trans
      (fcb.sub fun r hr => have ⟨r', h, hs⟩ := cbF_sub r hr; wE fun x hx => sfr_work to W r' h x (hs x hx))
  obtain dcb : ∀ {X : Region}, X.Disjoint (workR Wn W) → ∀ r ∈ cbF to W, X.Disjoint r := fun h =>
    cbF_disj (h.sub_right (Lay.wSub (by decide)))
  -- The first `P` bytes, by the interleaved loop, from `D` to `O`.
  obtain key₂c : KeyAt H s₂c.mem W := h₂.key.frame fcb (cbF_disj (L.w_w (.inl (by decide)) (by decide) (by decide)))
  obtain hH₂c : blockAt s₂c.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fcb (dcb (L.cw'.sub_left (Lay.ctxSub (by decide)))), h₂.hH]
  obtain hTb : Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb s₂c :=
    fun u heu hm' hrd hwr _ => htb u heu (by rw [hrd, rd₂c, h₂.rd]) (by rw [hwr, wr₂c, h₂.wr])
      (by rw [hm']; exact F₂c) (by rw [hm']; exact key₂c)
  obtain hmode : cond to (s₂c.gpr .x15 = O ∧ (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩) (O = D) := by
    cases to
    · exact o.out
    · exact ⟨x15₂c, (o.out : OutIn Ctx W D O n t).dd⟩
  obtain hsrc₂c : DataOk Wn (W + BitVec.ofNat 64 16) W s₂c D n := hdk.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr])
  obtain hout₂c : DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₂c O n := ow.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr])
  refine WP.seq (WP.mono (Stitch.stitchDM_ok L gh hTb ⟨he₂c, by rw [g₂c _ (by decide), h₂.x22, o.x22], hRb,
    by rw [g₂c _ (by decide), h₂.x23], by rw [g₂c _ (by decide), h₂.x26], hsrc₂c, hout₂c, hmode, hH₂c,
    by rw [blockAt_frame fcb (cbF_disj (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩))),
      cb₂],
    by rw [blockAt_frame fcb (cbF_disj (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩))),
      y₂],
    hx₁0⟩) fun s₂' hm₂ => ?_)
  have y₂' : blockAt s₂'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghash H (blocks (x₁ ++ bytesAt s₂c.mem D (Stitch.pre n))) := hm₂.y
  have ctr₂ := hm₂.ctr
  have dat₂ := hm₂.data
  generalize hP : Stitch.pre n = P at y₂' ctr₂ dat₂
  obtain hPn : P ≤ n := hP ▸ Nat.mul_div_le n 128
  obtain hP16 : P % 16 = 0 := by rw [← hP]; simp only [Stitch.pre]; omega_arith
  generalize hD' : D + BitVec.ofNat 64 P = D'
  obtain hsubD : Region.Sub ⟨D', n - P⟩ ⟨D, n⟩ := hD' ▸ Offset.sub_base D (by omega_arith)
  obtain g₂' : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₂'.gpr r = s₂.gpr r :=
    fun r hr => by rw [hm₂.gpr r hr, g₂c r (fun h => hr (by simp [h]))]
  -- The rest of the text, apart from what the loop writes.
  obtain dSF : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W O n, (⟨D', n - P⟩ : Region).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hdk.st.sub_left hsubD).sub_right (Lay.stSub (by decide))
    · exact (hdk.st.sub_left hsubD).sub_right (Lay.stSub (by decide))
    · cases to
      · have e : O = D := o.out
        subst e
        rw [← hD', hP]
        exact (Offset.base_disjoint O (Nat.le_refl _) (by omega_arith)).symm
      · rw [hP]
        exact ((o.out : OutIn Ctx W D O n t).dd.sub_left hsubD).sub_right (Region.sub_prefix hPn)
    · exact (ddW.sub_left hsubD).sub_right (Lay.wSub (by decide))
  -- The rest's whole blocks, by `gh`.
  rw [WP.seq_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ := Stitch.afterD_ok (u := s₂') (D := D) (n := n)
    (by rw [g₂' _ (by decide), h₂.x23]) (by rw [g₂' _ (by decide), h₂.x26]) hnlt
  rw [hP, hD'] at x23₃
  rw [hP] at x24₃
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain he₃ := hm₂.env.of_regs r₃
  obtain hdat₃ : DataOk Wn (W + BitVec.ofNat 64 16) W s₃ D' (n - P) :=
    hD' ▸ (hdk.drop hPn).of_eq (by rw [r₃.rd, hm₂.rd, rd₂c, h₂.rd]) (by rw [r₃.wr, hm₂.wr, wr₂c, h₂.wr])
  obtain dOP : (⟨O, Stitch.pre n⟩ : Region).Disjoint (workR Wn W) := doW.sub_left (Region.sub_prefix (Nat.mul_div_le n 128))
  obtain dKS : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W O n, (keyR W).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (dOP.sub_right (Lay.wSub (by decide))).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  obtain cS : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W O n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact ow.ctx.sub_right (Region.sub_prefix (Nat.mul_div_le n 128))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  obtain hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [r₃.mem, blockAt_frame hm₂.frame fun r hr => (cS r hr).sub_left (Lay.ctxSub (by decide))]
    exact hH₂c
  generalize hC₀ : bytesAt s₂c.mem D P = C₀ at dat₂ y₂'
  obtain hC₀l : C₀.length = P := by rw [← hC₀, length_bytesAt]
  obtain hM : AbsMid Wn Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 H (x₁ ++ C₀) D' (n - P) 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun r hr => by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [r₃.others _ (by decide), g₂' _ (by decide)],
      Nat.zero_le _, by rw [x23₃]; simp,
      by rw [x24₃, Nat.sub_zero], by rw [x25₃], hdat₃, hH₃, fun ha => by simpa [bytesAt] using ha,
      .inr (by rw [List.length_append, hC₀l]; omega_arith), Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  obtain FW : Frame [workR Wn W, ⟨O, n⟩] t.mem s₆.mem := by
    obtain F3 : Frame [workR Wn W, ⟨O, n⟩] s₂c.mem s₃.mem := by
      rw [r₃.mem]
      refine hm₂.frame.sub fun r hr => ?_
      simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact wE (stW (by decide))
      · exact wE (stW (by decide))
      · exact dO (Region.sub_prefix (Nat.mul_div_le n 128))
      · exact wE (Lay.wSub (by decide))
    obtain F6 : Frame [workR Wn W, ⟨O, n⟩] s₃.mem s₆.mem := by
      refine h₆.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact wE (stW (by decide))
      · exact wE (stW (by decide))
      · exact wE (Lay.wSub (by decide))
    exact (F₂c.trans F3).trans F6
  obtain rd₆' : s₆.rd = t.rd := by rw [rd₆, r₃.rd, hm₂.rd, rd₂c, h₂.rd]
  obtain wr₆' : s₆.wr = t.wr := by rw [wr₆, r₃.wr, hm₂.wr, wr₂c, h₂.wr]
  obtain exW : ∀ {R : Region}, Region.Sub R (workR Wn W) → ∀ r ∈ ex, R.Disjoint r :=
    fun hR r hr => (hexW r hr).sub_left hR
  obtain exS : ∀ {r : Region}, (∃ r' ∈ sfr to W, Region.Sub r r') → ∃ r' ∈ sfr to W ++ ex, Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_append_left _ h, hs⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2WithX_ok L (.inr rfl)
    (fun r hr => (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))) (exW (stW (by decide))) h₆
    (hgh s₆ h₆.call (stW (by decide)) (Lay.wSub (by decide)) rd₆' wr₆' h₆.env.sp FW
      (fun x hx => hsubD x (Offset.sub_base D' (by omega_arith) x hx)))))
    fun s₇ ⟨⟨⟨h₇, hlt₇⟩, I₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * ((n - P) / 16) = j at h₇ hlt₇
  obtain hjn : j ≤ n - P := by omega_arith
  obtain hx₁C : (x₁ ++ C₀).length % 16 = 0 := by rw [List.length_append, hC₀l]; omega_arith
  have he₇ := h₇.env
  obtain hab₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H (x₁ ++ C₀) := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁C, List.take_length, ← y₂', r₃.mem]
    · rw [hx₁C, Proof.Gcm.whole_of_mod hx₁C, List.drop_length]; rfl
  obtain hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghash H (blocks ((x₁ ++ C₀) ++ bytesAt s₃.mem D' j)) :=
    (h₇.abs hab₃).whole_eq (by rw [List.length_append, length_bytesAt]; omega_arith)
  obtain key₃ : KeyAt H s₃.mem W := key₂c.frame (by rw [r₃.mem]; exact hm₂.frame) dKS
  obtain key₇ : KeyAt H s₇.mem W := by
    refine key₃.frame h₇.frame fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact exW (Lay.wSub (by decide)) r hr
  -- `H'` again, `Y`, and the last bytes.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := H) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact key₇.2)
    key₇.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain he₈ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (loadRev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  obtain he₉ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - P - j) ∧ s₁₀.gpr .x12 = D' + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), h₇.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), h₇.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  obtain he₁₀ := he₉.of_regs r₁₀
  obtain hk₁₀ : HKey H s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  obtain hy₁₀ : s₁₀.v Y = ext8 (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) := by
    rw [v₁₀, l₉, he₈.x20, m₈, rev64b_read]
  obtain rd₁₀ : s₁₀.rd = s₃.rd := by rw [r₁₀.rd, o₉.rd, rd₈, rd₇, rd₆]
  obtain wr₁₀ : s₁₀.wr = s₃.wr := by rw [r₁₀.wr, o₉.wr, wr₈, wr₇, wr₆]
  obtain hdj : DataOk Wn (W + BitVec.ofNat 64 16) W s₁₀ (D' + BitVec.ofNat 64 j) (n - P - j) :=
    (hdat₃.drop hjn).of_eq rd₁₀ wr₁₀
  obtain x26₁₀ : s₁₀.gpr .x26 = BitVec.ofNat 64 n := by
    rw [r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  obtain hfull₁₀ : DataOk Wn (W + BitVec.ofNat 64 16) W s₁₀ D n :=
    hdk.of_eq (by rw [rd₁₀, r₃.rd, hm₂.rd, rd₂c, h₂.rd]) (by rw [wr₁₀, r₃.wr, hm₂.wr, wr₂c, h₂.wr])
  refine WP.seq (WP.mono (WP.with_rdwr (padMulT_ok hMK he₁₀ hk₁₀ hy₁₀ x12₁₀ x13₁₀ (by omega_arith) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))) x26₁₀ hnlt
    (pad_big hfull₁₀.rd hnlt (by rw [← hD', Offset.add_add]; congr 2; omega_arith) (by omega_arith))))
    fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  obtain m₁₀ : s₁₀.mem = s₇.mem := by rw [r₁₀.mem, o₉.mem, m₈]
  -- What the path has written so far.
  obtain Fb : Frame (sfr to W ++ ex) s₃.mem s₇.mem := by
    refine h₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact exS (sfr_lo' (by decide))
    · exact exS (sfr_lo' (by decide))
    · exact exS (sfr_hi (.inr ⟨by decide, by decide⟩))
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  obtain Fc : Frame (sfr to W) s₇.mem s₁₁.mem := by
    rw [← m₁₀]
    refine f₁₁.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact sfr_lo (by decide) (by decide)
  obtain mx : ∀ {m m' : Mem}, Frame (sfr to W) m m' → Frame (⟨O, n⟩ :: (sfr to W ++ ex)) m m' :=
    fun h => h.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr)
  obtain mx' : ∀ {m m' : Mem}, Frame (sfr to W) m m' → Frame (sfr to W ++ ex) m m' :=
    fun h => h.mono fun r hr => List.mem_append_left _ hr
  obtain my : ∀ {m m' : Mem}, Frame (sfr to W ++ ex) m m' → Frame (⟨O, n⟩ :: (sfr to W ++ ex)) m m' :=
    fun h => h.mono fun r hr => List.mem_cons_of_mem _ hr
  obtain fl : ∀ {r : Region}, (∃ r' ∈ sfr to W, Region.Sub r r') →
      ∃ r' ∈ (⟨O, n⟩ :: (sfr to W ++ ex)), Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_cons_of_mem _ (List.mem_append_left _ h), hs⟩
  obtain Fs₂ : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) s₂c.mem s₃.mem := by
    rw [r₃.mem]
    refine hm₂.frame.sub fun r hr => ?_
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fl (sfr_lo' (by decide))
    · exact fl (sfr_lo' (by decide))
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (Nat.mul_div_le n 128)⟩
    · exact fl (sfr_hi (.inr ⟨by decide, by decide⟩))
  obtain Fs : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) s₂.mem s₃.mem :=
    (fcb.sub fun r hr => fl (cbF_sub r hr)).trans Fs₂
  obtain dfr : ∀ {R : Region}, Region.Sub R (workR Wn W) → (∀ r ∈ sfr to W ++ ex, R.Disjoint r) →
      ∀ r ∈ (⟨O, n⟩ :: (sfr to W ++ ex)), R.Disjoint r := fun hR h r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact doW.symm.sub_left hR
    · exact h r hr
  obtain F₁₁ : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) t.mem s₁₁.mem :=
    (((mx Fa).trans Fs).trans (my Fb)).trans (mx Fc)
  obtain slot₁₁ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept F₁₁ (dfr (Lay.wSub (by decide)) (disj_ex (slots_sfr to W) (exW (Lay.wSub (by decide))))) h₁ h₂'
  -- The lengths block.
  unfold Impl.AesGcm.AArch64.Fast.lensTagAt
  rw [WP.seq_iff]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain w₁ := he₁₁.perm.wW (show 96 + 8 ≤ 512 by decide)
  obtain w₂ := he₁₁.perm.wW (show 104 + 8 ≤ 512 by decide)
  obtain q₁ := he₁₁.perm.wR (show 224 + 8 ≤ 512 by decide)
  obtain x26₁₁ : s₁₁.gpr .x26 = BitVec.ofNat 64 n := by
    rw [og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  obtain ⟨s₁₂, run₁₂, m₁₂, og₁₂, sp₁₂, rd₁₂, wr₁₂, v₁₂⟩ : ∃ s₁₂, runBlock isa
      [.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
        .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] s₁₁ = some s₁₂ ∧
      s₁₂.mem = (s₁₁.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s₁₁ s₁₂ ∧ s₁₂.sp = s₁₁.sp ∧ s₁₂.rd = s₁₁.rd ∧ s₁₂.wr = s₁₁.wr ∧
      s₁₂.v = s₁₁.v := by
    obtain e₁ : s₁₁.mem.read (W + 224#64) 8 = BitVec.ofNat 64 al := by
      rw [show s₁₁.mem.read (W + 224#64) 8 = s₁₁.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl,
        slot₁₁ 224 (by decide) (by decide), o.sL]
    refine ⟨_, by arun [he₁₁.x19, q₁, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc, gpr_write, ite_true, ite_false,
      reduceCtorEq, e₁, x26₁₁]
  refine WP.of_runBlock ⟨s₁₂, run₁₂, ?_⟩
  obtain he₁₂ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => og₁₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₂ rd₁₂ wr₁₂
  obtain fT₁₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s₁₁.mem s₁₂.mem := by rw [m₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hT₁₂ : blockAt s₁₂.mem (s₁₂.gpr .x19 + BitVec.ofNat 64 tO) = ofBytes (lensBlock al n) := by
    rw [he₁₂.x19, show tO = 96 from rfl, blockAt, m₁₂, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens,
      toNat_ofNat_of_lt (show al < 2 ^ 64 by omega_arith), toNat_ofNat_of_lt hnlt]
    rfl
  obtain hk₁₂ : HKey H s₁₂ := hk₁₁.of_v (by rw [v₁₂]) (by rw [v₁₂]) (by rw [v₁₂])
  obtain y₁₂ : s₁₂.v Y = ext8 (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j)))
      (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j))) := by rw [v₁₂]; exact y₁₁
  rw [WP.block_append_iff]
  refine WP.mono (mulT_ok hMK hk₁₂ y₁₂ (by rw [he₁₂.x19]; exact he₁₂.perm.wR (by decide)))
    fun s₁₃ ⟨y₁₃, _, o₁₃⟩ => ?_
  rw [hT₁₂] at y₁₃
  rw [WP.block_append_iff]
  refine WP.mono (storeY_ok y₁₃ (by rw [o₁₃.gpr, o₁₃.wr, he₁₂.x20]; exact he₁₂.perm.stW (by decide)))
    fun s₁₄ ⟨m₁₄, b₁₄, o₁₄⟩ => ?_
  obtain g₁₄ : s₁₄.gpr = s₁₂.gpr := by rw [o₁₄.gpr]; exact o₁₃.gpr
  rw [show s₁₃.gpr .x20 = W + BitVec.ofNat 64 16 by rw [o₁₃.gpr, he₁₂.x20]] at b₁₄ m₁₄
  obtain he₁₄ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ :=
    he₁₂.keep (fun r _ => by rw [g₁₄]) (by rw [o₁₄.sp, o₁₃.sp]) (by rw [o₁₄.rd, o₁₃.rd]) (by rw [o₁₄.wr, o₁₃.wr])
  obtain fY₁₄ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s₁₂.mem s₁₄.mem := by
    rw [m₁₄, o₁₃.mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain x22₁₄ : s₁₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x22 (by decide), h₂.x22, o.x22]
  -- The tag, to `W + uO`.
  refine WP.mono (WP.with_rdwr (tagSeg_ok L (o := uO) (.inr rfl) he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ hRb))
    fun s₁₆ ⟨h₁₆, rd₁₆, wr₁₆⟩ => ?_
  refine WP.seq (WP.mono (WP.with_rdwr (tagCall_ok L v (.inr rfl) h₁₆)) fun s₁₇ ⟨h₁₇, rd₁₇, wr₁₇⟩ => ?_)
  obtain Fd : Frame (sfr to W) s₁₁.mem s₁₄.mem := by
    refine (fT₁₂.sub fun r hr => ?_).trans (fY₁₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sfr_lo (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact sfr_lo' (by decide)
  obtain F₁₄ : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) t.mem s₁₄.mem := F₁₁.trans (mx Fd)
  obtain Fg : Frame (sfr to W) s₁₄.mem s₁₇.mem := by
    refine h₁₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sfr_lo (by decide) (by decide)
    · exact sfr_lo (by decide) (by decide)
    · exact sfr_lo (by decide) (by decide)
    · exact sfr_hi (.inr ⟨by decide, by decide⟩)
  obtain F₁₇ : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) t.mem s₁₇.mem := F₁₄.trans (mx Fg)
  -- The comparison, the tag length still in `x28`.
  obtain x28₁₄ : s₁₄.gpr .x28 = BitVec.ofNat 64 tl := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x28 (by decide), h₂.x28, o.x28]
  obtain x28₁₈ : s₁₇.gpr .x28 = BitVec.ofNat 64 tl := by rw [h₁₇.kept .x28 (by decide), x28₁₄]
  have he₁₈ := h₁₇.env
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L he₁₈ (fun _ _ => rfl : Kept s₁₇.gpr s₁₇) x28₁₈ hle))
    fun s₁₉ ⟨⟨x10₁₉, he₁₉, hk₁₉, _, f₁₉⟩, rd₁₉, wr₁₉⟩ => ?_)
  refine WP.mono (okBit_ok (b := decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₁₇.mem W tl)) (by rw [x10₁₉]; simp only [decide_eq_true_eq]))
    fun s₂₀ ⟨x27₂₀, r₂₀⟩ => ?_
  obtain he₂₀ := he₁₉.of_regs r₂₀
  obtain Fe : Frame (sfr to W) s₁₇.mem s₁₉.mem := by
    refine f₁₉.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact sfr_hi (.inl ⟨by decide, by decide⟩)
  obtain F₂₀ : Frame (⟨O, n⟩ :: (sfr to W ++ ex)) t.mem s₂₀.mem := by rw [r₂₀.mem]; exact F₁₇.trans (mx Fe)
  obtain I₂₀ : I s₂₀.mem := by
    rw [r₂₀.mem]
    exact hI I₇ ((((Fc.trans Fd).trans Fg).trans Fe).sub fun r hr =>
      ⟨workR Wn W, List.mem_singleton_self _, sfr_work to W r hr⟩)
  -- What the frames keep.
  obtain dCf : ∀ r ∈ sfr to W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (sfr_work to W) dcW
  obtain dDf : ∀ r ∈ sfr to W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (sfr_work to W) ddW
  obtain dOf : ∀ r ∈ sfr to W, (⟨O, n⟩ : Region).Disjoint r := keep_of_sub (sfr_work to W) doW
  obtain dcfr : ∀ r ∈ (⟨O, n⟩ :: (sfr to W ++ ex)), (⟨Ctx, 256⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ow.ctx
    · exact disj_ex dCf hexC r hr
  obtain hc₁₄ : ciphOf s₁₄.mem Ctx R = ciphOf t.mem Ctx R := ciph_frame F₁₄ dcfr hRb
  obtain hC₀t : C₀ = bytesAt t.mem D P := by
    rw [← hC₀, bytesAt_frame fcb (dcb (ddW.sub_left (Region.sub_prefix hPn))) (by omega_arith),
      bytesAt_frame Fa (fun r hr => (dDf r hr).sub_left (Region.sub_prefix hPn)) (by omega_arith)]
  obtain hrest₃ : bytesAt s₃.mem D' (n - P) = bytesAt t.mem D' (n - P) := by
    rw [r₃.mem, bytesAt_frame hm₂.frame dSF (by omega_arith), bytesAt_frame fcb (dcb (ddW.sub_left hsubD)) (by omega_arith),
      bytesAt_frame Fa (fun r hr => (dDf r hr).sub_left hsubD) (by omega_arith)]
  obtain ht₁₀ : bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j) =
      bytesAt s₃.mem (D' + BitVec.ofNat 64 j) (n - P - j) := by
    rw [m₁₀, bytesAt_frame h₇.frame (disj_absEx (data_absFrame L (.inr rfl) (hdat₃.drop hjn))
      fun r hr => (hexD r hr).sub_left (fun x hx => hsubD x (Offset.sub_base D' (by omega_arith) x hx))) (by omega_arith)]
  obtain hsplit : bytesAt t.mem D n =
      (C₀ ++ bytesAt s₃.mem D' j) ++ bytesAt s₃.mem (D' + BitVec.ofNat 64 j) (n - P - j) := by
    rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hjn, hrest₃, hC₀t, ← hD', ← bytesAt_add,
      Nat.add_sub_cancel' hPn]
  -- `J₀`, still at the state, and the first counter block.
  obtain dT : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st0_w L ⟨by decide, by have := L.hWn; omega⟩
  obtain hJ₁₄ : blockAt s₁₄.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H (bytesAt t.mem Np 12) := by
    obtain e₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame h₇.frame fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | rfl | hr
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by have := L.hWn; omega⟩
        · exact exW (Lay.wSub (by decide)) r hr
    rw [blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st0_disj L (by decide) (by decide)),
      blockAt_frame fT₁₂ dT, blockAt_frame f₁₁ dT, m₁₀, e₇, r₃.mem, blockAt_frame hm₂.frame (fun r hr => by
        simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact (ow.ok.st.symm.sub_left (Region.sub_prefix (by decide))).sub_right
            (Region.sub_prefix (Nat.mul_div_le n 128))
        · exact st0_w L ⟨by decide, by have := L.hWn; omega⟩),
      blockAt_frame fcb (cbF_disj (st0_w L ⟨by decide, by have := L.hWn; omega⟩)), j0₂, ← hJ0]
  obtain hcb : blockAt s₂₀.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      Nat.repeat inc32 (P / 16) (inc32 J0) := by
    obtain d₄₈ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩
    rw [r₂₀.mem, blockAt_frame f₁₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩),
      blockAt_frame h₁₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩),
      blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_st (a := 48) (n := 16) (d := 16) (k := 16) (.inr (by decide)) (by decide) (by decide)),
      blockAt_frame fT₁₂ d₄₈, blockAt_frame f₁₁ d₄₈, m₁₀,
      blockAt_frame h₇.frame (disj_absEx (fun r hr => (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide)))
        (exW (stW (by decide)))),
      r₃.mem, ctr₂.1, show (P + 15) / 16 = P / 16 by omega_arith]
  obtain Fz : Frame (sfr to W ++ ex) s₃.mem s₂₀.mem := by
    rw [r₂₀.mem]; exact Fb.trans (mx' (((Fc.trans Fd).trans Fg).trans Fe))
  obtain hcbs : cond to True (blockAt s₂₀.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) = inc32 J0) := by
    cases to with
    | true => trivial
    | false =>
    obtain cW : ∀ {d k : Nat}, (d + k ≤ 320 ∨ 336 ≤ d) → d + k ≤ Wn →
        (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun h hk => L.w_w (by simp only [Impl.AesGcm.AArch64.Stitch.cbO]; omega_arith) (by decide) hk
    obtain cS : ∀ {a k : Nat}, a + k ≤ 80 →
        (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint
          ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a, k⟩ :=
      fun h => (L.st_w h (.inr ⟨by decide, by decide⟩)).symm
    obtain cbD : (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint ⟨O, Stitch.pre n⟩ :=
      (dOP.sub_right (Lay.wSub (by decide))).symm
    rw [r₂₀.mem, blockAt_frame f₁₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)),
      blockAt_frame h₁₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using cS (a := 0) (k := 32) (by decide)
        · exact cW (.inl (by decide)) (by decide)
        · exact cW (.inl (by decide)) (by decide)
        · exact cW (.inr (by decide)) (by decide)),
      blockAt_frame fY₁₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cS (by decide)),
      blockAt_frame fT₁₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)),
      blockAt_frame f₁₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)), m₁₀,
      blockAt_frame h₇.frame (disj_absEx (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cS (by decide)
        · exact cS (by decide)
        · exact cW (.inr (by decide)) (by decide)) (exW (Lay.wSub (by decide)))),
      r₃.mem, blockAt_frame hm₂.frame (fun r hr => by
        simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact cS (by decide)
        · exact cS (by decide)
        · exact cbD
        · exact cW (.inr (by decide)) (by decide))]
    exact hcbs₂
  -- The tag.
  obtain hT : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.toBytes (ghashFrom H
      (ghash H (blocks (Proof.Gcm.padded (bytesAt t.mem A al) (bytesAt t.mem D n))))
      [ofBytes (lensBlock (bytesAt t.mem A al).length (bytesAt t.mem D n).length)] ^^^
      ciphOf t.mem Ctx R (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) := by
    rw [h₁₇.out, b₁₄, hJ₁₄, hc₁₄, hY₇, List.append_assoc x₁, ht₁₀, ← hx₁, hsplit,
      ghash_padded _ _ _ _ (by rw [List.length_append, hC₀l, length_bytesAt]; omega_arith)
        (by rw [length_bytesAt]; omega_arith)]
    simp only [List.length_append, hC₀l, length_bytesAt, show P + j + (n - P - j) = n by omega_arith]
    rfl
  obtain hT' : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H
      (bytesAt t.mem Np 12) (bytesAt t.mem A al) (bytesAt t.mem D n) := by
    rw [hT, Proof.Gcm.fullTag_eq]
  obtain hW₁₈ : bytesAt s₁₇.mem W tl = bytesAt t.mem W tl := by
    refine bytesAt_frame F₁₇ (fun r hr => ?_) (by omega_arith)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact doW.symm.sub_left (Region.sub_prefix (by omega_arith))
    rcases List.mem_append.mp hr with hr | hr
    · exact tag_sfr (show tl ≤ 16 by omega_arith) r hr
    · exact exW (Region.sub_prefix (by omega_arith)) r hr
  obtain hb : (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
        (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT', hW₁₈]
  generalize hBd : decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) = B at x27₂₀
  obtain hBeq : decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
      (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  obtain x22₂₀ : s₂₀.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₂₀.others _ (by decide), hk₁₉ .x22 (by decide), h₁₇.kept .x22 (by decide), x22₁₄]
  obtain hc₂c : ciphOf s₂c.mem Ctx R = ciphOf t.mem Ctx R := by
    rw [ciph_frame fcb (dcb dcW) hRb, ciph_frame Fa dCf hRb]
  obtain hpre : bytesAt s₂₀.mem O P = xorKs (ciphOf t.mem Ctx R) (inc32 J0) 0 (bytesAt t.mem D P) := by
    rw [bytesAt_frame Fz (fun r hr => (disj_ex dOf hexO r hr).sub_left (Region.sub_prefix hPn)) (by omega_arith),
      r₃.mem, dat₂, hc₂c, hC₀t]
  obtain hrest : bytesAt s₂₀.mem (D + BitVec.ofNat 64 P) (n - P) = bytesAt t.mem D' (n - P) := by
    rw [hD', bytesAt_frame Fz (fun r hr => (disj_ex dDf hexD r hr).sub_left hsubD) (by omega_arith), hrest₃]
  obtain hCs : bytesAt t.mem D P ++ bytesAt t.mem D' (n - P) = bytesAt t.mem D n := by
    rw [← hD', ← bytesAt_add, Nat.add_sub_cancel' hPn]
  obtain rd₂₀ : s₂₀.rd = t.rd := by
    rw [r₂₀.rd, rd₁₉, rd₁₇, rd₁₆, o₁₄.rd, o₁₃.rd, rd₁₂, rd₁₁, rd₁₀, r₃.rd, hm₂.rd, rd₂c, h₂.rd]
  obtain wr₂₀ : s₂₀.wr = t.wr := by
    rw [r₂₀.wr, wr₁₉, wr₁₇, wr₁₆, o₁₄.wr, o₁₃.wr, wr₁₂, wr₁₁, wr₁₀, r₃.wr, hm₂.wr, wr₂c, h₂.wr]
  obtain hout : cond to (OutIn Ctx W D O n s₂₀) (O = D) := by
    cases to with
    | false => exact o.out
    | true =>
      have ou : OutIn Ctx W D O n t := o.out
      refine OutIn.of_eq ou rd₂₀ wr₂₀ (F₂₀.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide))
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (doW.sub_right (Lay.wSub (by decide))).symm
      · exact disj_ex (dst_fastFrameP W) (exW (Lay.wSub (by decide))) r hr
  obtain hsl : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₂₀.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept F₂₀ (dfr (Lay.wSub (by decide)) (disj_ex (slots_sfr to W) (exW (Lay.wSub (by decide))))) h₁ h₂'
  subst hH
  refine ⟨⟨he₂₀, F₂₀.sub fun r hr => ?_, x22₂₀, by rw [x27₂₀, hCs, hBeq], data_of_eq o.dat rd₂₀ wr₂₀,
    by rw [hsl 232 (by decide) (by decide), o.sD], by rw [hsl 240 (by decide) (by decide), o.sN],
    by rw [← hP], length_bytesAt _ _ _, by rw [hJ0]; exact hpre, hrest, by rw [hJ0]; exact hcb,
    by rw [hJ0]; exact hcbs, ciph_frame F₂₀ dcfr hRb, hout⟩, I₂₀⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · obtain ⟨r', h, hs⟩ := sfr_sub r hr
    exact ⟨r', List.mem_cons_of_mem _ h, hs⟩

end

end VG.Proof.AesGcm.AArch64.Fast
