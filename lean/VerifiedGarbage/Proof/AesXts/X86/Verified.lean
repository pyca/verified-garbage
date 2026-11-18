module

public import VerifiedGarbage.Impl.AesXts.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesXts.X86.Steps
public import VerifiedGarbage.Proof.AesXts.Batch
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesCbc.X86.Body
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesXts.X86.Steps
meta import VerifiedGarbage.Proof.AesXts.Batch
meta import VerifiedGarbage.Proof.AesOcb.X86.Callee
meta import VerifiedGarbage.Impl.AesXts.X86
meta import VerifiedGarbage.Proof.AesCbc.X86.Body
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesXts.X86.CT`, which this module and modules that import it used -/

section

/-! ### `AesXts.X86.Body`, which only this module used -/

section

/-!
# XTS-AES on x86: all the blocks in one call

`crypt_wp`: from AES-CBC's loop invariant after no blocks
(`Proof/AesCbc/X86/Body.lean`), `batch` reaches it after all of them
(`batch_wp`), for `xtsMode enc`, for any implementation of the block
functions (`BlocksImpl`). The tweak is saved (`saveT_wp`); a pass XORs each
block's tweak into it, multiplying the tweak by `α` after each (`pass_wp`, by
`pstep_wp` for one block, whose invariant `PInv` says what `xored` the blocks
are); the tweak is restored and the block function called on all the blocks
(`callArgs_wp`, `call_wp`, from AES-OCB's `BCall`); and a second pass XORs
the tweaks in again (`AesXts.crypt_eq`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Impl.CmacAes.X86 (argOp setup advance restore xor4 zero4)
open VG.Impl.AesCbc.X86 (cOff)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov eval_ne)
open VG.Proof.AesCbc (xorIn4_bytes copy4Mem copy4Mem_frame copy4Mem_bytes Mode ciphOf length_blocksAt
  getElem_blocksAt)
open VG.Proof.AesCbc.X86
open VG.Proof.AesGcm.X86 (w64)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesXts (xored xored_zero xored_getElem xored_step xored_all crypt_eq blocksAt_frame blocksAt_of_out)
open VG.Proof.Cmac (bytesAt_frame)

/-- A pass over the blocks `ys`, after `i` of them. -/
structure PInv (s₀ : State) (ys : List (List Byte)) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ i
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = xored (iv0 s₀) ys i
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = Spec.Xts.next (iv0 s₀) i
  sv : bytesAt s.mem (Sv s₀) 16 = iv0 s₀

theorem length_xored (t : List Byte) (ys : List (List Byte)) (i : Nat) (hi : i ≤ ys.length) :
    (xored t ys i).length = ys.length := by
  simp [xored, AesXts.length_tweaks]; omega

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dataBlk {j : Nat} (hj : j < N s₀) {r : Region} (hr : (dataR s₀).Disjoint r) :
    (⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
  hr.sub_left (UPre.data_sub hj)

omit hp in
theorem PInv.big {ys : List (List Byte)} {i : Nat} {s : State} (h : PInv s₀ ys i s) :
    Frame (Big s₀) s₀.mem s.mem :=
  UPre.big_of h.frame

omit hp in
theorem passBody_eq : passBody = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ (mulA ++ advance)) := by
  simp only [passBody, List.append_assoc]; rfl

/-- One block of a pass. -/
theorem pstep_wp {ys : List (List Byte)} {i : Nat} (hi : i < N s₀) {s : State} (h : PInv s₀ ys i s) :
    WP isa (.block passBody) s fun s' => PInv s₀ ys (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N s₀)) := by
  obtain hd := hp.d32 hi
  obtain qN := hp.dataN hi
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain rwl : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hrw, hp.rd, hp.wr]; rfl
  obtain wl : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [passBody_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.args_of h.big 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  obtain i₃ : s₃.gpr .esi = D32 s₀ i := by rw [u₃.other _ (by decide), h.esi]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega_using [hi, hdf]) (by rw [b₃]; omega_using [hiv]) (by rw [i₃, qN]; omega_using [hi, hdf])
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hi (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, wl]; exact covBlk hi (by simp)) fun s₄ g₄ => ?_
  obtain m₄ : s₄.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ i) (blk s₀ i) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  obtain f₄ : Frame [⟨blk s₀ i, 16⟩] s.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain b₄ : s₄.gpr .ebx = Iv s₀ := by rw [g₄.gpr _ (by decide) (by decide), b₃]
  obtain rwl₄ : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rwl]
  obtain wl₄ : s₄.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [g₄.wr, u₃.wr, wl]
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ := mulA_ok s₄ (Q := (Iv s₀).setWidth 64) (by rw [b₄]) (by rw [b₄]; omega_using [hiv])
    (fun d n hdn => by rw [rwl₄]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega_using [hdn])⟩)
    (fun d n hdn => by rw [wl₄]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega_using [hdn])⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain f₅ : Frame [ivR s₀] s₄.mem s₅.mem := by rw [mem₅]; exact alphaMem_frame _ _
  obtain fStep : Frame [⟨blk s₀ i, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem :=
    (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₅.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have keep₅ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) (h₄ : r ≠ .edi) (h₅ : r ≠ .ebp)
      (h₆ : r ≠ .ebx) : s₅.gpr r = s.gpr r := by
    rw [g₅ r h₁ h₂ h₃ h₄ h₅, g₄.gpr _ h₁ h₂, u₃.other _ h₆]
  obtain bigStep : Frame (Big s₀) s₀.mem s₅.mem := h.big.trans ((stepFrame hi fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine WP.mono (advance_wp hp hi
    (by rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esi])
    (by rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp])
    (hp.args_of bigStep) (by rw [rd₅, wr₅, g₄.rd, g₄.wr, u₃.rd, u₃.wr, hrw]))
    fun s₈ ⟨esi₈, esp₈, _, mem₈, rd₈, wr₈, zf₈⟩ => ⟨?_, zf₈⟩
  obtain hy : i < ys.length := by rw [h.len]; exact hi
  obtain blkI : bytesAt s.mem (blk s₀ i) 16 = ys[i] := by
    have := congrArg (·[i]?) h.data
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi),
      getElem_blocksAt _ _ hi, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  obtain newBlk : bytesAt s₈.mem (blk s₀ i) 16 = Spec.Cbc.xor ys[i] (Spec.Xts.next (iv0 s₀) i) := by
    rw [mem₈, mem₅, bytesAt_frame (alphaMem_frame _ _) (one (hp.blk_iv hi)) (by decide), m₄,
      xorIn4_bytes _ (hp.blk_iv hi), blkI, h.iv]
  obtain newIv : bytesAt s₈.mem ((Iv s₀).setWidth 64) 16 = Spec.Xts.next (iv0 s₀) (i + 1) := by
    rw [mem₈, mem₅, alphaMem_bytes, m₄,
      bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hi).symm) (by decide), h.iv]
    rfl
  obtain newSv : bytesAt s₈.mem (Sv s₀) 16 = iv0 s₀ := by
    rw [mem₈, mem₅, bytesAt_frame (alphaMem_frame _ _) (one hp.iv_sv.symm) (by decide), m₄,
      bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_sv hi).symm) (by decide), h.sv]
  refine ⟨esi₈, esp₈, by rw [rd₈, rd₅, g₄.rd, u₃.rd, h.rd], by rw [wr₈, wr₅, g₄.wr, u₃.wr, h.wr],
    by rw [mem₈]; exact h.frame.trans (stepFrame hi fStep), h.len, ?_, newIv, newSv⟩
  rw [mem₈, hp.blocksAt_step hi fStep, h.data, ← mem₈, newBlk, xored_step _ hy]

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} (hN : 0 < N s₀) {s : State} (h : PInv s₀ ys 0 s) :
    WP isa pass s (PInv s₀ ys (N s₀)) := by
  refine WP.loop (M := isa) (body := .block passBody) (c := .ne) (Q := PInv s₀ ys (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ PInv s₀ ys j t) ?_ (N s₀ - 0) s
    ⟨0, rfl, hN, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (pstep_wp hp hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

omit hp in
theorem saveT_eq : saveT = .mov .ebx (argOp 2) :: .mov .ebp (argOp 5) ::
    (zero4 .ebp cOff ++ (xor4 .ebp .ebx .ebp cOff 0 cOff ++ [])) := by
  simp only [saveT, List.append_nil]; rfl

/-- The tweak saved. -/
theorem saveT_wp {M : Mode} (hM : ∀ R w t, M.chain R w t [] = t) (hO : ∀ R w t, M.out R w t [] = [])
    {s : State} (h : LInv M s₀ 0 s) :
    WP isa (.block saveT) s (PInv s₀ (blks s₀) 0) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain big := UPre.big_of h.frame
  obtain hargs := hp.args_of big
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  rw [saveT_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 5 (by decide))
    fun s₂ u₂ => ?_
  obtain b₂ : s₂.gpr .ebx = Iv s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have p₂ : s₂.gpr .ebp = S s₀ := u₂.gpr
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₂.wr, u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [p₂]; unfold cOff; omega_using [hsc]) (by rw [p₂, w₂]; exact covSv (by simp))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), p₂]
  obtain b₃ : s₃.gpr .ebx = Iv s₀ := by rw [g₃ _ (by decide), b₂]
  obtain rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₃]; unfold cOff; omega_using [hsc]) (by rw [b₃]; omega_using [hiv]) (by rw [p₃]; unfold cOff; omega_using [hsc])
    (by rw [p₃, rw₃]; exact covSv (by simp))
    (by rw [b₃, add0, rw₃]; exact covIv (by simp))
    (by rw [p₃, wr₃, w₂]; exact covSv (by simp)) fun s₄ g₄ => WP.block_nil ?_
  obtain m₄ : s₄.mem = copy4Mem s.mem (Sv s₀) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, p₃, b₃, add0, m₃, p₂, u₂.mem, u₁.mem]; rfl
  obtain fC : Frame [⟨Sv s₀, 16⟩] s.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  refine ⟨?_, ?_, by rw [g₄.rd, rd₃, u₂.rd, u₁.rd, h.rd], by rw [g₄.wr, wr₃, u₂.wr, u₁.wr, h.wr], ?_,
    by simp [Spec.Cbc.blocksAt], ?_, ?_, ?_⟩
  · rw [g₄.gpr _ (by decide) (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.esi]
  · rw [g₄.gpr _ (by decide) (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.esp]
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (UPre.dataBlk hj hp.data_scr).sub_right (UPre.scr_sub (by decide))), h.data, xored_zero]
    simp [outK, hO]
  · rw [bytesAt_frame fC (one hp.iv_sv) (by decide), h.iv]; simp [chainK, hM]; rfl
  · rw [m₄, copy4Mem_bytes _ hp.iv_sv.symm, h.iv]; simp [chainK, hM]

/-- The arguments of the block function on all the blocks. -/
theorem UPre.bcall {s : State} (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1)
    (edx : s.gpr .edx = Dp s₀) (ebx : s.gpr .ebx = arg s₀ 4) (ebp : s.gpr .ebp = S s₀)
    (esp : s.gpr .esp = E s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) := by
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hdf := hp.data_fit
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, edx, by rw [ebx]; exact arg_ofNat s₀ 4, ebp, hp.rounds,
    by rw [esp]; exact hp.esp24, hp.sch_data, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.data_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_data,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, hdf,
    by have := hp.scr_fit; omega_using [this], ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

omit hp in
theorem callArgs_eq : callArgs = .mov .ebx (argOp 2) :: .mov .ebp (argOp 5) ::
    (zero4 .ebx 0 ++ (xor4 .ebx .ebp .ebx 0 cOff 0 ++ ([.mov .esi (argOp 3), .mov .eax (argOp 0),
      .mov .ecx (argOp 1), .mov .edx (.reg .esi), .mov .ebx (argOp 4)] : List Instr))) := by
  simp only [callArgs, List.append_assoc]; rfl

/-- The tweak restored, `esi` back at the first block, and the arguments of
the block function. -/
theorem callArgs_wp {ys : List (List Byte)} {s : State} (h : PInv s₀ ys (N s₀) s) :
    WP isa (.block callArgs) s fun s' =>
      Proof.AesOcb.X86.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) ys (N s₀)) 0 s' := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of h.big
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  rw [callArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 5 (by decide))
    fun s₂ u₂ => ?_
  obtain b₂ : s₂.gpr .ebx = Iv s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have p₂ : s₂.gpr .ebp = S s₀ := u₂.gpr
  obtain w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₂.wr, u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [b₂]; omega_using [hiv]) (by rw [b₂, add0, w₂]; exact covIv (by simp))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  obtain p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), p₂]
  obtain b₃ : s₃.gpr .ebx = Iv s₀ := by rw [g₃ _ (by decide), b₂]
  obtain rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₃]; omega_using [hiv]) (by rw [p₃]; unfold cOff; omega_using [hsc]) (by rw [b₃]; omega_using [hiv])
    (by rw [b₃, add0, rw₃]; exact covIv (by simp))
    (by rw [p₃, rw₃]; exact covSv (by simp))
    (by rw [b₃, add0, wr₃, w₂]; exact covIv (by simp)) fun s₄ g₄ => ?_
  obtain m₄ : s₄.mem = copy4Mem s.mem ((Iv s₀).setWidth 64) (Sv s₀) := by
    rw [g₄.mem, p₃, b₃, add0, m₃, b₂, add0, u₂.mem, u₁.mem]; rfl
  obtain fC : Frame [ivR s₀] s.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  obtain big₄ : Frame (Big s₀) s₀.mem s₄.mem := h.big.trans (fC.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  obtain esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄.gpr _ (by decide) (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  obtain rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  obtain args₄ := hp.args_of big₄
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (args₄ 3 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), esp₄])
    (by rw [u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide)) (by rw [u₅.mem]; exact args₄ 0 (by decide))
    fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem]; exact args₄ 1 (by decide)) fun s₇ u₇ => ?_
  refine wp_mov fun s₈ u₈ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), esp₄])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide))
    (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact args₄ 4 (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have g (r : Reg) (h1 : r ≠ .ebx) (h2 : r ≠ .edx) (h3 : r ≠ .ecx) (h4 : r ≠ .eax) (h5 : r ≠ .esi) :
      s₉.gpr r = s₄.gpr r := by
    rw [u₉.other _ h1, u₈.other _ h2, u₇.other _ h3, u₆.other _ h4, u₅.other _ h5]
  obtain mem₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, g₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, wr₃, u₂.wr, u₁.wr, h.wr]
  obtain esi₉ : s₉.gpr .esi = Dp s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  obtain esp₉ : s₉.gpr .esp = E s₀ := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), esp₄]
  have hlen : ys.length = N s₀ := h.len
  refine ⟨UPre.bcall hp
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr])
    (by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr])
    u₉.gpr
    (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), g₄.gpr _ (by decide) (by decide), p₃])
    esp₉ rd₉ wr₉, ?_⟩
  refine ⟨by rw [esi₉]; simp [D32], esp₉, rd₉, wr₉, ?_, by rw [length_xored _ _ _ (by omega_using [hlen]), hlen], ?_, ?_, ?_⟩
  · rw [mem₉]; exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  · rw [mem₉, blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact UPre.dataBlk hj hp.iv_data.symm), h.data, xored_zero]
  · rw [mem₉, m₄, copy4Mem_bytes _ hp.iv_sv, h.sv]; rfl
  · rw [mem₉, bytesAt_frame fC (one hp.iv_sv.symm) (by decide), h.sv]

/-- The call of the block function on all the blocks. -/
theorem call_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {ys : List (List Byte)} {s : State}
    (hc : Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀)) (h : PInv s₀ ys 0 s) :
    WP isa (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) s
      (PInv s₀ (ys.map (ciphOf enc (R s₀) (wK s₀))) 0) := by
  refine WP.mono (Proof.AesOcb.X86.blk_call (fn := ⟨b.name, b.code⟩) ok nosp stack hc) fun s' c => ?_
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
  obtain fr : Frame [dataR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s'.mem := by
    have := c.frame; rw [hb] at this; exact this
  obtain fCall : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s'.mem :=
    fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain dIv : ∀ r ∈ [dataR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_data
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  obtain dSv : ∀ r ∈ [dataR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_right (UPre.scr_sub (by decide))).symm
    · exact hp.sv_scr
    · exact (hp.b_scr.sub_right (UPre.scr_sub (by decide))).symm
  obtain sched : bytesAt s.mem (w64 (W s₀)) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp h.big
  refine ⟨by rw [c.saved .esi (by simp [calleeSaved]), h.esi], by rw [c.saved .esp (by simp [calleeSaved]), h.esp],
    by rw [c.rd, h.rd], by rw [c.wr, h.wr], h.frame.trans fCall, by simp [h.len], ?_, ?_, ?_⟩
  · rw [blocksAt_of_out c.out (fun p => hf _ _ _ p), h.data, xored_zero, xored_zero, sched]
  · rw [bytesAt_frame fr dIv (by decide), h.iv]
  · rw [bytesAt_frame fr dSv (by decide), h.sv]

omit hp in
/-- After the second pass: XTS of all the blocks (`AesXts.crypt_eq`). -/
theorem final_of (enc : Bool) {s : State}
    (h : PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) (N s₀) s) :
    LInv (AesXts.xtsMode enc) s₀ (N s₀) s := by
  obtain hl : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  obtain ce := crypt_eq (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)
  rw [hl] at ce
  exact { esi := h.esi, esp := h.esp, rd := h.rd, wr := h.wr, frame := h.frame
          data := by
            rw [h.data, xored_all _ h.len, xored_all _ hl, ce, outK, AesXts.xtsMode_out,
              List.take_of_length_le (by omega_using [hl]), List.drop_of_length_le (by omega_using [hl]), List.append_nil]
          iv := by
            rw [h.iv, chainK, AesXts.xtsMode_chain, List.take_of_length_le (by omega_using [hl]), hl] }

/-- All the blocks. -/
theorem batch_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hN : 0 < N s₀) {s : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s) :
    WP isa (batch b) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h) fun _ h₁ =>
    WP.seq (WP.mono (pass_wp hp hN h₁) fun _ h₂ =>
      WP.seq (WP.mono (callArgs_wp hp h₂) fun _ ⟨c₃, h₃⟩ =>
        WP.seq (WP.mono (call_wp hp enc ok nosp stack hf c₃ h₃) fun _ h₄ =>
          WP.mono (pass_wp hp hN h₄) fun _ h₅ => final_of enc h₅))))

end

/-- The whole function. -/
theorem crypt_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {s₀ : State} (h0 : (modeX86 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt b) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 (AesXts.xtsMode enc)).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => batch_wp hp enc ok nosp stack hf hN h

end VG.Proof.AesXts.X86

end

end

/-!
# XTS-AES on x86: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/X86/CT.lean`): the taint
analysis covers the code around the call, from `esp`, the stack arguments
and `esi` (which the correctness proof pins to the public arguments,
`PInv`), and the call of the block function on all the blocks, in its frame,
is constant time by its own proof (AES-OCB's `blk_ct`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86
open VG.Proof.MdStream.X86 (eval_ne)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- A piece of code the taint analysis checks from the registers `rs`, `esp`
and the stack arguments, which agree in two runs, with what each run
reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (argTaint rs (4 + 4 * 6)) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ ha ht).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem saveT_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block saveT) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem passBody_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block passBody) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callArgs_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 6)) (.block callArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem PInv.pt {s₀ : State} (hp : UPre s₀) {ys : List (List Byte)} {i : Nat} {s : State}
    (h : PInv s₀ ys i s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep h.big hi⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (modeX86 (AesXts.xtsMode enc)).pub s₀ s₀')
include hq

theorem PInv.agree (hp : UPre s₀) (hp' : UPre s₀') {ys ys' : List (List Byte)} {i : Nat} {s₁ s₂ : State}
    (h₁ : PInv s₀ ys i s₁) (h₂ : PInv s₀' ys' i s₂) :
    VG.X86.Taint.Agree (argTaint [.esi] (4 + 4 * 6)) s₁ s₂ :=
  Pt.agree hq hp hp' (h₁.pt hp) (h₂.pt hp') fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.esi, h₂.esi, pub_D32 hq]

/-- A pass over the blocks, in two runs: the taint analysis checks each
iteration. -/
theorem pass_rel (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => PInv s₀ ys 0 a ∧ PInv s₀' ys' 0 b) pass
      fun a b => PInv s₀ ys (N s₀) a ∧ PInv s₀' ys' (N s₀') b := by
  have hN' := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ PInv s₀ ys k s₁ ∧ PInv s₀' ys' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (N s₀ - 0)).mono
    (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := taint_rel [.esi] passBody_taint
    (P := fun a b => N s₀ - k = N s₀ - k ∧ k < N s₀ ∧ PInv s₀ ys k a ∧ PInv s₀' ys' k b)
    (fun _ _ h => PInv.agree hq hp hp' h.2.2.1 h.2.2.2)
    (F₁ := fun (s : State) => PInv s₀ ys (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀)))
    (F₂ := fun (s : State) => PInv s₀' ys' (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀')))
    fun _ _ h => ⟨pstep_wp hp hk h.2.2.1, pstep_wp hp' (by rw [← hN']; exact hk) h.2.2.2⟩
  refine ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN']; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN', ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, h0], l₁, l₂⟩

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  have hN' : 0 < N s₀' := by rw [← pub_N hq]; exact hN
  -- The tweak saved.
  have a := taint_rel [] saveT_taint (P := fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧
      LInv (AesXts.xtsMode enc) s₀' 0 b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := PInv s₀ (blks s₀) 0) (F₂ := PInv s₀' (blks s₀') 0)
    fun _ _ h => ⟨saveT_wp hp (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.1,
      saveT_wp hp' (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.2⟩
  -- The first pass.
  have p₁ := pass_rel hq hp hp' hN (ys := blks s₀) (ys' := blks s₀')
  -- `T` restored, and the arguments of the call.
  have c := taint_rel [] callArgs_taint
    (P := fun a b => PInv s₀ (blks s₀) (N s₀) a ∧ PInv s₀' (blks s₀') (N s₀') b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) 0 s')
    (F₂ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
      PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) 0 s')
    fun _ _ h => ⟨callArgs_wp hp h.1, callArgs_wp hp' h.2⟩
  -- The call.
  have k := (RelCT.mono (Proof.AesOcb.X86.blk_ct (fn := ⟨b.name, b.code⟩) ok ct
      (I := fun s => Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧ s.gpr .esp = E s₀)
      fun _ h => h) (P' := fun a b =>
        (Proof.AesOcb.X86.BCall a (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
          PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) 0 a) ∧
        (Proof.AesOcb.X86.BCall b (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
          PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) 0 b))
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.esp⟩, by
        rw [pub_W hq, pub_Dp hq, pub_S hq, pub_R hq, pub_N hq, pub_E hq]; exact ⟨h.2.1, h.2.2.esp⟩⟩)
      fun _ _ _ => trivial).wp
    (F₁ := PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) 0)
    (F₂ := PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))) 0)
    fun _ _ h => ⟨call_wp hp enc ok nosp stack hf h.1.1 h.1.2, call_wp hp' enc ok nosp stack hf h.2.1 h.2.2⟩
  -- The second pass.
  have p₂ := (pass_rel hq hp hp' hN).mono (fun _ _ h => h) fun _ _ h =>
    (⟨final_of enc h.1, final_of enc h.2⟩ : LInv (AesXts.xtsMode enc) s₀ (N s₀) _ ∧
      LInv (AesXts.xtsMode enc) s₀' (N s₀') _)
  exact a.seq (p₁.seq (c.seq ((k.mono (fun _ _ h => h) fun _ _ h => h.2).seq p₂)))

end

theorem crypt_ct (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub (crypt b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' hN => batch_rel hq ok ct nosp stack hf hp hp' hN)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86

end

end

/-!
# XTS-AES on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean`, with 24
bytes of stack: the call of the block function pushes its five arguments and
the return address.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.decSpSafe]
  decide +kernel

end VG.Proof.AesXts.X86
