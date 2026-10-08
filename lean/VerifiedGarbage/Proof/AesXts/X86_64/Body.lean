import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.AesXts.Batch
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# XTS-AES on x86-64: all the blocks in one call

`batch_wp`: from AES-CBC's loop invariant after no blocks
(`Proof/AesCbc/X86_64/Loop.lean`), `batch` reaches it after all of them, for
`xtsMode enc`, for any implementation of the block functions (`BlocksImpl`).
The tweak is saved (`saveT_wp`); a pass XORs each block's tweak into it,
multiplying the tweak by `α` after each (`pass_wp`, by `pstep_wp` for one
block, whose invariant `PInv` says what `xored` the blocks are); the tweak is
restored and the block function called on all the blocks (`callArgs_wp`,
`call_wp`, from AES-OCB's `BCall`); and a second pass XORs the tweaks in
again (`AesXts.crypt_eq`).
-/

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore xorInto copy cOff advance)
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state
  aesInvWith_state Mode ciphOf length_blocksAt getElem_blocksAt bytesAt_toList)
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesXts (xored xored_zero xored_getElem xored_step xored_all crypt_eq)

/-- The saved copy of the tweak. -/
abbrev Sv (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 2048

/-- A pass over the blocks `ys`, after `i` of them, with `r10` and `r11`
kept. -/
structure PInv (s₀ : State) (ys : List (List Byte)) (x10 x11 : BitVec 64) (i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ i
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - i)
  r15 : s.gpr .r15 = S s₀
  r10 : s.gpr .r10 = x10
  r11 : s.gpr .r11 = x11
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = xored (iv0 s₀) ys i
  iv : bytesAt s.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) i
  sv : bytesAt s.mem (Sv s₀) 16 = iv0 s₀

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

theorem length_xored (t : List Byte) (ys : List (List Byte)) (i : Nat) (hi : i ≤ ys.length) :
    (xored t ys i).length = ys.length := by
  simp [xored, AesXts.length_tweaks]; omega

/-- The blocks after a frame outside them. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ j < n, ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  simp only [Spec.Cbc.blocksAt]
  exact List.map_congr_left fun j hj => bytesAt_frame hf (hd j (List.mem_range.mp hj)) (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dataBlk {j : Nat} (hj : j < N s₀) {r : Region} (hr : (dataR s₀).Disjoint r) :
    (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
  hr.sub_left (UPre.data_sub hj)

/-- One block of a pass. -/
theorem pstep_wp {ys : List (List Byte)} {x10 x11 : BitVec 64} {i : Nat} (hi : i < N s₀) {s : State}
    (h : PInv s₀ ys x10 x11 i s) :
    WP isa (.block passBody) s fun s' =>
      PInv s₀ ys x10 x11 (i + 1) s' ∧ s'.zf = some (decide (N s₀ - (i + 1) = 0)) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ i) (Q := Iv s₀) h.r13 h.r12
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hi))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hi)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hi))
  have hR₁ : s₁.rd ++ s₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₁, wr₁, hR]
  have hW₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, hW]
  obtain ⟨s₂, run₂, g₂, mem₂, rd₂, wr₂⟩ :=
    mulA_ok s₁ (Q := Iv s₀) (by rw [g₁ _ (by decide), h.r12])
      (by rw [hR₁]; exact in_rw (by simp) cIv0) (by rw [hR₁]; exact in_rw (by simp) cIv8)
      (by rw [hW₁]; exact in_rw (by simp) cIv0) (by rw [hW₁]; exact in_rw (by simp) cIv8)
  obtain ⟨s₃, run₃, r13₃, r14₃, zf₃, keep₃, mem₃, rd₃, wr₃⟩ := advance_regs (s := s₂) hi
    (by rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r13])
    (by rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r14])
  rw [passBody, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, WP.of_runBlock ⟨s₃, run₃, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .rdx) (h13 : r ≠ .r13) (h14 : r ≠ .r14) :
      s₃.gpr r = s.gpr r := by
    rw [keep₃ r h13 h14, g₂ r h1 h2 h3, g₁ r h1]
  have f₁ : Frame [⟨blk s₀ i, 16⟩] s.mem s₁.mem := by rw [mem₁]; exact xorMem_frame _ _ _
  have f₂ : Frame [ivR s₀] s₁.mem s₂.mem := by rw [mem₂]; exact alphaMem_frame _ _
  have fStep : Frame [⟨blk s₀ i, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₃.mem := by
    rw [mem₃]
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have hy : i < ys.length := by rw [h.len]; exact hi
  have blkI : bytesAt s.mem (blk s₀ i) 16 = ys[i] := by
    have := congrArg (·[i]?) h.data
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi),
      getElem_blocksAt _ _ hi, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  have newBlk : bytesAt s₃.mem (blk s₀ i) 16 = Spec.Cbc.xor ys[i] (Spec.Xts.next (iv0 s₀) i) := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one (hp.blk_iv hi)) (by decide), mem₁,
      xorMem_bytes _ (hp.blk_iv hi), blkI, h.iv]
  have newIv : bytesAt s₃.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (i + 1) := by
    rw [mem₃, mem₂, alphaMem_bytes, mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_iv hi).symm) (by decide), h.iv]
    rfl
  have newSv : bytesAt s₃.mem (Sv s₀) 16 = iv0 s₀ := by
    rw [mem₃, mem₂, bytesAt_frame (alphaMem_frame _ _) (one hp.iv_sv.symm) (by decide), mem₁,
      bytesAt_frame (xorMem_frame _ _ _) (one (hp.blk_sv hi).symm) (by decide), h.sv]
  refine ⟨⟨?_, ?_, ?_, r13₃, r14₃, ?_, ?_, ?_, ?_, ?_, ?_, h.frame.trans (stepFrame hi fStep), h.len,
    ?_, newIv, newSv⟩, zf₃⟩
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide) (by decide) (by decide), h.r12]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h.r15]
  · rw [g .r10 (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by decide) (by decide) (by decide) (by decide) (by decide), h.r11]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), h.rsp]
  · rw [rd₃, rd₂, rd₁, h.rd]
  · rw [wr₃, wr₂, wr₁, h.wr]
  · rw [hp.blocksAt_step hi fStep, h.data, newBlk, xored_step _ hy]

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} {x10 x11 : BitVec 64} (hN : 0 < N s₀) {s : State}
    (h : PInv s₀ ys x10 x11 0 s) : WP isa pass s (PInv s₀ ys x10 x11 (N s₀)) := by
  refine WP.loop (M := isa) (body := .block passBody) (c := .ne) (Q := PInv s₀ ys x10 x11 (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ PInv s₀ ys x10 x11 j t) ?_ (N s₀ - 0) s
    ⟨0, rfl, hN, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (pstep_wp hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

omit hp in
theorem movs_ok (s : State) :
    ∃ s', runBlock isa [.mov .r10 (.reg .r13), .mov .r11 (.reg .r14)] s = some s' ∧
      s'.gpr .r10 = s.gpr .r13 ∧ s'.gpr .r11 = s.gpr .r14 ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-- The tweak saved, and the data pointer and number of blocks kept. -/
theorem saveT_wp {M : Mode} (hM : ∀ R w t, M.chain R w t [] = t) (hO : ∀ R w t, M.out R w t [] = [])
    {s : State} (h : LInv M s₀ 0 s) :
    WP isa (.block saveT) s (PInv s₀ (blks s₀) (blk s₀ 0) (BitVec.ofNat 64 (N s₀)) 0) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .r15) (src := .r12) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.r15]; rfl) (by rw [h.r15, Offset.add_add]; rfl) (by simp [h.r12])
      (by simp [h.r12]) (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8) (by decide) (by decide)
  obtain ⟨s₂, run₂, r10₂, r11₂, g₂, mem₂, rd₂, wr₂⟩ := movs_ok s₁
  rw [saveT, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .r10) (h3 : r ≠ .r11) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h2 h3, g₁ r h1]
  have fC : Frame [⟨Sv s₀, 16⟩] s.mem s₂.mem := by rw [mem₂, mem₁]; exact copyMem_frame _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [Spec.Cbc.blocksAt], ?_, ?_, ?_⟩
  · rw [g .rbx (by decide) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide), h.r12]
  · rw [g .r13 (by decide) (by decide) (by decide), h.r13]
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [r10₂, g₁ _ (by decide), h.r13]
  · rw [r11₂, g₁ _ (by decide), h.r14]; rfl
  · rw [g .rsp (by decide) (by decide) (by decide), h.rsp]
  · rw [rd₂, rd₁, h.rd]
  · rw [wr₂, wr₁, h.wr]
  · exact h.frame.trans (fC.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩)
  · rw [blocksAt_frame fC (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (UPre.dataBlk hj hp.data_scr).sub_right (UPre.scr_sub (by decide))), h.data, xored_zero]
    simp [outK, hO]
  · rw [bytesAt_frame fC (one hp.iv_sv) (by decide), h.iv]; simp [chainK, hM]; rfl
  · rw [mem₂, mem₁, copyMem_bytes _ hp.iv_sv.symm, h.iv]; simp [chainK, hM]

end

end VG.Proof.AesXts.X86_64
