import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.BlocksCT
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds`. -/
section

/-! AES-NI round execution on IA-32. Register updates stay folded; the same
proof applies to any distinct block registers other than the key temporary. -/
namespace VG.Proof.Aes.X86.AesNi
open VG.X86
open VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ keyOp round aes)
open VG.Spec.Aes (roundKey bytesAt cipher)

structure XFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem XFrame.refl (rs : List XReg) (s : State) : VG.Proof.Aes.X86.AesNi.XFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XFrame.trans {rs : List XReg} {s s' s'' : State}
    (h : VG.Proof.Aes.X86.AesNi.XFrame rs s s') (h' : VG.Proof.Aes.X86.AesNi.XFrame rs s' s'') : VG.Proof.Aes.X86.AesNi.XFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XFrame.mono {rs rs' : List XReg} {s s' : State}
    (h : VG.Proof.Aes.X86.AesNi.XFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Aes.X86.AesNi.XFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem map_ok (op : XBinOp) : ∀ (regs : List XReg) (s : State),
    regs.Nodup → .xmm6 ∉ regs →
    WP isa (.block (regs.map fun b => .xop (.bin op b .xmm6))) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.xmm .xmm6)) ∧ VG.Proof.Aes.X86.AesNi.XFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, XFrame.refl _ _⟩
  | b :: bs, s, hnd, h6 => by
    have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ List.mem_cons_self ..)
    have h6' : .xmm6 ∉ bs := fun h => h6 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setXmm b (op.eval (s.xmm b) (s.xmm .xmm6)), rfl, ?_⟩
    refine WP.mono (VG.Proof.Aes.X86.AesNi.map_ok op bs _ (List.nodup_cons.mp hnd).2 h6')
      fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.xmm _ hbs, xmm_setXmm_self]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc, xmm_setXmm_of_ne _ _ hcb,
          xmm_setXmm_of_ne _ _ (Ne.symm hb6)]
    · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

theorem keyOp_ok (regs : List XReg) (op : XBinOp) (off : Nat) (s : State)
    (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax off)) 16) :
    WP isa (.block (keyOp regs op off)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b)
        (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax off)) 128)) ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  rw [keyOp, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm6 (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax off)) 128), by
    simp only [isa, exec, State.load128, hin, ite_true, Option.map_some], ?_⟩
  refine WP.mono (VG.Proof.Aes.X86.AesNi.map_ok op regs _ hnd h6) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ hb)
    rw [hv b hb, xmm_setXmm_of_ne _ _ hb6, xmm_setXmm_self]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

def RInv (regs : List XReg) (w : List Byte) (x : XReg → Spec.Aes.State)
    (k : Nat) (s : State) : Prop := ∀ b ∈ regs, VG.Proof.Aes.X86.AesNi.st (s.xmm b) = rnds w (x b) k

/-- The readable schedule and its byte representation. The ABI proof discharges
these facts using the public schedule address and its nonwrapping region. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  le : nr ≤ 14
  keys : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax (16 * j))) 16
  bytes : ∀ j ≤ nr, ∀ i < 16,
    byte (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax (16 * j))) 128) i = (roundKey w j).getD i 0

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State}
    (h : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hf : VG.Proof.Aes.X86.AesNi.XFrame rs s s') : VG.Proof.Aes.X86.AesNi.Keys nr w s' :=
  ⟨h.le, by simp only [State.ea, hf.rd, hf.wr, hf.gpr]; exact h.keys,
    by simp only [State.ea, hf.mem, hf.gpr]; exact h.bytes⟩

theorem round_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat}
    (hk : k + 1 ≤ nr) {s : State} (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86.AesNi.RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.RInv regs w x (k + 1) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOp_ok regs .aesenc _ s hnd h6 (hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenc_st _ _ (roundKey w (k + 1)) (hK.bytes _ hk), hI b hb, rnds_succ]

theorem rounds_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (s : State)
    (hk : k ≤ nr) (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86.AesNi.RInv regs w x 0 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.RInv regs w x k s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Aes.X86.AesNi.round_ok regs hnd h6 (k := k) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem start_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} (s : State) (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) :
    WP isa (.block (keyOp regs .pxor 0)) s fun s' =>
      VG.Proof.Aes.X86.AesNi.RInv regs w (fun b => VG.Proof.Aes.X86.AesNi.st (s.xmm b)) 0 s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOp_ok regs .pxor 0 s hnd h6 (hK.keys 0 (Nat.zero_le _)))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, pxor_st _ _ (roundKey w 0) (hK.bytes 0 (Nat.zero_le _)), rnds_zero]

theorem last_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} (s : State)
    (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86.AesNi.RInv regs w x (nr - 1) s) :
    WP isa (.block (keyOp regs .aesenclast (16 * nr))) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.X86.AesNi.st (s'.xmm b) = cipher nr w (x b)) ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOp_ok regs .aesenclast _ s hnd h6 (hK.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenclast_st _ _ (roundKey w nr) (hK.bytes nr (Nat.le_refl _)),
    hI b hb, VG.Proof.Aes.X86.AesNi.cipher_eq]

theorem cmpEcx_ok (s : State) (c : BitVec 32) :
    WP isa (.block [.alu .cmp .ecx (.imm c)]) s fun s' =>
      s'.zf = some (s.gpr .ecx - c == 0) ∧ VG.Proof.Aes.X86.AesNi.XFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86.readSrc,
    isa, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, gpr_arithFlags .., mem_arithFlags .., rd_arithFlags ..,
    wr_arithFlags .., fun _ _ => congrFun (xmm_arithFlags ..) _⟩

theorem two_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat}
    (hk : k + 2 ≤ nr) {s : State} (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86.AesNi.RInv regs w x k s) :
    WP isa (.block (round regs (k + 1) ++ round regs (k + 2))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.RInv regs w x (k + 2) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.round_ok regs hnd h6 (k := k) (by omega) hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (VG.Proof.Aes.X86.AesNi.round_ok regs hnd h6 (k := k + 1) (by omega) (hK.of_frame hf₁) hI₁)
    fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte}
    (s : State) (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s) (hc : s.gpr .ecx = BitVec.ofNat 32 nr) :
    WP isa (VG.Impl.Aes.X86.AesNi.aes regs) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.X86.AesNi.st (s'.xmm b) = cipher nr w (VG.Proof.Aes.X86.AesNi.st (s.xmm b))) ∧
      VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  let x := fun b => VG.Proof.Aes.X86.AesNi.st (s.xmm b)
  have hstart : WP isa (.block (keyOp regs .pxor 0 ++
      (List.range 9).flatMap (fun j => round regs (j + 1)))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.RInv regs w x 9 s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86.AesNi.start_ok regs hnd h6 s hK) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    have hn : 9 ≤ nr := by rcases hnr with h | h | h <;> omega
    exact WP.mono (VG.Proof.Aes.X86.AesNi.rounds_ok regs hnd h6 9 s₁ hn (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  unfold VG.Impl.Aes.X86.AesNi.aes
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hstart fun s₁ ⟨hI₁, hf₁⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86.AesNi.cmpEcx_ok s₁ 10) fun s₂ ⟨hz₂, hf₂⟩ => ?_
  have hf₀₂ := hf₁.trans (hf₂.mono (by simp))
  have hK₂ := hK.of_frame hf₀₂
  have hI₂ : VG.Proof.Aes.X86.AesNi.RInv regs w x 9 s₂ := fun b hb => by
    rw [hf₂.xmm b (by simp)]; exact hI₁ b hb
  rcases hnr with rfl | rfl | rfl
  · refine WP.ite true (by simp [VG.X86.eval, hz₂, hf₁.gpr, hc]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (VG.Proof.Aes.X86.AesNi.last_ok regs hnd h6 s₂ hK₂ hI₂)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₂.trans hf⟩
  all_goals
    refine WP.ite false (by simp [VG.X86.eval, hz₂, hf₁.gpr, hc]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86.AesNi.two_ok regs hnd h6 (k := 9) (by decide) hK₂ hI₂)
      fun s₃ ⟨hI₃, hf₃⟩ => ?_
    refine WP.mono (VG.Proof.Aes.X86.AesNi.cmpEcx_ok s₃ 12)
      fun s₄ ⟨hz₄, hf₄⟩ => ?_
    have hf₀₄ := hf₀₂.trans (hf₃.trans (hf₄.mono (by simp)))
    have hK₄ := hK.of_frame hf₀₄
    have hI₄ : VG.Proof.Aes.X86.AesNi.RInv regs w x 11 s₄ := fun b hb => by
      rw [hf₄.xmm b (by simp)]; exact hI₃ b hb
  · refine WP.ite true (by simp [VG.X86.eval, hz₄, hf₃.gpr, hf₀₂.gpr, hc]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (VG.Proof.Aes.X86.AesNi.last_ok regs hnd h6 s₄ hK₄ hI₄)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₄.trans hf⟩
  · refine WP.ite false (by simp [VG.X86.eval, hz₄, hf₃.gpr, hf₀₂.gpr, hc]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86.AesNi.two_ok regs hnd h6 (k := 11) (by decide) hK₄ hI₄)
      fun s₅ ⟨hI₅, hf₅⟩ => ?_
    exact WP.mono (VG.Proof.Aes.X86.AesNi.last_ok regs hnd h6 s₅ (hK₄.of_frame hf₅) hI₅)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₄.trans (hf₅.trans hf)⟩

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Dec`. -/
section

/-!
# AES-NI on x86 (32-bit): decryption

On registers holding states (`st`), `aesdec` with `InvMixColumns` of a round
key is a middle round of FIPS 197's inverse cipher, since `InvMixColumns`
is linear (the equivalent inverse cipher, §5.3.5): `aesdec_st`. With
`aesdeclast` and `aesimc` (`aesdeclast_st`, `st_aesimc`), `aesDec_ok`
proves that `Impl.Aes.X86.AesNi.aesDec` decrypts each register of a list,
from the round keys through `aesimc` and the last round key that `imcKeys`
leaves in the scratch buffer (`imcKeys_ok`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ keyOpAt imcKey copyLast imcKeys dround aesDec)
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns addRoundKey invSbox roundKey invCipher bytesAt)
open VG.Proof.Aes (rkState irnd invMid invMid_succ invCipher_eq invMixColumns_addRoundKey)

theorem invSbox_eq : aesInvSbox = invSbox := by
  funext b
  simp only [aesInvSbox, invSbox, Spec.Aes.invAffine, inv_eq, ofBits8]

theorem getD_invSubBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invSubBytes s).getD i 0 = invSbox (s.getD i 0) := by
  simp [invSubBytes, Vector.getD, h]

theorem getD_invShiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.invShiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [VG.Spec.Aes.invShiftRows, getD_ofFn h]

theorem getD_invMixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.invMixColumns s).getD i 0 =
      Spec.Aes.mul 0x0e (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0b (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0d (s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x09 (s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) := by
  rw [VG.Spec.Aes.invMixColumns, getD_ofFn h]

theorem byte_invShiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  rw [aesInvShiftRows, VG.Proof.Gcm.X86.byte_ofBytes _ h]

theorem byte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvMixColumns x) i =
      aesMul 0x0e (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, VG.Proof.Gcm.X86.byte_ofBytes _ h]

/-- `aesimc` is `InvMixColumns`. -/
theorem st_aesimc (k : BitVec 128) : VG.Proof.Aes.X86.AesNi.st (aesInvMixColumns k) = VG.Spec.Aes.invMixColumns (VG.Proof.Aes.X86.AesNi.st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, VG.Proof.Aes.X86.AesNi.byte_invMixColumns _ hi, VG.Proof.Aes.X86.AesNi.getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- InvSubBytes after InvShiftRows, byte by byte. -/
theorem byte_invSub (v : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (aesMapBytes aesInvSbox (aesInvShiftRows v)) i =
      (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86.AesNi.st v))).getD i 0 := by
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [byte_mapBytes _ _ hi, VG.Proof.Aes.X86.AesNi.byte_invShiftRows _ hi, VG.Proof.Aes.X86.AesNi.getD_invSubBytes _ hi, VG.Proof.Aes.X86.AesNi.getD_invShiftRows _ hi,
    getD_st _ (hs _), VG.Proof.Aes.X86.AesNi.invSbox_eq]

theorem st_invSub (v : BitVec 128) :
    VG.Proof.Aes.X86.AesNi.st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86.AesNi.st v)) :=
  st_ext fun i hi => by rw [getD_st _ hi, VG.Proof.Aes.X86.AesNi.byte_invSub _ hi]

/-- `aesdec` with `InvMixColumns` of the round key `rk` is a middle round of
the inverse cipher. -/
theorem aesdec_st (v k : BitVec 128) (rk : List Byte) (hk : VG.Proof.Aes.X86.AesNi.st k = VG.Spec.Aes.invMixColumns (rkState rk)) :
    VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .aesdec v k) =
      VG.Spec.Aes.invMixColumns (VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86.AesNi.st v))) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, ← hk, getD_st _ hi, getD_st _ hi]
  simp only [XBinOp.eval, byte_xor]
  rw [← VG.Proof.Aes.X86.AesNi.st_invSub, ← VG.Proof.Aes.X86.AesNi.st_aesimc, getD_st _ hi]

/-- `aesdeclast` is the last round of the inverse cipher. -/
theorem aesdeclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .aesdeclast v k) = VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86.AesNi.st v))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  rw [VG.Proof.Aes.X86.AesNi.byte_invSub _ hi]

/-! ## A round key from anywhere -/

theorem keyOpAt_ok (regs : List XReg) (op : XBinOp) (m : MemOp) (s : State)
    (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    WP isa (.block (keyOpAt regs op m)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.mem.readW (s.ea m) 128)) ∧
      VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  rw [keyOpAt, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm6 (s.mem.readW (s.ea m) 128), by
    simp only [isa, exec, State.load128, hin, ite_true, Option.map_some], ?_⟩
  refine WP.mono (VG.Proof.Aes.X86.AesNi.map_ok op regs _ hnd h6) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ hb)
    rw [hv b hb, xmm_setXmm_of_ne _ _ hb6, xmm_setXmm_self]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

/-! ## The rounds -/

/-- What decryption needs of the state: the key schedule at `eax`, readable,
round keys `1 … nr − 1` through `InvMixColumns` at `edx + 16 j`, and the
last round key at `edx + 224`. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  keys : VG.Proof.Aes.X86.AesNi.Keys nr w s
  imc : ∀ j, 1 ≤ j → j < nr →
    InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx (16 * j))) 16 ∧
    VG.Proof.Aes.X86.AesNi.st (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx (16 * j))) 128) = VG.Spec.Aes.invMixColumns (rkState (roundKey w j))
  last : InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx 224)) 16 ∧
    ∀ i < 16, byte (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx 224)) 128) i = (roundKey w nr).getD i 0

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : VG.Proof.Aes.X86.AesNi.DKeys nr w s)
    (hf : VG.Proof.Aes.X86.AesNi.XFrame rs s s') : VG.Proof.Aes.X86.AesNi.DKeys nr w s' :=
  ⟨h.keys.of_frame hf, by simp only [State.ea, hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc,
    by simp only [State.ea, hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.last⟩

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Spec.Aes.State) (m : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, VG.Proof.Aes.X86.AesNi.st (s.xmm b) = invMid nr w m (VG.Spec.Aes.addRoundKey (x b) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : VG.Proof.Aes.X86.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86.AesNi.DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.DInv regs nr w x (m + 1) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOpAt_ok regs .aesdec _ s hnd h6 hin)
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, VG.Proof.Aes.X86.AesNi.aesdec_st _ _ _ hst, hI b hb, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j) {s : State}
    (hK : VG.Proof.Aes.X86.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86.AesNi.DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      VG.Proof.Aes.X86.AesNi.DInv regs nr w x (m + 1) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact VG.Proof.Aes.X86.AesNi.dround_ok regs hnd h6 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : VG.Proof.Aes.X86.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86.AesNi.DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.DInv regs nr w x (nr - 10 + k) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega)
      (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : VG.Proof.Aes.X86.AesNi.DKeys nr w s)
    (hc : s.gpr .ecx = BitVec.ofNat 32 nr) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.X86.AesNi.st (s'.xmm b) = invCipher nr w (VG.Proof.Aes.X86.AesNi.st (s.xmm b))) ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => VG.Proof.Aes.X86.AesNi.st (s.xmm b)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOpAt_ok regs .pxor _ s hnd h6 hK.last.1) fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : VG.Proof.Aes.X86.AesNi.DInv regs nr w x 0 s₁ := fun b hb => by
    rw [hv₁ b hb, pxor_st _ _ (roundKey w nr) hK.last.2]; rfl
  refine WP.mono (VG.Proof.Aes.X86.AesNi.cmpEcx_ok s₁ 10) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : VG.Proof.Aes.X86.AesNi.DInv regs nr w x 0 s₁' := fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb
  have hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 nr := by rw [hf₁.gpr, hc]
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .ecx (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        VG.Proof.Aes.X86.AesNi.DInv regs nr w x (nr - 10) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s' := by
    have hc₁' : s₁'.gpr .ecx = BitVec.ofNat 32 nr := by rw [hf₁₁.gpr, hc]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [VG.X86.eval, hz₁, hc₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [VG.X86.eval, hz₁, hc₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.cmpEcx_ok s₁' 12) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : VG.Proof.Aes.X86.AesNi.DInv regs 12 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => VG.Proof.Aes.X86.AesNi.DInv regs 12 w x 0 s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [VG.X86.eval, hz₂, hc₁']) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show VG.Proof.Aes.X86.AesNi.DInv regs 12 w x 0 s₂ ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 11) (m := 0) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 10) (m := 1) (by omega) (by omega)
        (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [VG.X86.eval, hz₁, hc₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.cmpEcx_ok s₁' 12) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : VG.Proof.Aes.X86.AesNi.DInv regs 14 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := hK.of_frame hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => VG.Proof.Aes.X86.AesNi.DInv regs 14 w x 2 s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [VG.X86.eval, hz₂, hc₁']) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 12) (m := 1) (by omega) (by omega) (hK₂.of_frame hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            VG.Proof.Aes.X86.AesNi.DInv regs 14 w x (1 + 1) s' ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 11) (m := 2) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (VG.Proof.Aes.X86.AesNi.dround_ok' regs hnd h6 (j := 10) (m := 3) (by omega) (by omega)
          (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := hK.of_frame hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.drounds_ok regs hnd h6 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := hK₂.of_frame hf₃
  have k0 := hK₃.keys.bytes 0 (Nat.zero_le _)
  refine WP.mono (VG.Proof.Aes.X86.AesNi.keyOpAt_ok regs .aesdeclast _ s₃ hnd h6 (hK₃.keys.keys 0 (Nat.zero_le _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb, VG.Proof.Aes.X86.AesNi.aesdeclast_st _ _ (roundKey w 0) k0, hI₃ b hb,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Data`. -/
section

/-! XOR the encrypted SIMD lanes into writable data. The execution proof
keeps register updates folded, and expresses memory through writeW. -/
namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ xorData)
open VG.Proof.Gcm.X86 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (blockAt)

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩


theorem blockAt_writeW_sep (m : Mem) {p q : Addr} (v : BitVec 128) (h : Mem.Sep q 16 p 16) :
    VG.Spec.Gcm.blockAt (m.writeW p v) q = VG.Spec.Gcm.blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- A block of a region disjoint from the frame's is unchanged. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : VG.Spec.Gcm.blockAt m' p = VG.Spec.Gcm.blockAt m p :=
  Proof.Gcm.blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk


/-- A single lane XOR, with a public effective address. -/
theorem xor1_ok (b : XReg) (d : Nat) (s : State) (hb : b ≠ .xmm7)
    (hin : InRegions s.wr (s.ea (VG.Impl.Aes.X86.AesNi.at_ .esi d)) 16) :
    WP isa (.block [.movdquLoad .xmm7 (VG.Impl.Aes.X86.AesNi.at_ .esi d), .xop (.bin .pxor b .xmm7),
        .movdquStore (VG.Impl.Aes.X86.AesNi.at_ .esi d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .esi d))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .esi d)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm7 → s'.xmm r = s.xmm r) := by
  have hin' := VG.Proof.Aes.X86.AesNi.inRegions_wr hin
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, isa, State.load128, State.store128, VG.Proof.Aes.X86.AesNi.ea_setXmm,
    gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm,
    hin, hin', hb,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · intro r h1 h2
    simp only [h1, h2, ite_false]

/-- The written bytes represent XOR in the standard's block byte order. -/
theorem blockAt_writeW_xor (m : Mem) (p : Addr) (x : BitVec 128) :
    VG.Spec.Gcm.blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW p 128))) p =
      VG.Spec.Gcm.blockAt m p ^^^ XBinOp.eval .pshufb x revMask := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide)]
  change XBinOp.eval .pshufb (x ^^^ m.readW p 128) revMask = _
  rw [pshufb_rev_xor, BitVec.xor_comm]

theorem xorData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (h7 : .xmm7 ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hw : (s.gpr .esi).toNat + 16 * (j + regs.length) ≤ 2 ^ 32) :
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), VG.Spec.Gcm.blockAt s'.mem (((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) =
        VG.Spec.Gcm.blockAt s.mem (((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.xmm regs[k]) revMask) ∧
      Frame [⟨((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb7 : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h7' : .xmm7 ∉ bs := fun h => h7 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    have hwide : ((s.gpr .esi).setWidth 64).toNat = (s.gpr .esi).toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.gpr .esi).isLt; omega)
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86.AesNi.xor1_ok b (16 * j) s hb7 (by
      rw [ea_mk]; simp only [VG.Impl.Aes.X86.AesNi.at_]; rw [addr_eq (by omega)]; exact hin0)) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hbase : (s₁.gpr .esi).setWidth 64 = (s.gpr .esi).setWidth 64 := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h7' (fun k hk => by
        rw [wr₁, hbase, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [g₁]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hbase] at hb hf
    rw [ea_mk] at m₁
    simp only [VG.Impl.Aes.X86.AesNi.at_] at m₁
    rw [addr_eq (by omega)] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Offset.toNat_sub_add _ _ (by omega)] at h₁ h₂
      have := (a - (s.gpr .esi).setWidth 64).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [VG.Proof.Aes.X86.AesNi.blockAt_frame hf hdj, m₁, VG.Proof.Aes.X86.AesNi.blockAt_writeW_xor]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, VG.Proof.Aes.X86.AesNi.blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [Offset.toNat_sub_add _ _ (by omega)] at h₁ h₂
            have := (a - (s.gpr .esi).setWidth 64).isLt
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h7' (h ▸ List.getElem_mem hk'))]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Offset.toNat_sub_add _ _ (by omega)] at ha ⊢
      have := (a - (s.gpr .esi).setWidth 64).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2, x₁ r hr'.1 hr]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Imc`. -/
section

/-!
# AES-NI on x86 (32-bit): the round keys through `aesimc`

`imcKeys` writes `InvMixColumns` of round keys `1 … nr − 1` to
`scratch + 16 j`, and copies the last round key to `scratch + 224`
(`imcKeys_ok`); `dKeys_of_imc` turns that into what `aesDec` needs.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ imcKey copyLast imcKeys)
open VG.Proof.Aes.X86 (reg32 addr_add in_reg reg_contains in_rd part_contains part_sub_reg)
open VG.Spec.Aes (roundKey bytesAt invMixColumns)
open VG.Proof.Aes (rkState)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- Where the round keys go through `aesimc`: the key schedule at `eax`
(240 bytes, readable) and the scratch buffer at `edx` (2048 bytes,
writable), apart. -/
structure ImcSetup (s₀ : State) : Prop where
  sch : reg32 (s₀.gpr .eax) 240 ∈ s₀.rd ++ s₀.wr
  scr : reg32 (s₀.gpr .edx) 2048 ∈ s₀.wr
  fitS : (s₀.gpr .eax).toNat + 240 ≤ 2 ^ 32
  fitB : (s₀.gpr .edx).toNat + 2048 ≤ 2 ^ 32
  sep : (reg32 (s₀.gpr .eax) 240).Disjoint (reg32 (s₀.gpr .edx) 2048)

/-- After writing the round keys `S` through `aesimc` to the scratch buffer,
from `s₀`. -/
structure ImcInv (s₀ : State) (S : List Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : ∀ r, r ≠ .xmm6 → s.xmm r = s₀.xmm r
  frame : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] s₀.mem s.mem
  le : ∀ j ∈ S, j ≤ 13
  keys : ∀ j ∈ S, s.mem.readW (addr (s₀.gpr .edx) (16 * j)) 128 =
    aesInvMixColumns (s₀.mem.readW (addr (s₀.gpr .eax) (16 * j)) 128)

theorem ImcInv.refl (s₀ : State) : ImcInv s₀ [] s₀ :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem ImcInv.of_frame {s₀ s s' : State} {S : List Nat} (h : ImcInv s₀ S s) (hf : XFrame [] s s') :
    ImcInv s₀ S s' :=
  ⟨hf.gpr.trans h.gpr, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (hf.xmm r (by simp)).trans (h.xmm r hr), by rw [hf.mem]; exact h.frame, h.le,
    by rw [hf.mem]; exact h.keys⟩

section
variable {s₀ : State} (hs : ImcSetup s₀)
include hs

theorem ImcSetup.schIn {j : Nat} (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .eax) (16 * j)) 16 :=
  in_reg hs.sch hs.fitS (by omega) (by decide)

theorem ImcSetup.scrIn {o : Nat} (ho : o + 16 ≤ 240) :
    InRegions s₀.wr (addr (s₀.gpr .edx) o) 16 :=
  in_reg hs.scr hs.fitB (by omega) (by decide)

/-- Writes to bytes 16 … 239 of the scratch buffer leave the schedule. -/
theorem ImcSetup.sched {m m' : Mem} (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') {j : Nat} (hj : j ≤ 14) :
    m'.readW (addr (s₀.gpr .eax) (16 * j)) 128 = m.readW (addr (s₀.gpr .eax) (16 * j)) 128 :=
  hf.readW (reg_contains hs.fitS (by omega) (by decide))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (part_sub_reg hs.fitB (by omega))) (by decide)

theorem ImcSetup.frameIn {m m' : Mem} {o : Nat} (ho₁ : 16 ≤ o) (ho : o + 16 ≤ 240) (v : BitVec 128)
    (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') :
    Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m (m'.writeW (addr (s₀.gpr .edx) o) v) :=
  hf.writeW (List.mem_singleton_self _) _
    (part_contains hs.fitB (by omega) ho₁ (by omega) (by decide))

theorem imcKey_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 13) :
    WP isa (.block (imcKey j)) s (ImcInv s₀ (j :: S)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * j))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn (by omega)
  have hout : InRegions s.wr (s.ea (at_ .edx (16 * j))) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega)
  have ek : s.ea (at_ .eax (16 * j)) = addr (s₀.gpr .eax) (16 * j) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx (16 * j)) = addr (s₀.gpr .edx) (16 * j) := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [imcKey, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, XBinOp.eval, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, ?_, fun j' hj' => ?_,
    fun j' hj' => ?_⟩
  · exact hs.frameIn (by omega) (by omega) _ hI.frame
  · rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hj
    · exact hI.le j' hj'
  · rw [hs.sched hI.frame (by omega)]
    rcases List.mem_cons.mp hj' with rfl | hj'
    · rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
    · by_cases he : j' = j
      · subst he; rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
      · have h13 := hI.le j' hj'
        rw [Mem.readW_writeW_sep (by
            rw [addr_eq (by have := hs.fitB; omega), addr_eq (by have := hs.fitB; omega)]
            exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hI.keys j' hj']

/-- Some round keys through `aesimc`, those of `js`. -/
theorem imcRun_ok (js : List Nat) (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S : List Nat} {s : State}
    (hI : ImcInv s₀ S s) :
    WP isa (.block (js.flatMap imcKey)) s fun s' => ∃ S', ImcInv s₀ S' s' ∧ ∀ j, j ∈ js ∨ j ∈ S → j ∈ S' := by
  induction js generalizing S s with
  | nil => exact WP.block_nil ⟨S, hI, fun j h => by simpa using h⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (imcKey_ok hs hI (hjs j (by simp)).1 (hjs j (by simp)).2) fun s₁ hI₁ => ?_
    refine WP.mono (ih (fun j' hj' => hjs j' (by simp [hj'])) hI₁) fun s' ⟨S', hI', hS'⟩ =>
      ⟨S', hI', fun j' hj' => hS' j' ?_⟩
    rcases hj' with hj' | hj'
    · rcases List.mem_cons.mp hj' with rfl | hj'
      · exact .inr (by simp)
      · exact .inl hj'
    · exact .inr (by simp [hj'])

/-- The last round key, `nr`, copied to `scratch + 224`. -/
theorem copyLast_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {nr : Nat} (hnr : nr ≤ 14) :
    WP isa (.block (copyLast nr)) s fun s' => ImcInv s₀ S s' ∧
      s'.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128 := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * nr))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn hnr
  have hout : InRegions s.wr (s.ea (at_ .edx 224)) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega)
  have ek : s.ea (at_ .eax (16 * nr)) = addr (s₀.gpr .eax) (16 * nr) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx 224) = addr (s₀.gpr .edx) 224 := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [copyLast, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, hs.frameIn (by omega) (by omega) _ hI.frame,
    hI.le, fun j hj => ?_⟩, ?_⟩
  · have h13 := hI.le j hj
    rw [Mem.readW_writeW_sep (by
        rw [addr_eq (by have := hs.fitB; omega), addr_eq (by have := hs.fitB; omega)]
        exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hI.keys j hj]
  · rw [Mem.readW_writeW_self _ _ 16 _ (by decide), hs.sched hI.frame hnr]

omit hs in
theorem cmpEcx_imc {S : List Nat} {s : State} (hI : ImcInv s₀ S s) (c : BitVec 32) :
    WP isa (.block [.alu .cmp .ecx (.imm c)]) s fun s' =>
      s'.zf = some (s₀.gpr .ecx - c == 0) ∧ ImcInv s₀ S s' :=
  WP.mono (cmpEcx_ok s c) fun _ ⟨hz, hf⟩ => ⟨by rw [hz, hI.gpr], hI.of_frame hf⟩

/-- What `imcKeys` leaves. -/
def ImcDone (s₀ : State) (nr : Nat) (s : State) : Prop :=
  ∃ S, ImcInv s₀ S s ∧ (∀ j, 1 ≤ j → j < nr → j ∈ S) ∧
    s.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128

theorem imcKeys_ok {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hc : s₀.gpr .ecx = BitVec.ofNat 32 nr) : WP isa imcKeys s₀ (ImcDone s₀ nr) := by
  have run := fun js (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S s} (hI : ImcInv s₀ S s) => imcRun_ok hs js hjs hI
  refine WP.seq ?_
  rw [WP.block_append_iff, show ((List.range 9).flatMap fun j => imcKey (j + 1)) =
    ((List.range 9).map (· + 1)).flatMap imcKey by simp [List.flatMap_map]]
  refine WP.mono (run _ (by decide) (ImcInv.refl s₀)) fun s₁ ⟨S₁, hI₁, hS₁⟩ => ?_
  have h9 : ∀ j, 1 ≤ j → j ≤ 9 → j ∈ S₁ := fun j h1 h2 => hS₁ j (.inl (by
    simp only [List.mem_map, List.mem_range]; exact ⟨j - 1, by omega, by omega⟩))
  refine WP.mono (cmpEcx_imc hI₁ 10) fun s₂ ⟨hz₂, hI₂⟩ => ?_
  rw [hc] at hz₂
  rcases hnr with rfl | rfl | rfl
  · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₂ (by decide)) fun s₃ ⟨hI₃, hl₃⟩ =>
      ⟨S₁, hI₃, fun j h1 h2 => h9 j h1 (by omega), hl₃⟩
  all_goals
    refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff, show imcKey 10 ++ imcKey 11 = [10, 11].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₂) fun s₃ ⟨S₃, hI₃, hS₃⟩ => ?_
    have h11 : ∀ j, 1 ≤ j → j ≤ 11 → j ∈ S₃ := fun j h1 h2 => hS₃ j (by
      by_cases h : j ≤ 9
      · exact .inr (h9 j h1 h)
      · exact .inl (by simp; omega))
    refine WP.mono (cmpEcx_imc hI₃ 12) fun s₄ ⟨hz₄, hI₄⟩ => ?_
    rw [hc] at hz₄
  · refine WP.ite true (by simp [eval, hz₄]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₄ (by decide)) fun s₅ ⟨hI₅, hl₅⟩ =>
      ⟨S₃, hI₅, fun j h1 h2 => h11 j h1 (by omega), hl₅⟩
  · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [show imcKey 12 ++ imcKey 13 ++ copyLast 14 = [12, 13].flatMap imcKey ++ copyLast 14 by simp,
      WP.block_append_iff]
    refine WP.mono (run _ (by decide) hI₄) fun s₅ ⟨S₅, hI₅, hS₅⟩ => ?_
    exact WP.mono (copyLast_ok hs hI₅ (by decide)) fun s₆ ⟨hI₆, hl₆⟩ =>
      ⟨S₅, hI₆, fun j h1 h2 => hS₅ j (by
        by_cases h : j ≤ 11
        · exact .inr (h11 j h1 h)
        · exact .inl (by simp; omega)), hl₆⟩

/-- The round keys through `aesimc`, as decryption needs them. -/
theorem dKeys_of_imc {s : State} {nr : Nat} {w : List Byte} (hK : Keys nr w s₀)
    (hd : ImcDone s₀ nr s) : DKeys nr w s := by
  obtain ⟨S, hI, hS, hl⟩ := hd
  have hle := hK.le
  have ek : ∀ j, s.ea (at_ .eax (16 * j)) = s₀.ea (at_ .eax (16 * j)) := fun j => by
    rw [ea_at, ea_at, hI.gpr]
  have hK' : Keys nr w s := ⟨hle, fun j hj => by rw [ek, hI.rd, hI.wr]; exact hK.keys j hj,
    fun j hj => by
      rw [ek, ea_at, hs.sched hI.frame (by omega), ← ea_at]; exact hK.bytes j hj⟩
  refine ⟨hK', fun j h1 h2 => ⟨?_, ?_⟩, ⟨?_, fun i hi => ?_⟩⟩
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega))
  · rw [ea_at, hI.gpr, hI.keys j (hS j h1 h2), st_aesimc]
    refine congrArg invMixColumns ?_
    apply st_ext; intro i hi
    rw [getD_st _ hi, ← ea_at, hK.bytes j (by omega) i hi]
    simp [rkState, Vector.getD, hi]
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega))
  · rw [ea_at, hI.gpr, hl, ← ea_at]; exact hK.bytes nr (Nat.le_refl _) i hi

end

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop`. -/
section

/-!
# AES-NI on x86 (32-bit): the loops over whole blocks

The loops of `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`
are proven once for any transformation `f` of a list of block registers
that computes `F` on each, given what it needs of the state (`KP`, which
the loops keep): `aes` and `aesDec`. After `c` blocks, the first `c` data
blocks hold `F` of the original ones (`Inv`); the six-block and one-block
bodies are the same code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ regs6 loadData storeData blocks6 blocks1 blocksTail)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd)

/-! ## Blocks as states -/

theorem stateAt_eq (m : Mem) (a : Addr) : Spec.Aes.stateAt m a = VG.Proof.Aes.X86.AesNi.st (m.readW a 128) :=
  st_ext fun i hi => by
    rw [getD_st _ hi, VG.Proof.Gcm.X86.byte_readW _ _ hi]
    simp [Spec.Aes.stateAt, Vector.getD, hi]

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (16 * (j + k))) 16) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length),
        VG.Proof.Aes.X86.AesNi.st (s'.xmm regs[k]) = Spec.Aes.stateAt s.mem (addr (s.gpr .esi) (16 * (j + k)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (Q := fun s₁ => s₁ = s.setXmm b (s.mem.readW (addr (s.gpr .esi) (16 * j)) 128)) ?_
      fun s₁ e₁ => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, VG.Proof.Aes.X86.AesNi.ea_at, hin0,
        ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    subst e₁
    refine WP.mono (ih (j + 1) _ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd_setXmm, wr_setXmm, gpr_setXmm, show j + 1 + k = j + (k + 1) by omega]
        exact hin (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [gpr_setXmm, mem_setXmm] at hb
    refine ⟨fun k hk => ?_, g, m, rd, wr, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, xmm_setXmm_self, VG.Proof.Aes.X86.AesNi.stateAt_eq]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, xmm_setXmm_of_ne _ _ hr.1]

theorem addr_sep {p : BitVec 32} {a b n : Nat} (h : a + 16 ≤ b ∨ b + 16 ≤ a) (ha : p.toNat + a + 16 ≤ 2 ^ 32)
    (hb : p.toNat + b + 16 ≤ 2 ^ 32) (_hn : n = 16) : Mem.Sep (addr p a) n (addr p b) n := by
  subst _hn
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem storeData_ok (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length, InRegions s.wr (addr (s.gpr .esi) (16 * (j + k))) 16)
    (hw : (s.gpr .esi).toNat + 16 * (j + regs.length) ≤ 2 ^ 32) :
    WP isa (.block (storeData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), Spec.Aes.stateAt s'.mem (addr (s.gpr .esi) (16 * (j + k))) =
        VG.Proof.Aes.X86.AesNi.st (s.xmm regs[k])) ∧
      Frame [⟨addr (s.gpr .esi) (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    let s₁ : State := { s with mem := s.mem.writeW (addr (s.gpr .esi) (16 * j)) (s.xmm b) }
    refine WP.mono (Q := fun t => t = s₁) ?_ fun t e => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, VG.Proof.Aes.X86.AesNi.ea_at, hin0,
        ↓reduceIte, Option.some.injEq, exists_eq_left']
      rfl
    subst e
    have ha0 : addr (s.gpr .esi) (16 * j) = (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j) :=
      addr_eq (by omega)
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by show (s.gpr .esi).toNat + _ ≤ _; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    let R₀ : Region := ⟨(s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩
    -- The blocks after the first: apart from it, and within the whole run.
    have hrest : ∀ r ∈ [(⟨addr (s₁.gpr .esi) (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨(s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ r ∧ Region.Sub r R₀ := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      by_cases hl : bs.length = 0
      · rw [hl]
        exact ⟨fun a _ h => by simp [Region.Contains] at h, fun a h => by simp [Region.Contains] at h⟩
      · rw [show s₁.gpr .esi = s.gpr .esi from rfl, addr_eq (by omega)]
        exact ⟨Offset.disjoint _ (.inl (by omega)) (by omega) (by omega), Offset.sub _ (by omega) (by omega)⟩
    refine ⟨fun k hk => ?_, ?_, g, rd, wr, hx⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [VG.Proof.Aes.X86.AesNi.stateAt_eq, ha0, hf.readW (Region.contains_self _ _) (fun r hr => (hrest r hr).1) (by decide),
          ← ha0]
        exact congrArg VG.Proof.Aes.X86.AesNi.st (Mem.readW_writeW_self _ _ 16 _ (by decide))
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega]
        exact hb k (by simpa using hk)
    · rw [ha0]
      have hm : R₀ ∈ [R₀] := List.mem_singleton_self _
      refine (Frame.writeW (Frame.refl _ s.mem) hm (s.xmm b) ?_).trans
        (hf.sub fun r hr => ⟨_, hm, (hrest r hr).2⟩)
      rw [ha0]; exact Offset.contains _ (Nat.le_refl _) (by omega) (by omega)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Blocks`. -/
section

/-!
# AES-NI on x86 (32-bit): encryption and decryption of whole blocks

The loops are proven once for any transformation `f` of a list of block
registers that computes `F` on each, given what it needs of the state
(`KP`, which the loops keep): `aes` and `aesDec`. After `c` blocks, the
first `c` data blocks hold `F` of the original ones (`Inv`); the six-block
and one-block bodies are the same code for different lists of registers
(`blocks_ok`). `encrypt_correct` and `decrypt_correct` add the prologue,
which saves `esi` and `edi` in the scratch buffer and loads the arguments,
the round keys through `aesimc` for decryption, and the epilogue.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ aes aesDec regs6 loadData storeData blocks6 blocks1 blocksTail
  blocksPrologue blocksCmp blocksRestore imcKeys)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg reg_contains in_reg)
open VG.X86.Wp (Upd Fupd wp_addi wp_subi wp_cmpi wp_test wp_ldm wp_stm toNat_ofNat_lt ofNat_beq_zero)

namespace Ecb

section
variable (s₀ : State)

/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := (bDatP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev orig (k : Nat) : Spec.Aes.State := Spec.Aes.stateAt s₀.mem (VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k)
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1))

end

/-- What a transformation of the block registers needs of the state is kept
by writing data blocks and moving `esi` and `edi`. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → (∀ r, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
    Frame [bDatR s₀] s.mem s'.mem → KP s'

/-- `f` computes `F` on each block register, for both lists of registers. -/
def BlkOk (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ rs, (rs = regs6 ∨ rs = [.xmm0]) → ∀ s, KP s →
    WP isa (f rs) s fun s' => (∀ b ∈ rs, VG.Proof.Aes.X86.AesNi.st (s'.xmm b) = F (VG.Proof.Aes.X86.AesNi.st (s.xmm b))) ∧ VG.Proof.Aes.X86.AesNi.XFrame (.xmm6 :: rs) s s'

/-- After `c` blocks, with `esi` and `edi` at block `p`; the other registers
are `g`, and only the data has changed since `m₁`. -/
structure Inv (KP : State → Prop) (F : Spec.Aes.State → Spec.Aes.State) (s₀ : State) (g : Reg → BitVec 32)
    (m₁ : Mem) (c p : Nat) (s : State) : Prop where
  le : c ≤ bN s₀
  kp : KP s
  gpr : ∀ r, r ≠ .esi → r ≠ .edi → s.gpr r = g r
  esi : s.gpr .esi = bDatP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (bN s₀ - p)
  frame : Frame [bDatR s₀] m₁ s.mem
  blocks : ∀ k < bN s₀,
    Spec.Aes.stateAt s.mem (VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k) = if k < c then F (VG.Proof.Aes.X86.AesNi.Ecb.orig s₀ k) else VG.Proof.Aes.X86.AesNi.Ecb.orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) : rs.Nodup ∧ .xmm6 ∉ rs := by
  rcases h with rfl | rfl <;> decide

theorem regs_len (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) : 0 < rs.length ∧ rs.length ≤ 6 := by
  rcases h with rfl | rfl <;> decide

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} {g : Reg → BitVec 32} {m₁ : Mem} (hp : BPre s₀) (hst : VG.Proof.Aes.X86.AesNi.Ecb.Stable KP s₀) (hf : VG.Proof.Aes.X86.AesNi.Ecb.BlkOk f F KP)
include hp hst hf

/-- The loads, `f` and the stores, for the blocks `c … c + N - 1` (`N` the
number of registers). -/
theorem blocks_ok (rs : List XReg) (hrs : rs = regs6 ∨ rs = [.xmm0]) (tail : List Instr)
    {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ bN s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s)
    (hQ : ∀ s', VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (loadData rs 0)) (.seq (f rs) (.block (storeData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h6⟩ := VG.Proof.Aes.X86.AesNi.Ecb.regs_nodup rs hrs
  have hw := hp.fD
  have hlen := (VG.Proof.Aes.X86.AesNi.Ecb.regs_len rs hrs).1
  have haddr : ∀ k, c + k < bN s₀ →
      addr (s.gpr .esi) (16 * (0 + k)) = VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ (c + k) := fun k hk => by
    rw [hI.esi, addr_add, addr_eq (by omega), show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have hout : ∀ k, c + k < bN s₀ → InRegions s.wr (VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨bDatR s₀, by rw [hI.wr, hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.loadData_ok rs 0 s hnd fun k hk => by
      rw [haddr k (by omega)]; exact in_rd (hout k (by omega))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), VG.Proof.Aes.X86.AesNi.st (s₂.xmm rs[k]) = F (VG.Proof.Aes.X86.AesNi.Ecb.orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, haddr k (by omega), hI.blocks _ (by omega)]
    simp only [show ¬ c + k < c by omega, ite_false]
  have hesi₂ : s₂.gpr .esi = s.gpr .esi := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.storeData_ok rs 0 s₂ (fun k hk => by
      rw [hesi₂, haddr k (by omega), f₂.wr, wr₁]; exact hout k (by omega))
      (by rw [hesi₂, hI.esi, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hesi₂, show 16 * 0 = 16 * (0 + 0) by rfl, haddr 0 (by omega), Nat.add_zero] at fr₃
  rw [hesi₂] at b₃
  have fr₃' : Frame [bDatR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨bDatR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by omega)⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  refine ⟨Nat.le_trans (by omega) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
    (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 => by rw [g₃', hI.gpr r h1 h2],
    by rw [g₃', hI.esi], by rw [g₃', hI.edi], hI.frame.trans fr₃', ?_,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
  intro k hk
  have out : ¬ (c ≤ k ∧ k < c + rs.length) →
      Spec.Aes.stateAt s₃.mem (VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k) = Spec.Aes.stateAt s.mem (VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k) :=
    fun hn => by
      rw [VG.Proof.Aes.X86.AesNi.stateAt_eq, VG.Proof.Aes.X86.AesNi.stateAt_eq]
      exact congrArg VG.Proof.Aes.X86.AesNi.st <| fr₃.readW (r := ⟨VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega, ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
      have hj : j < rs.length := by omega
      rw [← haddr j (by omega), b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, hhi, ite_false]

omit hf in
/-- `add esi, 16 m; sub edi, m`, after `m` more blocks. -/
theorem advance_ok {rest : List Instr} {c m : Nat} (hc : c + m ≤ bN s₀) {s : State}
    (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (c + m) c s) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (c + m) (c + m) s' →
      s'.zf = some (decide (bN s₀ - (c + m) = 0)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 m)) :: rest)) s Q := by
  have hw := hp.fD
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ hz => hQ s₂ ?_ ?_
  · have g₂ : ∀ r, r ≠ .esi → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h1 h2 => by
      rw [u₂.other r h2, u₁.other r h1]
    refine ⟨hI.le, hst s s₂ hI.kp g₂ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _), fun r h1 h2 => by rw [g₂ r h1 h2, hI.gpr r h1 h2],
      ?_, ?_, by rw [u₂.mem, u₁.mem]; exact hI.frame, by rw [u₂.mem, u₁.mem]; exact hI.blocks,
      by rw [u₂.rd, u₁.rd, hI.rd], by rw [u₂.wr, u₁.wr, hI.wr]⟩
    · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · rw [u₂.gpr, u₁.other _ (by decide), hI.edi]
      have : bN s₀ < 2 ^ 32 := by omega
      bv_omega
  · have hn : bN s₀ < 2 ^ 32 := by omega
    have e : BitVec.ofNat 32 (bN s₀ - c) - BitVec.ofNat 32 m = BitVec.ofNat 32 (bN s₀ - (c + m)) := by
      bv_omega
    rw [hz, u₁.other _ (by decide), hI.edi, e, ofNat_beq_zero (by omega)]

/-- The six-block body. -/
theorem body6_ok {c : Nat} (hc : c + 6 ≤ bN s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s) :
    WP isa (blocks6 f) s fun s' => VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (c + 6) (c + 6) s' ∧
      s'.cf = some (decide (bN s₀ - (c + 6) < 6)) := by
  have hw := hp.fD
  refine VG.Proof.Aes.X86.AesNi.Ecb.blocks_ok hp hst hf regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  refine VG.Proof.Aes.X86.AesNi.Ecb.advance_ok hp hst (m := 6) hc hI₁ fun s₂ hI₂ _ => ?_
  refine wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ⟨?_, ?_⟩
  · exact { hI₂ with
      kp := hst _ _ hI₂.kp (fun r _ _ => by rw [u₃.gpr]) u₃.rd u₃.wr (by rw [u₃.mem]; exact Frame.refl _ _)
      gpr := fun r h1 h2 => by rw [u₃.gpr, hI₂.gpr r h1 h2]
      esi := by rw [u₃.gpr, hI₂.esi]
      edi := by rw [u₃.gpr, hI₂.edi]
      frame := by rw [u₃.mem]; exact hI₂.frame
      blocks := by rw [u₃.mem]; exact hI₂.blocks
      rd := by rw [u₃.rd, hI₂.rd]
      wr := by rw [u₃.wr, hI₂.wr] }
  · rw [hcf, hI₂.edi, toNat_ofNat_lt (by omega)]; rfl

/-- The one-block body. -/
theorem body1_ok {c : Nat} (hc : c < bN s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s) :
    WP isa (blocks1 f) s fun s' => VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (bN s₀ - (c + 1) = 0)) := by
  refine VG.Proof.Aes.X86.AesNi.Ecb.blocks_ok hp hst hf [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  exact VG.Proof.Aes.X86.AesNi.Ecb.advance_ok hp hst (m := 1) (rest := []) hc hI₁ fun s₂ hI₂ hz =>
    WP.block_nil ⟨hI₂, hz⟩

omit hf in
theorem test_ok {c : Nat} {s : State} (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s' ∧ s'.zf = some (decide (bN s₀ - c = 0)) := by
  have hw := hp.fD
  refine wp_test fun s' u hz => WP.block_nil ⟨?_, ?_⟩
  · exact { hI with
      kp := hst _ _ hI.kp (fun r _ _ => by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)
      gpr := fun r h1 h2 => by rw [u.gpr, hI.gpr r h1 h2]
      esi := by rw [u.gpr, hI.esi]
      edi := by rw [u.gpr, hI.edi]
      frame := by rw [u.mem]; exact hI.frame
      blocks := by rw [u.mem]; exact hI.blocks
      rd := by rw [u.rd, hI.rd]
      wr := by rw [u.wr, hI.wr] }
  · rw [hz, hI.edi, BitVec.and_self, ofNat_beq_zero (by omega)]

/-- The blocks left after `c₀`, six and then one at a time. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (bN s₀ - c₀ < 6))) :
    WP isa (blocksTail f) s₁ (VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (bN s₀) (bN s₀)) := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bN s₀ - c < 6 ∧ VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (bN s₀ - c₀ < 6)) (by simp [VG.X86.eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c + 6 ≤ bN s₀ ∧ VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s
      have hstep : ∀ m s, I6 m s → WP isa (blocks6 f) s (fun s' =>
          (VG.X86.eval .ae s' = some false ∧ ∃ c, bN s₀ - c < 6 ∧ VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s') ∨
          (VG.X86.eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.body6_ok hp hst hf hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : bN s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [VG.X86.eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [VG.X86.eval, hcf', hlt], bN s₀ - (c + 6), by omega, c + 6, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I6 hstep (bN s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.test_ok hp hst hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (bN s₀ - c = 0)) (by simp [VG.X86.eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = bN s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = bN s₀ - c ∧ c < bN s₀ ∧ VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blocks1 f) s (fun s' =>
        (VG.X86.eval .ne s' = some false ∧ VG.Proof.Aes.X86.AesNi.Ecb.Inv KP F s₀ g m₁ (bN s₀) (bN s₀) s') ∨
        (VG.X86.eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.body1_ok hp hst hf hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : bN s₀ - (c + 1) = 0
      · have : c + 1 = bN s₀ := by omega
        exact .inl ⟨by simp [VG.X86.eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [VG.X86.eval, hzf', hlast], bN s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < bN s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (bN s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

end Loops

end Ecb

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain`. -/
section

/-!
# AES-NI on x86 (32-bit): `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86.AesNi.encryptBlocks` and `decryptBlocks` against the contracts
of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through the
per-target contract of the bitsliced implementation (`Proof.Aes.blocksX86`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp aes aesDec blocksPrologue blocksCmp blocksRestore blocksTail imcKeys
  encryptBlocks decryptBlocks)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg part_sub reg_contains in_reg rd_wr_ne blocksτ₀ blocks_agree₀)
open VG.X86.Wp (wp_ldm wp_stm wp_cmpi toNat_ofNat_lt)
open VG.Proof.Aes.X86.AesNi.Ecb

namespace Ecb

theorem arg_eq' (s : State) (i : Nat) : VG.X86.arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  eax : s.gpr .eax = bSchP s₀
  ecx : s.gpr .ecx = VG.X86.arg s₀ 1
  edx : s.gpr .edx = bScrP s₀
  esi : s.gpr .esi = bDatP s₀
  edi : s.gpr .edi = VG.X86.arg s₀ 3
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (bScrP s₀) 0, 8⟩] s₀.mem s.mem
  savedEsi : s.mem.readW (addr (bScrP s₀) 0) 32 = s₀.gpr .esi
  savedEdi : s.mem.readW (addr (bScrP s₀) 4) 32 = s₀.gpr .edi

theorem prologue_ok {s₀ : State} (hp : BPre s₀) : WP isa (.block blocksPrologue) s₀ (VG.Proof.Aes.X86.AesNi.Ecb.P1 s₀) := by
  have fB := hp.fB; have fSp := hp.fSp
  let B := bScrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have hm : (⟨addr B 0, 8⟩ : Region) ∈ [⟨addr B 0, 8⟩] := List.mem_singleton_self _
  have dA : ∀ r ∈ [(⟨addr B 0, 8⟩ : Region)], (bArgR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.aB.sub_right (part_sub_reg fB (by omega))
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edx = B := by rw [u₁.gpr]; rfl
  refine wp_stm (B := B) (o := 0) e₁ (by rw [u₁.wr]; exact in_reg hwB fB (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (B := B) (o := 4) ((congrFun u₂.gpr _).trans e₁)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwB fB (by omega) (by decide))
    fun s₃ u₃ => ?_
  have esp₃ : s₃.gpr .esp = E := by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have f₃ : Frame [⟨addr B 0, 8⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW hm _ (part_contains fB (by omega) (by omega) (by omega) (by decide))).writeW
      hm _ (part_contains fB (by omega) (by omega) (by omega) (by decide))
  have a₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = VG.X86.arg s₀ i := fun i hi =>
    f₃.readW (argC i hi) dA (by decide)
  refine wp_ldm (B := E) (o := 4) esp₃ (argIn _ rd₃ 0 (by omega)) fun s₄ u₄ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₄.rd, u₄.wr]; exact argIn _ rd₃ 1 (by omega)) fun s₅ u₅ => ?_
  refine wp_ldm (B := E) (o := 12) (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 2 (by omega)) fun s₆ u₆ => ?_
  refine wp_ldm (B := E) (o := 16)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 3 (by omega)) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have esi₀ : s₂.mem.readW (addr B 0) 32 = s₀.gpr .esi := by
    rw [u₂.mem, u₁.other _ (by decide), Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃], by rw [m₇]; exact f₃, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact a₃ 0 (by omega)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem]
    exact a₃ 1 (by omega)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]
    exact a₃ 2 (by omega)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem]
    exact a₃ 3 (by omega)
  · rw [u₇.other r h5, u₆.other r h4, u₅.other r h2, u₄.other r h1, u₃.gpr, u₂.gpr, u₁.other r h3]
  · rw [m₇, u₃.mem, rd_wr_ne fB _ _ (N := 2048) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact esi₀
  · rw [m₇, u₃.mem, u₂.gpr, u₁.other _ (by decide), Mem.readW_writeW_self32]

/-! ## What the transformations need -/

theorem sch_frame {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1)) = VG.Proof.Aes.X86.AesNi.Ecb.sch s₀ := by
  have hn : 16 * (bRounds s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [VG.Proof.Aes.X86.AesNi.Ecb.sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(bSchP s₀).setWidth 64, 16 * (bRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (bRounds s₀ + 1) ≤ 2 ^ 64; omega) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys_of {s₀ s : State} (hp : BPre s₀) (heax : s.gpr .eax = bSchP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem s.mem) :
    VG.Proof.Aes.X86.AesNi.Keys (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀) s := by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have he : ∀ j ≤ bRounds s₀, s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax (16 * j)) =
      (bSchP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [VG.Proof.Aes.X86.AesNi.ea_at, heax]
    exact addr_eq (by have h := hp.fS; omega)
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    exact ⟨bSchR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  · rw [he j hj, ← VG.Proof.Aes.X86.AesNi.Ecb.sch_frame hp hf]
    have h := byte_roundKey s.mem ((bSchP s₀).setWidth 64) (L := 16 * (bRounds s₀ + 1)) (j := j) (by omega)
    rw [ofInt_natCast] at h
    exact h

/-- What encryption needs, from `s₀`. -/
def KPe (s₀ : State) (s : State) : Prop :=
  VG.Proof.Aes.X86.AesNi.Keys (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀

/-- What decryption needs, from `s₀`. -/
def KPd (s₀ : State) (s : State) : Prop :=
  VG.Proof.Aes.X86.AesNi.DKeys (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀ ∧
    s.gpr .edx = bScrP s₀

theorem keys_stable {nr : Nat} {w : List Byte} {s₀ s s' : State} (hp : BPre s₀) (hK : VG.Proof.Aes.X86.AesNi.Keys nr w s)
    (hle : 16 * nr + 16 ≤ 240) (heax : s.gpr .eax = bSchP s₀)
    (hg : s'.gpr .eax = s.gpr .eax) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [bDatR s₀] s.mem s'.mem) : VG.Proof.Aes.X86.AesNi.Keys nr w s' := by
  have he : ∀ j ≤ nr, s'.ea (VG.Impl.Aes.X86.AesNi.at_ .eax (16 * j)) = s.ea (VG.Impl.Aes.X86.AesNi.at_ .eax (16 * j)) := fun j _ => by
    rw [VG.Proof.Aes.X86.AesNi.ea_at, VG.Proof.Aes.X86.AesNi.ea_at, hg]
  refine ⟨hK.le, fun j hj => by rw [he j hj, hrd, hwr]; exact hK.keys j hj, fun j hj i hi => ?_⟩
  rw [he j hj, ← hK.bytes j hj i hi, VG.Proof.Aes.X86.AesNi.ea_at, heax]
  congr 1
  exact hf.readW (r := ⟨addr (bSchP s₀) (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.dSD.sub_left (part_sub_reg hp.fS (by omega))).symm.symm) (by decide)

theorem kpe_stable {s₀ : State} (hp : BPre s₀) : VG.Proof.Aes.X86.AesNi.Ecb.Stable (VG.Proof.Aes.X86.AesNi.Ecb.KPe s₀) s₀ := fun s s' ⟨hK, hc, ha⟩ hg hrd hwr hf => by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  exact ⟨VG.Proof.Aes.X86.AesNi.Ecb.keys_stable hp hK (by omega) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha]⟩

theorem kpd_stable {s₀ : State} (hp : BPre s₀) : VG.Proof.Aes.X86.AesNi.Ecb.Stable (VG.Proof.Aes.X86.AesNi.Ecb.KPd s₀) s₀ :=
  fun s s' ⟨hK, hc, ha, hd⟩ hg hrd hwr hf => by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have fB := hp.fB
  have hedx : s'.gpr .edx = s.gpr .edx := hg _ (by decide) (by decide)
  have he : ∀ o, s'.ea (VG.Impl.Aes.X86.AesNi.at_ .edx o) = s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx o) := fun o => by rw [VG.Proof.Aes.X86.AesNi.ea_at, VG.Proof.Aes.X86.AesNi.ea_at, hedx]
  have hm : ∀ o, 16 ≤ o → o + 16 ≤ 240 →
      s'.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx o)) 128 = s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .edx o)) 128 := fun o h1 h2 => by
    rw [VG.Proof.Aes.X86.AesNi.ea_at, hd]
    exact hf.readW (r := ⟨addr (bScrP s₀) o, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)
  refine ⟨⟨VG.Proof.Aes.X86.AesNi.Ecb.keys_stable hp hK.keys (by omega) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    fun j h1 h2 => ?_, ?_⟩, by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha],
    by rw [hedx, hd]⟩
  · obtain ⟨hin, hst⟩ := hK.imc j h1 h2
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega) (by omega)]; exact hst⟩
  · obtain ⟨hin, hb⟩ := hK.last
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega) (by omega)]; exact hb⟩

theorem aes_blkOk {s₀ : State} (hp : BPre s₀) :
    VG.Proof.Aes.X86.AesNi.Ecb.BlkOk VG.Impl.Aes.X86.AesNi.aes (Spec.Aes.cipher (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀)) (VG.Proof.Aes.X86.AesNi.Ecb.KPe s₀) :=
  fun rs hrs s ⟨hK, hc, _⟩ => by
    obtain ⟨hnd, h6⟩ := VG.Proof.Aes.X86.AesNi.Ecb.regs_nodup rs hrs
    exact VG.Proof.Aes.X86.AesNi.aes_ok rs hnd h6 hp.rounds s hK hc

theorem aesDec_blkOk {s₀ : State} (hp : BPre s₀) :
    VG.Proof.Aes.X86.AesNi.Ecb.BlkOk aesDec (Spec.Aes.invCipher (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀)) (VG.Proof.Aes.X86.AesNi.Ecb.KPd s₀) :=
  fun rs hrs s ⟨hK, hc, _, _⟩ => by
    obtain ⟨hnd, h6⟩ := VG.Proof.Aes.X86.AesNi.Ecb.regs_nodup rs hrs
    exact VG.Proof.Aes.X86.AesNi.aesDec_ok rs hnd h6 hp.rounds s hK hc

/-! ## The epilogue -/

/-- From the state after the loops, the restore and the postcondition. -/
theorem finish_ok {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s₀ s₁ s : State} (hp : BPre s₀) (h₁ : VG.Proof.Aes.X86.AesNi.Ecb.P1 s₀ s₁) {m₁ : Mem}
    (hm₁ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem m₁)
    (hI : VG.Proof.Aes.X86.AesNi.Ecb.Inv KP (F (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀)) s₀ s₁.gpr m₁ (bN s₀) (bN s₀) s) :
    WP isa (.block blocksRestore) s fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 F).post s₀ s' := by
  have fB := hp.fB
  have hscr : reg32 (bScrP s₀) 2048 ∈ s.rd ++ s.wr := by
    rw [hI.rd, hI.wr, hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hedx : s.gpr .edx = bScrP s₀ := by rw [hI.gpr _ (by decide) (by decide), h₁.edx]
  -- The scratch buffer's first eight bytes are as the prologue left them.
  have hsv : ∀ o, o + 4 ≤ 8 → s.mem.readW (addr (bScrP s₀) o) 32 = s₁.mem.readW (addr (bScrP s₀) o) 32 :=
    fun o ho => by
      rw [hI.frame.readW (r := ⟨addr (bScrP s₀) o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)]
      exact hm₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
  refine wp_ldm (B := bScrP s₀) (o := 0) hedx (in_reg hscr fB (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (B := bScrP s₀) (o := 4) (by rw [u₂.other _ (by decide)]; exact hedx)
    (by rw [u₂.rd, u₂.wr]; exact in_reg hscr fB (by omega) (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  -- Everything written since the entry: the scratch buffer and the data.
  have G : Frame [bDatR s₀, bScrR s₀] s₀.mem s₃.mem := by
    rw [hm₃]
    refine (h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
      ((hm₁.sub fun r hr => ⟨bScrR s₀, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
      (hI.frame.mono fun r hr => by simp at hr; simp [hr]))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.gpr, hsv 0 (by omega), h₁.savedEsi]
    · rw [u₃.gpr, u₂.mem, hsv 4 (by omega), h₁.savedEdi]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine G.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.rD
    · exact hp.rB
  · show Spec.Aes.statesAt s₃.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
    rw [hm₃]
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

/-! ## The two functions -/

theorem encrypt_correct {s₀ : State} (hp : BPre s₀) :
    WP isa VG.Impl.Aes.X86.AesNi.encryptBlocks s₀ fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 Spec.Aes.cipher).post s₀ s' := by
  have fD := hp.fD
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.prologue_ok hp) fun s₁ h₁ => ?_
  refine wp_cmpi fun s₂ u₂ hcf _ => WP.block_nil ?_
  have hf₁ : Frame [bDatR s₀, bScrR s₀] s₀.mem s₁.mem := h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg hp.fB (by omega)⟩
  have hI₂ : VG.Proof.Aes.X86.AesNi.Ecb.Inv (VG.Proof.Aes.X86.AesNi.Ecb.KPe s₀) (Spec.Aes.cipher (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀)) s₀ s₁.gpr s₁.mem 0 0 s₂ :=
    { le := Nat.zero_le _
      kp := ⟨VG.Proof.Aes.X86.AesNi.Ecb.keys_of hp (by rw [u₂.gpr]; exact h₁.eax) (by rw [u₂.rd, h₁.rd]) (by rw [u₂.wr, h₁.wr])
          (by rw [u₂.mem]; exact hf₁), by rw [u₂.gpr, h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [u₂.gpr]; exact h₁.eax⟩
      gpr := fun r _ _ => by rw [u₂.gpr]
      esi := by rw [u₂.gpr, h₁.esi]; simp
      edi := by rw [u₂.gpr, h₁.edi]; simp [bN]
      frame := by rw [u₂.mem]; exact Frame.refl _ _
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, VG.Proof.Aes.X86.AesNi.Ecb.orig]
        rw [u₂.mem, VG.Proof.Aes.X86.AesNi.stateAt_eq, VG.Proof.Aes.X86.AesNi.stateAt_eq]
        exact congrArg VG.Proof.Aes.X86.AesNi.st <| h₁.frame.readW (r := ⟨VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k, 16⟩) (w := 128)
          (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hp.dDB.sub_left (Offset.sub_base _ (by omega))).sub_right
              (part_sub_reg hp.fB (by omega))) (by decide)
      rd := by rw [u₂.rd, h₁.rd]
      wr := by rw [u₂.wr, h₁.wr] }
  have hcf' : s₂.cf = some (decide (bN s₀ - 0 < 6)) := by
    rw [hcf, h₁.edi, Nat.sub_zero]; rfl
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.tail_ok hp (VG.Proof.Aes.X86.AesNi.Ecb.kpe_stable hp) (VG.Proof.Aes.X86.AesNi.Ecb.aes_blkOk hp) hI₂ hcf') fun s hI => ?_)
  exact VG.Proof.Aes.X86.AesNi.Ecb.finish_ok (KP := VG.Proof.Aes.X86.AesNi.Ecb.KPe s₀) hp h₁ (Frame.refl _ _) hI

theorem dkeys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : VG.Proof.Aes.X86.AesNi.DKeys nr w s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.Aes.X86.AesNi.DKeys nr w s' := by
  have he : ∀ m, s'.ea m = s.ea m := fun m => by simp only [State.ea, hg]
  exact ⟨⟨h.keys.le, fun j hj => by rw [he, hrd, hwr]; exact h.keys.keys j hj,
      fun j hj => by rw [he, hm]; exact h.keys.bytes j hj⟩,
    fun j h1 h2 => by rw [he, hrd, hwr, hm]; exact h.imc j h1 h2,
    by rw [he, hrd, hwr, hm]; exact h.last⟩

theorem decrypt_correct {s₀ : State} (hp : BPre s₀) :
    WP isa VG.Impl.Aes.X86.AesNi.decryptBlocks s₀ fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s₀ s' := by
  have fD := hp.fD; have fB := hp.fB
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.prologue_ok hp) fun s₁ h₁ => ?_)
  have hf₁ : Frame [bDatR s₀, bScrR s₀] s₀.mem s₁.mem := h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩
  have hs : VG.Proof.Aes.X86.AesNi.ImcSetup s₁ :=
    { sch := by rw [h₁.eax, h₁.rd, hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..)
      scr := by rw [h₁.edx, h₁.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      fitS := by rw [h₁.eax]; exact hp.fS
      fitB := by rw [h₁.edx]; exact fB
      sep := by rw [h₁.eax, h₁.edx]; exact hp.dSB }
  have hK₁ : VG.Proof.Aes.X86.AesNi.Keys (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀) s₁ := VG.Proof.Aes.X86.AesNi.Ecb.keys_of hp h₁.eax h₁.rd h₁.wr hf₁
  have hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) := by
    rw [h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.imcKeys_ok hs hp.rounds hc₁) fun s₂ hd₂ => ?_)
  have hK₂ := VG.Proof.Aes.X86.AesNi.dKeys_of_imc hs hK₁ hd₂
  obtain ⟨S, hI₂, -, -⟩ := hd₂
  have hm₂ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem s₂.mem := by rw [← h₁.edx]; exact hI₂.frame
  refine WP.seq (wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ?_)
  have hI₃ : VG.Proof.Aes.X86.AesNi.Ecb.Inv (VG.Proof.Aes.X86.AesNi.Ecb.KPd s₀) (Spec.Aes.invCipher (bRounds s₀) (VG.Proof.Aes.X86.AesNi.Ecb.sch s₀)) s₀ s₁.gpr s₂.mem 0 0 s₃ :=
    { le := Nat.zero_le _
      kp := ⟨VG.Proof.Aes.X86.AesNi.Ecb.dkeys_congr hK₂ u₃.gpr u₃.mem u₃.rd u₃.wr,
        by rw [u₃.gpr, hI₂.gpr, hc₁], by rw [u₃.gpr, hI₂.gpr, h₁.eax], by rw [u₃.gpr, hI₂.gpr, h₁.edx]⟩
      gpr := fun r _ _ => by rw [u₃.gpr, hI₂.gpr]
      esi := by rw [u₃.gpr, hI₂.gpr, h₁.esi]; simp
      edi := by rw [u₃.gpr, hI₂.gpr, h₁.edi]; simp [bN]
      frame := by rw [u₃.mem]; exact Frame.refl _ _
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, VG.Proof.Aes.X86.AesNi.Ecb.orig]
        rw [u₃.mem, VG.Proof.Aes.X86.AesNi.stateAt_eq, VG.Proof.Aes.X86.AesNi.stateAt_eq]
        have G : Frame [bScrR s₀] s₀.mem s₂.mem :=
          (h₁.frame.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
          (hm₂.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩)
        exact congrArg VG.Proof.Aes.X86.AesNi.st <| G.readW (r := ⟨VG.Proof.Aes.X86.AesNi.Ecb.bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.dDB.sub_left (Offset.sub_base _ (by omega))) (by decide)
      rd := by rw [u₃.rd, hI₂.rd, h₁.rd]
      wr := by rw [u₃.wr, hI₂.wr, h₁.wr] }
  have hcf' : s₃.cf = some (decide (bN s₀ - 0 < 6)) := by
    rw [hcf, hI₂.gpr, h₁.edi, Nat.sub_zero]; rfl
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.Ecb.tail_ok hp (VG.Proof.Aes.X86.AesNi.Ecb.kpd_stable hp) (VG.Proof.Aes.X86.AesNi.Ecb.aesDec_blkOk hp) hI₃ hcf') fun s hI => ?_)
  exact VG.Proof.Aes.X86.AesNi.Ecb.finish_ok (KP := VG.Proof.Aes.X86.AesNi.Ecb.KPd s₀) hp h₁ hm₂ hI

end Ecb

end VG.Proof.Aes.X86.AesNi

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86
open VG.Proof.Aes.X86 (BPre blocksτ₀ blocks_agree₀ blocksSat)

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  (Ecb.encrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  (Ecb.decrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.AesNi.encryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.AesNi.decryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.encryptBlocks (Spec.Aes.encryptBlocksContract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.AesNi.encryptBlocks_correct VG.Proof.Aes.X86.AesNi.encryptBlocks_ct
    (by
      have a0 : VG.X86.arg blocksSat 0 = 0x1000 := by decide
      have a1 : VG.X86.arg blocksSat 1 = 10 := by decide
      have a2 : VG.X86.arg blocksSat 2 = 0x3000 := by decide
      have a3 : VG.X86.arg blocksSat 3 = 0 := by decide
      have a4 : VG.X86.arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.decryptBlocks (Spec.Aes.decryptBlocksContract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.AesNi.decryptBlocks_correct VG.Proof.Aes.X86.AesNi.decryptBlocks_ct
    (by
      have a0 : VG.X86.arg blocksSat 0 = 0x1000 := by decide
      have a1 : VG.X86.arg blocksSat 1 = 10 := by decide
      have a2 : VG.X86.arg blocksSat 2 = 0x3000 := by decide
      have a3 : VG.X86.arg blocksSat 3 = 0 := by decide
      have a4 : VG.X86.arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Load`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp ctrLoad)

/-- Reload the cached prefix, make any distinct lanes, and restore the public
schedule pointer from immutable arguments. -/
theorem ctrLoad_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (h7 : .xmm7 ∉ regs)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.at_ .ebp 16)) 16)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.AesNi.argOp 0)) 4) :
    WP isa (.block (ctrLoad regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] = counterLane
        (s.gpr .ebx + BitVec.ofNat 32 k) (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .ebp 16)) 128)) ∧
      s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 regs.length ∧
      s'.gpr .eax = s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.argOp 0)) 32 ∧
      CounterFrame (.xmm7 :: regs) s s' := by
  rw [ctrLoad, WP.block_append_iff, WP.block_append_iff]
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm7 (s.mem.readW (s.ea (VG.Impl.Aes.X86.AesNi.at_ .ebp 16)) 128), by
    simp only [isa, exec, State.load128, hp, ite_true, Option.map_some], ?_⟩
  rw [WP.block_nil_iff]
  refine WP.mono (counters_ok regs _ hnd h7) fun s₁ ⟨hv, hc, hf⟩ => ?_
  have ea : s₁.ea (VG.Impl.Aes.X86.AesNi.argOp 0) = s.ea (VG.Impl.Aes.X86.AesNi.argOp 0) := by
    rw [ea_mk, ea_mk]
    change addr (s₁.gpr .esp) 4 = addr (s.gpr .esp) 4
    rw [hf.gpr .esp (by decide) (by decide), gpr_setXmm]
  have ha₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.ea (VG.Impl.Aes.X86.AesNi.argOp 0)) 4 := by
    rw [ea, hf.rd, hf.wr, rd_setXmm, wr_setXmm]
    exact ha
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg .eax (s₁.mem.readW (s₁.ea (VG.Impl.Aes.X86.AesNi.argOp 0)) 32), by
    simp only [isa, exec, VG.X86.readSrc, State.load32, ha₁, ite_true, Option.map_some], ?_⟩
  apply WP.block_nil
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [xmm_setReg, hv k hk, gpr_setXmm, xmm_setXmm_self]
  · rw [gpr_setReg_of_ne _ _ (by decide), hc, gpr_setXmm]
  · rw [gpr_setReg_self, ea, hf.mem, mem_setXmm]
  · refine ⟨fun r h1 h2 => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [gpr_setReg_of_ne _ _ h1, hf.gpr r h1 h2, gpr_setXmm]
    · rw [mem_setReg, hf.mem, mem_setXmm]
    · rw [rd_setReg, hf.rd, rd_setXmm]
    · rw [wr_setReg, hf.wr, wr_setXmm]
    · simp only [List.mem_cons, not_or] at hr
      rw [xmm_setReg, hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Context`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP schR ctrR datR scrR argR)
open VG.Spec.Gcm (Block blockAt aesWith)

section
variable (s₀ : State)
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1))
abbrev cb : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)
abbrev ciph : VG.Spec.Gcm.Block → VG.Spec.Gcm.Block := VG.Spec.Gcm.aesWith (nRounds s₀) (VG.Proof.Aes.X86.AesNi.sch s₀)
abbrev bAddr (k : Nat) : Addr := (datP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Aes.X86.AesNi.bAddr s₀ k)
abbrev pfx : BitVec 96 := (s₀.mem.readW ((ctrP s₀).setWidth 64) 128).extractLsb' 0 96
end

namespace CPre
variable {s₀ : State} (hp : CPre s₀)
include hp

omit hp in
theorem key_contains {j : Nat} (hj : j ≤ 14) :
    (schR s₀).Contains ((schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

theorem block_contains {k : Nat} (hk : k < nBlk s₀) :
    (datR s₀).Contains (VG.Proof.Aes.X86.AesNi.bAddr s₀ k) 16 :=
  Offset.contains_base _ (by omega) (by have h := hp.fD; omega)

theorem block_out {k : Nat} (hk : k < nBlk s₀) : InRegions s₀.wr (VG.Proof.Aes.X86.AesNi.bAddr s₀ k) 16 :=
  ⟨datR s₀, by simp [hp.wr], VG.Proof.Aes.X86.AesNi.CPre.block_contains hp hk⟩

/-- Data and scratch writes preserve every byte of the schedule. -/
theorem sch_frame {m : Mem} (hf : Frame [datR s₀, scrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1)) = VG.Proof.Aes.X86.AesNi.sch s₀ := by
  have hn : 16 * (nRounds s₀ + 1) ≤ 240 := by
    rcases hp.rounds with h | h | h <;> omega
  simp only [VG.Proof.Aes.X86.AesNi.sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(schP s₀).setWidth 64, 16 * (nRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (nRounds s₀ + 1) ≤ 2 ^ 64; omega) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys {s : State} (hptr : s.gpr .eax = schP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [datR s₀, scrR s₀] s₀.mem s.mem) :
    VG.Proof.Aes.X86.AesNi.Keys (nRounds s₀) (VG.Proof.Aes.X86.AesNi.sch s₀) s := by
  have hnr : nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have he : ∀ j ≤ nRounds s₀, s.ea (Impl.Aes.X86.AesNi.at_ .eax (16 * j)) =
      (schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [ea_mk]
    simp only [Impl.Aes.X86.AesNi.at_]
    rw [hptr]
    exact addr_eq (by have h := hp.fS; omega)
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    refine ⟨schR s₀, ?_, VG.Proof.Aes.X86.AesNi.CPre.key_contains (Nat.le_trans hj hnr)⟩
    simp only [hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or]
  · rw [he j hj, ← VG.Proof.Aes.X86.AesNi.CPre.sch_frame hp hf]
    have h := byte_roundKey s.mem ((schP s₀).setWidth 64)
      (L := 16 * (nRounds s₀ + 1)) (j := j) (by omega)
    rw [ofInt_natCast] at h
    exact h

end CPre
end VG.Proof.Aes.X86.AesNi

end
