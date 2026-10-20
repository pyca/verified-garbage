module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Workspace
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Omega

/-! # The parameter generator needs no initialized scratch memory -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem workspaceHead_ok {s : State} {B : Addr} {Z w : Nat}
    (h : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hw : w < 2 ^ 24) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.workspaceHead w)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = (s.mem.writeW (off B 48) (BitVec.ofNat 64 w)).writeW (off B 56) (0#64) ∧
      Keep [.rax, .r12] s t := by
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = (s.mem.writeW (off B 48) (BitVec.ofNat 64 w)).writeW (off B 56) (0#64)) (by
    xrun [Impl.Dsa.X86_64.Generation.workspaceHead, State.ea, hdr, hdrOff, sW, sMinv, hdi,
      h.st (d := 48) (by omega), h.st (d := 56) (by omega)]
    have he : (BitVec.ofNat 32 w).setWidth 64 = BitVec.ofNat 64 w := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : w < 2 ^ 32)]
    simp only [he]
    exact ⟨True.intro, rfl⟩) rfl) fun _ ⟨⟨h12, hm⟩, hk⟩ => ⟨h12, hm, hk⟩

theorem workspace_ok {s : State} {B : Addr} {Z w : Nat}
    (h : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : slot w 16 ≤ Z)
    (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24) :
    WP isa (Impl.Dsa.X86_64.Generation.workspace w) s fun t =>
      Ws t B Z w ∧ Good t B Z w 0 ∧
      Frm B [(48, 80), (224, 8)] s.mem t.mem ∧ Keep [.rax, .rdx, .r12] s t := by
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  unfold Impl.Dsa.X86_64.Generation.workspace
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceHead_ok h hdi hz hw2) fun u ⟨h12, hm, ku⟩ => ?_)
  have hu := h.congr ku.2.2
  have hudi := (ku.gpr (by decide)).trans hdi
  refine WP.seq (WP.mono (setBases_ok hu hudi h12 (by unfold sArr; omega))
    fun v ⟨harr, fv, kv⟩ => ?_)
  have hv := hu.congr kv.2.2
  have hvdi := (kv.gpr (by decide)).trans hudi
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = v.mem.writeW (off B 224) (BitVec.ofNat 64 (8 * (w + 2)))) (by
    xrun [Impl.Dsa.X86_64.Generation.workspaceStride, State.ea, hdr, hdrOff, sStride, sFn, hvdi,
      hv.st (d := 224) (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * (w + 2) < 2 ^ 32)]) rfl) fun t ⟨htm, kt⟩ => ?_
  have ft : Outside B 224 8 v.mem t.mem := by rw [htm]; exact writeW_outside _ _ _ (by decide)
  have allk := (ku.trans kv).trans kt
  have hw : word t.mem B 48 = BitVec.ofNat 64 w := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm,
      (writeW_outside _ B _ (d := 56) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  have hminv : word t.mem B 56 = 0 := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm, word_writeW_self]
    rfl
  have ha : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j) := by
    intro j hj
    rw [ft.word (Or.inl (by unfold sArr; omega)) (by unfold sArr; omega)]
    exact harr j hj
  have hs := h.congr allk.2.2
  have ht := allk.gpr (by decide) |>.trans hdi
  refine ⟨⟨hs, ht, hw, ?_, ha, hZ, hw1, hw2⟩, ⟨hs, ht, ⟨hw, hminv, ha⟩⟩, ?_, allk.mono (by decide)⟩
  · rw [htm]; exact word_writeW_self _ _ _ _
  · have fh : Outside B 48 16 s.mem u.mem := by
      rw [hm]
      exact ((writeW_outside _ B _ (d := 48) (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ B _ (d := 56) (by decide)).mono (by decide) (by decide))
    have fhv : Outside B 48 80 s.mem v.mem :=
      (fh.mono (by decide) (by decide)).trans (fv.mono (by decide) (by decide))
    exact (Frm.of_outside fhv (by simp)).trans (Frm.of_outside ft (by simp))

end VG.Proof.Dsa.X86_64.Generation
