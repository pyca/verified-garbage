import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSqueeze

/-! ## From `CommitTailPaddingWord.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.Sha3.AArch64 (WP.cons Upd)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def xorWord (A : Spec.Sha3.State) (j : Nat) (w : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val=j then A[i] ^^^ w else A[i]

theorem xorWord_get (A : Spec.Sha3.State) (j : Nat) (w : BitVec 64) (i : Nat) (hi : i<25) :
    (xorWord A j w)[i]! = if i=j then A[i]! ^^^ w else A[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq A hi]
  simp only [xorWord,Vector.getElem_ofFn,Fin.getElem_fin]

def paddingWord (j : Nat) (imm : BitVec 16) (shift : Nat) : List Instr :=
  [.movz .x .x7 imm shift,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),
    .vop (.logic .eor (vreg j) (vreg j) .v25)]

/-- One low-lane padding constant never affects the cached mask stream. -/
theorem paddingWord_ok {s : State} {A B : Spec.Sha3.State} {j : Nat} (hj : j<25)
    (imm : BitVec 16) (shift : Nat) (hs : shift<4) (hp : Pairs s A B) :
    WP isa (.block (paddingWord j imm shift)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (xorWord A j (imm.setWidth 64 <<< (16*shift))) B := by
  unfold paddingWord
  let w : BitVec 64 := imm.setWidth 64 <<< (16*shift)
  refine WP.cons (s':=s.write .x .x7 w) (by simp [exec,w,Size.bits,Nat.mul_comm]; omega) ?_
  have hu := Upd.write64 s .x7 w
  refine wp_vop (d:=.v25) rfl fun a ha =>
    wp_vop (d:=.v25) rfl fun b hb =>
    wp_vop (d:=vreg j) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((((RegKeep.upd hu).trans (RegKeep.vupd ha)).trans (RegKeep.vupd hb)).trans
    (RegKeep.vupd ht)).mono (by simp),ht.mem.trans (hb.mem.trans (ha.mem.trans hu.mem)),?_⟩
  have hj25 : vreg j≠.v25 := by
    change vreg j≠vreg 25
    rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]; omega
  have hv25 : b.v .v25=ofVDwords w 0 := by
    rw [hb.v,ha.v,ha.gpr,hu.gpr]
    apply vec64_ext
    · change (setLane 0 64 0 w).extractLsb' (64*0) 64=_
      rw [extract_setLane64 0 w (i:=0) (j:=0) (by decide) (by decide),vdword_ofVDwords_0]
      rfl
    · change (setLane 0 64 0 w).extractLsb' (64*1) 64=_
      rw [extract_setLane64 0 w (i:=0) (j:=1) (by decide) (by decide),vdword_ofVDwords_1]
      rfl
  intro i hi
  have hi25 : vreg i≠.v25 := by
    change vreg i≠vreg 25
    rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]; omega
  by_cases he : i=j
  · subst i
    rw [ht.v,hv25,hb.get _ hj25,ha.get _ hj25,hu.vec,hp j hj,pair_xor,xorWord_get _ _ _ _ hj,
      ite_eq_left rfl,show B[j]! ^^^ (0:BitVec 64)=B[j]! from BitVec.xor_zero]
  · have he' : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    rw [ht.get _ he',hb.get _ hi25,ha.get _ hi25,hu.vec,hp i hi,xorWord_get _ _ _ _ hi,ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailPadding.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def paddedState (A : Spec.Sha3.State) (j : Nat) : Spec.Sha3.State :=
  xorWord (xorWord A j 0x1f) 16 0x8000000000000000

/-- Adds SHAKE256 domain separation and the rate-block terminal bit. -/
theorem padding_ok {s : State} {A B : Spec.Sha3.State} {j : Nat}
    (hj : j<25) (hp : Pairs s A B) :
    WP isa (.block (paddingWord j 31 0 ++ paddingWord 16 0x8000 3)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t (paddedState A j) B := by
  rw [WP.block_append_iff]
  refine WP.mono (paddingWord_ok hj 31 0 (by decide) hp) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (paddingWord_ok (by decide) 0x8000 3 (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

/-- ML-DSA-65 has two words left after six complete rate blocks. -/
theorem tail_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<2, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block tail) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (paddedState (xorWords A s.mem (s.gpr .x5) 2) 2) B := by
  change WP isa (.block (((List.range 2).flatMap fun j => lowWord (vreg j) (8*j)) ++
    (paddingWord 2 31 0 ++ paddingWord 16 0x8000 3))) s _
  rw [WP.block_append_iff]
  refine WP.mono (lowWords_ok hp 2 (by decide) hin) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (padding_ok (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
