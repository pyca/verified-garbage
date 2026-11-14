module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory

/-! ### `MlDsa.AArch64.Sign.CommitTailPadding`, which only this module used -/

section

/-! ## From `CommitTailPaddingWord.lean` -/

@[expose] public section

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
  refine WP.cons (s':=s.write .x .x7 w) (by simp [exec,w,Size.bits,Nat.mul_comm]; omega_using [hs]) ?_
  have hu := Upd.write64 s .x7 w
  refine wp_vop (d:=.v25) rfl fun a ha =>
    wp_vop (d:=.v25) rfl fun b hb =>
    wp_vop (d:=vreg j) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((((RegKeep.upd hu).trans (RegKeep.vupd ha)).trans (RegKeep.vupd hb)).trans
    (RegKeep.vupd ht)).mono (by simp),ht.mem.trans (hb.mem.trans (ha.mem.trans hu.mem)),?_⟩
  have hj25 : vreg j≠.v25 := by
    change vreg j≠vreg 25
    rw [ne_eq,vreg_inj j (by omega_using [hj]) 25 (by decide)]; omega_using [hj]
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
    rw [ne_eq,vreg_inj i (by omega_using [hi]) 25 (by decide)]; omega_using [hi]
  by_cases he : i=j
  · subst i
    rw [ht.v,hv25,hb.get _ hj25,ha.get _ hj25,hu.vec,hp j hj,pair_xor,xorWord_get _ _ _ _ hj,
      ite_eq_left rfl,show B[j]! ^^^ (0:BitVec 64)=B[j]! from BitVec.xor_zero]
  · have he' : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he
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

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted RateBlock StreamOutput)

/-- Low-lane absorb performed after permutation `i`. The last permutation
has no following absorb; only its digest is serialized. -/
def absorbAfter (wlen : Nat) (m : Mem) (w1 : Addr) (i : Nat) (A : Spec.Sha3.State) : Spec.Sha3.State :=
  let n := (64+wlen)/136
  if i<n-1 then xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 17
  else if i=n-1 then
    if wlen=768 then paddedState (xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 2) 2
    else paddedState A 0
  else A

def lowRun (wlen : Nat) (m : Mem) (w1 : Addr) (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | i+1 => absorbAfter wlen m w1 i (Spec.Sha3.keccakF (lowRun wlen m w1 A i))

def fullCount (wlen i : Nat) : Nat := min i ((64+wlen)/136-1)

def inputPtr (wlen : Nat) (w1 : Addr) (i : Nat) : Addr :=
  w1+BitVec.ofNat 64 (72+136*fullCount wlen i)

/-- One newly serialized high-lane block leaves previous blocks unchanged. -/
theorem streamOutput_append {m m' : Mem} {p : Addr} {j : Nat} {B : Spec.Sha3.State}
    (hj : j<5) (h : StreamOutput m p 8 j B)
    (hn : RateBlock m' (p+BitVec.ofNat 64 (136*j)) 8 (permuted B (j+1)))
    (hf : Frame [⟨p+BitVec.ofNat 64 (136*j),136⟩] m m') :
    StreamOutput m' p 8 (j+1) B := by
  intro i hi
  by_cases he : i=j
  · subst i; exact hn
  · refine (h i (by omega_using [hi, he])).keep (by decide) hf ?_
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact VG.Proof.MlDsa.AArch64.Optimized.Resident.block_disjoint (by decide) (by omega_using [hi, he]) (by omega_using [hj])

/-- Absorbs depend only on the words in their readable input slice. -/
theorem xorWords_congr {A : Spec.Sha3.State} {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀j<n,m'.readW (p+BitVec.ofNat 64 (8*j)) 64=m.readW (p+BitVec.ofNat 64 (8*j)) 64) :
    xorWords A m' p n=xorWords A m p n := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get,
    VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get]
  by_cases hn : i<n
  · rw [ite_eq_left hn,ite_eq_left hn]
    exact congrArg (fun x=>A[i] ^^^ x) (h i hn)
  · rw [ite_eq_right hn,ite_eq_right hn]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
