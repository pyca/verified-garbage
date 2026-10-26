module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawRange
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomMask
public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! A full scalar draw: copy, account for bytes, compare and update fuel. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_draw_full_ok {s : State} {B R Q : Addr} {used draws : Nat} {qBytes rand : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R)
    (hrlen : word s.mem B Random.oRandLen = BitVec.ofNat 64 rand.length)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 (VG.Proof.Dsa.significant qBytes).1)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length)
    (hm : word s.mem B Random.oMask = randomMaskValue (VG.Proof.Dsa.significant qBytes).2.toNat)
    (hq : word s.mem B Random.oQ = Q + BitVec.ofNat 64
      (qBytes.length - (VG.Proof.Dsa.significant qBytes).1))
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hrand : Src s B Random.frameBytes R rand) (hqs : Src s B Random.frameBytes Q qBytes)
    (hqlen : qBytes.length ≤ 32) (hrbound : rand.length < 2 ^ 64)
    (hpos : 0 < (VG.Proof.Dsa.significant qBytes).1)
    (hfull : used + (VG.Proof.Dsa.significant qBytes).1 ≤ rand.length)
    (hdpos : 0 < draws) (hdbound : draws < 2 ^ 64) :
    WP isa Random.draw s fun t => ∃ m : Mem, ∃ copied : List Byte,
      copied.length = (VG.Proof.Dsa.significant qBytes).1 ∧
      (∀ i (hi : i < copied.length), m
        (off B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1) + BitVec.ofNat 64 i) = copied[i]) ∧
      Spec.Dsa.decodeBE copied = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qBytes)
        ((rand.drop used).take (VG.Proof.Dsa.significant qBytes).1) ∧
      Outside B (200 + qBytes.length - (VG.Proof.Dsa.significant qBytes).1)
        (VG.Proof.Dsa.significant qBytes).1 s.mem m ∧
      t.mem = randomDrawFinishMem
        (m.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + copied.length))) B
        (decide (0 < Spec.Dsa.decodeBE copied ∧ Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE qBytes)) draws ∧
      Keep [.x0, .x3, .x4, .x2, .x8, .x10, .x12, .x9, .x15] s t := by
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit : n ≤ qBytes.length := VG.Proof.Dsa.significant_fits qBytes
  unfold Random.draw
  refine WP.seq (WP.mono (random_drawHead_ok hs hsp hrlen hu hn (by omega) hrbound (by omega))
    fun a ⟨hac, ham, hka⟩ => ?_)
  change a.gpr .x3 = BitVec.ofNat 64 (if rand.length - used < n then 1 else 0) at hac
  have hshort : ¬ rand.length - used < n := by omega
  refine WP.ite false (by simp [eval, State.read, hac, hshort])
    (fun h => Bool.noConfusion h) (fun _ => ?_)
  have has := hs.congr hka.wr
  have hasp := hka.sp.trans hsp
  have harand := hrand.congrK (show InScr B Random.frameBytes s.mem a.mem from by
    rw [ham]; exact InScr.refl _ _ _) hka
  refine WP.seq (WP.mono (random_copy_draw_ok has hasp
    (by rw [ham]; exact hR) (by rw [ham]; exact hu) (by rw [ham]; exact hn)
    (by rw [ham]; exact hl) (by rw [ham]; exact hm) harand hqlen hpos hfull)
    fun b ⟨copied, hclen, hcv, hcdec, hbf, hkb⟩ => ?_)
  have hbk := hka.trans hkb
  have hbs := hs.congr hbk.wr
  have hbsp := hbk.sp.trans hsp
  have hbf' : Outside B 200 32 s.mem b.mem := by
    rw [← ham]
    exact hbf.mono (by omega) (by omega)
  have hbu : word b.mem B Random.oUsed = BitVec.ofNat 64 used := by
    rw [hbf'.word (by decide) (by decide)]; exact hu
  have hbn : word b.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hbf'.word (by decide) (by decide)]; exact hn
  refine WP.seq (WP.mono (random_used_ok hbs hbsp hbu hbn)
    fun c ⟨hcm, hkc⟩ => ?_)
  have hck := hbk.trans hkc
  have hcs := hs.congr hck.wr
  have hcsp := hck.sp.trans hsp
  have hcf : Outside B Random.oUsed 8 b.mem c.mem := by
    rw [hcm]; exact writeW_outside _ _ _ (by decide)
  have hcqsrc := hqs.congrK
    ((InScr.of_outside hbf' (by decide)).trans (InScr.of_outside hcf (by decide))) hck
  have hcl : word c.mem B Random.oQLen = BitVec.ofNat 64 qBytes.length := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hl
  have hcn : word c.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hcf.word (by decide) (by decide)]; exact hbn
  have hcq : word c.mem B Random.oQ = Q + BitVec.ofNat 64 (qBytes.length - n) := by
    rw [hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hq
  have hccv : ∀ i (hi : i < copied.length), c.mem
      (off B (200 + qBytes.length - n) + BitVec.ofNat 64 i) = copied[i] := by
    intro i hi
    rw [hcf _ (by
      rw [random_nonce_offset B hnfit hqlen (by omega)]
      right
      unfold Random.oUsed
      omega)]
    exact hcv i hi
  refine WP.seq (WP.mono (random_check_candidate_ok hcs hcsp hcl hcn hcq hcqsrc
      hqlen hpos hclen rfl hccv)
    fun d ⟨hdz, hdm, hkd⟩ => ?_)
  have hdk := hck.trans hkd
  have hdd : word d.mem B Random.oDraws = BitVec.ofNat 64 draws := by
    rw [hdm, hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hd
  refine WP.mono (random_drawFinish_ok (accept := decide (0 < Spec.Dsa.decodeBE copied ∧
      Spec.Dsa.decodeBE copied < Spec.Dsa.decodeBE qBytes)) (hs.congr hdk.wr)
    (hdk.sp.trans hsp) hdd (by simpa only [decide_eq_true_eq] using hdz) hdpos hdbound)
    fun t ⟨htm, hkt⟩ => ?_
  refine ⟨b.mem, copied, hclen, hcv, hcdec, (by rw [← ham]; exact hbf), ?_, (hdk.trans hkt).mono (by decide)⟩
  rw [htm, hdm, hcm, hclen]

end VG.Proof.Dsa.AArch64
