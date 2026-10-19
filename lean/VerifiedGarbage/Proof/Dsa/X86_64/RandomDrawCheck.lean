module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomState
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory

/-! Isolate the draw prefix before the acceptance branch. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomDrawCheck : Prog isa :=
  .seq Random.copy (.seq (.block [.mov .rax (.mem (Random.sp Random.oUsed)),
    .alu .add .rax (.mem (Random.sp Random.oWidth)), .store (Random.sp Random.oUsed) .rax]) Random.inRange)

theorem random_drawCheck_ok {C : RandomContext} {s : State} {used draws : Nat}
    (hr : RandomReady C used draws s)
    (hfull : used + (VG.Proof.Dsa.significant C.qBytes).1 ≤ C.rand.length) :
    WP isa randomDrawCheck s fun t =>
      Scr t C.B Random.frameBytes ∧ t.gpr .rsp = C.B ∧
      word t.mem C.B Random.oDraws = BitVec.ofNat 64 draws ∧
      t.zf = some (!decide (0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
        ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1) ∧
        Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE C.qBytes)
        ((C.rand.drop used).take (VG.Proof.Dsa.significant C.qBytes).1) < Spec.Dsa.decodeBE C.qBytes)) := by
  let B := C.B
  let Q := C.Q
  let qBytes := C.qBytes
  let n := (VG.Proof.Dsa.significant qBytes).1
  have hnfit := VG.Proof.Dsa.significant_fits qBytes
  have hs := hr.scr
  have hsp := hr.sp
  have hR := hr.rand
  have hu := hr.usedWord
  have hn := hr.width
  have hl := hr.qLen
  have hm := hr.mask
  have hq := hr.q
  have hd := hr.draws
  have hrand := hr.randSrc
  have hqs := hr.qSrc
  have hqlen := C.qlen
  have hpos := C.positive
  dsimp only [qBytes] at *
  unfold randomDrawCheck
  refine WP.seq (WP.mono (random_copy_draw_ok hs hsp
    hR hu hn
    hl hm hrand hqlen hpos hfull)
    fun b ⟨copied, hclen, hcv, hcdec, hbf, hkb⟩ => ?_)
  have hbk := hkb
  have hbs := hs.congr hbk.2.2
  have hbsp := (hbk.gpr (by decide)).trans hsp
  have hbf' : Outside B 200 32 s.mem b.mem := by
    exact hbf.mono (by omega) (by omega)
  have hbu : word b.mem B Random.oUsed = BitVec.ofNat 64 used := by
    rw [hbf'.word (by decide) (by decide)]; exact hu
  have hbn : word b.mem B Random.oWidth = BitVec.ofNat 64 n := by
    rw [hbf'.word (by decide) (by decide)]; exact hn
  refine WP.seq (WP.mono (random_used_ok hbs hbsp hbu hbn)
    fun c ⟨hcm, hkc⟩ => ?_)
  have hck := hbk.trans hkc
  have hcs := hs.congr hck.2.2
  have hcsp := (hck.gpr (by decide)).trans hsp
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
  refine WP.mono (random_check_candidate_ok hcs hcsp hcl hcn hcq hcqsrc
      hqlen hpos hclen rfl hccv)
    fun d ⟨hdz, hdm, hkd⟩ => ?_
  have hdk := hck.trans hkd
  have hdd : word d.mem B Random.oDraws = BitVec.ofNat 64 draws := by
    rw [hdm, hcf.word (by decide) (by decide), hbf'.word (by decide) (by decide)]; exact hd
  exact ⟨hs.congr hdk.2.2, (hdk.gpr (by decide)).trans hsp, hdd,
    by rw [hdz, hcdec]⟩

end VG.Proof.Dsa.X86_64
