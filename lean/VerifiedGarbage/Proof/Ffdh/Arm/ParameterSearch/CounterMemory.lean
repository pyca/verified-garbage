module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Counter
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller

/-! Load, decrement and store the entire native u64 attempt budget. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

theorem counterLoads_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4]) s fun t =>
      (t.gpr .r9 = lowWord s.mem base 0 ∧ t.gpr .r10 = s.mem.readW (off (State.addr base) 4) 32 ∧ t.mem = s.mem) ∧
      Rest [.r9, .r10] s t := by
  refine withRest_all [.r9, .r10] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.ldf lowWord
  ffrun [controllerAddr h 0 (by decide), controllerAddr h 4 (by decide),
    h.space.read (off := 0) (by decide), h.space.read (off := 4) (by decide)]

theorem decrement_ok (s : State) {base : BitVec 32} {n : Nat} (h : Controller base s)
    (positive : 0 < n) (bound : n ≤ 2 ^ 32)
    (counter : s.mem.readW (State.addr base) 64 = BitVec.ofNat 64 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.decrement) s fun t =>
      t.mem = s.mem.writeW (State.addr base) (BitVec.ofNat 64 (n - 1)) ∧ Rest [.r9, .r10, .r12] s t := by
  have fits : n < 2 ^ 64 := by omega
  have lo : lowWord s.mem base 0 = BitVec.ofNat 32 n :=
    packedLow s.mem base 0 n fits (by simpa [off] using counter)
  have hi : s.mem.readW (off (State.addr base) 4) 32 = BitVec.ofNat 32 (n / 2 ^ 32) :=
    packedHigh s.mem base 0 n fits (by simpa [off] using counter)
  change WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
    (VG.Impl.Ffdh.Arm.ParameterSearch.decrementWords ++
      [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 0, .str .r10 .r4 4]))) s _
  rw [WP.block_append_iff]
  refine WP.mono (counterLoads_ok s h) ?_
  rintro u ⟨⟨lowU, highU, memU⟩, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (decrementWords_ok u positive bound (lowU.trans lo) (highU.trans hi)) ?_
  rintro v ⟨⟨lowV, highV, memV⟩, restV⟩
  have restUV : Rest [.r9, .r10, .r12] s v := (restU.mono (by simp)).trans restV
  have context : Controller base v :=
    ⟨h.space.congr restUV.wr, (restUV.gpr .r4 (by simp)).trans h.ptr⟩
  have raw : WP isa (.block [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r9 0, .str .r10 .r4 4]) v fun t =>
      t.mem = s.mem.writeW (State.addr base) (BitVec.ofNat 64 (n - 1)) ∧ Rest [] v t := by
    refine withRest_all [] ?_ (by rfl) (by rfl)
    unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
    ffrun [controllerAddr context 0 (by decide), controllerAddr context 4 (by decide),
      context.space.write (off := 0) (by decide), context.space.write (off := 4) (by decide),
      lowV, highV, memV, memU]
    simpa [off] using writeCounter s.mem base (n - 1) (by omega)
  exact WP.mono raw (fun _ post => ⟨post.1, restUV.trans (post.2.mono (by simp))⟩)

end VG.Proof.Ffdh.Arm.ParameterSearch
