module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save

import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

/-- The rest after the chunks, with `Small.xor`. -/
theorem ttail_ok {sve : Bool} {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.TPre s₀) {t : Nat}
    {s : State} (h : TRest s₀ t s) :
    WP isa (Impl.ChaCha20.AArch64.Small.xor sve) s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (VG.Proof.ChaCha20.AArch64.Xor.rest_ok (VG.Proof.ChaCha20.AArch64.Small.xor_noFrames sve)
    (fun s hs _ => (VG.Proof.ChaCha20.AArch64.Small.correct s hs).mono fun _ ⟨ha, hu⟩ =>
      ⟨⟨ha.1, ha.2.1⟩, hu⟩)
    hp (n := 512 * t) h.le (by omega) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 512 * t / 64 = 8 * t by omega]) h.data h.src).mono
    fun _ ⟨ha, hpost, h0, h1⟩ => ⟨⟨fun r hr => (ha.1 r hr).trans (h.cs r hr), ha.2.trans h.sp⟩, hpost, h0, h1⟩

end VG.Proof.ChaCha20.AArch64.Mixed8
