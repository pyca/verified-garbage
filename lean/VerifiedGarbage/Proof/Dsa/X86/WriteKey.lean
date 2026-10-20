module

public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.Result

/-! # Assemble the derived key under its acceptance mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem writeKey_ok {s : State} {base : Addr} {size pLen qLen : Nat} {out : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (accepted : Prop) [Decidable accepted]
    (hm : flagW base (Layout.field .mask) s = mask32 accepted)
    (hp : pointerValue base s (.input .out) = out)
    (R : ∀ part ∈ [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)],
      KeyPartReady s base (out.setWidth 64) (3 * pLen + 2 * qLen) part)
    (ho : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (small : 3 * pLen + 2 * qLen < 2 ^ 32)
    (A : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (write : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (Generate.writeKey pLen qLen) s fun t =>
      t.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        (keyPartsBytes s base [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)]).map
          (fun b => (b.setWidth 32 &&& mask32 accepted).setWidth 8) ∧
      Outside (out.setWidth 64) 0 (3 * pLen + 2 * qLen) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  let parts : List (Pointer × Nat) := [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)]
  have count : keyPartsSize parts = 3 * pLen + 2 * qLen := by simp [parts, keyPartsSize]; omega
  have maskBound : Layout.field .mask + 4 ≤ size := by have : 8256 ≤ size := hz; change 8248 ≤ size; omega
  have outBound : Layout.field .out + 4 ≤ size := by have : 8256 ≤ size := hz; change 8228 ≤ size; omega
  unfold Generate.writeKey Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (wp_movS (readSrc_sc hs maskBound) fun u su _ => ?_)
  refine wp_movS (readSrc_sc (hs.of_keeps su.keeps (by decide)) outBound) fun v uv _ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx] s v := (su.keeps.mono (by decide)).trans (uv.keeps.mono (by decide))
  have mem : v.mem = s.mem := uv.mem.trans su.mem
  have ptr (p : Pointer) : pointerValue base v p = pointerValue base s p := by
    cases p <;> simp only [pointerValue, mem, K.1 .edi (by decide)]
  have Rv : ∀ part ∈ parts, KeyPartReady v base (out.setWidth 64) (keyPartsSize parts) part := by
    intro part member
    have H := R part member
    rw [count]
    exact ⟨H.positive, by rw [ptr]; exact H.fits,
      by rw [ptr, K.2.1, K.2.2]; exact H.read, by rw [ptr]; exact H.apart⟩
  refine WP.seq (WP.mono (keyCopyParts_ok (mask := mask32 accepted) parts (hs.of_keeps K (by decide)) hz Rv
    (by rw [count]; exact ho) (by rw [count]; exact small) (by rw [count]; exact A)
    (by rw [uv.gpr]; change u.mem.readW _ 32 = out; rw [su.mem]; exact hp)
    (by rw [uv.other _ (by decide), su.gpr]; exact hm)
    (by rw [count, K.2.2]; exact write)) fun w ⟨B, D, M, O, Kw⟩ => ?_)
  have mask : flagW base (Layout.field .mask) w = mask32 accepted := by
    have H := external_pointer (hs.of_keeps K (by decide)) hz O (by rw [count]; exact A) Kw (.input .mask)
    change flagW base (Layout.field .mask) w = flagW base (Layout.field .mask) v at H
    rw [H]; change v.mem.readW _ 32 = _; rw [mem]; exact hm
  refine WP.seq (WP.mono (result_ok ((hs.of_keeps K (by decide)).of_keeps Kw (by decide)) hz accepted mask)
    fun t ⟨V, Kt, Mt⟩ => WP.block_nil ⟨V, ?_, ?_, ?_⟩)
  · rw [Mt, ← count, B]
    congr 1
    unfold keyPartsBytes
    congr 1
    funext part
    rw [ptr, mem]
  · rw [Mt, ← count, ← mem]; exact O
  · exact (K.mono (by decide)).trans ((Kw.mono (by decide)).trans (Kt.mono (by decide)))

end VG.Proof.Dsa.X86
