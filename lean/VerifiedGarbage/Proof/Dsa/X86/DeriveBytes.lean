module

public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

import VerifiedGarbage.Proof.Dsa.X86.KeyPartsReady
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Result
/-! # Derivation writes the original domain, the computed public key, and x -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/WriteKey.lean`, which only this module imported.
section

/-! # Assemble the derived key under its acceptance mask -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem maskedBytes (bs : List Byte) (accepted : Prop) [Decidable accepted] :
    bs.map (fun b => (b.setWidth 32 &&& mask32 accepted).setWidth 8) =
      if accepted then bs else List.replicate bs.length 0 := by
  by_cases H : accepted
  · simp only [mask32, H, ite_true, BitVec.and_allOnes]
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq] using List.map_id' bs
  · simp only [mask32, H, ite_false, BitVec.ofNat_eq_ofNat, BitVec.and_zero, BitVec.setWidth_zero]
    exact List.map_const'

theorem deriveBytesWith_ok {base : Addr} {size pLen qLen p q g x : Nat} {s : State} {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (mask : flagW base (Layout.field .mask) s = BitVec.allOnes 32)
    (hp : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (compute : Prog isa)
    (compute_ok : WP isa compute s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t=flagW base (Layout.field .mask) s &&&
        mask32 (((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
          (0<x ∧ x<q) ∧ (1<g^x%p ∧ g^x%p<p)) ∧
      operandValue t base (.local t2) pLen=g^x%p ∧ Execution base s t) :
    let accepted := ((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
      (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p)
    WP isa (.seq compute (Generate.writeKey pLen qLen)) s fun sf =>
      sf.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        (if accepted then
          Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) ++
          Spec.Dsa.encodeBE pLen (g ^ x % p) ++
          Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen
        else List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  intro accepted
  have L := M.lengths
  refine WP.seq (WP.mono compute_ok fun t ⟨Mt, F, Y, E⟩ => ?_)
  have ptr (f : Field) (stable : StablePointer (.input f)) :
      pointerValue base t (.input f) = pointerValue base s (.input f) :=
    runFrame_pointer E.mem E.keeps (by decide) stable
  have bytes {len : Nat} {f : Field} (B : CallerBuffer s base size (.input f) len)
      (stable : StablePointer (.input f)) :
      Spec.Rsa.bytesAt t.mem ((pointerValue base t (.input f)).setWidth 64) len =
        Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input f)).setWidth 64) len := by
    rw [ptr f stable]
    exact runFrame_bytes E.mem M.extent (by have := B.fits; omega) B.apart B.stack
  have partP := (E.buffer Params (by decide)).keyPart (by omega) (by rw [ptr .p (by decide)]; exact pa)
  have partX := (E.buffer X (by decide)).keyPart (by omega) (by rw [ptr .nonce (by decide)]; exact xa)
  have partY := localKeyPart Mt.scr (by omega : 0 < pLen)
    (Nat.le_trans (Mt.wideFit (d := t2) (by decide)) Mt.extent) ha
  refine WP.mono (writeKey_ok Mt.scr Mt.saved accepted (by rw [F, mask, BitVec.allOnes_and])
    ((ptr .out (by decide)).trans hp)
    (by intro part member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl; exact partP; exact partY; exact partX)
    hf (by omega) ha (by rw [E.keeps.2.2]; exact hw)) fun sf ⟨V, B, O, K⟩ => ?_
  have keyBytes : keyPartsBytes t base [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)] =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) ++
        Spec.Dsa.encodeBE pLen (g ^ x % p) ++
        Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen := by
    simp only [keyPartsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have Ybytes : Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local t2)).setWidth 64) pLen =
        Spec.Dsa.encodeBE pLen (g ^ x % p) := by
      rw [← Y]
      simpa only [operandValue, Spec.Rsa.bytesAt, List.length_map, List.length_range] using
        (encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local t2)).setWidth 64) pLen)).symm
    rw [bytes Params (by decide), bytes X (by decide), Ybytes, List.append_assoc]
  refine ⟨V, ?_, E.keeps.trans (K.mono (by decide)), ?_, ?_⟩
  · rw [B, maskedBytes, keyBytes]
    split_ifs <;> simp only [List.length_append, Spec.Rsa.bytesAt, List.length_map, List.length_range, encodeBE_length]
    congr 1; omega
  · intro a hb ho hstack
    exact (O a (.inr (by omega))).trans ((execution_outside E) a hb hstack)
  · intro regs saved
    have O' : OutputFrame base (out.setWidth 64) 0 (3 * pLen + 2 * qLen) t.mem sf.mem :=
      fun a _ h => O a (.inr (by omega))
    exact O'.saved ha (by decide) (by have H : 15712 ≤ size := Mt.extent; omega)
      (by have := Mt.scr.nowrap; omega) (E.saved saved)

theorem deriveBytes_ok {base : Addr} {size pLen qLen p q g x : Nat} {s : State} {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .nonce) qLen = x)
    (mask : flagW base (Layout.field .mask) s = BitVec.allOnes 32)
    (hp : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩) :
    let accepted := ((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
      (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p)
    WP isa (.seq (Generate.deriveCompute pLen qLen) (Generate.writeKey pLen qLen)) s fun sf =>
      sf.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        (if accepted then
          Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) ++
          Spec.Dsa.encodeBE pLen (g ^ x % p) ++
          Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen
        else List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters :=
  deriveBytesWith_ok M Params X mask hp hf hw ha pa xa _ (deriveCompute_ok M G X hg hx)

end VG.Proof.Dsa.X86
