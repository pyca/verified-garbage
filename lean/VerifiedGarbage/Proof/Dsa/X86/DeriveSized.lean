module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.KeyPartsReady
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86.KeyCopyParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Result
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Dsa.X86.DeriveBytes`, which only this module used -/

section

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
    exact runFrame_bytes E.mem M.extent (by have := B.fits; omega_using [this]) B.apart B.stack
  have partP := (E.buffer Params (by decide)).keyPart (by omega_using [L]) (by rw [ptr .p (by decide)]; exact pa)
  have partX := (E.buffer X (by decide)).keyPart (by omega_using [L]) (by rw [ptr .nonce (by decide)]; exact xa)
  have partY := localKeyPart Mt.scr (by omega_using [L] : 0 < pLen)
    (Nat.le_trans (Mt.wideFit (d := t2) (by decide)) Mt.extent) ha
  refine WP.mono (writeKey_ok Mt.scr Mt.saved accepted (by rw [F, mask, BitVec.allOnes_and])
    ((ptr .out (by decide)).trans hp)
    (by intro part member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl; exact partP; exact partY; exact partX)
    hf (by omega_using [L]) ha (by rw [E.keeps.2.2]; exact hw)) fun sf ⟨V, B, O, K⟩ => ?_
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
    congr 1; omega_using []
  · intro a hb ho hstack
    exact (O a (.inr (by omega_using [ho]))).trans ((execution_outside E) a hb hstack)
  · intro regs saved
    have O' : OutputFrame base (out.setWidth 64) 0 (3 * pLen + 2 * qLen) t.mem sf.mem :=
      fun a _ h => O a (.inr (by omega_using [h]))
    exact O'.saved ha (by decide) (by have H : 15712 ≤ size := Mt.extent; omega_using [H])
      (by have := Mt.scr.nowrap; omega_using [this]) (E.saved saved)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.DeriveSpec`, which only this module used -/

section

/-! # The generation checks in the order of the x86 implementation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem deriveSpec {pLen qLen p q g x : Nat} {params scalar : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen)
    (paramsLen : params.length = 2 * pLen + qLen) (scalarLen : scalar.length = qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (scalarValue : Spec.Dsa.decodeBE scalar = x) :
    Spec.Dsa.deriveKeyBytes pLen qLen params scalar =
      if shapeValid p q ∧ (((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
        (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p))
      then some (params ++ Spec.Dsa.encodeBE pLen (g ^ x % p) ++ scalar) else none := by
  rw [deriveKeyBytes_eq widths paramsLen scalarLen]
  simp only [paramsValue, scalarValue, powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  congr 1
  simp only [shapeValid, and_assoc, and_comm, and_left_comm]

end VG.Proof.Dsa.X86

end

end

/-! # Shape checking followed by derivation or full output clearing -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/DeriveFailure.lean`, which only this module imported.
section

/-! # Invalid shapes clear the complete derived key -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem deriveFailure_ok {s : State} {base : Addr} {size pLen qLen : Nat} {out : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hl : 0 < 3 * pLen + 2 * qLen) (hb : 3 * pLen + 2 * qLen < 2 ^ 32)
    (hp : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (Generate.deriveFailure pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) (3 * pLen + 2 * qLen) = List.replicate (3 * pLen + 2 * qLen) 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 (3 * pLen + 2 * qLen) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  have bound : 8256 ≤ size := hz
  unfold Generate.deriveFailure Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (wp_movS (readSrc_sc hs (d := Layout.field .out) (by change 8228 ≤ size; omega)) fun s1 U1 _ => ?_)
  refine wp_movS rfl fun s2 U2 _ => ?_
  refine wp_movS rfl fun s3 U3 _ => WP.block_nil ?_
  have K3 : Keeps [.esi, .ecx, .eax] s s3 :=
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))
  have O3 : s3.mem = s.mem := by rw [U3.mem, U2.mem, U1.mem]
  refine WP.seq (WP.mono (failureLoop_ok hl hb hf
    (by rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr]; exact hp)
    (by rw [U3.other _ (by decide), U2.gpr]) U3.gpr
    (by intro i hi; rw [K3.2.2]; exact hw i hi)) fun t ⟨V, Z, O, K⟩ => ?_)
  exact WP.block_nil ⟨V, Z, by simpa only [O3] using O, K3.trans (K.mono (by decide))⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem deriveSizedWith_spec {base : Addr} {size pLen qLen p q g x : Nat}
    {s : State} {out : BitVec 32} {params scalar : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .nonce) qLen = x)
    (paramBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) = params)
    (scalarBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen = scalar)
    (ho : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (compute : Nat → Nat → Prog isa) (I : Mem → Prop) (initial : I s.mem)
    (stable : ∀ {m m'}, Outs base shapeRanges m m' → I m → I m')
    (compute_ok : ∀ {t : State}, Moduli base size pLen qLen p q t →
      CallerBuffer t base size (.input .g) pLen → CallerBuffer t base size (.input .nonce) qLen →
      operandValue t base (.input .g) pLen=g → operandValue t base (.input .nonce) qLen=x → I t.mem →
      WP isa (compute pLen qLen) t fun u =>
        Moduli base size pLen qLen p q u ∧
        flagW base (Layout.field .mask) u=flagW base (Layout.field .mask) t &&&
          mask32 (((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
            (0<x ∧ x<q) ∧ (1<g^x%p ∧ g^x%p<p)) ∧
        operandValue u base (.local t2) pLen=g^x%p ∧ Execution base t u) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (Generate.deriveSizedWith compute pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  dsimp only
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  have sz : 8272 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  have L : 128 ≤ pLen ∧ pLen ≤ 384 ∧ 20 ≤ qLen ∧ qLen ≤ 32 := by unfold Spec.Dsa.lengthsValid at widths; omega_using [widths]
  have spec := deriveSpec widths
    (show params.length = 2 * pLen + qLen by rw [← paramBytes]; simp [Spec.Rsa.bytesAt])
    (show scalar.length = qLen by rw [← scalarBytes]; simp [Spec.Rsa.bytesAt]) paramsValue
    (show Spec.Dsa.decodeBE scalar = x by rw [← scalarBytes]; exact hx)
  unfold Generate.deriveSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    have Ct := compute_ok Mt (G.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((X.value_keep_shape O K (by decide) (by decide) bound).trans hx) (stable O initial)
    refine WP.mono (deriveBytesWith_ok Mt
      (Params.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      (by rw [F]; simp only [mask32, valid, ite_true])
      ((shapeFrame_field O (by decide)).trans ho) hf
      (by rw [K.2.2]; exact hw) ha
      (by rw [shapeFrame_field O (by decide : Field.p ≠ .mask ∧ Field.p ≠ .digestPrefixLen)]; exact pa)
      (by rw [shapeFrame_field O (by decide : Field.nonce ≠ .mask ∧ Field.nonce ≠ .digestPrefixLen)]; exact xa) _ Ct)
      fun sf ⟨V, B, Kf, Of, Saved⟩ => ?_
    rw [Params.bytes_keep_shape O K (by decide) (by decide) bound,
      X.bytes_keep_shape O K (by decide) (by decide) bound, paramBytes, scalarBytes] at B
    rw [spec]
    simp only [valid, true_and]
    refine ⟨?_, ?_, (K.mono (by decide)).trans Kf, ?_, fun regs saved => Saved regs (shapeFrame_saved O saved)⟩
    · rw [V]; split_ifs <;> rfl
    · split_ifs at B ⊢ <;> exact B
    · intro a hb hout hstack
      exact (Of a hb hout (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at hb; omega_using [hb])))
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (deriveFailure_ok (scr.of_keeps K (by decide)) (by change 8256 ≤ size; omega_using [sz])
      (by omega_using [L]) (by omega_using [L]) ((shapeFrame_field O (by decide)).trans ho) hf
      (by rw [K.2.2]; exact hw)) fun sf ⟨B, V, Of, Kf⟩ => ?_
    have Fout : OutputFrame base (out.setWidth 64) 0 (3 * pLen + 2 * qLen) t.mem sf.mem :=
      fun a _ h => Of a (.inr (by omega_using [h]))
    rw [spec]
    simp only [valid, false_and, ite_false, Option.getD_none]
    refine ⟨by rw [V]; rfl, B, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · intro a hb hout _
      exact (Fout a (by omega_using []) hout).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at hb; omega_using [hb])))
    · intro regs saved
      exact Fout.saved ha (by decide) sz (by have := scr.nowrap; omega_using [this]) (shapeFrame_saved O saved)

theorem deriveSized_spec {base : Addr} {size pLen qLen p q g x : Nat}
    {s : State} {out : BitVec 32} {params scalar : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .nonce) qLen = x)
    (paramBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) = params)
    (scalarBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen = scalar)
    (ho : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (Generate.deriveSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters :=
  deriveSizedWith_spec scr extent widths Params P Q G X hp hq hg hx paramBytes scalarBytes
    ho hf hw ha pa xa paramsValue Generate.deriveCompute (fun _ => True) trivial
    (fun _ _ => trivial) (fun M G X hg hx _ => deriveCompute_ok M G X hg hx)

end VG.Proof.Dsa.X86
