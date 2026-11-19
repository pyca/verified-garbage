module

public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
public import VerifiedGarbage.Proof.Ed25519.RootPower
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
public import VerifiedGarbage.Proof.X25519.X86_64.Env
public import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Recover
meta import VerifiedGarbage.Proof.Ed25519.RootPower
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
meta import VerifiedGarbage.Proof.X25519.X86_64.Env
meta import VerifiedGarbage.Proof.X25519.Invert
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
meta import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
meta import VerifiedGarbage.Proof.Ed25519.Decode
meta import VerifiedGarbage.Proof.Ed25519.Recover
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.X25519.X86_64.Freeze
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Ed25519.X86_64.VerifyContext`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86_64.PointDecode`, which only this module used -/

section

/-! ### `Ed25519.X86_64.RecoverPoint`, which only this module used -/

section

/-! Candidate root and its squared check agree with the decoding specification. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

/-- The square root's power of `y`'s decoding: `(u v⁷)^((p - 5) / 8)`. -/
def rootPow (y : Spec.X25519.Fe) : Spec.X25519.Fe :=
  Spec.X25519.pow (rootU y * Spec.X25519.pow (rootV y) 7) ((Spec.X25519.P - 5) / 8)

private theorem recoverPrep_eval (e : Env) :
    evalOps recoverPrepOps e 1 = e 1 ∧
    evalOps recoverPrepOps e 6 = rootU (e 1) ∧
    evalOps recoverPrepOps e 7 = rootV (e 1) ∧
    evalOps recoverPrepOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverPrepOps e 15 = e 15 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  exact pow_three _

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The candidate, from the power in slot 15 (`hp`). -/
theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hp : env s.mem base 15 = rootPow (env s.mem base 1)) :
    WP isa (recoverCandidate fld) s fun t => RbxKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.mono (fieldCodeWide_ok hs (recoverPrepOps ++ recoverFinishOps)) fun t ⟨kt, vt⟩ => ?_
  have ve : env t.mem base = evalOps recoverFinishOps (evalOps recoverPrepOps (env s.mem base)) := by
    rw [vt, evalOps, List.foldl_append]; rfl
  obtain ⟨ay, au, av, av3, ap⟩ := recoverPrep_eval (env s.mem base)
  have bx : evalOps recoverPrepOps (env s.mem base) 6 * evalOps recoverPrepOps (env s.mem base) 9 *
      evalOps recoverPrepOps (env s.mem base) 15 = rootX (env s.mem base 1) := by
    rw [au, av3, ap, hp]
    rfl
  refine ⟨RbxKeep.of_keep kt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ve, (recoverFinish_eval _).1, bx]
  · rw [ve, (recoverFinish_eval _).2.1, ay]
  · rw [ve, (recoverFinish_eval _).2.2.1]
  · rw [ve, (recoverFinish_eval _).2.2.2.1, au]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.1, av]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.2.1, bx, av]
  · rw [ve, (recoverFinish_eval _).2.2.2.2.2.2, au]

end VG.Proof.Ed25519.X86_64

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa (recoverSign fld) s fun t => RbxKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨RbxKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) (hp : env s.mem base 15 = rootPow (env s.mem base 1)) :
    WP isa (recoverPoint fld) s fun t => RbxKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs hp) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scratch hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (RbxKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by change c.zf = _; rw [cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scratch hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scratch hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (RbxKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by change d.zf = _; rw [dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCodeWide_ok (kacd.scratch hs) [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (RbxKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scratch hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (RbxKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.X86_64

end

end


/-! Merged from `Proof.Ed25519.X86_64.DecodeLoad`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86_64.CanonicalY`. -/
section
/-! Canonical decoding checks y before reduction modulo p. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (low63)
open VG.Proof.X25519.X86_64 (val4 Keeps freezeB freezeB_ok mask)

theorem setLow63_ok (s : State) :
    WP isa (.block [.movImm64 .rdx low63]) s fun t => t.gpr .rdx = low63 ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem canonicalMask_ok {s : State} (n : Nat)
    (hm : s.gpr .rcx = mask (decide (Spec.X25519.P ≤ n))) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      t.zf = some (decide (n < Spec.X25519.P)) ∧ Keeps [] s t := by
  have hz : (mask (decide (Spec.X25519.P ≤ n)) == 0#64) = decide (n < Spec.X25519.P) := by
    by_cases h : Spec.X25519.P ≤ n
    · rw [decide_eq_true h, decide_eq_false (by omega_using [h] : ¬ n < Spec.X25519.P)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega_using [h] : n < Spec.X25519.P)]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hm]
  exact ⟨hz, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = n) :
    WP isa (.block canonicalY) s fun t => t.zf = some (decide (n < Spec.X25519.P)) ∧
      Keeps [.rdx, .r12, .r13, .r14, .r15, .rax, .rcx] s t := by
  change WP isa (.block (([.movImm64 .rdx low63] : List Instr) ++ freezeB ++
    [.alu .test .rcx (.reg .rcx)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setLow63_ok s) fun a ⟨ad, ka⟩ => ?_
  have av : val4 (a.gpr .r8) (a.gpr .r9) (a.gpr .r10) (a.gpr .r11) = n := by
    rw [val4, ka.1 .r8 (by decide), ka.1 .r9 (by decide), ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
    exact hv
  rw [WP.block_append_iff]
  refine WP.mono (freezeB_ok a (by rw [av]; omega_using [hn]) ad) fun b ⟨bc, _, kb⟩ => ?_
  rw [av] at bc
  refine WP.mono (canonicalMask_ok n bc) fun t ⟨tz, kt⟩ => ?_
  exact ⟨tz, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.StoreWords`. -/
section
/-! Save four words in an Ed25519 field slot. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr st4)

theorem storeWordsWide_ok {s : State} {base : Addr} (hs : Scratch s base) (o : Slot) :
    WP isa (.block (Impl.X25519.X86_64.store4 (offset o))) s fun t =>
      t.mem = st4 s.mem base (offset o) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega_using [this]⟩
  obtain ⟨tr, t, he, hm, hg, _, _⟩ := Proof.X25519.X86_64.store4_ok hn (o := offset o)
    (by simp only [offset]; omega_using [])
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hm, hg, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
end

/-! Point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside clob F st4_outside fe_st4 val4)

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : DecodeKeep base s t) (k : DecodeKeep base t u) : DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : DecodeKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .rbx ∨ r = .rsi) : DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.2.1]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => DecodeKeep base s t ∧
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      t.zf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P)) ∧
      env t.mem base 15 = env s.mem base 15 := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.1 _ (by decide)).trans hp)
    (by intro d hd; rw [ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.2.1] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (storeWordsWide_ok (kab.scratch hs) 1) fun c ⟨cm, cg, cr, cw⟩ => ?_
  have cmem : Outside base (offset 1) 32 b.mem c.mem := by
    rw [cm]; exact st4_outside _ _ (by decide) _ _ _ _
  have kc : DecodeKeep base b c := ⟨fun r _ _ _ => cg r, cr, cw, cmem.mono (by decide) (by decide)⟩
  have cy : env c.mem base 1 = Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change F c.mem base (offset 1) = _
    rw [F, cm, fe_st4 _ _ (by decide), byval]
  have cv : val4 (c.gpr .r8) (c.gpr .r9) (c.gpr .r10) (c.gpr .r11) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 := by
    rw [val4, cg .r8, cg .r9, cg .r10, cg .r11]; exact byval
  refine WP.mono (canonicalY_ok c _ (Nat.mod_lt _ (by decide)) cv) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz, ?_⟩
  · rw [kt.1 .rsi (by decide), cg .rsi, kb.1 .rsi (by decide)]; exact asign
  · rw [kt.2.1]; exact cy
  · change F t.mem base (offset 15) = F s.mem base (offset 15)
    rw [kt.2.1, Outside_F cmem (by simp only [offset]; omega_using []) (Or.inr (by simp only [offset]; omega_using [])),
      kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end

/-! Canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

/-- The y-coordinate the 32 bytes `bs` encode, their top bit masked. -/
def decodedY (bs : List Byte) : Spec.X25519.Fe := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)

/-- Decoding, with its square root's power in slot 15 (`hpow`). -/
theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8)
    (hpow : env s.mem base 15 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem p 32))) :
    WP isa (pointDecode fld) s fun t => DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az, a15⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by exact az)
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign (by rw [a15, hpow, ay]; rfl))
      fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx (RbxKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.X86_64

end

end


/-! Merged from `Proof.Ed25519.X86_64.VerifyTables`. -/

@[expose] public section

section
/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movImm64 .rbx 0]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scratch s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).rdi o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.2.1, ka.2.1]
  · rw [table_env kt.mem hlo, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end

/-! The verification inputs remain readable and outside the workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps)

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scratch s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarBytes : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1
  challengeRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1
  challengeRead8 : ∀ d, d + 8 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 8
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)
  bTab : BaseTbl s base (s.mem.readW (off base 7960) 64)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) (k : VerifyKeep base s t) :
    VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar, by
      rw [k.header (d := 7960) (by decide) (by decide) (by decide)]
      exact h.bTab.of_powers k (by decide)⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarBytes _ ‹_›
  · exact h.challengeRead _ ‹_›
  · exact h.challengeRead8 _ ‹_›

theorem VerifyContext.kRead8 {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    ∀ j < 8, InRegions (s.rd ++ s.wr) (off challenge (8 * j)) 8 :=
  fun j _ => h.challengeRead8 _ (by omega_arith)

theorem VerifyContext.sRead8 {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    ∀ j < 4, InRegions (s.rd ++ s.wr) (off sig (32 + 8 * j)) 8 :=
  fun j _ => by
    rw [show off sig (32 + 8 * j) = off (off sig 32) (8 * j) from (Offset.add_add _ _ _).symm]
    exact h.scalarRead _ (by omega_arith)

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

theorem testResult_ok {s : State} (b : Bool) (hs : s.gpr .rax = signWord b) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

theorem decodedThen_ok {s : State} {base : Addr} {p : Option Spec.Ed25519.Point}
    {next : Prog isa} {P : State → Prop} (hr : DecodeResult base p s)
    (hn : ∀ t, Keeps [] s t → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, Keeps [] s t → p = some a → point (env t.mem base) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  rw [decodedThen]
  cases hp : p with
  | none =>
    rw [hp] at hr
    refine WP.seq (WP.mono (testResult_ok false hr) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite false (by simp only [eval, tz, Option.map_some, Bool.not_false, Bool.not_true])
    · intro h; contradiction
    · intro _; exact hn t kt hp
  | some a =>
    rw [hp] at hr
    refine WP.seq (WP.mono (testResult_ok true hr.1) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite true (by simp only [eval, tz, Option.map_some, Bool.not_true, Bool.not_false])
    · intro _; exact hy t a kt hp (by rw [kt.2.1]; exact hr.2)
    · intro h; contradiction

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.RootPair`, which only this module used -/

section

/-! ### `X25519.X86_64.Inv`, which only this module used -/

section

/-!
# X25519 on x86-64: the counter of runs of squarings

A run of squarings (`sqn`) counts in `rbx`: `rbx = k` (`setRbx_ok`), and its
decrement (`decRbx_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-! ## Runs of squarings -/

/-- `rbx = k`. -/
theorem setRbx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 k))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega_using [hk])]

/-- `rbx -= 1`, from `rbx = k + 1`: the flag `ZF` says whether `k = 0`. -/
theorem decRbx_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k = 0)) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zf : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega_using [h])]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk])] at this
      exact absurd this (by simp; omega_using [h])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb', RegUpd.gpr_setReg_self, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, zf]
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false,
    RegUpd.gpr_arithFlags], trivial, trivial, trivial, trivial⟩

end VG.Proof.X25519.X86_64

end

end


/-!
# Ed25519 on x86-64: two square roots' powers at once

`rootPower2` is `rootPower`'s addition chain for slot 2 (into slot 15) and for slot 3 (into
slot 19), each step beside its copy. Its parts that change the slots by a function of them
(`RSpec`) keep everything else but `rbx` and `clob`. Past `2^5 - 1`, its steps
`W = W^(2^n) T` run in a loop (`rootStep_ok`), reading `n` and where `T` comes from out of
`rsi` (`stepsFrom`), whose value slot 14 keeps meanwhile; `ChainInv` is what the loop keeps,
and `chainVals` the values of `W` and of the value saved, `S`, after `j` steps.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519 (sqn)
open VG.Proof.X25519.X86_64 (Outside setRbx_ok decRbx_ok)

variable {fld : Arith} [EdArith fld]

/-- `c` changes the slots by `f`, and keeps everything else but `rbx` and `clob`. -/
def RSpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scratch s base → WP isa c s fun t => RbxKeep base s t ∧ env t.mem base = f (env s.mem base)

theorem RSpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : RSpec base c₁ f)
    (h₂ : RSpec base c₂ g) : RSpec base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scratch hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem RSpec.ops (base : Addr) (ops : List FieldOp) :
    RSpec base (.block (fieldCode fld ops)) (evalOps ops) := fun _ hs =>
  WP.mono (fieldCodeWide_ok hs ops) fun _ ⟨k, e⟩ => ⟨RbxKeep.of_keep k, e⟩

/-- Slots `o` and `o'` set to `v` and `v'`. -/
abbrev upd2 (e : Env) (o o' : Slot) (v v' : Spec.X25519.Fe) : Env :=
  Function.update (Function.update e o v) o' v'

theorem sq2_eval (e : Env) {o o' : Slot} (ho : o ≠ o') (v v' : Spec.X25519.Fe) :
    evalOps [.sqr o o, .sqr o' o'] (upd2 e o o' v v') = upd2 e o o' (v * v) (v' * v') := by
  funext i
  simp only [evalOps, List.foldl_cons, List.foldl_nil, evalOp, Function.update_apply, ↓reduceIte,
    ho, Ne.symm ho]
  by_cases h₁ : i = o' <;> simp only [h₁, ↓reduceIte]
  by_cases h₂ : i = o <;> simp only [h₂, ↓reduceIte]

theorem sq2_first (e : Env) {o a o' a' : Slot} (ha : o ≠ a') :
    evalOps [.sqr o a, .sqr o' a'] e = upd2 e o o' (sqn (e a) 1) (sqn (e a') 1) := by
  funext i
  simp only [evalOps, List.foldl_cons, List.foldl_nil, evalOp, Function.update_apply, ↓reduceIte,
    Ne.symm ha]
  rfl

/-- The loop of `sqn2`, with the counter `rbx = m` and slots `o` and `o'` squared `n - m`
times since `s₀`. -/
theorem sq2Loop_ok {s₀ : State} {base : Addr} (hs₀ : Scratch s₀ base) {o o' : Slot} (ho : o ≠ o')
    (x x' : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → RbxKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) →
      WP isa (.loop (.block (fieldCode fld ([.sqr o o, .sqr o' o'] : List FieldOp) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun t =>
        RbxKeep base s₀ t ∧ env t.mem base = upd2 (env s₀.mem base) o o' (sqn x n) (sqn x' n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ RbxKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m))) ?_ m s
    ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (hk.scratch hs₀) [.sqr o o, .sqr o' o']) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (decRbx_ok (by omega_arith) ((k1.gpr _ (by decide)).trans hb))
    fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : RbxKeep base s₀ s2 := hk.trans ((RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have e2 : env s2.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) := by
    rw [m2, e1, he, sq2_eval _ ho, show n - m = (n - (m + 1)) + 1 by omega_arith]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, k2, b2, e2⟩

/-- `sqn2 o a o' a' n`: slots `o` and `o'` become slots `a` and `a'` squared `n` times. -/
theorem sqn2_spec (base : Addr) {o a o' a' : Slot} (ho : o ≠ o') (ha : o ≠ a') (n : Nat)
    (hn : 2 ≤ n) (hn' : n < 2 ^ 32) :
    RSpec base (sqn2 fld o a o' a' n) fun e => upd2 e o o' (sqn (e a) n) (sqn (e a') n) := by
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs [.sqr o a, .sqr o' a']) fun s1 ⟨k1, e1⟩ => ?_
  refine WP.mono (setRbx_ok s1 (n - 1) (by omega_arith)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : RbxKeep base s s2 := (RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine sq2Loop_ok hs ho (env s.mem base a) (env s.mem base a') n hn' (n - 1) s2 (by omega_arith)
    (by omega_arith) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega_arith, sq2_first _ ha]

/-! ## The chain's steps in a loop -/

/-- The squaring loop from `rbx = m`, slots `o` and `o'` squared `n - m` times since `s₀`,
changing no byte but theirs. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scratch s₀ base) {o o' : Slot} (ho : o ≠ o')
    (x x' : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m ≤ n → RbxKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      (∀ y, Outs [.sqr o o, .sqr o' o'] base y → s.mem y = s₀.mem y) →
      env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) →
      WP isa (.loop (.block (fieldCode fld ([.sqr o o, .sqr o' o'] : List FieldOp) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun t =>
        RbxKeep base s₀ t ∧ (∀ y, Outs [.sqr o o, .sqr o' o'] base y → t.mem y = s₀.mem y) ∧
        env t.mem base = upd2 (env s₀.mem base) o o' (sqn x n) (sqn x' n) := by
  intro m s h1 h2 hk hb hf he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m ≤ n ∧ RbxKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧ (∀ y, Outs [.sqr o o, .sqr o' o'] base y → s.mem y = s₀.mem y) ∧
    env s.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m))) ?_ m s
    ⟨h1, h2, hk, hb, hf, he⟩
  intro m s ⟨h1, h2, hk, hb, hf, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_frame (hk.scratch hs₀) [.sqr o o, .sqr o' o']) fun s1 ⟨k1, e1, f1⟩ => ?_
  refine WP.mono (decRbx_ok (by omega_arith) ((k1.gpr _ (by decide)).trans hb))
    fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : RbxKeep base s₀ s2 := hk.trans ((RbxKeep.of_keep k1).trans
    ⟨fun r _ hr => g2 r hr, rd2, wr2, by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have f2 : ∀ y, Outs [.sqr o o, .sqr o' o'] base y → s2.mem y = s₀.mem y := fun y hy => by
    rw [m2, f1 y hy, hf y hy]
  have e2 : env s2.mem base = upd2 (env s₀.mem base) o o' (sqn x (n - m)) (sqn x' (n - m)) := by
    rw [m2, e1, he, sq2_eval _ ho, show n - m = (n - (m + 1)) + 1 by omega_arith]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, f2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, k2, b2, f2, e2⟩

/-- A step of `rootSteps` on one lane's `W` and `S`. -/
def stepVals (st : Nat × Bool × Bool) (p : Spec.X25519.Fe × Spec.X25519.Fe) :
    Spec.X25519.Fe × Spec.X25519.Fe :=
  let w := sqn p.1 st.1 * (if st.2.1 then p.2 else p.1)
  (w, if st.2.2 then w else p.2)

/-- The first `j` steps. -/
def chainVals (p : Spec.X25519.Fe × Spec.X25519.Fe) (j : Nat) : Spec.X25519.Fe × Spec.X25519.Fe :=
  (rootSteps.take j).foldl (fun q st => stepVals st q) p

/-- `rootSteps`' words, from step `j`. -/
def stepsFrom (j : Nat) : Nat :=
  (rootSteps.drop j).foldr (fun st acc => st.1 + 128 * st.2.1.toNat + 256 * st.2.2.toNat + 512 * acc) 0

/-- What `rootStep` reads of `rsi`, for each step. -/
theorem stepsFrom_facts : ∀ j < 7,
    (BitVec.ofNat 64 (stepsFrom j) &&& 128 == 0) = !(rootSteps.getD j (0, false, false)).2.1 ∧
    (BitVec.ofNat 64 (stepsFrom j) &&& 256 == 0) = !(rootSteps.getD j (0, false, false)).2.2 ∧
    BitVec.ofNat 64 (stepsFrom j) &&& 127 = BitVec.ofNat 64 (rootSteps.getD j (0, false, false)).1 ∧
    1 ≤ (rootSteps.getD j (0, false, false)).1 ∧ (rootSteps.getD j (0, false, false)).1 < 2 ^ 32 ∧
    BitVec.ofNat 64 (stepsFrom j) >>> 9 = BitVec.ofNat 64 (stepsFrom (j + 1)) ∧
    (BitVec.ofNat 64 (stepsFrom (j + 1)) == 0) = decide (j + 1 = 7) := by
  decide

/-- The chain's values after a step, from those before. -/
theorem step_env (e : Env) (n : Nat) (u v : Bool) :
    let e₁ := evalOps (if u then [.copy 16 17, .copy 20 21] else [.copy 16 15, .copy 20 19]) e
    let e₂ := upd2 e₁ 15 19 (sqn (e₁ 15) n) (sqn (e₁ 19) n)
    let e₃ := evalOps [.mul 15 15 16, .mul 19 19 20] e₂
    let e₄ := if v then evalOps [.copy 17 15, .copy 21 19] e₃ else e₃
    (e₄ 15, e₄ 17) = stepVals (n, u, v) (e 15, e 17) ∧
      (e₄ 19, e₄ 21) = stepVals (n, u, v) (e 19, e 21) ∧ e₄ 2 = e 2 ∧ e₄ 3 = e 3 := by
  cases u <;> cases v <;>
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, stepVals, Bool.false_eq_true, ↓reduceIte, and_self]

theorem chainVals_succ (p : Spec.X25519.Fe × Spec.X25519.Fe) {j : Nat} (hj : j < 7) :
    chainVals p (j + 1) = stepVals (rootSteps.getD j (0, false, false)) (chainVals p j) := by
  have : rootSteps.take (j + 1) = rootSteps.take j ++ [rootSteps.getD j (0, false, false)] := by
    have h : ∀ j < 7, rootSteps.take (j + 1) = rootSteps.take j ++ [rootSteps.getD j (0, false, false)] := by
      decide
    exact h j hj
  rw [chainVals, this, List.foldl_append]
  rfl

/-- The two-lane field program `A` or `B`, as the flag `ne` says. -/
theorem iteOps_ok {s : State} {base : Addr} (hs : Scratch s base) (b : Bool)
    (hc : isa.eval .ne s = some b) (A B : List FieldOp) :
    WP isa (.ite .ne (.block (fieldCode fld A)) (.block (fieldCode fld B))) s fun t => Keep base s t ∧
      env t.mem base = evalOps (if b then A else B) (env s.mem base) ∧
      ∀ x, Outs (if b then A else B) base x → t.mem x = s.mem x := by
  refine WP.ite b hc (fun h => ?_) (fun h => ?_) <;> subst h <;> exact fieldCodeWide_frame hs _

/-- The word at byte 512 (slot 14's first) of a program writing only slots past it. -/
theorem word14_of_outs {ops : List FieldOp} (hops : ∀ op ∈ ops, 520 ≤ offset op.out) {base : Addr}
    {m m' : Mem} (hf : ∀ x, Outs ops base x → m' x = m x) :
    X25519.X86_64.word m' base 512 = X25519.X86_64.word m base 512 :=
  Mem.readW_congr (w := 64) fun i hi => hf _ fun op hop => by
    have := hops op hop
    rw [X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith

/-- What the loop keeps of the state before it (`s₁`), and the chain after `j` of its steps. -/
structure ChainInv (base : Addr) (s₁ s : State) (r₀ : BitVec 64) (a b a' b' : Spec.X25519.Fe)
    (j : Nat) : Prop where
  gpr : ∀ r, r ∉ X25519.X86_64.clob → r ≠ .rbx → r ≠ .rsi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  mem : Outside base 64 704 s₁.mem s.mem
  saved : X25519.X86_64.word s.mem base 512 = r₀
  rsi : s.gpr .rsi = BitVec.ofNat 64 (stepsFrom j)
  lane : (env s.mem base 15, env s.mem base 17) = chainVals (a, b) j
  lane' : (env s.mem base 19, env s.mem base 21) = chainVals (a', b') j
  x2 : env s.mem base 2 = env s₁.mem base 2
  x3 : env s.mem base 3 = env s₁.mem base 3

theorem ChainInv.scratch {base : Addr} {s₁ s : State} {r₀ : BitVec 64} {a b a' b' : Spec.X25519.Fe}
    {j : Nat} (h : ChainInv base s₁ s r₀ a b a' b' j) (hs : Scratch s₁ base) : Scratch s base :=
  ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `rootStep` runs step `j` of `rootSteps`, and sets ZF past the last. -/
theorem rootStep_ok {s₁ s : State} {base : Addr} (hs₁ : Scratch s₁ base) {r₀ : BitVec 64}
    {a b a' b' : Spec.X25519.Fe} {j : Nat} (hj : j < 7) (h : ChainInv base s₁ s r₀ a b a' b' j) :
    WP isa (rootStep fld) s fun t => ChainInv base s₁ t r₀ a b a' b' (j + 1) ∧
      t.zf = some (decide (j + 1 = 7)) := by
  have hs := h.scratch hs₁
  have hn := hs.nowrap
  obtain ⟨fu, fv, fn, fn1, fn2, fsh, fz⟩ := stepsFrom_facts j hj
  generalize hst : rootSteps.getD j (0, false, false) = st at fu fv fn fn1 fn2
  obtain ⟨n, u, v⟩ := st
  dsimp only at fu fv fn fn1 fn2
  unfold rootStep
  -- `test rsi, 128`.
  refine WP.seq (WP.mono (show WP isa (.block [.alu .test .rsi (.imm 128)]) s fun t =>
      t.zf = some !u ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, h.rsi,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
      show BitVec.signExtend 64 (128 : BitVec 32) = 128 by decide, fu]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩) fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂]; exact hs.rdi, wr₂ ▸ hs.wr, hn⟩
  -- `T`.
  refine WP.seq (WP.mono (iteOps_ok hs₂ u (by simp only [eval, z₂, Option.map_some, Bool.not_not])
    [.copy 16 17, .copy 20 21] [.copy 16 15, .copy 20 19]) fun s₃ ⟨k₃, e₃, f₃⟩ => ?_)
  have hs₃ := hs₂.of_keep k₃
  -- `rbx = n`.
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rbx (.reg .rsi), .alu .and .rbx (.imm 127)]) s₃
      fun t => t.gpr .rbx = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rbx → t.gpr r = s₃.gpr r) ∧ t.mem = s₃.mem ∧
        t.rd = s₃.rd ∧ t.wr = s₃.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self,
      RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg,
      RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
      show BitVec.signExtend 64 (127 : BitVec 32) = 127 by decide]
    refine ⟨?_, fun r hr => ?_, trivial, trivial, trivial⟩
    · rw [k₃.gpr _ (by decide), g₂, h.rsi, fn]
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  have hs₄ : Scratch s₄ base := ⟨by rw [g₄ _ (by decide)]; exact hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  -- The squarings.
  have k₄ : RbxKeep base s₄ s₄ := ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
  refine WP.seq (WP.mono (sqLoop_ok (fld := fld) hs₄ (o := 15) (o' := 19) (by decide)
    (env s₄.mem base 15) (env s₄.mem base 19) n fn2 n s₄ fn1 (Nat.le_refl _) k₄ b₄ (fun _ _ => rfl)
    (by rw [Nat.sub_self]; simp only [upd2, sqn, Function.update_eq_self]))
    fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  have hs₅ := k₅.scratch hs₄
  -- The products, and `test rsi, 256`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_frame hs₅ [.mul 15 15 16, .mul 19 19 20])
    fun s₆ ⟨k₆, e₆, f₆⟩ => ?_
  have rsi₆ : s₆.gpr .rsi = BitVec.ofNat 64 (stepsFrom j) := by
    rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide) (by decide), g₄ _ (by decide),
      k₃.gpr _ (by decide), g₂, h.rsi]
  refine WP.mono (show WP isa (.block [.alu .test .rsi (.imm 256)]) s₆ fun t =>
      t.zf = some !v ∧ t.gpr = s₆.gpr ∧ t.mem = s₆.mem ∧ t.rd = s₆.rd ∧ t.wr = s₆.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, rsi₆,
      Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
      show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide, fv]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩) fun s₇ ⟨z₇, g₇, m₇, rd₇, wr₇⟩ => ?_
  have hs₇ : Scratch s₇ base := ⟨by rw [g₇]; exact (hs₅.of_keep k₆).rdi, wr₇ ▸ (hs₅.of_keep k₆).wr, hn⟩
  -- `S`.
  refine WP.seq (WP.mono (iteOps_ok hs₇ v (by simp only [eval, z₇, Option.map_some, Bool.not_not])
    [.copy 17 15, .copy 21 19] []) fun s₈ ⟨k₈, e₈, f₈⟩ => ?_)
  have rsi₈ : s₈.gpr .rsi = BitVec.ofNat 64 (stepsFrom j) := by rw [k₈.gpr _ (by decide), g₇, rsi₆]
  -- `rsi` to the next step.
  refine WP.mono (show WP isa (.block [.shift .shr .rsi 9, .alu .test .rsi (.reg .rsi)]) s₈ fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (stepsFrom (j + 1)) ∧ t.zf = some (decide (j + 1 = 7)) ∧
        (∀ r, r ≠ .rsi → t.gpr r = s₈.gpr r) ∧ t.mem = s₈.mem ∧ t.rd = s₈.rd ∧ t.wr = s₈.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec, readSrc, execAlu, execShift, rsi₈,
      show (1 ≤ 9 ∧ 9 ≤ 63) = True from by decide, ite_true, runStep_some, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, BitVec.and_self, fsh, fz, Option.bind_some]
    refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun t ⟨rsiT, zT, gT, mT, rdT, wrT⟩ => ?_
  have eT : env t.mem base = (let e₁ := evalOps (if u then [.copy 16 17, .copy 20 21] else
        [.copy 16 15, .copy 20 19]) (env s.mem base)
      let e₂ := upd2 e₁ 15 19 (sqn (e₁ 15) n) (sqn (e₁ 19) n)
      let e₃ := evalOps [.mul 15 15 16, .mul 19 19 20] e₂
      if v then evalOps [.copy 17 15, .copy 21 19] e₃ else e₃) := by
    have hv4 : ∀ e, evalOps (if v then [.copy 17 15, .copy 21 19] else []) e =
        if v then evalOps [.copy 17 15, .copy 21 19] e else e := fun e => by cases v <;> rfl
    rw [mT, e₈, hv4, m₇, e₆, e₅, m₄, e₃, m₂]
  obtain ⟨l₁, l₂, l₃, l₄⟩ := step_env (env s.mem base) n u v
  rw [← eT] at l₁ l₂ l₃ l₄
  have hu : ∀ op ∈ (if u then [FieldOp.copy 16 17, .copy 20 21] else [.copy 16 15, .copy 20 19]),
      520 ≤ offset op.out := by cases u <;> decide
  have hv : ∀ op ∈ (if v then [FieldOp.copy 17 15, .copy 21 19] else []), 520 ≤ offset op.out := by
    cases v <;> decide
  refine ⟨⟨fun r hr hb hs' => ?_, ?_, ?_, ?_, ?_, rsiT, ?_, ?_, ?_, ?_⟩, zT⟩
  · rw [gT r hs', k₈.gpr r hr, g₇, k₆.gpr r hr, k₅.gpr r hr hb, g₄ r hb, k₃.gpr r hr, g₂,
      h.gpr r hr hb hs']
  · rw [rdT, k₈.rd, rd₇, k₆.rd, k₅.rd, rd₄, k₃.rd, rd₂, h.rd]
  · rw [wrT, k₈.wr, wr₇, k₆.wr, k₅.wr, wr₄, k₃.wr, wr₂, h.wr]
  · refine h.mem.trans (fun x _ => by rw [m₂]) |>.trans k₃.mem |>.trans (fun x _ => by rw [m₄])
      |>.trans k₅.mem |>.trans k₆.mem |>.trans (fun x _ => by rw [m₇]) |>.trans k₈.mem
      |>.trans (fun x _ => by rw [mT])
  · rw [mT, word14_of_outs hv f₈, m₇, word14_of_outs (by decide) f₆, word14_of_outs (by decide) f₅,
      m₄, word14_of_outs hu f₃, m₂, h.saved]
  · rw [chainVals_succ _ hj, hst, ← h.lane]; exact l₁
  · rw [chainVals_succ _ hj, hst, ← h.lane']; exact l₂
  · rw [l₃, h.x2]
  · rw [l₄, h.x3]

/-- `2^5 - 1`, then the steps, the last two squarings and the product: `rootPower`, for each
lane. -/
theorem chain_rootPower (e : Env) (b b' : Spec.X25519.Fe) :
    let e₃ := evalOps [.mul 15 2 15, .mul 19 3 19, .mul 14 14 15, .mul 18 18 19, .sqr 16 14, .sqr 20 18,
      .mul 15 15 16, .mul 19 19 20] (evalOps [.sqr 15 14, .sqr 19 18, .sqr 15 15, .sqr 19 19]
        (evalOps [.sqr 14 2, .sqr 18 3] e))
    sqn (chainVals (e₃ 15, b) 7).1 2 * e₃ 2 = VG.Proof.Ed25519.rootPower (e 2) ∧
      sqn (chainVals (e₃ 19, b') 7).1 2 * e₃ 3 = VG.Proof.Ed25519.rootPower (e 3) := by
  simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, evalOp,
    Function.update_apply, ↓reduceIte, chainVals, rootSteps, List.take, List.foldl, stepVals]
  exact ⟨rfl, rfl⟩

/-- `rootPowerLoop2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3)
into slot 19. -/
theorem rootPowerLoop2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPowerLoop2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  have hn := hs.nowrap
  unfold rootPowerLoop2
  -- `2^5 - 1`.
  refine WP.seq (WP.mono (fieldCodeWide_ok hs _) fun s₁ ⟨k₁, e₁⟩ => ?_)
  have hs₁ := hs.of_keep k₁
  refine WP.seq (WP.mono (fieldCodeWide_ok hs₁ _) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have hs₂ := hs₁.of_keep k₂
  refine WP.seq (WP.mono (fieldCodeWide_ok hs₂ _) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ := hs₂.of_keep k₃
  -- `rsi` into slot 14, the steps into `rsi`.
  have hw : InRegions s₃.wr (X25519.X86_64.off base 512) 8 :=
    ⟨_, hs₃.wr, Offset.contains_base base (show 512 + 8 ≤ 8192 by decide) (by omega_arith)⟩
  refine WP.seq (WP.mono (show WP isa (.block [.store (Impl.X25519.X86_64.sc (offset 14)) .rsi,
      .movImm64 .rsi (BitVec.ofNat 64 rootStepsWord)]) s₃ fun t =>
      t.mem = s₃.mem.writeW (X25519.X86_64.off base 512) (s₃.gpr .rsi) ∧
      t.gpr .rsi = BitVec.ofNat 64 rootStepsWord ∧ (∀ r, r ≠ .rsi → t.gpr r = s₃.gpr r) ∧
      t.rd = s₃.rd ∧ t.wr = s₃.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, X25519.X86_64.ea_sc, hs₃.rdi,
      State.store64, show offset 14 = 512 from rfl, hw, ite_true, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg]
    refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₄ ⟨m₄, rsi₄, g₄, rd₄, wr₄⟩ => ?_)
  have O₄ : Outside base 512 8 s₃.mem s₄.mem := by
    rw [m₄]; exact X25519.X86_64.writeW_outside _ _ _ (by omega_arith)
  have v₄ : ∀ i : Slot, i ≠ 14 → env s₄.mem base i = env s₃.mem base i := fun i hi => by
    have : i.val ≠ 14 := fun h => hi (Fin.ext h)
    simp only [env, X25519.X86_64.F]
    rw [O₄.fe (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith)]
  have I₀ : ChainInv base s₃ s₄ (s₃.gpr .rsi) (env s₃.mem base 15) (env s₃.mem base 17)
      (env s₃.mem base 19) (env s₃.mem base 21) 0 :=
    ⟨fun r _ _ hr => g₄ r hr, rd₄, wr₄, O₄.mono (by decide) (by decide),
      by rw [m₄]; exact Mem.readW_writeW_self64 _ _ _, rsi₄,
      by rw [v₄ 15 (by decide), v₄ 17 (by decide)]; rfl,
      by rw [v₄ 19 (by decide), v₄ 21 (by decide)]; rfl, v₄ 2 (by decide), v₄ 3 (by decide)⟩
  -- The steps.
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => ChainInv base s₃ t (s₃.gpr .rsi)
      (env s₃.mem base 15) (env s₃.mem base 17) (env s₃.mem base 19) (env s₃.mem base 21) 7)
    (fun m t => ∃ j, j < 7 ∧ m = 7 - j ∧ ChainInv base s₃ t (s₃.gpr .rsi) (env s₃.mem base 15)
      (env s₃.mem base 17) (env s₃.mem base 19) (env s₃.mem base 21) j)
    (fun m t ⟨j, hj, hm, hI⟩ => WP.mono (rootStep_ok hs₃ hj hI) fun t' ⟨hI', z'⟩ => by
      simp only [eval, z', Option.map_some]
      by_cases h7 : j + 1 = 7
      · exact .inl ⟨by simp [h7], h7 ▸ hI'⟩
      · exact .inr ⟨by simp [h7], 7 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, hI'⟩)
    7 s₄ ⟨0, by decide, rfl, I₀⟩) fun s₅ I₅ => ?_)
  have hs₅ := I₅.scratch hs₃
  -- `rsi` back.
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rsi (.mem (Impl.X25519.X86_64.sc (offset 14)))]) s₅
      fun t => t.gpr .rsi = s₃.gpr .rsi ∧ (∀ r, r ≠ .rsi → t.gpr r = s₅.gpr r) ∧ t.mem = s₅.mem ∧
        t.rd = s₅.rd ∧ t.wr = s₅.wr by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      X25519.X86_64.readSrc_sc (show X25519.X86_64.Scr s₅ base 8192 from ⟨hs₅.rdi, hs₅.wr, hn⟩)
        (show offset 14 + 8 ≤ 8192 by decide), Option.map_some, Option.some.injEq,
      exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg]
    refine ⟨I₅.saved, fun r hr => ?_, trivial, trivial, trivial⟩
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₆ ⟨rsi₆, g₆, m₆, rd₆, wr₆⟩ => ?_)
  have hs₆ : Scratch s₆ base := ⟨by rw [g₆ _ (by decide)]; exact hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  -- The last squarings and the product.
  refine WP.seq (WP.mono (sqn2_spec (fld := fld) base (o := 15) (a := 15) (o' := 19) (a' := 19)
    (by decide) (by decide) 2 (by decide) (by decide) s₆ hs₆) fun s₇ ⟨k₇, e₇⟩ => ?_)
  refine WP.mono (fieldCodeWide_ok (k₇.scratch hs₆) _) fun t ⟨k₈, e₈⟩ => ?_
  refine ⟨⟨fun r hr hb => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k₈.gpr r hr, k₇.gpr r hr hb]
    by_cases hsi : r = .rsi
    · subst hsi; rw [rsi₆, k₃.gpr _ hr, k₂.gpr _ hr, k₁.gpr _ hr]
    · rw [g₆ r hsi, I₅.gpr r hr hb hsi, k₃.gpr _ hr, k₂.gpr _ hr, k₁.gpr _ hr]
  · rw [k₈.rd, k₇.rd, rd₆, I₅.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₈.wr, k₇.wr, wr₆, I₅.wr, k₃.wr, k₂.wr, k₁.wr]
  · exact k₁.mem.trans k₂.mem |>.trans k₃.mem |>.trans I₅.mem |>.trans (fun x _ => by rw [m₆])
      |>.trans k₇.mem |>.trans k₈.mem
  · have hl : env s₅.mem base 15 = (chainVals (env s₃.mem base 15, env s₃.mem base 17) 7).1 :=
      congrArg Prod.fst I₅.lane
    rw [← VG.Proof.Ed25519.rootPower_eq, ← (chain_rootPower (env s.mem base) (env s₃.mem base 17)
      (env s₃.mem base 21)).1, ← e₁, ← e₂, ← e₃, ← hl, ← I₅.x2, ← m₆, e₈, e₇]
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, ↓reduceIte]
  · have hl : env s₅.mem base 19 = (chainVals (env s₃.mem base 19, env s₃.mem base 21) 7).1 :=
      congrArg Prod.fst I₅.lane'
    rw [← VG.Proof.Ed25519.rootPower_eq, ← (chain_rootPower (env s.mem base) (env s₃.mem base 17)
      (env s₃.mem base 21)).2, ← e₁, ← e₂, ← e₃, ← hl, ← I₅.x3, ← m₆, e₈, e₇]
    simp only [Fin.isValue, Fin.reduceEq, evalOps, List.foldl_cons, List.foldl_nil, evalOp, upd2,
      Function.update_apply, ↓reduceIte]

theorem rootPowerUnrolled2_spec (base : Addr) :
    ∃ f, RSpec base (rootPowerUnrolled2 fld) f ∧ ∀ e, f e 15 = VG.Proof.Ed25519.rootPower (e 2) ∧
      f e 19 = VG.Proof.Ed25519.rootPower (e 3) := by
  refine ⟨_, (RSpec.ops base _).seq <| (RSpec.ops base _).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 5 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 10 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 20 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 10 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 50 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 100 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 50 (by decide) (by decide)).seq <| (RSpec.ops base _).seq <|
    (sqn2_spec base (by decide) (by decide) 2 (by decide) (by decide)).seq (RSpec.ops base _),
    fun e => ⟨?_, ?_⟩⟩
  all_goals
    dsimp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, upd2, evalOps, List.foldl_cons, List.foldl_nil,
      evalOp, Function.update_apply]
    rfl

/-- `rootPowerUnrolled2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3) into
slot 19. -/
theorem rootPowerUnrolled2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPowerUnrolled2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  obtain ⟨f, hf, hv⟩ := rootPowerUnrolled2_spec (fld := fld) base
  refine WP.mono (hf s hs) fun t ⟨k, e⟩ => ⟨k, ?_, ?_⟩
  · rw [e, (hv _).1, VG.Proof.Ed25519.rootPower_eq]
  · rw [e, (hv _).2, VG.Proof.Ed25519.rootPower_eq]

/-- `rootPower2` in the scratch: A's power (of slot 2) into slot 15 and R's (of slot 3) into
slot 19. -/
theorem rootPower2_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (rootPower2 fld) s fun t => RbxKeep base s t ∧
      env t.mem base 15 = Spec.X25519.pow (env s.mem base 2) ((Spec.X25519.P - 5) / 8) ∧
      env t.mem base 19 = Spec.X25519.pow (env s.mem base 3) ((Spec.X25519.P - 5) / 8) := by
  unfold rootPower2
  split
  · exact rootPowerLoop2_ok hs
  · exact rootPowerUnrolled2_ok hs

end VG.Proof.Ed25519.X86_64

end

end

/-!
# Ed25519 verification on x86-64: both square roots' powers first

`decodePowers` loads the y-coordinates of R and of A, computes the input `u v⁷` of each one's
square root's power, and both powers at once (`rootPower2_ok`): A's into slot 15, where
decoding A takes it, and R's into byte 7680 of the scratch, which decoding A keeps and
`powerRestore` moves back into slot 15 before R is decoded.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside clob F fe fe_st4 st4_outside)

variable {fld : Arith} [EdArith fld]

theorem rootInput3_eval (e : Env) :
    evalOps (rootInputOps 3) e 3 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 :=
  congrArg (rootU (e 1) * ·) (pow_seven _)

theorem rootInput2_eval (e : Env) :
    evalOps (rootInputOps 2) e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 ∧
    evalOps (rootInputOps 2) e 3 = e 3 :=
  ⟨congrArg (rootU (e 1) * ·) (pow_seven _), rfl⟩

private theorem loadY_clob : ∀ r ∈ [Reg.r8, .r9, .r10, .r11, .rax], r ∈ clob := by decide

/-- The y-coordinate at `p` into slot 1, and the power's input of it into slot `o`. -/
theorem decodeInput_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) (o : Slot) :
    WP isa (.block (decodeInput fld o)) s fun t => Keep base s t ∧
      env t.mem base = evalOps (rootInputOps o)
        (Function.update (env s.mem base) 1 (decodedY (Spec.Ed25519.bytesAt s.mem p 32))) := by
  rw [decodeInput, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadY_ok s p hp hr) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  have has : Scratch a base := hs.of_keeps ka (by decide)
  refine WP.mono (storeWordsWide_ok has 1) fun b ⟨bm, bg, brd, bwr⟩ => ?_
  have bo : Outside base (offset 1) 32 a.mem b.mem := by
    rw [bm]; exact st4_outside _ _ (by decide) _ _ _ _
  have be : env b.mem base =
      Function.update (env s.mem base) 1 (decodedY (Spec.Ed25519.bytesAt s.mem p 32)) := by
    rw [env_update 1 bo, ka.2.1]
    refine congrArg (Function.update (env s.mem base) 1) ?_
    rw [F, bm, fe_st4 _ _ (by decide), av]
    rfl
  have kab : Keep base s b :=
    ⟨fun r hr => (bg r).trans (ka.1 r fun hm => hr (loadY_clob r hm)), brd.trans ka.2.2.1,
      bwr.trans ka.2.2.2, by rw [← ka.2.1]; exact bo.mono (by decide) (by decide)⟩
  refine WP.mono (fieldCodeWide_ok (hs.of_keep kab) (rootInputOps o)) fun t ⟨kt, vt⟩ => ?_
  exact ⟨kab.trans kt, by rw [vt, be]⟩

theorem movRaxRdi_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi)]) s fun t => t.gpr .rax = s.gpr .rdi ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem rax_base {s : State} {base : Addr} (hs : Scratch s base) (h : s.gpr .rax = s.gpr .rdi) :
    s.gpr .rax = off base 0 := by
  rw [h, hs.rdi]
  exact (BitVec.add_zero base).symm

/-- Slot 19 to byte 7680. -/
theorem powerSave_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block powerSave) s fun t => PowersKeep base 7680 32 s t ∧
      env t.mem base = env s.mem base ∧ F t.mem base 7680 = env s.mem base 19 := by
  rw [powerSave, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movRaxRdi_ok s) fun a ⟨ap, ka⟩ => ?_
  have has : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadsFieldWide_ok has 19) fun b ⟨bv, kb⟩ => ?_
  have hbs : Scratch b base := has.of_keeps kb (by decide)
  have bp : b.gpr .rax = off base 0 :=
    rax_base hbs ((kb.1 _ (by decide)).trans (ap.trans (ka.1 _ (by decide)).symm) |>.trans
      (kb.1 _ (by decide)).symm)
  refine WP.mono (tableWords_ok hbs bp 7680 (by decide)) fun t ⟨tm, tg, trd, twr⟩ => ?_
  rw [Nat.zero_add] at tm
  have hto : Outside base 7680 32 b.mem t.mem := by
    rw [tm]; exact st4_outside _ _ (by decide) _ _ _ _
  have sm : b.mem = s.mem := kb.2.1.trans ka.2.1
  refine ⟨⟨fun r _ _ hr => (congrFun tg r).trans ((kb.1 r fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)).trans
      (ka.1 r fun hm => hr (by rw [List.mem_singleton.mp hm]; decide))),
    trd.trans (kb.2.2.1.trans ka.2.2.1), twr.trans (kb.2.2.2.trans ka.2.2.2),
    TableFrame.table (sm ▸ hto)⟩, by rw [table_env hto (by decide), sm], ?_⟩
  change F t.mem base 7680 = F s.mem base (offset 19)
  rw [F, F, tm, fe_st4 _ _ (by decide), bv, ka.2.1]

/-- Byte 7680 back to slot 15. -/
theorem powerRestore_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block powerRestore) s fun t => Keep base s t ∧
      env t.mem base = Function.update (env s.mem base) 15 (F s.mem base 7680) := by
  rw [powerRestore, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movRaxRdi_ok s) fun a ⟨ap, ka⟩ => ?_
  have has : Scratch a base := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok has (rax_base has ((ap.trans (ka.1 _ (by decide)).symm))) 7680
    (by decide)) fun b ⟨bv, kb⟩ => ?_
  refine WP.mono (storeWordsWide_ok (has.of_keeps kb (by decide)) 15) fun t ⟨tm, tg, trd, twr⟩ => ?_
  have hto : Outside base (offset 15) 32 b.mem t.mem := by
    rw [tm]; exact st4_outside _ _ (by decide) _ _ _ _
  have sm : b.mem = s.mem := kb.2.1.trans ka.2.1
  refine ⟨⟨fun r hr => (tg r).trans ((kb.1 r fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)).trans
      (ka.1 r fun hm => hr (by rw [List.mem_singleton.mp hm]; decide))),
    trd.trans (kb.2.2.1.trans ka.2.2.1), twr.trans (kb.2.2.2.trans ka.2.2.2),
    sm ▸ hto.mono (by decide) (by decide)⟩, ?_⟩
  rw [env_update 15 hto, sm]
  refine congrArg (Function.update (env s.mem base) 15) ?_
  rw [F, F, tm, fe_st4 _ _ (by decide), bv, Nat.zero_add, ka.2.1]

/-- Both powers: A's into slot 15 and R's into byte 7680. -/
theorem decodePowers_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (decodePowers fld) s fun t => VerifyKeep base s t ∧
      env t.mem base 15 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem pk 32)) ∧
      F t.mem base 7680 = rootPow (decodedY (Spec.Ed25519.bytesAt s.mem sig 32)) := by
  rw [decodePowers]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  refine WP.seq (WP.mono (decodeInput_ok (fld := fld) ha.scratch (ap.trans h.sigHeader) ha.rRead 3)
    fun b ⟨kb, vb⟩ => ?_)
  have kbp : VerifyKeep base a b := PowersKeep.of_keep kb
  have hb := ha.of_keep kbp
  refine WP.seq (WP.mono (loadPointer_ok hb.scratch .rdx 7936 (by decide)) fun c ⟨cp, kc⟩ => ?_)
  have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
  have hc := hb.of_keep kcp
  refine WP.seq (WP.mono (decodeInput_ok (fld := fld) hc.scratch (cp.trans hb.pkHeader) hc.pkRead 2)
    fun d ⟨kd, vd⟩ => ?_)
  have kdp : VerifyKeep base c d := PowersKeep.of_keep kd
  have hd := hc.of_keep kdp
  refine WP.seq (WP.mono (rootPower2_ok hd.scratch) fun e ⟨ke, e15, e19⟩ => ?_)
  have kep : VerifyKeep base d e := PowersKeep.of_rbx ke
  refine WP.mono (powerSave_ok (kep.scratch hd.scratch)) fun t ⟨kt, tv, tf⟩ => ?_
  have ktp : VerifyKeep base e t := kt.mono (by decide) (by decide)
  have bsig : Spec.Ed25519.bytesAt a.mem sig 32 = Spec.Ed25519.bytesAt s.mem sig 32 :=
    verifyKeep_bytes kap h.rFar
  have bpk : Spec.Ed25519.bytesAt c.mem pk 32 = Spec.Ed25519.bytesAt s.mem pk 32 :=
    verifyKeep_bytes ((kap.trans kbp).trans kcp) h.pkFar
  have d2 : env d.mem base 2 = rootU (decodedY (Spec.Ed25519.bytesAt s.mem pk 32)) *
      Spec.X25519.pow (rootV (decodedY (Spec.Ed25519.bytesAt s.mem pk 32))) 7 := by
    rw [vd, (rootInput2_eval _).1, Function.update_self, bpk]
  have d3 : env d.mem base 3 = rootU (decodedY (Spec.Ed25519.bytesAt s.mem sig 32)) *
      Spec.X25519.pow (rootV (decodedY (Spec.Ed25519.bytesAt s.mem sig 32))) 7 := by
    rw [vd, (rootInput2_eval _).2, Function.update_of_ne (by decide), kc.2.1, vb, rootInput3_eval,
      Function.update_self, bsig]
  refine ⟨(((((kap.trans kbp).trans kcp).trans kdp).trans kep).trans ktp), ?_, ?_⟩
  · rw [tv, e15, d2]; rfl
  · rw [tf, e19, d3]; rfl

/-! ## Constant time -/

private theorem seq_pub {P Q : State → Prop} {c c' : Prog isa}
    (hct : RelCT isa (fun s t => P s ∧ P t) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s Q)
    (hn : RelCT isa (fun s t => Q s ∧ Q t) c' (fun _ _ => True)) :
    RelCT isa (fun s t => P s ∧ P t) (.seq c c') (fun _ _ => True) := by
  have hp := VG.RelCT.wp hct (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) hn

private theorem rdi_rdx_agree {base p : Addr} {s t : State} (hs : s.gpr .rdi = base)
    (ht : t.gpr .rdi = base) (ps : s.gpr .rdx = p) (pt : t.gpr .rdx = p) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rdx]) s t := Taint.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.trans ht.symm
  · exact ps.trans pt.symm)

/-- `decodePowers`' trace, between states with the same context (`hc`), which their keeping
(`hk`) preserves. -/
theorem decodePowers_ct (base pk sig challenge : Addr) (P : State → Prop)
    (hc : ∀ s, P s → VerifyContext s base pk sig challenge)
    (hk : ∀ s t, P s → VerifyKeep base s t → P t) :
    RelCT isa (fun s t => P s ∧ P t) (decodePowers fld) (fun _ _ => True) := by
  have rdiCT {Q : State → Prop} (hq : ∀ s, Q s → P s) {c : Prog isa}
      (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
        (VG.X86_64.taint.check (Taint.ofRegs [.rdi]) c hc).isSome = true) :
      RelCT isa (fun s t => Q s ∧ Q t) c (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree (hc _ (hq _ h.1)).scratch.rdi
      (hc _ (hq _ h.2)).scratch.rdi) h
  have loadWP (d : Nat) (p : Addr) (hd : d + 8 ≤ 8192)
      (hp : ∀ s, P s → s.mem.readW (off base d) 64 = p) (s : State) (h : P s) :
      WP isa (.block [.mov .rdx (.mem (Impl.X25519.X86_64.sc d))]) s fun t => P t ∧ t.gpr .rdx = p := by
    refine WP.mono (loadPointer_ok (hc s h).scratch .rdx d hd) fun t ⟨tp, kt⟩ => ?_
    exact ⟨hk s t h (PowersKeep.of_keeps kt (by decide)), tp.trans (hp s h)⟩
  have inputCT {o : Slot} {p : Addr} (h : ∃ hc : VG.Taint.Hint VG.X86_64.Taint.T,
      (VG.X86_64.taint.check (Taint.ofRegs [.rdi, .rdx]) (.block (decodeInput fld o)) hc).isSome = true) :
      RelCT isa (fun s t => (P s ∧ s.gpr .rdx = p) ∧ (P t ∧ t.gpr .rdx = p))
        (.block (decodeInput fld o)) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi, .rdx]) (fun _ _ h => rdi_rdx_agree (hc _ h.1.1).scratch.rdi
      (hc _ h.2.1).scratch.rdi h.1.2 h.2.2) h
  have inputWP (o : Slot) {p : Addr} (hr : ∀ s, P s → ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8)
      (s : State) (h : P s ∧ s.gpr .rdx = p) : WP isa (.block (decodeInput fld o)) s P :=
    WP.mono (decodeInput_ok (hc s h.1).scratch h.2 (hr s h.1) o) fun t ⟨kt, _⟩ =>
      hk s t h.1 (PowersKeep.of_keep kt)
  rw [decodePowers]
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (loadWP 7944 sig (by decide) fun s h => (hc s h).sigHeader) ?_
  refine seq_pub (inputCT (by fld_taint_decide)) (inputWP 3 fun s h => (hc s h).rRead) ?_
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (loadWP 7936 pk (by decide) fun s h => (hc s h).pkHeader) ?_
  refine seq_pub (inputCT (by fld_taint_decide)) (inputWP 2 fun s h => (hc s h).pkRead) ?_
  refine seq_pub (rdiCT (fun _ h => h) (by fld_taint_decide))
    (fun s h => WP.mono (rootPower2_ok (fld := fld) (hc s h).scratch) fun t ⟨kt, _⟩ =>
      hk s t h (PowersKeep.of_rbx kt)) ?_
  exact rdiCT (fun _ h => h) (by fld_taint_decide)

theorem powerRestore_ct (base : Addr) :
    RelCT isa (fun s t => s.gpr .rdi = base ∧ t.gpr .rdi = base) (.block powerRestore)
      (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
  exact fun _ _ h => rdi_agree h.1 h.2

end VG.Proof.Ed25519.X86_64
