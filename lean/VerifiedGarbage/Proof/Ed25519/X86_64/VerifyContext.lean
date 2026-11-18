module

public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Taint

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
