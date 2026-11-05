module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

-- separate module: the end's symbolic execution, built in parallel with the constant-time proofs importing `RefillLoop`

/-! # The refillable-tape search's end on x86-64

`finish`: the words written to `used` and `state` for each way the
controller ended (`results`), the parameters or zeros at `out`
(`finishOutput`), and the status returned (`returnStatus`). -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-! ## The output and the status -/

theorem returnStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa Impl.Dsa.X86_64.Generation.Refill.returnStatus s fun t =>
      t.gpr .rax = (if W 19 = 2 then 3 else W 19) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.Refill.returnStatus
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = W 19 ∧ t.zf = some (W 19 == 2) ∧
    t.mem = s.mem) ?_ rfl) fun u ⟨⟨ra, zu, mu⟩, ku⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl]
    rw [sub_beq_zero]
  by_cases h2 : W 19 = 2
  · refine WP.ite true (by simp only [eval, zu, h2, beq_self_eq_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 3 ∧ t.mem = u.mem) (by xrun) rfl)
      fun t ⟨⟨rt, mt⟩, kt⟩ => ⟨by simp only [rt, h2, ↓reduceIte], mt.trans mu, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite false (by simp only [eval, zu, beq_eq_false_iff_ne.mpr h2]) (fun hh => Bool.noConfusion hh)
      (fun _ => WP.block_nil ⟨by simp only [ra, h2, ↓reduceIte], mu, ku⟩)

/-- `finishOutput` then `returnStatus`, for any status. -/
theorem finishTail_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : (W 19 ≠ 1 ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)) :
    WP isa (.seq Impl.Dsa.X86_64.Generation.finishOutput Impl.Dsa.X86_64.Generation.Refill.returnStatus) s fun t =>
      t.gpr .rax = (if W 19 = 2 then 3 else W 19) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  obtain ⟨V, R⟩ := h.rep
  apply WP.seq
  unfold Impl.Dsa.X86_64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  have hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.2.2]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr h19])
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    unfold Impl.Dsa.X86_64.Generation.outputZero
    refine WP.seq (WP.mono (zeroArgs_ok mu.layout Ru) fun u₁ ⟨L₁, R₁, f₁, k₁⟩ => ?_)
    refine WP.mono (zeroOut_ok L₁ R₁ (by simp [upd, h6]) (by simpa [upd] using h7) (by omega) (by omega)
      (by rw [k₁.2.2]; exact hwu) o.bound o.apart) fun u₂ ⟨L₂, k₂, R₂, _, bytes₂, f₂⟩ => ?_
    refine WP.mono (returnStatus_ok L₂ R₂) fun t ⟨rt, mt, kt⟩ => ?_
    refine ⟨by simpa [upd] using rt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mt, he]; exact bytes₂
    · rw [mt, ← hm]
      exact (f₁.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp)).trans
        (f₂.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp))
    · rw [kt.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), ku.gpr (by decide)]
    · rw [kt.2.1, k₂.2.1, k₁.2.1, ku.2.1]
    · rw [kt.2.2, k₂.2.2, k₁.2.2, ku.2.2]
  · refine WP.ite true (by simp only [eval, hz, h19, beq_self_eq_true])
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    have bytesu : Spec.Rsa.bytesAt u.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun u₁ ⟨_, bt, f₁, k₁⟩ => ?_
    obtain ⟨Vu, Ru⟩ := mu.rep
    have R₁ : Rep u₁.mem p.geo.F p.geo.hash Vu W := Ru.apart o.apart f₁
    have L₁ := lay_of_rep mu.layout Ru R₁ rfl (k₁.gpr (by decide)) k₁.2.2
    refine WP.mono (returnStatus_ok L₁ R₁) fun t ⟨rt, mt, kt⟩ => ?_
    refine ⟨rt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mt, he]; exact bt
    · rw [mt, ← hm]
      exact f₁.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp)
    · rw [kt.gpr (by decide), k₁.gpr (by decide), ku.gpr (by decide)]
    · rw [kt.2.1, k₁.2.1, ku.2.1]
    · rw [kt.2.2, k₁.2.2, ku.2.2]

/-! ## The words for `used` and `state` -/

/-- The memory with `state[0]`, `state[3]` and `used[0]` written. -/
def written (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) : Mem :=
  ((m.writeW St r0).writeW (off St 24) r3).writeW U uv

/-- What the blocks writing the words read and write. -/
structure ResEnv (s : State) (F St U : Addr) : Prop where
  rsp : s.gpr .rsp = F
  ctl : ∀ k < 4, InRegions (s.rd ++ s.wr) (off F (296 + 8 * k)) 8
  frame : ∀ d, d + 8 ≤ frameBytes → InRegions (s.rd ++ s.wr) (off F d) 8
  st0 : InRegions s.wr St 8
  st3 : InRegions s.wr (off St 24) 8
  us : InRegions s.wr U 8

theorem ea_24 (t : State) (b : Reg) : t.ea { base := b, disp := 24 } = off (t.gpr b) 24 := rfl

theorem wordsEntropy_ok {s : State} {F St U : Addr} (e : ResEnv s F St U) {K c3 : BitVec 64}
    (h1 : s.mem.readW (off F 304) 64 = St) (h2 : s.mem.readW (off F 312) 64 = K)
    (h3 : ∀ a b : BitVec 64, ((s.mem.writeW St a).writeW (off St 24) b).readW (off F 320) 64 = c3)
    (h0 : ∀ a b : BitVec 64, ((s.mem.writeW St a).writeW (off St 24) b).readW (off F 296) 64 = U) :
    WP isa (.block [.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1)),
        .mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax,
        .store { base := .rcx, disp := 24 } .rdx, .mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0)), .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax]) s
      fun t => t.mem = written s.mem St U K (s.gpr .rdx) c3 ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, ea_at0', e.rsp,
    e.ctl 0 (by decide), e.ctl 1 (by decide), e.ctl 2 (by decide), e.ctl 3 (by decide), e.st0, e.st3, e.us,
    h1, h2, h3, h0, written, ea_24]

theorem wordsZero_ok {s : State} {F St U : Addr} (e : ResEnv s F St U) {c3 : BitVec 64}
    (h1 : s.mem.readW (off F 304) 64 = St)
    (h3 : ∀ a b : BitVec 64, ((s.mem.writeW St a).writeW (off St 24) b).readW (off F 320) 64 = c3)
    (h0 : ∀ a b : BitVec 64, ((s.mem.writeW St a).writeW (off St 24) b).readW (off F 296) 64 = U) :
    WP isa (.block [.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1)), .mov32 .rax (.imm 0),
        .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax,
        .mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0)), .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax]) s
      fun t => t.mem = written s.mem St U 0 0 c3 ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, ea_at0', e.rsp,
    e.ctl 0 (by decide), e.ctl 1 (by decide), e.ctl 3 (by decide), e.st0, e.st3, e.us,
    h1, h3, h0, written, ea_24, zext_ofNat (by decide : 0 < 2 ^ 32)]
  rfl

theorem wordsAccepted_ok {s : State} {F St U : Addr} (e : ResEnv s F St U) {w19 : BitVec 64}
    (h1 : s.mem.readW (off F 304) 64 = St)
    (h19 : ∀ a b : BitVec 64, ((s.mem.writeW St a).writeW (off St 24) b).readW (off F 152) 64 = w19) :
    WP isa (.block [.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1)), .mov32 .rax (.imm 0),
        .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax,
        .mov .rax (.mem (sp 152)), .alu .cmp .rax (.imm 1)]) s
      fun t => (t.mem = (s.mem.writeW St (0 : BitVec 64)).writeW (off St 24) (0 : BitVec 64) ∧
        t.zf = some (w19 == 1)) ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, ea_at0', e.rsp,
    e.ctl 1 (by decide), e.frame 152 (by decide), e.st0, e.st3,
    h1, h19, ea_24, zext_ofNat (by decide : 0 < 2 ^ 32)]
  refine ⟨rfl, ?_⟩
  rw [sub_beq_zero]

theorem usedWord_ok {s : State} {F U : Addr} (hsp : s.gpr .rsp = F) (hus : InRegions s.wr U 8)
    (h0r : InRegions (s.rd ++ s.wr) (off F 296) 8) (h0 : s.mem.readW (off F 296) 64 = U) {src : MemOp} {x : BitVec 64}
    {a : Addr} (hea : s.ea src = a) (hsr : InRegions (s.rd ++ s.wr) a 8) (hx : s.mem.readW a 64 = x) :
    WP isa (.block [.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0)),
        .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax]) s
      fun t => t.mem = s.mem.writeW U x ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, ea_at0', hsp,
    hea, hsr, hx, hus, h0r, h0]

/-! ## A seed that ran out: the next tape's length -/

theorem ranOutCmp_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (h3r : InRegions (s.rd ++ s.wr) (off F 320) 8)
    {c len : Nat} (h3 : s.mem.readW (off F 320) 64 = BitVec.ofNat 64 c) (h15 : W 15 = BitVec.ofNat 64 len)
    (hc : c ≤ len) (hl : len < 2 ^ 32) {pLen : Nat} (hp : pLen ≤ 384) :
    WP isa (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.budget pLen))),
        .alu .cmp .rcx (.reg .rdx)]) s fun t =>
      (t.gpr .rcx = BitVec.ofNat 64 (len - c) ∧ t.gpr .rdx = BitVec.ofNat 64 (32769 * pLen) ∧
        t.cf = some (decide (len - c < 32769 * pLen)) ∧ t.mem = s.mem) ∧ Keep [.rcx, .rdx] s t := by
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  refine WP.keep [.rcx, .rdx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    Impl.Dsa.X86_64.Generation.Refill.budget, ea_sp, L.rsp, L.ld (d := 120) (by decide),
    R.slot (d := 120) (k := 15) rfl (by decide) h15, h3r, h3, hsub, zext_ofNat (by omega : 32769 * pLen < 2 ^ 32),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 32769 * pLen < 2 ^ 64)]

theorem request_ok {s : State} {L B pLen : Nat} (hL : L < 2 ^ 32) (hB : B < 2 ^ 31) (hp : 256 * pLen < 2 ^ 31)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 L) (hrdx : s.gpr .rdx = BitVec.ofNat 64 B) :
    WP isa (.seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (256 * pLen))), .alu .cmp .rcx (.reg .rax)])
        (.seq (.ite .b (.block []) (.block [.mov .rax (.reg .rcx)]))
          (.seq (.block [.alu .add .rax (.reg .rax), .alu .cmp .rax (.reg .rdx)])
            (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block []))))) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (Spec.Entropy.request (256 * pLen) B L) ∧ t.mem = s.mem ∧
        Keep [.rax, .rcx, .rdx] s t := by
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (256 * pLen) ∧
    t.cf = some (decide (L < 256 * pLen)) ∧ t.mem = s.mem ∧ t.gpr .rcx = BitVec.ofNat 64 L) ?_ rfl)
    fun u ⟨⟨ra, cu, mu, rcu⟩, ku⟩ => ?_)
  · xrun [hrcx, zext_ofNat (by omega : 256 * pLen < 2 ^ 32), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : L < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 256 * pLen < 2 ^ 64)]
  have step2 : ∀ u' : State, u'.gpr .rax = BitVec.ofNat 64 (max L (256 * pLen)) → u'.mem = s.mem →
      Keep [.rax, .rcx] s u' → WP isa (.seq (.block [.alu .add .rax (.reg .rax), .alu .cmp .rax (.reg .rdx)])
        (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block []))) u' fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (Spec.Entropy.request (256 * pLen) B L) ∧ t.mem = s.mem ∧
        Keep [.rax, .rcx, .rdx] s t := by
    intro u' ra' mu' ku'
    have hrdx' : u'.gpr .rdx = BitVec.ofNat 64 B := (ku'.gpr (by decide)).trans hrdx
    have hM : 2 * max L (256 * pLen) < 2 ^ 33 := by omega
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 * max L (256 * pLen)) ∧
      t.cf = some (decide (2 * max L (256 * pLen) < B)) ∧ t.mem = u'.mem) ?_ rfl) fun w ⟨⟨rw, cw, mw⟩, kw⟩ => ?_)
    · xrun [ra', hrdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : B < 2 ^ 64)]
      refine ⟨by rw [← BitVec.ofNat_add]; congr 1; omega, ?_⟩
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      congr 2; omega
    have hrdxw : w.gpr .rdx = BitVec.ofNat 64 B := (kw.gpr (by decide)).trans hrdx'
    by_cases h2 : 2 * max L (256 * pLen) < B
    · refine WP.ite true (by simp only [eval, cw, h2, decide_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
      refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 (2 * max L (256 * pLen)) ∧
        t.mem = w.mem) (by xrun [rw]) rfl) fun t ⟨⟨rt, mt⟩, kt⟩ => ⟨?_, mt.trans (mw.trans mu'),
          ((ku'.trans kw).trans kt).mono (by decide)⟩
      rw [rt, Spec.Entropy.request, Nat.min_eq_left (by omega)]
    · refine WP.ite false (by simp only [eval, cw, h2, decide_false]) (fun hh => Bool.noConfusion hh)
        (fun _ => WP.block_nil ⟨?_, mw.trans mu', (ku'.trans kw).mono (by decide)⟩)
      rw [hrdxw, Spec.Entropy.request, Nat.min_eq_right (by omega)]
  apply WP.seq
  by_cases h1 : L < 256 * pLen
  · refine WP.ite true (by simp only [eval, cu, h1, decide_true]) (fun _ => WP.block_nil ?_)
      (fun hh => Bool.noConfusion hh)
    exact step2 u (by rw [ra, Nat.max_eq_right (by omega)]) mu ku
  · refine WP.ite false (by simp only [eval, cu, h1, decide_false]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 L ∧ t.mem = u.mem)
      (by xrun [rcu]) rfl) fun u₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
    exact step2 u₂ (by rw [r₂, Nat.max_eq_left (by omega)]) (m₂.trans mu) ((ku.trans k₂).mono (by decide))

theorem genMem_keep {p : GenerationContext} {W : Nat → BitVec 64} {s t : State} (hm : GenerationMemory p W s)
    (hmem : t.mem = s.mem) {rs : List Reg} (hk : Keep rs s t) (hsp : Reg.rsp ∉ rs) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hmem ▸ R
  exact hm.frame (lay_of_rep hm.layout R Rt rfl (hk.gpr hsp) hk.2.2) ⟨V, Rt⟩ (fun _ _ => rfl)
    (by rw [hmem]; exact Frame.refl _ _) hk.2.1 hk.2.2

theorem ranOut_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s)
    (h3r : InRegions (s.rd ++ s.wr) (off p.geo.F 320) 8) {c len : Nat}
    (h3 : s.mem.readW (off p.geo.F 320) 64 = BitVec.ofNat 64 c) (h15 : W 15 = BitVec.ofNat 64 len)
    (hc : c ≤ len) (hl : len < 2 ^ 32) {pLen : Nat} (hp : pLen ≤ 384) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.ranOut pLen) s fun t => Keep [.rax, .rcx, .rdx] s t ∧
      ((len - c < 32769 * pLen ∧ t.gpr .rdx = BitVec.ofNat 64 (Spec.Dsa.parameterRequest pLen (len - c)) ∧
          GenerationMemory p W t ∧ t.mem = s.mem) ∨
        (32769 * pLen ≤ len - c ∧ GenerationMemory p (upd W 19 2) t ∧ Frame p.changed s.mem t.mem)) := by
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.X86_64.Generation.Refill.ranOut
  refine WP.seq (WP.mono (ranOutCmp_ok hm.layout R h3r h3 h15 hc hl hp) fun u ⟨⟨rcu, rdu, cu, mu⟩, ku⟩ => ?_)
  have mmu := genMem_keep hm mu ku (by decide)
  by_cases hL : len - c < 32769 * pLen
  · refine WP.ite true (by simp only [eval, cu, hL, decide_true]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    refine WP.mono (request_ok (L := len - c) (by omega) (by omega) (by omega) rcu rdu) fun t ⟨rt, mt, kt⟩ => ?_
    have k := (ku.trans kt).mono (rs' := [.rax, .rcx, .rdx]) (by decide)
    exact ⟨k, Or.inl ⟨hL, by rw [rt]; rfl, genMem_keep hm (mt.trans mu) k (by decide), mt.trans mu⟩⟩
  · refine WP.ite false (by simp only [eval, cu, hL, decide_false]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.mono (VG.Proof.Dsa.X86_64.Generation.Refill.statusMem_ok mmu 2 (by decide)) fun t ⟨mt, ft, kt⟩ => ?_
    exact ⟨(ku.trans kt).mono (by decide), Or.inr ⟨by omega, mt, mu ▸ ft⟩⟩

theorem zeroTest_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (hm : GenerationMemory p W s) :
    WP isa (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (W 19 == 0) ∧ GenerationMemory p W t ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (W 19 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨z, mt⟩, kt⟩ => ⟨z, genMem_keep hm mt kt (by decide), mt, kt⟩
  xrun [ea_sp, hm.layout.rsp, hm.layout.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl,
    BitVec.and_self]

theorem written_frame (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) :
    Frame [⟨St, 32⟩, ⟨U, 8⟩] m (written m St U r0 r3 uv) :=
  ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_head St (by decide))).writeW (List.mem_cons_self ..) _
    (Offset.contains_base St (d := 24) (by decide) (by decide)) |>.writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (contains_head U (by decide))

theorem tapeMemory_frame {g : GenerationGeometry} {tape : GenerationTape g} {s t : State}
    (h : GenerationTapeMemory tape s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint r) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationTapeMemory tape t where
  cover := by rw [hr, hw]; exact h.cover
  bytes := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt hf hd (Nat.le_of_lt tape.size)]
    exact h.bytes

/-- The expected parameters. -/
def expectedOf (r : Spec.Dsa.ParameterSearchResult) : Option Spec.Dsa.Params :=
  match r.outcome with
  | .accepted a => some a
  | _ => none

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem state_hash : (inState s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.scrState.symm.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

theorem used_hash : (inUsed s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.usedScr.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

theorem written_regions : ∀ r ∈ [inState s₀, inUsed s₀],
    r.Disjoint ⟨refillBase s₀, frameBytes⟩ ∧ r.Disjoint ⟨(refillGeometry h).hash, oRsa⟩ ∧
      (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region).Disjoint r ∧
      r.Disjoint (ctlRegion (refillBase s₀)) ∧ r.Disjoint ⟨s₀.gpr .r9, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  have hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hrl]
  rcases hr with rfl | rfl
  · exact ⟨h.frame_disjoint (r := inState s₀) (by simp) _ (by simp), state_hash h, h.randState,
      h.frame_disjoint (r := inState s₀) (by simp) _ (by simp), h.scrState.symm.sub_right h.arena_sub⟩
  · exact ⟨h.frame_disjoint (r := inUsed s₀) (by simp) _ (by simp), used_hash h, h.usedRand.symm,
      h.frame_disjoint (r := inUsed s₀) (by simp) _ (by simp), h.usedScr.sub_right h.arena_sub⟩

theorem genMem_written {hs : GenerationTape (refillGeometry h)} (hin : HsIn h hs) {W : Nat → BitVec 64} {s t : State}
    (hm : GenerationMemory ((refillContext h).withHs hs) W s) (hf : Frame [inState s₀, inUsed s₀] s.mem t.mem)
    (hsp : t.gpr .rsp = s.gpr .rsp) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationMemory ((refillContext h).withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => ((written_regions h) r hr).1.symm)
      (fun r hr => ((written_regions h) r hr).2.1.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_frame hm.seeds hf (fun r hr => ((written_regions h) r hr).2.2.1) hr hw,
    tapeMemory_frame hm.hs hf (fun r hr => ((written_regions h) r hr).2.2.1.sub_left hin) hr hw,
    tapeMemory_frame hm.rand hf (fun r hr => ((written_regions h) r hr).2.2.1) hr hw⟩

/-- A word read past the writes to `state`. -/
theorem past_state {x : Addr} (hx : (⟨x, 8⟩ : Region).Disjoint (inState s₀)) (m : Mem) (a b : BitVec 64) :
    ((m.writeW (stackArg s₀ 1) a).writeW (off (stackArg s₀ 1) 24) b).readW x 64 = m.readW x 64 := by
  have hf : Frame [inState s₀] m ((m.writeW (stackArg s₀ 1) a).writeW (off (stackArg s₀ 1) 24) b) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_head _ (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (d := 24) (by decide) (by decide))
  exact hf.readW (Region.contains_self _ _) (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact hx)
    (by decide)

include h in
theorem ctl_state {k : Nat} (hk : k < 4) :
    (⟨off (refillBase s₀) (296 + 8 * k), 8⟩ : Region).Disjoint (inState s₀) :=
  (h.frame_disjoint (r := inState s₀) (by simp) _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))).symm.sub_left
    (Offset.sub (refillBase s₀) (e := 296) (k := 32) (by omega) (by omega))

include h in
theorem frame_state {d : Nat} (hd : d + 8 ≤ frameBytes) :
    (⟨off (refillBase s₀) d, 8⟩ : Region).Disjoint (inState s₀) :=
  (h.frame_disjoint (r := inState s₀) (by simp) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).symm.sub_left
    (Offset.sub_base (refillBase s₀) hd)

/-- After `results`: the words written to `state` and `used` over the memory `m₁` the
controller left, and the status and parameters still to output. -/
def ResultsDone (v t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (m₁ : Mem) (r0 r3 uv : BitVec 64), HsIn h hs ∧
    GenerationMemory ((refillContext h).withHs hs) W t ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem m₁ ∧
    t.mem = written m₁ (stackArg s₀ 1) (s₀.gpr .rdx) r0 r3 uv ∧
    r0 = BitVec.ofNat 64 (total h).remaining ∧ r3 = BitVec.ofNat 64 (total h).requested ∧
    uv = BitVec.ofNat 64 (total h).used ∧ (if W 19 = 2 then 3 else W 19) = BitVec.ofNat 64 (total h).status ∧
    ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
      (W 19 = 1 ∧ ∃ a, expectedOf (total h) = some a ∧
        Spec.Rsa.bytesAt t.mem (off (s₀.gpr .r9) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
          Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) a)) ∧
    t.gpr .rsp = refillBase s₀ ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem results_ok {v t : State} (hcv : ctlRegion (refillBase s₀) ∈ v.wr) (hwv : ∀ r ∈ s₀.wr, r ∈ v.wr)
    (hd : LoopDone h v t) : WP isa (Impl.Dsa.X86_64.Generation.Refill.results pBytes) t (ResultsDone h v) := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rdv, wrv, cases⟩ := hd
  have hb := refillBase_bound h
  have hp : pBytes ≤ 384 := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hframe : (⟨refillBase s₀, frameBytes⟩ : Region) ∈ v.wr := wrv ▸ hm.layout.fr
  have stv : inState s₀ ∈ v.wr := hwv _ (by rw [h.wr]; simp)
  have usv : inUsed s₀ ∈ v.wr := hwv _ (by rw [h.wr]; simp)
  have env : ∀ x : State, x.gpr .rsp = refillBase s₀ → x.wr = v.wr →
      ResEnv x (refillBase s₀) (stackArg s₀ 1) (s₀.gpr .rdx) := fun x hsp hw =>
    { rsp := hsp
      ctl := fun k hk => ⟨_, List.mem_append_right _ (hw ▸ hcv), ctl_contains _ hk⟩
      frame := fun d hd => ⟨_, List.mem_append_right _ (hw ▸ hframe),
        Offset.contains_base _ hd (by unfold frameBytes at hd; omega)⟩
      st0 := ⟨_, hw ▸ stv, contains_head _ (by decide)⟩
      st3 := ⟨_, hw ▸ stv, Offset.contains_base _ (d := 24) (by decide) (by decide)⟩
      us := ⟨_, hw ▸ usv, contains_head _ (by decide)⟩ }
  have hlen : (randTape h).bytes.length < 2 ^ 32 := by
    have hr := h.randLength
    rw [h.width] at hr
    change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat).length < _
    rw [bytesAt_length]; unfold Spec.Dsa.parameterEntropy at hr; omega
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  have ctlR : ∀ {x : State} {k : Nat}, k < 4 → ctlWord x.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k →
      (∀ a b : BitVec 64, ((x.mem.writeW (stackArg s₀ 1) a).writeW (off (stackArg s₀ 1) 24) b).readW
        (off (refillBase s₀) (296 + 8 * k)) 64 = ctlWord t.mem (refillBase s₀) k) := fun hk hx a b => by
    rw [past_state (ctl_state h hk)]; exact hx
  have ctlM : ∀ {x : State} {k : Nat}, x.mem = t.mem → ctlWord x.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k :=
    fun hx => by rw [hx]
  have eaCtl : ∀ (x : State) (k : Nat), x.gpr .rsp = refillBase s₀ →
      x.ea (Impl.Dsa.X86_64.Generation.Refill.ctl k) = off (refillBase s₀) (296 + 8 * k) := fun x k hx => by
    rw [Impl.Dsa.X86_64.Generation.Refill.ctl, ea_sp, hx]; rfl
  have eaSp : ∀ (x : State) (d : Nat), x.gpr .rsp = refillBase s₀ → x.ea (sp d) = off (refillBase s₀) d :=
    fun x d hx => by rw [ea_sp, hx]
  have packedSub : ∀ r ∈ [inState s₀, inUsed s₀],
      (⟨off (s₀.gpr .r9) packed, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r := by
    have qn : Spec.Dsa.generationQLen pBytes ≤ 32 := by unfold Spec.Dsa.generationQLen; split <;> omega
    intro r hr
    exact ((written_regions h) r hr).2.2.2.2.symm.sub_left ((refillGeometry h).part_sub
      ((refillGeometry h).small_bound (d := packed) (n := 2 * pBytes + Spec.Dsa.generationQLen pBytes) (by decide)
        (by unfold arithmeticBytes; omega)))
  unfold Impl.Dsa.X86_64.Generation.Refill.results
  refine WP.seq (WP.mono (zeroTest_ok hm) fun t₁ ⟨z₁, hm₁, mem₁, k₁⟩ => ?_)
  have sp₁ : t₁.gpr .rsp = refillBase s₀ := (k₁.gpr (by decide)).trans hm.layout.rsp
  have wr₁ : t₁.wr = v.wr := k₁.2.2.trans wrv
  have rd₁ : t₁.rd = v.rd := k₁.2.1.trans rdv
  obtain ⟨V₁, R₁⟩ := hm₁.rep
  have w19 : ∀ a b : BitVec 64, ((t₁.mem.writeW (stackArg s₀ 1) a).writeW (off (stackArg s₀ 1) 24) b).readW
      (off (refillBase s₀) 152) 64 = W 19 := fun a b => by
    rw [past_state (frame_state h (d := 152) (by decide))]
    exact R₁.slot (d := 152) (k := 19) rfl (by decide) rfl
  rcases cases with ⟨h19, c, hc, c3, htot⟩ | ⟨h19, c, k, hc, c3, c2, hk, htot⟩ | ⟨h19, a, u, hu, h16, htot, bytes⟩
  · -- no seeds left
    refine WP.ite false (by simp only [eval, z₁, h19]; rfl) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono (wordsAccepted_ok (env t₁ sp₁ wr₁) (by rw [mem₁]; exact c1) w19)
      fun t₂ ⟨⟨mem₂, z₂⟩, k₂⟩ => ?_)
    refine WP.ite false (by simp only [eval, z₂, h19]; rfl) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    have sp₂ : t₂.gpr .rsp = refillBase s₀ := (k₂.gpr (by decide)).trans sp₁
    have wr₂ : t₂.wr = v.wr := k₂.2.2.trans wr₁
    refine WP.mono (usedWord_ok sp₂ (env t₂ sp₂ wr₂).us ((env t₂ sp₂ wr₂).ctl 0 (by decide))
      (by rw [mem₂]; exact (ctlR (k := 0) (by decide) (ctlM mem₁) 0 0).trans c0) (x := BitVec.ofNat 64 c) (eaCtl t₂ 3 sp₂)
      ((env t₂ sp₂ wr₂).ctl 3 (by decide)) (by rw [mem₂]; exact (ctlR (k := 3) (by decide) (ctlM mem₁) 0 0).trans c3))
      fun t₃ ⟨mem₃, k₃⟩ => ?_
    have fw : Frame [inState s₀, inUsed s₀] t₁.mem t₃.mem := by
      rw [mem₃, mem₂]; exact written_frame t₁.mem _ _ _ _ _
    refine ⟨hs, W, t.mem, 0, 0, BitVec.ofNat 64 c, hin,
      genMem_written h hin hm₁ fw ((k₃.gpr (by decide)).trans (k₂.gpr (by decide))) (k₃.2.1.trans k₂.2.1)
        (k₃.2.2.trans k₂.2.2), fv, by rw [mem₃, mem₂, mem₁] <;> rfl, by rw [htot] <;> rfl, by rw [htot] <;> rfl,
      by rw [htot] <;> rfl, by rw [h19, htot] <;> rfl, Or.inl ⟨by rw [h19]; decide, by rw [htot] <;> rfl⟩,
      (k₃.gpr (by decide)).trans sp₂, k₃.2.1.trans (k₂.2.1.trans rd₁), k₃.2.2.trans wr₂⟩
  · -- the tape ran out
    refine WP.ite true (by simp only [eval, z₁, h19]; rfl) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    apply WP.seq
    refine WP.mono (ranOut_ok hm₁ ((env t₁ sp₁ wr₁).ctl 3 (by decide)) (by rw [mem₁]; exact c3) h15 hc hlen hp)
      fun t₂ ⟨k₂, hr⟩ => ?_
    have sp₂ : t₂.gpr .rsp = refillBase s₀ := (k₂.gpr (by decide)).trans sp₁
    have wr₂ : t₂.wr = v.wr := k₂.2.2.trans wr₁
    rcases hr with ⟨hL, rdx₂, hm₂, mem₂⟩ | ⟨hL, hm₂, f₂⟩
    · refine WP.seq (WP.mono (zeroTest_ok hm₂) fun t₃ ⟨z₃, hm₃, mem₃, k₃⟩ => ?_)
      refine WP.ite true (by simp only [eval, z₃, h19]; rfl) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
      have sp₃ : t₃.gpr .rsp = refillBase s₀ := (k₃.gpr (by decide)).trans sp₂
      have wr₃ : t₃.wr = v.wr := k₃.2.2.trans wr₂
      have m₃ : t₃.mem = t.mem := mem₃.trans (mem₂.trans mem₁)
      refine WP.mono (wordsEntropy_ok (env t₃ sp₃ wr₃) (K := BitVec.ofNat 64 k) (by rw [m₃]; exact c1) (by rw [m₃]; exact c2)
        (fun a b => (ctlR (k := 3) (by decide) (ctlM m₃) a b).trans c3)
        (fun a b => (ctlR (k := 0) (by decide) (ctlM m₃) a b).trans c0)) fun t₄ ⟨mem₄, k₄⟩ => ?_
      have fw : Frame [inState s₀, inUsed s₀] t₃.mem t₄.mem := by rw [mem₄]; exact written_frame t₃.mem _ _ _ _ _
      have hL' : ¬Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega
      refine ⟨hs, W, t.mem, BitVec.ofNat 64 k, t₃.gpr .rdx, BitVec.ofNat 64 c, hin,
        genMem_written h hin hm₃ fw (k₄.gpr (by decide)) k₄.2.1 k₄.2.2, fv, by rw [mem₄, m₃], ?_, ?_, ?_, ?_,
        Or.inl ⟨by rw [h19]; decide, ?_⟩, (k₄.gpr (by decide)).trans sp₃, k₄.2.1.trans (k₃.2.1.trans (k₂.2.1.trans rd₁)),
        k₄.2.2.trans wr₃⟩
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte]
      all_goals first | rfl | (rw [(k₃.gpr (by decide)).trans rdx₂]; rfl) | (rw [h19]; rfl)
    · obtain ⟨V₂, R₂⟩ := hm₂.rep
      refine WP.seq (WP.mono (zeroTest_ok hm₂) fun t₃ ⟨z₃, hm₃, mem₃, k₃⟩ => ?_)
      refine WP.ite false (by simp only [eval, z₃, upd]; rfl) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
      have sp₃ : t₃.gpr .rsp = refillBase s₀ := (k₃.gpr (by decide)).trans sp₂
      have wr₃ : t₃.wr = v.wr := k₃.2.2.trans wr₂
      have cw : ∀ {k}, k < 4 → ctlWord t₃.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun hk => by
        rw [mem₃, ctlWord_changed h f₂ hk, mem₁]
      refine WP.mono (wordsZero_ok (env t₃ sp₃ wr₃) (by rw [← c1]; exact cw (k := 1) (by decide))
        (fun a b => (ctlR (k := 3) (by decide) (cw (by decide)) a b).trans c3)
        (fun a b => (ctlR (k := 0) (by decide) (cw (by decide)) a b).trans c0)) fun t₄ ⟨mem₄, k₄⟩ => ?_
      have fw : Frame [inState s₀, inUsed s₀] t₃.mem t₄.mem := by rw [mem₄]; exact written_frame t₃.mem _ _ _ _ _
      have hL' : Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega
      refine ⟨hs, upd W 19 2, t₂.mem, 0, 0, BitVec.ofNat 64 c, hin,
        genMem_written h hin hm₃ fw (k₄.gpr (by decide)) k₄.2.1 k₄.2.2,
        fv.trans ((mem₁ ▸ f₂).mono fun r hr => List.mem_cons_of_mem _ hr), by rw [mem₄, mem₃], ?_, ?_, ?_, ?_,
        Or.inl ⟨by simp [upd], ?_⟩, (k₄.gpr (by decide)).trans sp₃, k₄.2.1.trans (k₃.2.1.trans (k₂.2.1.trans rd₁)),
        k₄.2.2.trans wr₃⟩
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte]
      all_goals rfl
  · -- parameters
    refine WP.ite false (by simp only [eval, z₁, h19]; rfl) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono (wordsAccepted_ok (env t₁ sp₁ wr₁) (by rw [mem₁]; exact c1) w19)
      fun t₂ ⟨⟨mem₂, z₂⟩, k₂⟩ => ?_)
    refine WP.ite true (by simp only [eval, z₂, h19]; rfl) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    have sp₂ : t₂.gpr .rsp = refillBase s₀ := (k₂.gpr (by decide)).trans sp₁
    have wr₂ : t₂.wr = v.wr := k₂.2.2.trans wr₁
    refine WP.mono (usedWord_ok sp₂ (env t₂ sp₂ wr₂).us ((env t₂ sp₂ wr₂).ctl 0 (by decide))
      (by rw [mem₂]; exact (ctlR (k := 0) (by decide) (ctlM mem₁) 0 0).trans c0) (x := BitVec.ofNat 64 u) (eaSp t₂ 128 sp₂)
      ((env t₂ sp₂ wr₂).frame 128 (by decide))
      (by rw [mem₂, past_state (frame_state h (d := 128) (by decide))]
          exact R₁.slot (d := 128) (k := 16) rfl (by decide) h16))
      fun t₃ ⟨mem₃, k₃⟩ => ?_
    have fw : Frame [inState s₀, inUsed s₀] t₁.mem t₃.mem := by
      rw [mem₃, mem₂]; exact written_frame t₁.mem _ _ _ _ _
    refine ⟨hs, W, t.mem, 0, 0, BitVec.ofNat 64 u, hin,
      genMem_written h hin hm₁ fw ((k₃.gpr (by decide)).trans (k₂.gpr (by decide))) (k₃.2.1.trans k₂.2.1)
        (k₃.2.2.trans k₂.2.2), fv, by rw [mem₃, mem₂, mem₁] <;> rfl, by rw [htot] <;> rfl, by rw [htot] <;> rfl,
      by rw [htot] <;> rfl, by rw [h19, htot] <;> rfl, Or.inr ⟨h19, a, by rw [htot] <;> rfl, ?_⟩,
      (k₃.gpr (by decide)).trans sp₂, k₃.2.1.trans (k₂.2.1.trans rd₁), k₃.2.2.trans wr₂⟩
    rw [VG.Proof.Dsa.Generation.frame_bytesAt fw packedSub (by unfold Spec.Dsa.generationQLen; split <;> omega), mem₁]
    exact bytes

end

end VG.Proof.Dsa.X86_64.Generation.Refill
