module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
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
    (hsr : InRegions (s.rd ++ s.wr) (s.ea src) 8) (hx : s.mem.readW (s.ea src) 64 = x) :
    WP isa (.block [.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0)),
        .store (VG.Impl.Bignum.X86_64.at0 .rcx) .rax]) s
      fun t => t.mem = s.mem.writeW U x ∧ Keep [.rax, .rcx] s t := by
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp, ea_at0', hsp,
    hsr, hx, hus, h0r, h0]

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

end VG.Proof.Dsa.X86_64.Generation.Refill
