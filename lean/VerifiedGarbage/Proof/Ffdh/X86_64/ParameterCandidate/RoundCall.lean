module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundResult`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundStatus`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: count accepted passing rounds -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Rsa.X86_64.Crt
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def passStatus (i checks : Nat) : Nat := if i + 1 < checks then 4 else 1

def passMem (m : Mem) (O : Addr) (i checks : Nat) : Mem :=
  (m.writeW (off O (8 * oIndex)) (BitVec.ofNat 64 (i + 1))).writeW
    (off O (8 * oStatus)) (BitVec.ofNat 64 (passStatus i checks))

theorem roundPass_ok {s : State} {B O : Addr} {Z i checks : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hi : word s.mem O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31) :
    WP isa (.block roundPass) s fun t => t.mem = passMem s.mem O i checks ∧
      Keep [.r9, .rcx, .rax, .rdx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 := fun j hj => ho.ld (by omega_using [hj])
  have hwr : ∀ j < 32, InRegions s.wr (off O (8 * j)) 8 := fun j hj => ho.st (by omega_using [hj])
  have hcf : decide ((BitVec.ofNat 64 (i + 1)).toNat < (BitVec.ofNat 64 checks).toNat) = decide (i + 1 < checks) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi32] : i + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hc32] : checks < 2 ^ 64)]
  have hstatus : (if !decide (i + 1 < checks) then (1#32).setWidth 64 else (4#32).setWidth 64) =
      BitVec.ofNat 64 (passStatus i checks) := by
    by_cases h : i + 1 < checks <;> simp [passStatus, h]
  refine WP.mono (WP.keep [.r9, .rcx, .rax, .rdx] (Q := fun t => t.mem = passMem s.mem O i checks)
    ?_ rfl) fun t ⟨hm, k⟩ => ⟨hm, k⟩
  xrun [roundPass, passMem, State.ea, hdr, hdi, hdrOff, ws, hl,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oIndex (by decide), hrd oChecks (by decide), hwr oIndex (by decide), hwr oStatus (by decide), hi, hc,
    hdrStore_hdr _ _ _ (i := oIndex) (k := oChecks) (by decide) (by decide) (by decide),
    ofNat_add_one, hcf, cmov_reg_value, eval]
  congr 1

theorem passMem_frame (m : Mem) (O : Addr) (i checks : Nat) :
    Frm O [(8 * oIndex, 16)] m (passMem m O i checks) := by
  unfold passMem
  exact (Frm.of_outside ((writeW_outside m O (d := 8 * oIndex) _ (by decide)).mono
    (o' := 8 * oIndex) (n' := 16) (by decide) (by decide)) (by simp)).trans
    (Frm.of_outside ((writeW_outside _ O (d := 8 * oStatus) _ (by decide)).mono
      (o' := 8 * oIndex) (n' := 16) (by decide) (by decide)) (by simp))

theorem passMem_index (m : Mem) (O : Addr) (i checks : Nat) :
    word (passMem m O i checks) O (8 * oIndex) = BitVec.ofNat 64 (i + 1) := by
  unfold passMem
  rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem passMem_status (m : Mem) (O : Addr) (i checks : Nat) :
    word (passMem m O i checks) O (8 * oStatus) = BitVec.ofNat 64 (passStatus i checks) := by
  unfold passMem
  exact word_writeW_self _ _ _ _

theorem roundFail_ok {s : State} {B O : Addr} {Z : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O) :
    WP isa (.block roundFail) s fun t => t.mem = s.mem.writeW (off O (8 * oStatus)) (2#64) ∧
      Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off O (8 * oStatus)) (2#64))
    ?_ rfl) fun t ⟨hm, k⟩ => ⟨hm, k⟩
  xrun [roundFail, State.ea, hdr, hdi, hdrOff, ws, hl,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz), ho.st (d := 8 * oStatus) (by decide)]
  rfl

theorem roundFlag_ok {s : State} {B : Addr} {Z : Nat} {pass : Bool}
    (hs : Scr s B Z) (hz : 184 ≤ Z) (hdi : s.gpr .rdi = B)
    (hf : word s.mem B (8 * kFlag) = mask pass) :
    WP isa (.block [.mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!pass) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hm : (mask pass == 0) = !pass := by
    cases pass
    · rfl
    · change (BitVec.allOnes 64 == 0) = false
      decide +kernel
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!pass) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hzf, hmem⟩, k⟩ => ⟨hzf, hmem, k⟩
  xrun [State.ea, hdr, hdi, hdrOff, hf, hs.ld (d := 8 * kFlag) (by change 184 ≤ Z; exact hz),
    BitVec.and_self, hm]

theorem statusTest_ok {s : State} {B O : Addr} {Z n : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hn : word s.mem O (8 * oStatus) = BitVec.ofNat 64 n) (hn64 : n < 2 ^ 64) :
    WP isa (.block statusTest) s fun t => t.zf = some (decide (n = 0)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (n = 0)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨hzf, hm⟩, k⟩ => ⟨hzf, hm, k⟩
  xrun [statusTest, State.ea, hdr, hdi, hdrOff, ws, hl, hn,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz), ho.ld (d := 8 * oStatus) (by decide),
    BitVec.and_self]
  simpa only [BitVec.sub_zero] using ofNat_sub_beq (N := 0) hn64 (by decide)

theorem statusMore_ok {s : State} {B O : Addr} {Z n : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hn : word s.mem O (8 * oStatus) = BitVec.ofNat 64 n) (hn64 : n < 2 ^ 64) :
    WP isa (.block statusMore) s fun t => t.zf = some (decide (n = 4)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (n = 4)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨hzf, hm⟩, k⟩ => ⟨hzf, hm, k⟩
  xrun [statusMore, State.ea, hdr, hdi, hdrOff, ws, hl, hn,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz), ho.ld (d := 8 * oStatus) (by decide),
    show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 from by decide]
  exact ofNat_sub_beq hn64 (by decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: composite or next accepted round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)

theorem roundResult_ok {p : WitnessParams} {rp : Addr} {used i checks : Nat} {pass : Bool}
    {bs : List Byte} {s : State} (h : DrawState p rp used bs s)
    (hflag : word s.mem p.I (8 * kFlag) = mask pass)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31) :
    WP isa roundResult s fun t => DrawState p rp used bs t ∧
      word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (if pass then passStatus i checks else 2) ∧
      word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (if pass then i + 1 else i) ∧
      RoundSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have h184 : 184 ≤ p.IZ := by
    have hz := p.dims.z
    unfold slot VG.Impl.Bignum.hdrBytes at hz
    omega_using [hz]
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold roundResult
  refine WP.seq (WP.mono (roundFlag_ok h.ready.good.scr h184 h.ready.good.rdi hflag)
    fun u ⟨hz, hm, k⟩ => ?_)
  have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
  have hiu : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 i := by rw [hm]; exact hi
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by rw [hm]; exact hc
  cases pass
  · refine WP.ite true (by simp only [eval, hz, Bool.not_false]) (fun _ => ?_) (by simp)
    refine WP.mono (roundFail_ok hu.ready.good.scr p.space_bounds.2.1 (houter.congr k.2.2)
      hu.ready.good.rdi hu.link) fun t ⟨hmt, kt⟩ => ?_
    obtain ⟨ht, _, hh, hf⟩ := hu.status_write (2#64) hmt kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    refine ⟨ht, ?_, ?_, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact word_writeW_self _ _ _ _
    · simpa only [Bool.false_eq_true, ↓reduceIte] using (hh _ (by decide) (by decide)).trans hiu
    · intro j hj _ _ _ _ h19
      rw [hh j hj h19, hm]
    · rw [← hm]; exact hf
  · refine WP.ite false (by simp only [eval, hz, Bool.not_true]) (by simp) (fun _ => ?_)
    refine WP.mono (roundPass_ok hu.ready.good.scr p.space_bounds.2.1 (houter.congr k.2.2)
      hu.ready.good.rdi hu.link hiu hcu hi32 hc32) fun t ⟨hmt, kt⟩ => ?_
    have hf : Frm p.O [(8 * oIndex, 16)] u.mem t.mem := by rw [hmt]; exact passMem_frame _ _ _ _
    have hlo : ∀ r ∈ [(8 * oIndex, 16)], 136 ≤ r.1 := by simp [oIndex]
    have hhi : ∀ r ∈ [(8 * oIndex, 16)], r.1 + r.2 ≤ 256 := by simp [oIndex]
    have ht := hu.outer_frame hf hlo hhi kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    refine ⟨ht, ?_, ?_, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact passMem_status _ _ _ _
    · rw [hmt]; exact passMem_index _ _ _ _
    · intro j hj _ _ _ h18 h19
      rw [hf.word_eq (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        change 8 * j + 8 ≤ 144 ∨ 160 ≤ 8 * j
        omega_using [h18, h19]) (by omega_using [hj]), hm]
    · rw [← hm]
      exact DrawFrame.of_scr (InScr.of_frm hf (fun r hr => Nat.le_trans (hhi r hr) p.space_bounds.1))

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawLoop`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.CutRestore`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.TapeHead`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: random-tape header operations -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Rsa.X86_64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem drawHead_ok {s : State} {B O : Addr} {Z left len : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hle : word s.mem O (8 * oRandLeft) = BitVec.ofNat 64 left)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len)
    (hleft : left < 2 ^ 64) (hln : len < 2 ^ 64) :
    WP isa (.block drawHead) s fun t => t.cf = some (decide (left < len)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega_using [hj])
  refine WP.mono (WP.keep [.rax, .rcx]
    (Q := fun t => t.cf = some (decide (left < len)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, k⟩
  xrun [drawHead, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oRandLeft (by decide), hrd oWitnessLen (by decide), hle, hlen]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hln]

theorem drawShort_ok {s : State} {B O : Addr} {Z : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O) :
    WP isa (.block drawShort) s fun t =>
      t.mem = s.mem.writeW (off O (8 * oStatus)) (0#64) ∧
      t.zf = some false ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off O (8 * oStatus)) (0#64) ∧ t.zf = some false) ?_ rfl)
    fun t ⟨⟨hm, hf⟩, k⟩ => ⟨hm, hf, k⟩
  xrun [drawShort, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    ho.st (d := 8 * oStatus) (by unfold oStatus; omega_using [])]
  rfl

theorem drawFinish_ok {s : State} {B O : Addr} {Z : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O) :
    WP isa (.block drawFinish) s fun t =>
      t.mem = s.mem.writeW (off O (8 * oStatus)) (1#64) ∧
      t.zf = s.zf ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off O (8 * oStatus)) (1#64) ∧ t.zf = s.zf) ?_ rfl)
    fun t ⟨⟨hm, hf⟩, k⟩ => ⟨hm, hf, k⟩
  xrun [drawFinish, State.ea, hdr, hdi, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    ho.st (d := 8 * oStatus) (by unfold oStatus; omega_using [])]
  rfl

theorem drawLoad_ok {s : State} {B O op : Addr} {Z len : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hbp : s.gpr .rbp = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hop : word s.mem O (8 * oOut) = op)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len) :
    WP isa (.block drawLoad) s fun t => t.gpr .rdi = B ∧ t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.mem = s.mem ∧ Keep [.rdi, .rax, .rsi, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega_using [hj])
  refine WP.mono (WP.keep [.rdi, .rax, .rsi, .rcx] (Q := fun t => t.gpr .rdi = B ∧ t.gpr .rsi = op ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hd, hr, hc, hm⟩, k⟩ => ⟨hd, hr, hc, hm, k⟩
  xrun [drawLoad, State.ea, hdr, hbp, hdrOff, ws, hl, hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oOut (by decide), hrd oWitnessLen (by decide), hop, hlen]

/-- Advancing a draw keeps the old pointer in RSI for the masked copy. -/
theorem drawSetup_ok {s : State} {B O op rp : Addr} {Z len bits left used : Nat}
    (hs : Scr s B Z) (hz : 136 ≤ Z) (ho : Scr s O 256) (hdi : s.gpr .rdi = B)
    (hl : word s.mem B (8 * sLink) = O)
    (hop : word s.mem O (8 * oOut) = op)
    (hp : word s.mem O (8 * oRandPtr) = rp)
    (hle : word s.mem O (8 * oRandLeft) = BitVec.ofNat 64 left)
    (hu : word s.mem O (8 * oUsed) = BitVec.ofNat 64 used)
    (hlen : word s.mem O (8 * oWitnessLen) = BitVec.ofNat 64 len)
    (hb : word s.mem O (8 * oWitnessBits) = BitVec.ofNat 64 bits)
    (hln : len < 2 ^ 64) (hleft : len ≤ left) :
    WP isa (.block drawSetup) s fun t =>
      t.mem = ((s.mem.writeW (off O (8 * oRandPtr)) (off rp len)).writeW
        (off O (8 * oRandLeft)) (BitVec.ofNat 64 (left - len))).writeW
        (off O (8 * oUsed)) (BitVec.ofNat 64 (used + len)) ∧
      t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rbp = B ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 bits ∧
      Keep [.rax, .rsi, .rcx, .rdx, .r8, .rbp, .rdi] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off O (8 * j)) 8 :=
    fun j hj => ho.ld (by omega_using [hj])
  have hwr : ∀ j < 32, InRegions s.wr (off O (8 * j)) 8 := fun j hj => ho.st (by omega_using [hj])
  have hskip (m : Mem) (v : BitVec 64) {i j : Nat} (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
      word (m.writeW (off O (8 * i)) v) O (8 * j) = word m O (8 * j) :=
    hdrStore_hdr m O v hi hj hne
  have hsub : BitVec.ofNat 64 left - BitVec.ofNat 64 len = BitVec.ofNat 64 (left - len) :=
    BitVec.ofNat_sub_ofNat_of_le left len hln hleft
  refine WP.mono (WP.keep [.rax, .rsi, .rcx, .rdx, .r8, .rbp, .rdi] (Q := fun t =>
    t.mem = ((s.mem.writeW (off O (8 * oRandPtr)) (off rp len)).writeW
      (off O (8 * oRandLeft)) (BitVec.ofNat 64 (left - len))).writeW
      (off O (8 * oUsed)) (BitVec.ofNat 64 (used + len)) ∧
    t.gpr .rsi = rp ∧ t.gpr .rdi = op ∧ t.gpr .rbp = B ∧
    t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 bits) ?_ rfl)
    fun t ⟨⟨hm, hp', ho', hb', hc, hd⟩, k⟩ => ⟨hm, hp', ho', hb', hc, hd, k⟩
  xrun [drawSetup, State.ea, hdr, hdi, hdrOff, ws, hl,
    hs.ld (d := 8 * sLink) (by change 136 ≤ Z; exact hz),
    hrd oRandPtr (by decide), hrd oWitnessLen (by decide), hrd oWitnessBits (by decide),
    hrd oRandLeft (by decide), hrd oUsed (by decide), hrd oOut (by decide),
    hwr oRandPtr (by decide), hwr oRandLeft (by decide), hwr oUsed (by decide),
    hp, hlen, hb, hle, hu, hop,
    hskip (i := oRandPtr) (j := oRandLeft) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandPtr) (j := oUsed) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandLeft) (j := oUsed) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandPtr) (j := oOut) _ _ (by decide) (by decide) (by decide),
    hskip (i := oRandLeft) (j := oOut) _ _ (by decide) (by decide) (by decide),
    hskip (i := oUsed) (j := oOut) _ _ (by decide) (by decide) (by decide), hsub,
    BitVec.ofNat_add_ofNat]

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: mask a draw and restore the modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem cutRestore_ok {p : WitnessParams} {s₀ s : State} {rp : Addr} {bs : List Byte}
    (hready : ModulusReady s₀ p.I p.IZ p.w p.mi p.N) (hwr : s.wr = s₀.wr)
    (hwords : ∀ d, d + 8 ≤ p.IZ → word s.mem p.I d = word s₀.mem p.I d)
    (hs : Scr s p.O p.Z) (hl : word s.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O)
    (hop : word s.mem p.O (8 * oOut) = p.op)
    (hlen : word s.mem p.O (8 * oWitnessLen) = BitVec.ofNat 64 p.len)
    (hdi : s.gpr .rdi = p.op) (hsi : s.gpr .rsi = rp) (hbp : s.gpr .rbp = p.I)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 p.len) (hdx : s.gpr .rdx = BitVec.ofNat 64 p.bits)
    (hsrc : Src s p.O p.Z rp bs) (ho : OutOk s p.O p.Z p.op p.len)
    (ha : Apart p.op p.len rp bs.length) (hbl : bs.length = p.len) :
    WP isa cutRestore s fun t => ModulusReady t p.I p.IZ p.w p.mi p.N ∧
      t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.len) = Spec.Rsa.os2ip bs % 2 ^ p.bits ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.O d = word s.mem p.O d) ∧
      (∀ d, d + 8 ≤ p.IZ → word t.mem p.I d = word s.mem p.I d) ∧
      DrawFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) hs.nowrap
  have hiz64 : p.IZ ≤ 2 ^ 64 := by unfold WitnessParams.IZ; omega_using [hz64]
  have hi := output_inner ho hz64
  have hb1 : 16 ≤ p.bits := by have := p.bits1; omega_using [this]
  have hlen' : bs.length = (p.bits + 7) / 8 := hbl
  have hcount : s.gpr .rcx = BitVec.ofNat 64 bs.length := by rw [hbl]; exact hcx
  unfold cutRestore
  refine WP.seq (WP.mono (witnessCut_ok hb1 p.bits2 hlen' hsi hdi hcount hdx hsrc.rd
    (fun i hi => ho.wr i (by omega_using [hbl, hi]))
    (fun i hi => by
      rw [hsrc.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => ha j (by omega_using [hbl, hj]) i hi he.symm)) fun u ⟨_, hv, hf, k⟩ => ?_)
  have hf' : ∀ a, (∀ i < p.len, a ≠ off p.op i) → u.mem a = s.mem a := by
    simpa only [hbl] using hf
  have hwO := words_outside_bytes hz64 hf' ho.sep
  have hwI := words_outside_bytes hiz64 hf' hi.sep
  have hI136 : 136 ≤ p.IZ := by
    have hroom := p.room
    unfold WitnessParams.IZ
    simp only [slot, VG.Impl.Bignum.hdrBytes] at hroom
    omega_using [hroom]
  have hsO : Scr u p.O 256 := by
    have hsize : 256 ≤ p.Z := by have := p.room; omega_using [this]
    simpa [off] using (hs.congr k.2.2).sub (o := 0) (n := 256) (by omega_using [hsize]) (by decide)
  have hlink : word u.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [hwI _ (by change 136 ≤ p.IZ; exact hI136)]
    exact hl
  have hOut : word u.mem p.O (8 * oOut) = p.op := by
    rw [hwO _ (by have := p.room; unfold oOut; omega_using [this])]
    exact hop
  have hLen : word u.mem p.O (8 * oWitnessLen) = BitVec.ofNat 64 p.len := by
    rw [hwO _ (by have := p.room; unfold oWitnessLen; omega_using [this])]
    exact hlen
  refine WP.mono (drawLoad_ok (hready.good.scr.congr (k.2.2.trans hwr)) hI136 hsO
    ((k.gpr (by decide)).trans hbp) hlink hOut hLen) fun t ⟨hdt, hst, hct, hmt, kt⟩ => ?_
  have hwOt : ∀ d, d + 8 ≤ p.Z → word t.mem p.O d = word s.mem p.O d := by
    intro d hd; rw [hmt]; exact hwO d hd
  have hwIt : ∀ d, d + 8 ≤ p.IZ → word t.mem p.I d = word s.mem p.I d := by
    intro d hd; rw [hmt]; exact hwI d hd
  refine ⟨hready.of_words p.dims (fun d hd => (hwIt d hd).trans (hwords d hd))
    (kt.2.2.trans (k.2.2.trans hwr)) hdt, hst, hct, ?_, hwOt, hwIt, ?_,
    (k.trans kt).mono (by decide)⟩
  · rw [hmt]
    simpa only [hbl] using hv
  · rw [hmt]
    exact DrawFrame.of_bytes hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawBody`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawPrefix`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.LoadWitness`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: load a masked witness into Xm -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem loadWitness_ok {p : WitnessParams} {s : State}
    (h : ModulusReady s p.I p.IZ p.w p.mi p.N)
    (ho : OutOk s p.I p.IZ p.op p.len)
    (hsi : s.gpr .rsi = p.op) (hcx : s.gpr .rcx = BitVec.ofNat 64 p.len)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) < 2 ^ (64 * p.w)) :
    WP isa (loadNumber aXm) s fun t =>
      ModulusReady t p.I p.IZ p.w p.mi p.N ∧
      wv t.mem p.I (slot p.w aXm) p.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.len) ∧
      Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.len
  have hlen : bs.length = p.len := bytesAt_length _ _ _
  have hw : p.w = (bs.length + 7) / 8 := by rw [hlen]; exact p.width
  have hb := p.width_bounds
  have hcx' : s.gpr .rcx = BitVec.ofNat 64 bs.length := by rw [hlen]; exact hcx
  refine WP.mono (loadNumber_ok (by decide : aXm < 8) h.good p.dims.z hsi hcx'
    (by omega_using [hlen, hb.2.2.1]) (by omega_using [hlen, hb.2.2.2.1])
    (by omega_using [hw]) (by omega_using [hw]) hv
    (fun i hi => by
      obtain ⟨r, hr, hc⟩ := ho.wr i (by omega_using [hlen, hi])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun i hi => bytesAt_read _ _ (by omega_using [hlen, hi] : i < p.len))
    (fun i hi => Or.inr (by
      have hs := ho.sep i (by omega_using [hlen, hi])
      change p.IZ ≤ ofs p.I (off p.op i) at hs
      have hf := slot_le (w := p.w) (show aXm < 8 by decide)
      omega_using [hs, hf, hw, p.dims.z]))) fun t ⟨hv', hg, hf, k⟩ => ?_
  have hf' : Frm p.I [(slot p.w aXm, 8 * (p.w + 2))] s.mem t.mem :=
    Frm.of_outside (hf.mono (o' := slot p.w aXm) (n' := 8 * (p.w + 2)) (Nat.le_refl _) (by omega_using [hw])) (by simp)
  refine ⟨h.of_frm p.dims hf' k hg.rdi (by rng_disj) (by rng_disj) (by rng_disj), hv', hf',
    k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: consume, mask and load one draw -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem drawPrefix_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (havail : p.len ≤ bs.length) :
    WP isa drawPrefix s fun t =>
      DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits ∧
      (∀ j < 32, word t.mem p.O (8 * j) =
        word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j)) ∧
      DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  have hl64 : p.len < 2 ^ 64 := by omega_using [p.width_bounds.2.2.2.1]
  unfold drawPrefix cutLoad
  refine WP.seq (WP.mono (drawSetup_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
    h.link h.outPtr h.ptr h.left h.usedWord h.len h.bits hl64 havail)
    fun u ⟨hm, hsi, hdi, hbp, hcx, hdx, k⟩ => ?_)
  have hmem : u.mem = advanceMem s.mem p.O rp p.len bs.length used := hm
  have hfa : Frm p.O [(8 * oRandPtr, 24)] s.mem u.mem := by rw [hmem]; exact advanceMem_frame _ _ _ _ _ _
  have hfai : InScr p.O p.Z s.mem u.mem :=
    InScr.of_frm hfa (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      change 120 ≤ p.Z
      omega_using [p.space_bounds.1])
  have hwI : ∀ d, d + 8 ≤ p.IZ → word u.mem p.I d = word s.mem p.I d :=
    outer_words hfa (by simp [oRandPtr]) (by omega_using [p.space_bounds.2.2, hz64])
  have hstatic : ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → word u.mem p.O (8 * j) = word s.mem p.O (8 * j) := by
    intro j hj h12 h13 h14
    apply hfa.word_eq
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j
      omega_using [h12, h13, h14]
    · omega_using [hj]
  have hsrc := source_take (h.rand.congrK hfai k) p.len
  have ho : OutOk u p.O p.Z p.op p.len :=
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩
  refine WP.seq (WP.mono (cutRestore_ok h.ready k.2.2 hwI (h.scr.congr k.2.2)
    ((hwI _ p.space_bounds.2.1).trans h.link)
    ((hstatic _ (by decide) (by decide) (by decide) (by decide)).trans h.outPtr)
    ((hstatic _ (by decide) (by decide) (by decide) (by decide)).trans h.len)
    hdi hsi hbp hcx hdx hsrc ho
    (fun i hi j hj => h.apart i hi j (by rw [List.length_take] at hj; omega_using [hj]))
    (by rw [List.length_take, Nat.min_eq_left havail]))
    fun v ⟨hrv, hsiv, hcxv, hv, hwO, hwIv, hfv, kv⟩ => ?_)
  have hkov := k.trans kv
  have hov : OutOk v p.O p.Z p.op p.len :=
    ⟨fun i hi => by rw [hkov.2.2]; exact h.out.wr i hi, h.out.sep⟩
  have hval : Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem p.op p.len) < 2 ^ (64 * p.w) := by
    rw [hv]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) p.width_bounds.2.2.2.2)
  refine WP.mono (loadWitness_ok hrv (output_inner hov hz64) hsiv hcxv hval)
    fun t ⟨hrt, hxm, hft, kt⟩ => ?_
  have hfit : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], r.1 + r.2 ≤ p.IZ := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact Nat.le_trans (slot_le (w := p.w) (show aXm < 8 by decide)) p.dims.z
  have hh : ∀ j < 32, word t.mem p.O (8 * j) =
      word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j) := by
    intro j hj
    rw [inner_header hft hfit hz64 j hj, hwO _ (by omega_using [hj, p.space_bounds.1]), hmem]
  have hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [inner_link hft (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      unfold slot VG.Impl.Bignum.hdrBytes aXm
      omega_using []), hwIv (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1,
      hwI (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1]
    exact h.link
  have hf : DrawFrame p s.mem t.mem :=
    ((DrawFrame.of_scr hfai).trans hfv).trans (DrawFrame.of_inner hft hfit hz64)
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' : Keep mmRegs s t := keep_modulus kk (hrt.good.rdi.trans h.ready.good.rdi.symm)
  refine ⟨h.after_sample havail hrt hl (fun j hj _ => hh j hj) hf kk', ?_, hh, hf, kk'⟩
  rw [hxm, hv]

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: checked draw or tape exhaustion -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/DrawSample.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: one rejection-sampling iteration -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem drawSample_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (havail : p.len ≤ bs.length) :
    WP isa drawSample s fun t =>
      let a := Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits
      DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = a ∧ t.zf = some (!decide (2 ≤ a ∧ a < p.N - 1)) ∧
      word t.mem p.O (8 * oStatus) = 1 ∧
      (∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) =
        word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j)) ∧
      DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  unfold drawSample
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (drawPrefix_ok h havail) fun u ⟨hu, hx, hh, hf, k⟩ => ?_)
  refine WP.seq (WP.mono (witnessRange_ok hu.ready p.dims p.odd hx)
    fun v ⟨_, hz, hrv, hxv, hfr, kr⟩ => ?_)
  have hfit : ∀ r ∈ [(slot p.w aTmp, 8 * p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)],
      r.1 + r.2 ≤ p.IZ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hb := slot_le (w := p.w) (show aTmp < 8 by decide)
      omega_using [hb, p.dims.z]
    · change 248 ≤ p.IZ
      have hb := p.dims.z
      unfold slot VG.Impl.Bignum.hdrBytes at hb
      omega_using [hb]
  have hhlo : ∀ r ∈ [(slot p.w aTmp, 8 * p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)], 136 ≤ r.1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold slot VG.Impl.Bignum.hdrBytes aTmp; omega
    · decide
  have hhv := inner_header hfr hfit hz64
  have hfv := DrawFrame.of_inner hfr hfit hz64
  have hlv := (inner_link hfr hhlo).trans hu.link
  have hv := hu.transport hrv hlv (fun j hj _ => hhv j hj) hfv kr
  have houter : Scr v p.O 256 := by
    simpa [off] using hv.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (drawFinish_ok hv.ready.good.scr p.space_bounds.2.1 houter hv.ready.good.rdi hv.link)
    fun t ⟨hm, hzf, kt⟩ => ?_
  obtain ⟨ht, hxt, hht, hft⟩ := hv.status_write (1#64) hm kt ((kt.gpr (by decide)).trans hv.ready.good.rdi)
  refine ⟨ht, hxt.trans hxv, hzf.trans hz, ?_, ?_, (hf.trans hfv).trans hft,
    ((k.trans kr).trans kt).mono (by decide)⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro j hj hne
    exact ((hht j hj hne).trans (hhv j hj)).trans (hh j hj)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def drawValue (p : WitnessParams) (bs : List Byte) : Nat :=
  Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits

def DrawStep (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (s t : State) : Prop :=
  (if p.len ≤ bs.length then
    DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = drawValue p bs ∧
      t.zf = some (!decide (2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1)) ∧
      word t.mem p.O (8 * oStatus) = 1
   else DrawState p rp used bs t ∧ t.zf = some false ∧ word t.mem p.O (8 * oStatus) = 0) ∧
    DrawSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t

theorem drawBody_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) : WP isa drawBody s (DrawStep p rp used bs s) := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold drawBody
  refine WP.seq (WP.mono (drawHead_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
    h.link h.left h.len (by omega_using [h.countBound]) (by omega_using [p.width_bounds.2.2.2.1]))
    fun u ⟨hcf, hm, k⟩ => ?_)
  have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
  by_cases havail : p.len ≤ bs.length
  · refine WP.ite false (by simp [eval, hcf, show ¬bs.length < p.len by omega_using [havail]]) (by simp) (fun _ => ?_)
    refine WP.mono (drawSample_ok hu havail) fun t ⟨ht, hx, hz, hs, hh, hf, kt⟩ => ?_
    simp only [DrawStep, ite_eq_left havail]
    refine ⟨⟨ht, hx, hz, hs⟩, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · intro j hj h12 h13 h14 h19
      rw [hh j hj h19, advanceMem_saved _ _ _ _ _ _ j hj h12 h13 h14, hm]
    · rw [← hm]; exact hf
  · have hshort : bs.length < p.len := by omega_using [havail]
    refine WP.ite true (by simp [eval, hcf, hshort]) (fun _ => ?_) (by simp)
    have houteru : Scr u p.O 256 := houter.congr k.2.2
    refine WP.mono (drawShort_ok hu.ready.good.scr p.space_bounds.2.1 houteru hu.ready.good.rdi hu.link)
      fun t ⟨hmt, hz, kt⟩ => ?_
    obtain ⟨ht, _, hh, hf⟩ := hu.status_write (0#64) hmt kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    simp only [DrawStep, ite_eq_right havail]
    refine ⟨⟨ht, hz, ?_⟩, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact word_writeW_self _ _ _ _
    · intro j hj _ _ _ h19
      rw [hh j hj h19, hm]
    · rw [← hm]; exact hf

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: the terminating rejection loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawPost (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (s t : State) : Prop :=
  ∃ n, n ≤ bs.length ∧ DrawState p (off rp n) (used + n) (bs.drop n) t ∧
    (match Spec.Ffdh.drawWitness p.N bs with
      | none => word t.mem p.O (8 * oStatus) = 0
      | some (a, rest) => word t.mem p.O (8 * oStatus) = 1 ∧ rest = bs.drop n ∧
          wv t.mem p.I (slot p.w aXm) p.w = a) ∧
    t.zf = some false ∧ DrawSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t

private theorem draw_equation (p : WitnessParams) (bs : List Byte) :
    Spec.Ffdh.drawWitness p.N bs =
      if p.len ≤ bs.length then
        if 2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1
          then some (drawValue p bs, bs.drop p.len)
          else Spec.Ffdh.drawWitness p.N (bs.drop p.len)
      else none := by
  rw [VG.Proof.Ffdh.ParameterCandidate.drawWitness_eq (by
    rw [p.octets]; omega_using [p.width_bounds.2.2.1])]
  simp only [p.octets, p.predBits, drawValue]
  rfl

/-- Every retry consumes a positive number of bytes. Accepted witnesses,
exhaustion, and the exact consumed count agree with the octet-tape spec. -/
theorem drawWitness_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) : WP isa drawWitness s (DrawPost p rp used bs s) := by
  induction bs using (measure List.length).wf.induction generalizing rp used s with
  | h bs ih =>
    obtain ⟨trace, u, he, hstep, hs, hf, k⟩ := drawBody_ok h
    have hspec := draw_equation p bs
    by_cases havail : p.len ≤ bs.length
    · simp only [ite_eq_left havail] at hstep
      obtain ⟨hu, hx, hz, hstatus⟩ := hstep
      by_cases ha : 2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1
      · have hspec' : Spec.Ffdh.drawWitness p.N bs = some (drawValue p bs, bs.drop p.len) := by
          simpa only [ite_eq_left havail, ite_eq_left ha] using hspec
        have hzf : u.zf = some false := by simpa [ha] using hz
        refine ⟨_, u, Exec.loopExit he (by simp only [eval, hzf]), p.len, havail, hu, ?_, hzf, hs, hf, k⟩
        rw [hspec']
        exact ⟨hstatus, rfl, hx⟩
      · have hdrop : (bs.drop p.len).length < bs.length := by
          rw [List.length_drop]
          omega_using [havail, p.width_bounds.2.2.1]
        have hspec' : Spec.Ffdh.drawWitness p.N bs = Spec.Ffdh.drawWitness p.N (bs.drop p.len) := by
          simpa only [ite_eq_left havail, ite_eq_right ha] using hspec
        obtain ⟨trace', t, he', n, hn, ht, hr, hzt, hs', hf', k'⟩ := ih _ hdrop hu
        have hzf : isa.eval .e u = some true := by simp only [eval, hz, ha, decide_false, Bool.not_false]
        refine ⟨_, t, Exec.loopNext he hzf he', p.len + n, ?_, ?_, ?_, hzt, hs.trans hs', hf.trans hf',
          (k.trans k').mono (by decide)⟩
        · rw [List.length_drop] at hn
          omega_using [hn, havail]
        · simpa only [off_off, Nat.add_assoc, List.drop_drop] using ht
        · rw [hspec']
          simpa only [List.drop_drop] using hr
    · simp only [ite_eq_right havail] at hstep
      obtain ⟨hu, hz, hstatus⟩ := hstep
      have hspec' : Spec.Ffdh.drawWitness p.N bs = none := by simpa only [ite_eq_right havail] using hspec
      refine ⟨_, u, Exec.loopExit he (by simp only [eval, hz]), 0, by omega_using [], ?_, ?_, hz, hs, hf, k⟩
      · simpa [off] using hu
      · rw [hspec']; exact hstatus

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: reusable shared primality round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

theorem witnessRoundRanges_bounds (p : WitnessParams) :
    ∀ r ∈ witnessRoundRanges p.w, 136 ≤ r.1 ∧ r.1 + r.2 ≤ p.IZ := by
  have hz : 256 + 28 * (8 * (p.w + 2)) ≤ p.IZ := by
    have hr : 256 + (256 + 28 * (8 * (p.w + 2))) ≤ p.Z := p.room
    unfold WitnessParams.IZ
    omega_using [hr]
  simp only [witnessRoundRanges, Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    Caller.pad, slot, VG.Impl.Bignum.hdrBytes, aAcc, aTmp, aXm, VG.Impl.RsaKeyGen.X86_64.Candidate.aR1,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_using [hz]

theorem witnessRound_state_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used a : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hx : wv s.mem p.I (slot p.w aXm) p.w = a) :
    WP isa (witnessRound M.mm K.run) s fun t => DrawState p rp used bs t ∧
      word t.mem p.I (8 * VG.Impl.RsaKeyGen.X86_64.Candidate.kFlag) = mask (Spec.Ffdh.mrRound p.N a) ∧
      (∀ j < 32, word t.mem p.O (8 * j) = word s.mem p.O (8 * j)) ∧
      RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have hrs := witnessRoundRanges_bounds p
  have hfit : ∀ r ∈ witnessRoundRanges p.w, r.1 + r.2 ≤ p.IZ := fun r hr => (hrs r hr).2
  refine WP.mono (witnessRound_ok M K h.ready p.dims (by omega_using [p.room, p.space_bounds.2.2]) hroom.call p.odd p.n3 hx)
    fun t ⟨hrt, hflag, hf, k⟩ => ?_
  have hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [hf.word_eq (d := 8 * VG.Impl.Rsa.X86_64.Crt.sLink) (fun r hr => Or.inl (hrs r hr).1) p.space_bounds.2.1 h.ready.good.scr.nowrap (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hroom.call.disjoint)]
    exact h.link
  have hh := round_outer_header hroom hf hfit hz64
  have hframe := RoundFrame.of_inner hf hfit hz64
  exact ⟨h.after_round hroom hrt hl hh hframe k, hflag, hh, hframe, k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
