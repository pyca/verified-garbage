module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.RsaKeyGen.Table

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
